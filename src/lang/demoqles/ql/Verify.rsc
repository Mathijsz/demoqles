module lang::demoqles::ql::Verify

import lang::demoqles::ql::QL;
import lang::demoqles::ql::Flatten;
import lang::demoqles::ql::Bind;
import lang::demoqles::ql::Check; // for use/def

import Set;
import IO;
import ParseTree;
import Relation;
import List;
import util::ShellExec;
import String;
import Message;
/*
 To check
 
 - determinism
 - reachability
 - use when defined
 
*/

//void testSMT() {
//  pt = parse(#start[Form], |project://demoqles/input/tax.dql|);
//  <f, ds> = definitions(pt.top);
//  f = bind(f, ds);
//  l = |file:///tmp/tax.smt2|;
//  if (detectCycles(f) != {}) {
//    println("Cycles");
//  }
//  else {
//    for (e <- verifyForm(f, l)) {
//      println(e);
//    }
//  }
//}

str SOLVER_PATH = "/usr/local/bin/z3";

// requires bind
// no cycles
set[Message] verifyForm(Form f, loc tempfile) {
  if (!exists(|file://<SOLVER_PATH>|)) {
    return {warning("Solver does not exist at <SOLVER_PATH>", f.name@\loc)};
  }
  qs = sort(flatten(f));
  smt = qs2smt(qs);
  ds = form2nonDetChecks(f);
  rs = form2reachabilityChecks(f);
  us = form2undefinedChecks(f);
  nonDet = checkScopes(ds);
  reach = checkScopes(rs);
  undef = checkScopes(us);

  output = runSMTsolver(tempfile, "<smt>\n<nonDet>\n<reach>\n<undef>");
  // TODO: check output for well-formedness.
  results = parseOutput(output); 
  j = 0;
  set[Message] errs = {};
  for (i <- [0..size(ds)]) {
    errs += { warning("Non-deterministic", q@\loc) | q <- ds[i][1], results[j] == "sat" };
    j += 1;
  }
  for (i <- [0..size(rs)]) {
    errs += { warning("Unreachable", rs[i][1]@\loc) | results[j] == "unsat" };
    j += 1;
  }
  for (i <- [0..size(us)]) {
    errs += { warning("Possibly undefined use", us[i][1]@\loc) | results[j] == "sat" };
    j += 1;
  }
  return errs;
}

list[str] parseOutput(str output) {
  r = [];
  
  while (/^<result:(un)?sat>/ := output) {
    r += [result];
    output = output == result ? "" : output[size(result)..];
  }
  
  return r;
}

str runSMTsolver(loc tmpfile, str input) {
  pid = createProcess(SOLVER_PATH, ["-smt2", "-nw", "-in"]);
  writeFile(tmpfile, input);
  writeTo(pid, "<input>\n(exit)\n");
  x = trim(readEntireStream(pid));
  killProcess(pid);
  return x;
}

str checkScopes(lrel[str, &T] as)
  = intercalate("\n", [ "(push)\n<a>\n(check-sat)\n(pop)" | <a, _> <- as] );

str qName(str n, loc l) = "<n>_<l.offset>";
str qName(Question q) = qName("<q.var>", q@\loc);
str qVisible(Question q) = "<qName(q)>_visible";

lrel[str, set[Question]] form2nonDetChecks(Form f) {
  vq = { <q.var, q> | /Question q := f, q has var };
  as = [];
  for (v <- domain(vq), size(vq[v]) > 1) {
    <q0, qs> = takeOneFrom(vq[v]);
    xor = ( "<qName(q0)>_visible" | "(xor <qName(q2)>_visible <it>)" | q2 <- qs );
    as += [<"(assert (not <xor>))", vq[v]>];
  }
  return as;
}

lrel[str, Question] form2reachabilityChecks(Form f) 
  = [ <"(assert <qName(q)>_visible)", q> | /Question q := f, q has var  ];
  
lrel[str, Question] form2undefinedChecks(Form f) {
  // TODO: factor out in cycle check.
  rel[str, loc] uses(Question q) 
    = { <"<x>", l> | /e:(Expr)`<Id x>` := q, l <- e@links };
  checks = [];
  top-down visit (f) {
    case q:(Question)`<Label l> <Var n>: <Type t> = <Expr e>`: {
      us = uses(q);
      conjs = for (x <- domain(us)) {
        <l0, ls> = takeOneFrom(us[x]);
        // TODO: this could use qName/qVisible...
        // A variable x is visible if any of its question occurrences
        // is visible.
        xvis =  ( "<x>_<l0.offset>_visible" 
                | "(or <it> <x>_<l.offset>_visible)" | loc l <- ls );
        append xvis;
      }
      // if q (occ) is visible, it's used variables should be
      // visible (=> q_visible (AND (or ...) (or ...)))
      if (conjs != []) {
        conj = ( conjs[0] | "(and <it> <c>)" | c <- /*conjs[1..]*/ tail(conjs) );
        checks += [<"(assert (not (=\> <qVisible(q)> <conj>)))", q>];
      }
    }
  }
  return checks;
}

// NB: does not terminate if cyclic dependencies.
list[Question] sort(list[Question] qs) {
  solve (qs) {
    if ([*qs1, Question q1, *qs2, Question q2, *qs3] := qs, defs(q2) <= uses(q1)) {
      qs = [*qs1, q2, *qs2, q1, *qs3];
    }
  }
  return qs;
  
  //for ([*qs1, Question q1, *qs2, Question q2, *qs3] := qs, uses(q1) != {}, uses(q1) <= defs(q2)) {
  //  // werkt niet!!?!?!?!?!?! q1 can be empty in the body...
  //  println("Uses q1: <uses(q1)> (q1 = <q1>)");
  //  println("Defs q2: <defs(q2)> (q2 = <q2>");
  //  qs = [*qs1, q2, *qs2, q1, *qs3];
  //}
}


// requires bind
str qs2smt(list[Question] qs) = intercalate("\n", [ ifthen2smt(q) | q <- qs ]); 

str ifthen2smt((Question)`if (<Expr c>) <Question q>`)
  = "(define-fun <qName(q)>_visible () Bool <expr2smt(c)>)\n"
  + question2smt(q);


str question2smt(q:(Question)`<Label l> <Var v>: <Type t>`)
  = "(declare-const <qName(q)> <type2smt(t)>)";

str question2smt(q:(Question)`<Label l> <Var v>: <Type t> = <Expr e>`)
  = "(define-fun <qName(q)> () <type2smt(t)> <expr2smt(e)>)";

str type2smt((Type)`boolean`) = "Bool";
str type2smt((Type)`integer`) = "Int";
str type2smt((Type)`string`) = "(Array Int Int)";
str type2smt((Type)`money`) = "Real";
default str type2smt(Type t) { throw "Unsupported type: <t>"; }


str expr2smt(e:(Expr)`<Id x>`) {
  qLocs = e@links;
  str varAt(loc l) = "<x>_<l.offset>";
  <q, qLocs> = takeOneFrom(qLocs);
  return ( varAt(q) | "(ite <v>_visible <v> <it>)" | l <- qLocs, v := varAt(l) );
}
 
str expr2smt((Expr)`(<Expr e>)`) = "<expr2smt(e)>";
str expr2smt((Expr)`<Integer x>`) = "<x>.0";
str expr2smt((Expr)`true`) = "true";
str expr2smt((Expr)`false`) = "false";

str expr2smt((Expr)`!<Expr e>`) = "(not <expr2smt(e)>)";
str expr2smt((Expr)`<Expr lhs> * <Expr rhs>`) = "(* <expr2smt(lhs)> <expr2smt(rhs)>)";
str expr2smt((Expr)`<Expr lhs> / <Expr rhs>`) = "(/ <expr2smt(lhs)> <expr2smt(rhs)>)";
str expr2smt((Expr)`<Expr lhs> + <Expr rhs>`) = "(+ <expr2smt(lhs)> <expr2smt(rhs)>)";
str expr2smt((Expr)`<Expr lhs> - <Expr rhs>`) = "(- <expr2smt(lhs)> <expr2smt(rhs)>)";
str expr2smt((Expr)`<Expr lhs> \> <Expr rhs>`) = "(\> <expr2smt(lhs)> <expr2smt(rhs)>)";
str expr2smt((Expr)`<Expr lhs> \>= <Expr rhs>`) = "(\>= <expr2smt(lhs)> <expr2smt(rhs)>)";
str expr2smt((Expr)`<Expr lhs> \< <Expr rhs>`) = "(\< <expr2smt(lhs)> <expr2smt(rhs)>)";
str expr2smt((Expr)`<Expr lhs> \<= <Expr rhs>`) = "(\<= <expr2smt(lhs)> <expr2smt(rhs)>)";
str expr2smt((Expr)`<Expr lhs> == <Expr rhs>`) = "(= <expr2smt(lhs)> <expr2smt(rhs)>)";
str expr2smt((Expr)`<Expr lhs> != <Expr rhs>`) = "(not (= <expr2smt(lhs)> <expr2smt(rhs)>))";
str expr2smt((Expr)`<Expr lhs> && <Expr rhs>`) = "(and <expr2smt(lhs)> <expr2smt(rhs)>)";
str expr2smt((Expr)`<Expr lhs> || <Expr rhs>`) = "(or <expr2smt(lhs)> <expr2smt(rhs)>)";

default str expr2smt(Expr e) { throw "Expression <e> not supported"; }


