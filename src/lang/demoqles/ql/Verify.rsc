module lang::demoqles::ql::Verify

import lang::demoqles::ql::QL;
import lang::demoqles::ql::Flatten;
import lang::demoqles::ql::Bind;
import lang::demoqles::ql::Check; // for use/def

import lang::smtlib2::theory::core::Ast;
import lang::smtlib2::theory::ints::Ast;
import lang::smtlib2::command::Ast;
import lang::smtlib2::\solve::Z3;

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

void testSMT() {
  pt = parse(#start[Form], |project://demoqles/input/errors.dql|);
  <f, ds> = definitions(pt.top);
  f = bind(f, ds);
  l = |file:///tmp/tax.smt2|;
  Script scr = script(qs2smt(sort(flatten(f))));
  iprintln(verifyForm(f, |file:///|));
  //if (detectCycles(f) != {}) {
  //  println("Cycles");
  //}
  //else {
  //  for (e <- verifyForm(f, l)) {
  //    println(e);
  //  }
  //}
}

str SOLVER_PATH = "/usr/local/bin/z3";

// requires bind
// no cycles
set[Message] verifyForm(Form f, loc tempfile) {
  if (!exists(|file://<SOLVER_PATH>|)) {
    return {warning("Solver does not exist at <SOLVER_PATH>", f.name@\loc)};
  }
  
  pid = startZ3(pathToZ3 = "/usr/local");
  spec = script(qs2smt(sort(flatten(f)))); 
  run(pid, spec, debug=true);
  
  errs = {};
  
  errs += { warning("Unreachable", q@\loc) | /Question q := f, q has var, 
               !check(pid, [\assert(var(qVisible(q)))]) };


  vq = { <q.var, q> | /Question q := f, q has var };
  for (v <- domain(vq), size(vq[v]) > 1) {
    <q0, qs> = takeOneFrom(vq[v]);
    excl = ( var(qVisible(q0)) | xor(var(qVisible(q2)),  it) | q2 <- qs );
    
    errs += { warning("Non-deterministic", subject@\loc) |  
               check(pid, [\assert(not(excl))]), subject <- vq[v] };
  }

  stopZ3(pid);

  return errs;
  
}

str qName(str n, loc l) = "<n>_<l.offset>";
str qName(Question q) = qName("<q.var>", q@\loc);
str qVisible(Question q) = "<qName(q)>_visible";


bool check(int z3Pid, list[Command] commands) {
    commands = [push(1), *commands, checkSatisfiable(), pop(1)];
    result = run(z3Pid, script(commands), debug=true);
    return /sat() := result;
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
list[Command] qs2smt(list[Question] qs) = ( [] | it + ifthen2smt(q) | q <- qs ); 

list[Command] ifthen2smt((Question)`if (<Expr c>) <Question q>`)
  = [defineFunction("<qName(q)>_visible", [], \bool(), expr2smt(c))]
  + question2smt(q);

list[Command] question2smt(q:(Question)`<Label l> <Var v>: <Type t>`)
  = [declareFunction(qName(q), [], type2smt(t))];

list[Command] question2smt(q:(Question)`<Label l> <Var v>: <Type t> = <Expr e>`)
  = [defineFunction(qName(q), [], type2smt(t), expr2smt(e))];

Sort type2smt((Type)`boolean`) = \bool();
Sort type2smt((Type)`integer`) = \int();
// todo!!!
Sort type2smt((Type)`string`) = \int();
Sort type2smt((Type)`money`) = \int();

default Sort type2smt(Type t) { throw "Unsupported type: <t>"; }


Expr expr2smt(e:(Expr)`<Id x>`) {
  qLocs = e@links;
  str varAt(loc l) = "<x>_<l.offset>";
  <q, qLocs> = takeOneFrom(qLocs);
  return ( var(varAt(q)) | ite(var("<v>_visible"), var(v), it) | l <- qLocs, v := varAt(l) );
}
 
Expr expr2smt((Expr)`(<Expr e>)`) = expr2smt(e);
Expr expr2smt((Expr)`<Integer x>`) = lit(intVal(toInt("<x>")));
Expr expr2smt((Expr)`true`) = lit(\true());
Expr expr2smt((Expr)`false`) = lit(\false());

Expr expr2smt((Expr)`!<Expr e>`) = not(expr2smt(e));
Expr expr2smt((Expr)`<Expr lhs> * <Expr rhs>`) = mul(expr2smt(lhs), expr2smt(rhs));
Expr expr2smt((Expr)`<Expr lhs> / <Expr rhs>`) = div(expr2smt(lhs), expr2smt(rhs));
Expr expr2smt((Expr)`<Expr lhs> + <Expr rhs>`) = add(expr2smt(lhs), expr2smt(rhs));
Expr expr2smt((Expr)`<Expr lhs> - <Expr rhs>`) = sub(expr2smt(lhs), expr2smt(rhs));
Expr expr2smt((Expr)`<Expr lhs> \> <Expr rhs>`) = gt(expr2smt(lhs), expr2smt(rhs));
Expr expr2smt((Expr)`<Expr lhs> \>= <Expr rhs>`) = gte(expr2smt(lhs), expr2smt(rhs));
Expr expr2smt((Expr)`<Expr lhs> \< <Expr rhs>`) = lt(expr2smt(lhs), expr2smt(rhs));
Expr expr2smt((Expr)`<Expr lhs> \<= <Expr rhs>`) = lte(expr2smt(lhs), expr2smt(rhs));
Expr expr2smt((Expr)`<Expr lhs> == <Expr rhs>`) = eq(expr2smt(lhs), expr2smt(rhs));
Expr expr2smt((Expr)`<Expr lhs> != <Expr rhs>`) = not(eq(expr2smt(lhs), expr2smt(rhs)));
Expr expr2smt((Expr)`<Expr lhs> && <Expr rhs>`) = and(expr2smt(lhs), expr2smt(rhs));
Expr expr2smt((Expr)`<Expr lhs> || <Expr rhs>`) = or(expr2smt(lhs), expr2smt(rhs));

default Expr expr2smt(Expr e) { throw "Expression <e> not supported"; }


