module lang::demoqles::ql::Check

import lang::demoqles::ql::Types;
import lang::demoqles::ql::QL;
import lang::demoqles::ql::Bind;
import lang::demoqles::ql::Flatten;
import Message;
import ParseTree;
import IO;
import Relation;
import Set;

set[Message] checkForm(Form f, Info inf) 
  = tc(f, inf) + checkEmbeds(f, inf) + detectCycles(f, inf);
  
set[Message] checkEmbeds(Form f, Info i) {
  msgs = {};
  visit (f) {
     case Embed e: {
       println("Embed in check: <e>");
       msgs += tc(e.expr, i);
     }
  }
  return msgs;
}

set[Message] detectCycles(Form f, Info i) 
  = {};
  //{ error("Cycle involving <x>", f.name@\loc) | x <- carrier(g), <x, x> in g }
  //when g := ( {} | it + defs(q) * uses(q) | q <- flatten(f) )+;


set[Message] tc(Form f, Info i) = ( {} | it + tc(q, i) | q <- f.questions );

set[Message] tci(Expr c, Info i) 
  = { error("Condition should be boolean", c@\loc) | qlTypeOf(c, i) != boolean() }
  + tc(c, i);

set[Message] tc((Question)`if (<Expr c>) <Question q>`, Info i) 
  = tci(c, i) + tc(q, i);

set[Message] tc((Question)`if (<Expr c>) <Question q1> else <Question q2>`, Info i)
  = tci(c, i) + tc(q1, i) + tc(q2, i);

set[Message] tc((Question)`{ <Question* qs> }`, Info i) 
  = ( {} | it + tc(q, i) |  q <- qs );

set[Message] tcq(Label l, Id n, Info i)
  = { error("Redeclared with different type", n@\loc) | hasMultipleTypes(n@\loc, i) }
  + { warning("Duplicate label", l@\loc) | hasDuplicateLabel(l, i) }
  ;

set[Message] tc(q:(Question)`<Label l> <Id n>: <Type t> = <Expr e>`, Info i)
  = tcq(l, n, i) + tc(e ,i) + 
  { error("Incompatible expression type", e@\loc) | qlTypeOf(e, i) != qlType(t) };


set[Message] tc(q:(Question)`<Label l> <Id n>: <Type t> = <Expr e> [<Expr v>]`, Info i)
  = tcq(l, n, i) + tc(e ,i) + 
  { error("Incompatible expression type", e@\loc) | qlTypeOf(e, i) != qlType(t) };

set[Message] tc(q:(Question)`<Label l> <Id n>: <Type t>`, Info i)  
  = tcq(l, n, i);

set[Message] tc(q:(Question)`<Label l> <Id n>: <Type t> [<Expr v>]`, Info i)  
  = tcq(l, n, i) 
  + { error("Incompatible value", v@\loc) | qlTypeOf(v, i) != qlType(t) }; 

default set[Message] tc(Question q, Info i) = {};

bool hasMultipleTypes(loc x, Info i) = size(i.refs.def[x]) > 1;

bool hasDuplicateLabel(Label l, Info i) = size(i.labels[l]) > 1;

  

default set[Message] tc(Expr _, Info i) = {};

set[Message] tc((Expr)`<Id x>`, Info i) 
  = { error("Undefined question", x@\loc) | x@\loc notin i.refs.use<0> };
  
set[Message] tc((Expr)`(<Expr e>)`, Info i) = tc(e, i);
set[Message] tc(n:(Expr)`!<Expr e>`, Info i) = tc(n, checkBoolean, e);
set[Message] tc(e:(Expr)`<Expr lhs> * <Expr rhs>`, Info i) = tc(e, checkNumeric, i, lhs, rhs);
set[Message] tc(e:(Expr)`<Expr lhs> / <Expr rhs>`, Info i) = tc(e, checkNumeric, i, lhs, rhs);
set[Message] tc(e:(Expr)`<Expr lhs> + <Expr rhs>`, Info i) = tc(e, checkNumeric, i, lhs, rhs);
set[Message] tc(e:(Expr)`<Expr lhs> - <Expr rhs>`, Info i) = tc(e, checkNumeric, i, lhs, rhs);
set[Message] tc(e:(Expr)`<Expr lhs> \> <Expr rhs>`, Info i) = tc(e, checkNumeric, i, lhs, rhs);
set[Message] tc(e:(Expr)`<Expr lhs> \>= <Expr rhs>`, Info i) = tc(e, checkNumeric, i, lhs, rhs);
set[Message] tc(e:(Expr)`<Expr lhs> \< <Expr rhs>`, Info i) = tc(e, checkNumeric, i, lhs, rhs);
set[Message] tc(e:(Expr)`<Expr lhs> \<= <Expr rhs>`, Info i) = tc(e, checkNumeric, i, lhs, rhs);
set[Message] tc(e:(Expr)`<Expr lhs> == <Expr rhs>`, Info i) = tc(e, checkEq, lhs, i, rhs);
set[Message] tc(e:(Expr)`<Expr lhs> != <Expr rhs>`, Info i) = tc(e, checkEq, lhs, i, rhs);
set[Message] tc(e:(Expr)`<Expr lhs> && <Expr rhs>`, Info i) = tc(e, checkBoolean, i, lhs, rhs);
set[Message] tc(e:(Expr)`<Expr lhs> || <Expr rhs>`, Info i) = tc(e, checkBoolean, i, lhs, rhs);

/*
 * Helper function to do automatic calling of tc on sub-expressions
 * and to prevent type-checking if the sub-expressions can't be typed.
 */

set[Message] tc(Expr e, set[Message](list[QLType], loc) check, Info i, Expr kids...) {
  ts = [ qlTypeOf(k, i) | k <- kids ];
  errs = ( {} | it + tc(k, i) | k <- kids );
  if (bottom() notin ts) {
    errs += check(ts, e@\loc);
  }
  return errs;
}

set[Message] checkBoolean(list[QLType] ts, loc l)  
  = ( true | it && boolean() !:= t | t <- ts )
  ? { error("Expression should have boolean type", l) }
  : {}; 

set[Message] checkNumeric(list[QLType] ts, loc l)  
  = ( true | it && (integer() := t || money() := t) | t <- ts )
  ? {}
  : { error("Expression should have numeric type", l) }; 

set[Message] checkString(list[QLType] ts, loc l)  
  = ( true | it && string() !:= t | t <- ts ) 
  ? { error("Expression should have string type", l) } 
  : {}; 

set[Message] checkEq(list[QLType] ts, loc l) 
  = { error("Incomparable types", l) | ts[0] != ts[1] }; 


default QLType qlTypeOf(Expr _, Info i) = QLType::bottom();
  
QLType qlTypeOf(e:(Expr)`<Id x>`, Info i) = t 
  when
    loc use := e@\loc,
    <use, loc def> <- i.refs.use,
    <def, QLType t> <- i.refs.def;
   
QLType qlTypeOf((Expr)`(<Expr e>)`, Info i) = qlTypeOf(e, i);
QLType qlTypeOf((Expr)`<Integer _>`, Info i) = QLType::integer();
QLType qlTypeOf((Expr)`<Money _>`, Info i) = money();
QLType qlTypeOf((Expr)`true`, Info i) = boolean();
QLType qlTypeOf((Expr)`false`, Info i) = boolean();
QLType qlTypeOf((Expr)`<String _>`, Info i) = string();
QLType qlTypeOf(n:(Expr)`!<Expr e>`, Info i) = boolean();
QLType qlTypeOf(e:(Expr)`<Expr lhs> * <Expr rhs>`, Info i) = lub(qlTypeOf(lhs, i), qlTypeOf(rhs), i);
QLType qlTypeOf(e:(Expr)`<Expr lhs> / <Expr rhs>`, Info i) = lub(qlTypeOf(lhs, i), qlTypeOf(rhs, i));
QLType qlTypeOf(e:(Expr)`<Expr lhs> + <Expr rhs>`, Info i) = lub(qlTypeOf(lhs, i), qlTypeOf(rhs, i));
QLType qlTypeOf(e:(Expr)`<Expr lhs> - <Expr rhs>`, Info i) = lub(qlTypeOf(lhs, i), qlTypeOf(rhs, i));
QLType qlTypeOf(e:(Expr)`<Expr lhs> \> <Expr rhs>`, Info i) = boolean();
QLType qlTypeOf(e:(Expr)`<Expr lhs> \>= <Expr rhs>`, Info i) = boolean();
QLType qlTypeOf(e:(Expr)`<Expr lhs> \< <Expr rhs>`, Info i) = boolean();
QLType qlTypeOf(e:(Expr)`<Expr lhs> \<= <Expr rhs>`, Info i) = boolean();
QLType qlTypeOf(e:(Expr)`<Expr lhs> == <Expr rhs>`, Info i) = boolean();
QLType qlTypeOf(e:(Expr)`<Expr lhs> != <Expr rhs>`, Info i) = boolean();
QLType qlTypeOf(e:(Expr)`<Expr lhs> && <Expr rhs>`, Info i) = boolean();
QLType qlTypeOf(e:(Expr)`<Expr lhs> || <Expr rhs>`, Info i) = boolean();


QLType lub(money(), QLType::integer()) = money();
QLType lub(QLType::integer(), money()) = money();
QLType lub(QLType t1, QLType t2) = t1 when t1 == t2;
default QLType lub(QLType t1, QLType t2) = bottom();
