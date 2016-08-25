module lang::demoqles::const::Check

import lang::demoqles::const::Const;
extend lang::demoqles::ql::Check;

set[Message] tc(q:(Question)`const <Id n>: <Type t> = <Expr v>`, Info i)  
  = { error("Redeclared constant", n@\loc) | hasMultipleTypes(n@\loc, i) }
  + { error("Incompatible value", v@\loc) | qlTypeOf(v, i) != qlType(t) }; 
