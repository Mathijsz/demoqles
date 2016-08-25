module lang::demoqles::const::Const

extend lang::demoqles::ql::QL;

syntax Question
  = constant: "const" Var var ":" Type type "=" Const value
  ;

