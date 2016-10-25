module lang::demoqles::unless::Unless

extend lang::demoqles::ql::QL;

syntax Question = "unless" "(" Expr expr ")" Question;
  
