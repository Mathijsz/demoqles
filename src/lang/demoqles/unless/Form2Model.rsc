module lang::demoqles::unless::Form2Model

import lang::demoqles::unless::Unless;
extend lang::demoqles::ql::Form2Model;

list[str] toFields((Question)`unless (<Expr c>) <Question q>`, Expr cond, Info i) = 
   toFields(q, (Expr)`<Expr cond> && !<Expr c>`, i);

