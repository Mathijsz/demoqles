module lang::demoqles::ql::Flatten

import lang::demoqles::ql::QL;
import ParseTree; 
import IO;

list[Question] flatten(Form f) 
  = ( [] | it + flatten(q, (Expr)`true`) | q <- f.questions );

list[Question] flatten((Question)`if (<Expr c1>) <Question q>`, Expr c2)
  = flatten(q, (Expr)`<Expr c2> && <Expr c1>`);

list[Question] flatten((Question)`if (<Expr c1>) <Question q1> else <Question q2>`, Expr c2)
  = flatten(q1, (Expr)`<Expr c2> && <Expr c1>`)
  + flatten(q2, (Expr)`<Expr c2> && !(<Expr c1>)`);

list[Question] flatten((Question)`{<Question* qs>}`, Expr c)
  = ( [] | it + flatten(q, c) | q <- qs );

list[Question] flatten(q:(Question)`<Label l> <Var v>: <Type t>`, Expr c)
  = [(Question)`if (<Expr c>) <Question q>`];

list[Question] flatten(q:(Question)`<Label l> <Var v>: <Type t> = <Expr e>`, Expr c)
  = [(Question)`if (<Expr c>) <Question q>`];

