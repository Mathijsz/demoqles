module lang::demoqles::ql::Form2Model

import lang::demoqles::ql::QL;
import lang::demoqles::ql::Expr2JS;
import lang::demoqles::ql::Types;
import lang::demoqles::ql::Bind;
import ParseTree;
import List;
import IO;

// todo: separate qName in utils or something
str qName(Question q) = "<q.var>_<q@\loc.offset>";

// needs bindings on f
str form2model(Form f, str name, Info i) {
   fields = form2fields(f, i);
   return "function <name>() {
          '  var self = this;
          '  <intercalate("\n", fields)>
          '}";
}

list[str] form2fields(Form f, Info i) 
  = ( [] | it + toFields(q, (Expr)`true`, i) | q <- f.questions );

list[str] toFields((Question)`if (<Expr c>) <Question q>`, Expr cond, Info i) = 
   toFields(q, (Expr)`<Expr cond> && <Expr c>`, i);

list[str] toFields((Question)`if (<Expr c>) <Question q1> else <Question q2>`, Expr cond, Info i) 
  = toFields(q1, (Expr)`<Expr cond> && <Expr c>`, i)
  + toFields(q2, (Expr)`<Expr cond> && !(<Expr c>)`, i);

list[str] toFields((Question)`{ <Question* qs> }`, Expr cond, Info i) 
  = ( [] | it + toFields(q, cond, i) |  q <- qs );

list[str] toFields(q:(Question)`<Label l> <Var n>: <Type t> <Value _>`, Expr cond, Info i)
  = toFields((Question)`<Label l> <Var n>: <Type t>`[@\loc=q@\loc], cond, i);

list[str] toFields(q:(Question)`<Label l> <Var n>: <Type t>`, Expr cond, Info i)  
  = ["self.<qName(q)> = ko.observable(<initValue(t)>);",
     "self.<qName(q)>_visible = <computed(cond, i)>;"];
  
list[str] toFields(q:(Question)`<Label l> <Var n>: <Type t> = <Expr e>`, Expr cond, Info i) 
  = ["self.<qName(q)> = <computed(e, i)>;",
     "self.<qName(q)>_readonly = true;",
     "self.<qName(q)>_visible = <computed(cond, i)>;"];

list[str] toFields(q:(Question)`<Label l> <Var n>: <Type t> = <Expr e> <Value _>`, Expr cond, Info i)
  = toFields((Question)`<Label l> <Var n>: <Type t> = <Expr e>`[@\loc=q@\loc], cond, i);

str computed(Expr e, Info i) = "ko.computed(function() {
				                       '  console.log(\"Computing: <e>\\n\");
				                       '  return <expr2js(e, str(Id x) { return selectVisibleWrap(x, i); })>;
				                       '}, self, {deferEvaluation: true})";

str selectVisibleWrap(Id var, Info i) {
  loc use = var@\loc; 
  qLocs = { def | <use, loc def> <- i.refs.use };
  x = "<var>";
  str selfVar(loc l) = "self.<x>_<l.offset>";
  
  if ({loc l} := qLocs) 
    return "<selfVar(l)>()";
  
  return ( "null" | "(<v>_visible() ? <v>() : <it>)" | l <- qLocs, v := selfVar(l) );
}

str initValue((Type)`boolean`) = "false";
str initValue((Type)`integer`) = "0";
str initValue((Type)`money`) = "0.0";
str initValue((Type)`string`) = "\'\'";
