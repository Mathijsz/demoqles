module lang::demoqles::ql::Outline

import lang::demoqles::ql::QL;
import util::IDE;
import ParseTree;
import Relation;
import List;
import String;

node outline(Form f) {
 list[node] qs = [];
 rel[str, str, loc] types = {};
 list[node] es = [];
 list[node] cs = []; 
 list[node] ls = [];
 list[node] vs = [];
 
 void addQuestion(Question q) {
   qn = "question"()[@label="<q.var>"][@\loc=q@\loc];
   qs += [qn]; 
   l = "<q.label>"[1..-1];
   ls += ["label"()[@label=l][@\loc=q.label@\loc]];
   types += {<"<q.\type>", "<q.var>", q@\loc>}; 
 }
 
 void addCond(Expr c) {
   cs += ["cond"()[@label="<c>"][@\loc=c@\loc]];
 }
 
 top-down visit (f) {
   case q:(Question)`<Label l> <Var x>: <Type t>`: addQuestion(q);
   case q:(Question)`<Label l> <Var x>: <Type t> [<Expr v>]`: {
     addQuestion(q);
     vs += ["val"()[@label="<x>: <v>"][@\loc=v@\loc]];
   }
   case q:(Question)`<Label l> <Var x>: <Type t> = <Expr e>`: {
     addQuestion(q);
     es += ["expr"()[@label="<e>"][@\loc=e@\loc]];
   }

   case q:(Question)`<Label l> <Var x>: <Type t> = <Expr e> [<Expr v>]`: {
     addQuestion(q);
     vs += ["val"()[@label="<x>: <v>"][@\loc=v@\loc]];
     es += ["expr"()[@label="<e>"][@\loc=e@\loc]];
   }
   
   case Question q: if (q has cond) addCond(q.cond);
   
   //case q:(Question)`if (<Expr c>) <Question q>`: 
   //  addCond(c); 
   //case q:(Question)`if (<Expr c>) <Question q1> else <Question q2>`: 
   //  addCond(c); 
 }

 ts = for (t <- domain(types)) {
   subqs = [ "q"()[@label=qn][@\loc=ql] | <str qn, loc ql> <- types[t] ];
   append "type"(subqs)[@label=capitalize(t)];
 }

 return "outline"(
  "questions"(qs)[@label="Questions (<size(qs)>)"],
  "types"(ts)[@label="Types (<size(ts)>)"],
  "conditions"(cs)[@label="Conditions (<size(cs)>)"],
  "expressions"(es)[@label="Expressions (<size(es)>)"],
  "labels"(ls)[@label="Labels (<size(ls)>)"],
  "values"(vs)[@label="Values (<size(vs)>)"]
 );
}
