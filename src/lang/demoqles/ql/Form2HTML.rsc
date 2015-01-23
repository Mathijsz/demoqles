module lang::demoqles::ql::Form2HTML

import lang::demoqles::ql::Types;
import lang::demoqles::ql::QL;
import lang::demoqles::ql::Expr2JS;
import lang::demoqles::ql::Form2Model;
import lang::demoqles::ql::Bind;
import IO;
import ParseTree;

//void testGen() {
//  pt = parse(#start[Form], |project://demoqles/input/tax.mql|);
//  <f, defs> = definitions(pt.top);
//  f = bind(f, defs);
//  g = form2html(f);
//  println(g);
//}  

loc TEMPLATE = |project://demoqles/src/lang/demoqles/template.html|;

str qName(Question q) = "<q.var>_<q@\loc.offset>";
str qLabel(Question q) = "<q.label>"[1..-1];

str ql2html(Form f) = form2html(f, form2items, form2model);

// requires bindings on f.
str form2html(Form f, str(Form) items, str(Form, str) model) {
  name = "<f.name>";
  t = readFile(TEMPLATE);
  return top-down-break visit (t) {
    case /TITLE/ => name
    case /CONTENT/ => items(f)
    // MAJOR BUG? if "<name>$model" is changed to name + "$model" the
    // second occurrence of name is changed too!!!
    case /INIT/ => "<model(f, "<name>$model")>
                   '$(document).ready(function() {
                   '   ko.applyBindings(new <name>$model());
                   '});"
  }
}

str form2items(Form f) = 
  "\<ul\>
  '  <( "" | it + question2item(q) + "\n" | /Question q := f, q has var)>
  '\</ul\>"; 

str expr2js(Expr e) = expr2js(e, str(str x) { return x; });

// TODO: let this be reused in sheet2html
str question2item(Question q) 
  = "\<li data-bind=\"visible: <qName(q)>_visible\"\>
    '  <question2html(q)>
    '\</li\>";

str question2html(Question q, bool label = true) 
  = labeledWidget(q, inputWidget(qName(q), "checkbox", "checked: <qName(q)>"), label = label)
  when (Type)`boolean` := q.\type;

default str question2html(Question q, bool label = true) = // ignore type for now 
  labeledWidget(q, inputWidget(qName(q), "text", "value: <qName(q)>"), label = label);

str inputWidget(str name, str tipe, str bind) 
  = "\<input name=\"<name>\" id=\"<name>\" type=\"<tipe>\" data-bind=\"<bind>\" /\>";

str labeledWidget(Question q, str w, bool label = true) 
  = label ? "\<label for=\"<qName(q)>\"\><qLabel(q)>\</label\>\n<w>" : w;



