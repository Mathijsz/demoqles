module lang::demoqles::qls::Sheet2HTML

import lang::demoqles::qls::Normalize;
import lang::demoqles::ql::Form2HTML;
import lang::demoqles::ql::Form2Model;
import List;
import ParseTree;
import String;
import IO;

/*
 Presupposes normalization which has the questions inlined into 
 the style sheet
 So we can assume
 - there are only questions at the leaves in the sheet
 - all questions have a style 
 - if there's widget it is the first style element.
 
*/     

//void testHTML() {
//  pt = parse(#start[Form], |project://muql/input/tax.mql|);
//  s = parse(#start[Stylesheet], |project://muql/input/tax.mqls|);
//  <f, defs> = definitions(pt.top);
//  f = bind(f, defs);
//  println(qls2html(s.top, f)); 
//}

// requires bindings on f.
str qls2html(Stylesheet s, Form f) {
  str sheet2items(Form f) = sheet2html(normalize(s, f));
  nPages = size([ p | p <- s.pages ]);
  str sheet2model(Form f, str name) {
    fields = form2fields(f);
    return "function <name>() {
           '  var self = this;
           '  <intercalate("\n", fields)>
           '  <if (nPages > 1) {>
           '  self.$page = ko.observable(0);
           '  self.$prevPage = function () {
           '    if (self.$page() \> 0)  
           '     self.$page(self.$page() - 1);
           '  };
           '  self.$nextPage = function () {
           '    if (self.$page() \< <nPages - 1>)  
           '     self.$page(self.$page() + 1);
           '  };
           '  <}>
           '}";
  }
  
  return form2html(f, sheet2items, sheet2model);
}

str sheet2html((Stylesheet)`stylesheet <Id n> <Page p>`) 
  = rule2html(p.rule, 1); 

default str sheet2html(Stylesheet s) {
  int n = 0;
  return "<for (p <- s.pages) {>
         ' <page2html(p, n)>
         '<n += 1; }>"; 
}

str page2html((Page)`page <Id n> <Rule r>`, int n) 
  = "\<div id=\"<n>:page\" data-bind=\"visible: ($page() === <n>)\"\>
    '  <rule2html(r, 1)>
    '  \<button data-bind=\"click: $prevPage\"\>Previous\</button\>
    '  \<button data-bind=\"click: $nextPage\"\>Next\</button\>
    '\</div\>";

str rule2html((Rule)`{<Rule* rs>}`, int level)
  = ( "" | it + rule2html(r, level) + "\n" | r <- rs );
  
str rule2html((Rule)`section <String t> <Rule r>`, int level)
  = "\<h<level>\><h>\</h<level>\>
    '<rule2html(r, level + 1)>"
  when str h := "<t>"[1..-1];
  
str rule2html((Rule)`<Question q> {widget <WidgetType w> <Style* ys>}`, int level)
  = condP(q, span((Style)`{<Style* ys>}`, widget2widget(w, q)));  
  
default str rule2html((Rule)`<Question q> <Style y>`, int _)
  = condP(q, span(y, question2html(q, label = false)));

str widget2widget((WidgetType)`slider(<Integer a>, <Integer b>, <Integer c>)`, Question q)
  = "\<input type=\"range\" min=\"<a>\" max=\"<b>\" step=\"<c>\"
    '   data-bind=\"value: <qName(q)>\" 
    '   name=\"<qName(q)>\" id=\"<qName(q)>\" /\>";
  
str widget2widget((WidgetType)`spinbox`, Question q)
  = "\<input type=\"number\" data-bind=\"value: <qName(q)>\"
    '   name=\"<qName(q)>\" id=\"<qName(q)>\" /\>";
  
str widget2widget((WidgetType)`radio(<String yes>, <String no>)`, Question q)
  = "\<input type=\"radio\" name=\"<qName(q)>\" id=\"<qName(q)>\" 
    '     value=\"true\" data-bind=\"checked: <qName(q)>\"  /\>
    '    <syes>
    '\<input type=\"radio\" name=\"<qName(q)>\" id=\"<qName(q)>\" 
    '     value=\"\" data-bind=\"checked: <qName(q)>\" /\>
    '    <sno>"
  when 
    str syes := "<yes>"[1..-1],
    str sno := "<no>"[1..-1];
  
default str widget2widget(WidgetType _, Question q)
  = question2html(q, label = false);
  
str condP(Question q, str x) = 
  "\<p data-bind=\"visible: <qName(q)>_visible\"\><qLabel(q)>&nbsp;<x>\</p\>"; 
  
str span(Style y, str s) = "\<span style=\"<style2css(y)>\"\><s>\</span\>";

str style2css((Style)`{<Style* ys>}`) 
  = ( "" | it + "<n>: <s>; " | (Style)`<Id n>: <Value v>` <- ys, s := escape("<v>") );

str escape(str x) = escape(x, ("\"": "&quot;"));

