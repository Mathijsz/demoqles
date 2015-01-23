module lang::demoqles::qls::Check

import lang::demoqles::ql::QL;
import lang::demoqles::qls::QLS;
import Message;
import ParseTree;
import List;
import Map;

/*
 To check:
 - referenced questions exist in questionnaire
 - all questions are placed
 - no duplicate placement of questions
 - compatibility of widgets to types.
 - multiple defs of widgets
*/


set[Message] checkSheet(Stylesheet s, Form f) {
  qt = ( q.var: q.\type | /Question q := f, q has var ); 
  msgs = {};
  placed = {};

  void check(Rule r, Var v) {
    if (v in placed) 
      msgs += {error("Question already placed", r@\loc)};
    else   
      placed += {v};
    if (v notin qt) 
      msgs += {error("Undefined question", r@\loc)};
    //else
    //   return r[@link=...];
  }
  
  void checkType(WidgetType w, Type t) {
    if (!compatible(t, w)) 
      msgs += {error("Widget incompatible to type", w@\loc)};
  }
  
  void checkStyle(Style y, Type t) {
    ws = [ w | /WidgetType w := y ];
    if (WidgetType w <- ws) 
      checkType(w, t);
    if (size(ws) > 1) {
      msgs += { warning("Widget already defined", w@\loc) | w <- tail(ws) };  
    }
  }
  
  top-down visit (s) {
    case r:(Rule)`question <Var v>`: check(r, v);
    case r:(Rule)`question <Var v> <Style y>`: {
       check(r, v);
       if (v in qt) 
         checkStyle(y, qt[v]);
    }
    case r:(Rule)`default <Type t> <Style y>`: checkStyle(y, t);      
  }
  
  qs = domain(qt);
  if (placed & qs != qs) {
    missing = intercalate(", ", [ "<q>" | q <- qs - placed ]);
    // should we link each error to the var in the questionnaire?
    msgs += {error("Missing placement for <missing>", s.name@\loc)}; 
  }
  
  return msgs;
}

bool compatible((Type)`boolean`, (WidgetType)`checkbox`) = true;
bool compatible((Type)`boolean`, (WidgetType)`radio(<String _>, <String _>)`) = true;
bool compatible((Type)`integer`, (WidgetType)`textbox`) = true;
bool compatible((Type)`integer`, (WidgetType)`slider(<Integer _>, <Integer _>, <Integer _>)`) = true;
bool compatible((Type)`integer`, (WidgetType)`spinbox`) = true;
bool compatible((Type)`money`, (WidgetType)`textbox`) = true;
bool compatible((Type)`money`, (WidgetType)`spinbox`) = true;
default bool compatible(Type _, WidgetType _) = false;
