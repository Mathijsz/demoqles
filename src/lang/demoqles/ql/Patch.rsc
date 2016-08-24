module lang::demoqles::ql::Patch

import lang::demoqles::ql::Eval;
import lang::demoqles::ql::QL;
import ParseTree;
import IO;

lrel[loc, str] patch(Form f, Env env) {
  lrel[loc, str] p = [];
  hasInput = false;
  
  void toggleVisibility(Question q, bool visible) {
    if (visible) {
      if ((Question)`(<Question* qs>)` := q) {
        l1 = q@\loc;
        l1.length = 1;
        p += [<l1, "{">];
        l2 = q@\loc;
        l2.offset += l2.length - 1;
        l2.length = 1;
        p += [<l2, "}">];
      }
    }
    else {
      if ((Question)`{<Question* qs>}` := q) {
        l1 = q@\loc;
        l1.length = 1;
        p += [<l1, "(">];
        l2 = q@\loc;
        l2.offset += l2.length - 1;
        l2.length = 1;
        p += [<l2, ")">];
      }
      else if ((Question)`(<Question* qs>)` !:= q){
        l1 = q@\loc;
        l1.length = 0;
        l2 = q@\loc;
        l2.offset += l2.length;
        l2.length = 0;
        p += [<l1, "(">, <l2, ")">];
      }
    }
  }
  
  top-down visit (f) {
    case (Question)`<Label _> <Id x>: <Type _> <Value _>`:
      hasInput = true;
      
    case (Question)`if (<Expr c>) <Question q>`: {
      println("Eval of condition: <c> = <eval(c, env)>");
      toggleVisibility(q, true := eval(c, env)); 
    }

    case (Question)`if (<Expr c>) <Question q1> else <Question q2>`: {
      b = true := eval(c, env); 
      toggleVisibility(q1, b);
      toggleVisibility(q2, !b);
    } 
      
    case (Question)`<Label _> <Id x>: <Type _> = <Expr e>`: {
      loc l = e@\loc;
      l.offset += l.length + 1;
      l.length = 0;
      p += [<l, "[<env[x]>]">];
    }
    case (Question)`<Label _> <Id x>: <Type _> = <Expr _> [<Expr v>]`: {
      str newVal = "<env[x]>";
      if (newVal != "<v>") {
        p += [<v@\loc, "<env[x]>">];
      }
    }
  }
  if (hasInput) {
    return p;
  }
  return [];
}