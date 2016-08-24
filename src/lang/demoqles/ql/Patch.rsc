module lang::demoqles::ql::Patch

import lang::demoqles::ql::Eval;
import lang::demoqles::ql::QL;
import ParseTree;

lrel[loc, str] patch(Form f, Env env) {
  lrel[loc, str] p = [];
  
  top-down visit (f) {
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
  
  return p;
}