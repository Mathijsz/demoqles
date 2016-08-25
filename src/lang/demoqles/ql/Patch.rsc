module lang::demoqles::ql::Patch

import lang::demoqles::ql::Eval;
import lang::demoqles::ql::QL;
import ParseTree;
import IO;

lrel[loc, str] toggleVisibility(Question q, bool visible) {
  p = [];
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
  return p;
}

lrel[loc, str] patch(Form f, Env env, bool visibility) {
  lrel[loc, str] p = [];
  hasInput = false;
  
  top-down visit (f) {
    case Question q: {
      <hasInput2, p2> = patch(q, env, visibility);
      hasInput = hasInput || hasInput2;
      p += p2;
    }
  }
  if (hasInput) {
    return p;
  }
  return [];
}

tuple[bool, lrel[loc, str]] patch((Question)`<Label _> <Id x>: <Type _> <Value _>`, Env env, bool visibility)
  = <true, []>; 

      
tuple[bool, lrel[loc, str]] patch((Question)`if (<Expr c>) <Question q>`, Env env, bool visibility) {
  if (visibility) {
    return <false, toggleVisibility(q, true := eval(c, env))>;
  } 
  return <false, []>;
}
    
tuple[bool, lrel[loc, str]] patch((Question)`(<Question* qs>)`, Env env, bool visibility) {
  p = [];
  if (!visibility) {
    l1 = q@\loc;
    l1.length = 1;
    p += [<l1, "{">];
    l2 = q@\loc;
    l2.offset += l2.length - 1;
    l2.length = 1;
    p += [<l2, "}">];
  }
  return <false, p>;
}

tuple[bool, lrel[loc, str]] patch((Question)`if (<Expr c>) <Question q1> else <Question q2>`, Env env, bool visibility) {
  if (visibility) {
    b = true := eval(c, env); 
    return <false, toggleVisibility(q1, b)
       + toggleVisibility(q2, !b)>;
  }
  return <false, []>;
} 
      
tuple[bool, lrel[loc, str]] patch((Question)`<Label _> <Id x>: <Type _> = <Expr e>`, Env env, bool visibility) {
  loc l = e@\loc;
  l.offset += l.length + 1;
  l.length = 0;
  return <false, [<l, "[<env[x]>]">]>;
}

tuple[bool, lrel[loc, str]] patch((Question)`<Label _> <Id x>: <Type _> = <Expr _> [<Expr v>]`, Env env, bool visibility) {
  str newVal = "<env[x]>";
  if (newVal != "<v>") {
    return <false, [<v@\loc, "<env[x]>">]>;
  }
  return <false, []>;
}

tuple[bool, lrel[loc, str]] patch(Question _, Env env, bool visibility) = <false, []>;