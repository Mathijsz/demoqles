module lang::demoqles::unless::Patch

import lang::demoqles::unless::Unless;
extend lang::demoqles::ql::Patch;

tuple[bool, lrel[loc, str]] patch((Question)`unless (<Expr c>) <Question q>`, Env env, bool visibility) {
  if (visibility) {
    return <false, toggleVisibility(q, false := eval(c, env))>;
  } 
  return <false, []>;
}