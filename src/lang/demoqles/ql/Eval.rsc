module lang::demoqles::ql::Eval

import lang::demoqles::ql::QL;
import util::Math;
import String;

alias Env = map[Id, value];

value initValue((Type)`boolean`) = false;
value initValue((Type)`integer`) = 0;
value initValue((Type)`money`) = 0.0;
value initValue((Type)`string`) = "";

Env initEnv(Form f) = ( x: initValue(q.\type) | /Question q := f, q has var, (Var)`<Id x>` := q.var );

Env userEnv(Form f) = ( x: eval(v, ()) | /(Question)`<Label _> <Id x>: <Type _> [<Expr v>]` := f );

Env evalForm(Form f) {
  env = initEnv(f) + userEnv(f);
  solve (env) {
    visit (f) {
      case (Question)`<Label _> <Id x>: <Type _> = <Expr e>`: 
        env[x] = eval(e, env);
      case (Question)`<Label _> <Id x>: <Type _> = <Expr e> <Value _>`: 
        env[x] = eval(e, env);
    }
  }
  return env;
}

value eval((Expr)`<Id x>`, Env env) = env[x];
 
value eval((Expr)`(<Expr e>)`, Env env) = eval(e, env);

value eval((Expr)`<Integer x>`, Env env) = toInt("<x>");

value eval((Expr)`<Money x>`, Env env) = toReal("<x>");

value eval((Expr)`true`, Env env) = true;

value eval((Expr)`false`, Env env) = false;

value eval((Expr)`<String x>`, Env env) = "<x>"[1..-1];

value eval((Expr)`!<Expr e>`, Env env) = !v 
  when 
    bool v := eval(e, env);

value eval((Expr)`<Expr lhs> * <Expr rhs>`, Env env) 
  =  v1 * v2
  when 
    num v1 := eval(lhs, env),
    num v2 := eval(rhs, env);


value eval((Expr)`<Expr lhs> / <Expr rhs>`, Env env)
  =  v1 / v2
  when 
    num v1 := eval(lhs, env),
    num v2 := eval(rhs, env);
    
value eval((Expr)`<Expr lhs> + <Expr rhs>`, Env env)
  =  v1 + v2
  when 
    num v1 := eval(lhs, env),
    num v2 := eval(rhs, env);
    
value eval((Expr)`<Expr lhs> - <Expr rhs>`, Env env) 
  =  v1 - v2
  when 
    num v1 := eval(lhs, env),
    num v2 := eval(rhs, env);
    
value eval((Expr)`<Expr lhs> \> <Expr rhs>`, Env env)
  =  v1 > v2
  when 
    num v1 := eval(lhs, env),
    num v2 := eval(rhs, env);
    
value eval((Expr)`<Expr lhs> \>= <Expr rhs>`, Env env)
  =  v1 >= v2
  when 
    num v1 := eval(lhs, env),
    num v2 := eval(rhs, env);
    
value eval((Expr)`<Expr lhs> \< <Expr rhs>`, Env env)
  =  v1 < v2
  when 
    num v1 := eval(lhs, env),
    num v2 := eval(rhs, env);
    
value eval((Expr)`<Expr lhs> \<= <Expr rhs>`, Env env)
  =  v1 <= v2
  when 
    num v1 := eval(lhs, env),
    num v2 := eval(rhs, env);
    
value eval((Expr)`<Expr lhs> == <Expr rhs>`, Env env)
  =  v1 == v2
  when 
    value v1 := eval(lhs, env),
    value v2 := eval(rhs, env);
    
value eval((Expr)`<Expr lhs> != <Expr rhs>`, Env env)
  =  v1 != v2
  when 
    value v1 := eval(lhs, env),
    value v2 := eval(rhs, env);
    
value eval((Expr)`<Expr lhs> && <Expr rhs>`, Env env)
  =  v1 && v2
  when 
    bool v1 := eval(lhs, env),
    bool v2 := eval(rhs, env);
    
value eval((Expr)`<Expr lhs> || <Expr rhs>`, Env env)
  =  v1 || v2
  when 
    bool v1 := eval(lhs, env),
    bool v2 := eval(rhs, env);
