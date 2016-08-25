module lang::demoqles::unless::Plugin

import lang::demoqles::unless::Unless;
import lang::demoqles::ql::Bind;
import lang::demoqles::unless::Check;
import lang::demoqles::ql::Eval;
import lang::demoqles::ql::Outline;
import lang::demoqles::unless::Form2HTML;
import lang::demoqles::ql::Patch;


import ParseTree;
import util::IDE;
import Message;
import IO;

private str DEMO_QL ="DemoQL+unless";

anno rel[loc, loc, str] Tree@hyperlinks;

public void setupQL() {
  bool doVisibility = false;
  
  registerLanguage(DEMO_QL, "dql-unless", Tree(str src, loc l) {
    return parse(#start[Form], src, l);
  });
  
  contribs = {
     outliner(node(Tree pt) {
      if (Form f := pt.top) {
        return outline(f);
      }
      throw "Error: not a form";
    }),
    
    annotator(Tree(Tree pt) {
      if (Form f := pt.args[1]) {
        inf = resolve(f);
        msgs = checkForm(f, inf);
        return pt[@messages=msgs][@hyperlinks=computeXRef(inf)][@docs=computeDocs(inf)];
      }
      return pt[@messages={error("BUG: not a form", pt@\loc)}];
    }),
    
    liveUpdater(lrel[loc,str] (&T<:Tree pt) {
      if (Form f := pt.top) {
        inf = resolve(f);
        msgs = checkForm(f, inf);
        if (msgs == {}) {
          env = evalForm(f);
	        //for (k <- env) {
	        //  println("<k>: <env[k]>");
	        //}
          return patch(f, env, doVisibility);
        }
      }
      return [];
    }),
    
    menu(menu("Demoqles+Unless", [
        toggle("Visualize visibility", 
          bool() { return doVisibility; }, 
          void((&T<:Tree) tree, loc selection) { doVisibility = !doVisibility; })])),
    
    builder(set[Message] (Tree pt) {
      if (Form f := pt.args[1]) {
        inf = resolve(f);
        msgs = checkForm(f, inf);
        if (msgs == {}) {
          h = pt@\loc[extension="html"].top;
          writeFile(h, ql2html(f, inf));
          //temp = pt@\loc[extension="smt2"];
          //return verifyForm(f, temp);
        }
        return msgs;
      }
      return {error("BUG: Not a form", pt@\loc)};
    })
  };
  
  registerContributions(DEMO_QL, contribs);
}

