module lang::demoqles::Plugin

import lang::demoqles::ql::QL;
import lang::demoqles::ql::Bind;
import lang::demoqles::ql::Check;
import lang::demoqles::ql::Eval;
import lang::demoqles::ql::Verify;
import lang::demoqles::ql::Outline;
import lang::demoqles::ql::Form2HTML;
import lang::demoqles::ql::Patch;
import lang::demoqles::qls::QLS;
import lang::demoqles::qls::Check;
import lang::demoqles::qls::Outline;
import lang::demoqles::qls::Sheet2HTML;


import ParseTree;
import util::IDE;
import Message;
import IO;

private str DEMO_QL ="DemoQL";
private str DEMO_QLS ="DemoQLS";

anno rel[loc, loc, str] Tree@hyperlinks;

public void setupQL() {
  bool doVisibility = false;
  
  registerLanguage(DEMO_QL, "dql", Tree(str src, loc l) {
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
    
    menu(menu("Demoqles", [
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


public void setupQLS() {
  registerLanguage(DEMO_QLS, "dqls", Tree(str src, loc l) {
    return parse(#start[Stylesheet], src, l);
  });
  
  contribs = {

    annotator(Tree(Tree pt) {
       msgs = doWithSheetAndForm(pt, checkSheet);
       return pt[@messages=msgs];
    }),
    
    outliner(node(Tree pt) {
      if (Stylesheet s := pt.args[1]) {
        return outline(s);
      }
      return error("BUG: not a sheet", pt@\loc);
    }),
    
    builder(set[Message] (Tree pt) {
      set[Message] doit(Stylesheet s, Form f) {
        l = pt@\loc;
        l.extension = "html";
        writeFile(l, qls2html(s, f));
        return {};
      }
      return doWithSheetAndForm(pt, doit);
    })
  };
  
  registerContributions(DEMO_QLS, contribs);
}


set[Message] doWithSheetAndForm(Tree pt, set[Message](Stylesheet, Form) doit) {
  if (Stylesheet s := pt.args[1]) {
    l = s@\loc;
    l.extension = "dql";
    try {
      pt2 = parse(#start[Form], l);
      if (Form f := pt2.args[1]) {
        f_and_defs = definitions(f);
        f = bind(f_and_defs[0], f_and_defs[1]);
        msgs = tc(f);
        if (msgs == {}) {
          return doit(s, f);
        }
        return {error("QL file has errors", s.name@\loc)};
      }
      return {error("BUG: QL file is not valid", s.name@\loc)};
    }
    catch _: 
      return {error("Can\'t parse QL file", s.name@\loc)};
  }
  return {error("BUG: Not a sheet", pt@\loc)};
}