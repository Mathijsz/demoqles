module lang::demoqles::ql::Bind

import lang::demoqles::ql::QL;
import lang::demoqles::ql::Types;
import Message;
import IO;
import ParseTree;
import List;
import Set;

alias Use = rel[loc use, loc def];
alias Def = rel[loc def, QLType typ];

alias Refs = tuple[Use use, Def def];
alias Labels = rel[Label label, loc question];
alias Info = tuple[Refs refs, Labels labels];

Info resolve(Form f) {
  // Lazy because of declare after use.
  map[loc, set[loc]()] useLazy = ();
  Def def = {};
  Labels labels = {};
  
  rel[Id, loc] env = {};    
  
  // Return a function that looks up declaration of `n` in defs when called.
  set[loc]() lookup(Id n) = set[loc]() { return env[n]; };


  void addUse(Id name) {
    useLazy[name@\loc] = lookup(name);
  }
  
  void addLabel(Id x, Label label) {
    labels += {<label, x@\loc>};
  }
  
  void addDef(Id n, Type t) {
    env += {<n, n@\loc>};
    def += {<n@\loc, qlType(t)>};
  }
  
  visit (f) {
    case Embed emb: println("Embed: <emb>");
    case Expr e: resolve(e, addUse);
    case Question q: resolve(q, addLabel, addDef);
  }
  
  // Force the closures in `use` to resolve references.
  use = { <u, d> | u <- useLazy, d <- useLazy[u]() };
  return <<use, def>, labels>;
}


void resolve((Expr)`<Id x>`, void(Id) use) {
  println("USE: <x>");
  use(x);
} 
 
default void resolve(Expr _, void(Id) use) { }   

void resolve((Question)`<Label l> <Id x>: <Type t>`, void(Id, Label) label, void(Id,Type) def) {
  label(x, l);
  def(x, t);
}

void resolve((Question)`<Label l> <Id x>: <Type t> <Value _>`, void(Id, Label) label, void(Id,Type) def) {
  label(x, l);
  def(x, t);
}
 
void resolve((Question)`<Label l> <Id x>: <Type t> = <Expr e>`, void(Id, Label) label, void(Id,Type) def) {
  label(x, l);
  def(x, t);
}     
 
void resolve((Question)`<Label l> <Id x>: <Type t> = <Expr e> <Value _>`, void(Id, Label) label, void(Id,Type) def) {
  label(x, l);
  def(x, t);
}     

default void resolve(Question _, void(Id, Label) label, void(Id,Type) def) {}

rel[loc,loc,str] computeXRef(Info i) 
  = { <u, d, "<l>"> | <u, d> <- i.refs.use, <l, d> <- i.labels }; 

map[loc, str] computeDocs(Info i) {
  docs = { <u, "<l>"> | <u, d>  <- i.refs.use, <l, d> <- i.labels };
  return ( k: intercalate("\n", toList(docs[k])) | k <- docs<0> );
}
  


