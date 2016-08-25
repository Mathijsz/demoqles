module lang::demoqles::const::Bind

import lang::demoqles::const::Const;
extend lang::demoqles::ql::Bind;

void resolve((Question)`const <Id x>: <Type t> = <Const _>`, void(Id, Label) label, void(Id,Type) def) {
  def(x, t);
}
