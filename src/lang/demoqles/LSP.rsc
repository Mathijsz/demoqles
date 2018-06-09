module lang::demoqles::LSP

import lang::demoqles::ql::QL;
import lang::demoqles::ql::Bind;
import lang::demoqles::ql::Check;

import LanguageServer;
import Protocol;

import ParseTree;
import IO;
import Set;
import Relation;
import String;

str languageName = "dql";

tuple[Form form, Info info] infoFromFile(loc file) = infoFromTree(parse(#start[Form], readFile(toLocation(file.uri)), file));

tuple[Form form, Info info] infoFromTree(Tree tree) {
  if (Form f := tree.args[1]) {
    return <f, resolve(f)>;
  }
  return <parse(#Form, "form undefined {}"), <<{},{}>,{}>>;
}

Info getInfo(loc file) = infoFromFile(file).info;

set[Message] getMessages(loc file) = checkForm(fi.form, fi.info)
  when fi := infoFromFile(file);

LSPResponse allDiagsFromDocument(TextDocument doc) {
  try {
    return publishDiagnostics(doc.uri.uri,
      [ diagnostic(m.at, m.msg, severity=convertMessageLevel(m)) | m <- getMessages(doc.uri)],
      methodOverride = "textDocument/publishDiagnostics");
  }
  catch ParseError(loc l):
    return publishDiagnostics(doc.uri.uri, [diagnostic(l, "Parse error", severity=diagSeverity["Error"])],
      methodOverride = "textDocument/publishDiagnostics");
}

bool isOnLocation(loc p, loc w) = p.offset >= w.offset && p.offset <= w.offset + w.length;

void registerLSP() {
  register(languageName,
    LSPResponse (LSPRequest request) {
      switch (request) {
        case initialize(): {
          return initializeResult();
        }
        case definition(document): {
          for (usage <- getInfo(document.uri).refs.use, isOnLocation(document.uri, usage.use)) {
            return locationResult(usage.def.uri, usage.def);
          }
        }
        case references(document): {
          Info inf = getInfo(document.uri);

          for (usage <- inf.refs.use, isOnLocation(document.uri, usage.use))
            return locationsResult([ u.use, u.def | u <- inf.refs.use, u.def == usage.def]);
          for (def <- inf.refs.def, isOnLocation(document.uri, def.def))
            return locationsResult([ z | z <- toList(invert(inf.refs.use)[def.def]) ] + [def.def]);
        }
        case didOpen(document): {
          return allDiagsFromDocument(document);
        }
        case didClose(document): {
          return publishDiagnostics(document.uri.uri, [],
            methodOverride = "textDocument/publishDiagnostics");
        }
        case didSave(document): {
          return allDiagsFromDocument(document);
        }
      }
      return none();
    }
  );
}

void deregisterLSP() {
  deregister(languageName);
}

void startLSP() {
  registerLSP();
  startServer();
}

void stopLSP() {
  deregisterLSP();
  stopServer();
}