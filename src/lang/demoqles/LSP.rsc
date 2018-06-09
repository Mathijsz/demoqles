module lang::demoqles::LSP

import lang::demoqles::ql::QL;
import lang::demoqles::ql::Bind;
import lang::demoqles::ql::Check;

import LanguageServer; // Needs to be in search path (Properties -> Project References -> check 'rls-project')
import Protocol;

import ParseTree;
import IO;
import Set;
import Relation;
import String;

str languageName = "dql";

tuple[Form form, Info info] getInfoAndForm(loc file) = InfoFromTree(parse(#start[Form], readFile(toLocation(file.uri)), file));
//tuple[Form form, Info info] getInfoAndForm(str contents) = InfoFromTree(parse(#start[Form], contents));

tuple[Form form, Info info] InfoFromTree(Tree tree) {
  if (Form f := tree.args[1]) {
    return <f, resolve(f)>;
  }
  return <parse(#Form, "form undefined {}"), <<{},{}>,{}>>;
}

Info getInfo(loc file) = getInfoAndForm(file).info;
//Info getInfo(str contents) = getInfoAndForm(contents).info;

set[Message] getMessages(loc file) = checkForm(fi.form, fi.info)
  when fi := getInfoAndForm(file);


LSPResponse allDiagsFromDocument(TextDocument doc) {
  try {
    return publishDiagnostics(doc.uri.uri,
      [ diagnostic(fixLocation(m.at), m.msg, severity=convertLevel(m)) | m <- getMessages(doc.uri)],
      methodOverride = "textDocument/publishDiagnostics");
  }
  catch ParseError(loc l):
    return publishDiagnostics(doc.uri.uri, [diagnostic(fixLocation(l), "Parse error", severity=diagSeverity["Error"])],
      methodOverride = "textDocument/publishDiagnostics");
}

int convertLevel(Message m) {
  if (m is error)     return diagSeverity["Error"];
  if (m is warning)   return diagSeverity["Warning"];
  if (m is info)      return diagSeverity["Information"];
  return diagSeverity["Hint"];
}

// The original plugins' locations start at 0 for columns, yet at 1 for lines
// Subtract 1 off line numbers to line them up with our client
loc fixLocation(loc l) {
  l.begin.line -= 1;
  l.end.line -= 1;
  return l;
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
            return locationResult(usage.def.uri, fixLocation(usage.def));
          }
        }
        case references(document): {
          Info inf = getInfo(document.uri);

          for (usage <- inf.refs.use, isOnLocation(document.uri, usage.use))
            return locationsResult([ fixLocation(u.use), fixLocation(u.def) | u <- inf.refs.use, u.def == usage.def]);
          for (def <- inf.refs.def, isOnLocation(document.uri, def.def))
            return locationsResult([ fixLocation(z) | z <- toList(invert(inf.refs.use)[def.def]) ] + [fixLocation(def.def)]);
          return none();
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