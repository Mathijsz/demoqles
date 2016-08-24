module lang::demoqles::qls::QLS

extend lang::demoqles::ql::QL;

start syntax Stylesheet
  = stylesheet: "stylesheet" Id name Page* pages;

syntax Page = page: "page" Id name Rule rule;

syntax Rule
  = section: "section" String title Rule rule
  | question: "question" Var name
  | styledQuestion: "question" Var name Style style
  | defaultStyle: "default" Type type Style style
  | @Foldable group: "{" Rule* rules "}"
  ;

syntax Style
  = style: Id property ":" Value val
  | widget: "widget" WidgetType widget
  | group: "{" Style* styles "}"
  ;
  
syntax WidgetType
  = "checkbox"
  | "textbox"
  | "slider" "(" Integer "," Integer "," Integer ")"
  | "spinbox"
  | "radio" "(" String "," String ")" 
  ;

syntax Value
  = integer: Integer
  | money: Money
  | string: String
  | symbol: Id
  | color: Color
  ;
  
lexical Color
  = @category="Constant" [#][0-9A-F][0-9A-F][0-9A-F][0-9A-F][0-9A-F][0-9A-F];
  