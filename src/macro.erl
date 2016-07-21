-module(macro).
-compile(export_all).

file(F) ->  {ok,B} = file:read_file(F), unicode:characters_to_list(B).
lexer(S) -> {ok,T,_} = macro_lexer:string(S), T.
parser(T) -> {ok,AST} = macro_parser:parse(T), AST.
file2ast(F) -> {ok,parser(lexer(file(F++".macro")))}.
