-module(macro).
-compile(export_all).

file(F) -> case file:read_file(F) of
        {ok,B} ->
            {ok,unicode:characters_to_list(B)};
        {error,E} ->
            io:format(lists:concat(["File ", F, " : ", E, "~n"])),
            {error,file}
    end.

lexer({error,E}) -> {error,E};
lexer({ok,S}) -> case macro_lexer:string(S) of
        {ok,T,_} -> {ok,T};
        {error,{L,A,X},_} ->
            io:format(lists:concat(["Line ", L, " ", A, " : ", element(2,X)])),
            io:format("~n"),
            {error,lexer}
    end.

parser({error,E}) -> {error,E};
parser({ok,T}) -> case macro_parser:parse(T) of
        {ok,AST} -> {ok,AST};
        {error,{L,A,S}} ->
            io:format(lists:concat(["Line ", L, " ", A, " : "| S])),
            io:format("~n"),
            {error,parser}
    end.

% helpers
file2str(F) -> file(F++".macro").
file2lex(F) -> lexer(file2str(F)).
file2ast(F) -> parser(file2lex(F)).
