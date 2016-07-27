-module(macro).
-compile(export_all).

file(F) -> case file:read_file(F) of
        {ok,B} ->
            {ok,unicode:characters_to_list(B)};
        {error,E} ->
            io:format(lists:concat(["File ", F, " : ", E, "~n"])),
            {error,file}
    end.

lexer(S) -> case macro_lexer:string(S) of
        {ok,T,_} -> {ok,T};
        {error,{L,A,X},_} ->
            io:format(lists:concat(["Line ", L, " ", A, " : ", element(2,X)])),
            io:format("~n"),
            {error,lexer}
    end.

parser(T) -> case macro_parser:parse(T) of
        {ok,AST} -> {ok,AST};
        {error,{L,A,S}} ->
            io:format(lists:concat(["Line ", L, " ", A, " : "| S])),
            io:format("~n"),
            {error,parser}
    end.

%
maybe_bind(F,{ok,Y}) -> F(Y);
maybe_bind(F,E)      -> E.

% helpers
file2str(F) -> file(lists:concat(["test","/",F,".","macro"])).
file2lex(F) -> maybe_bind(fun lexer/1, file2str(F)).
file2ast(F) -> maybe_bind(fun parser/1, file2lex(F)).
