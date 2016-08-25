-module(exe).
-description('Exe Compiler').
-behaviour(supervisor).
-behaviour(application).
-export([init/1, start/2, stop/1]).
-compile(export_all).

opt()        -> [ set, named_table, { keypos, 1 }, public ].
tables()     -> [ programs ].
boot()       -> [ ets:new(T,opt()) || T <- tables() ],
                [ code:del_path(S) || S <- code:get_path(), string:str(S,"stdlib") /= 0 ].
unicode()    -> io:setopts(standard_io, [{encoding, unicode}]).
main(A)      -> unicode(), case A of [] -> mad:main(["sh"]); A -> console(A) end.
start()      -> start(normal,[]).
start(_,_)   -> unicode(), supervisor:start_link({local,exe},exe,[]).
stop(_)      -> ok.
init([])     -> boot(), mode("normal"), {ok, {{one_for_one, 5, 10}, []}}.
ver(_)       -> ver().
ver()        -> string:join([keyget(I,element(2,application:get_all_key(exe)))||I<-[description,vsn]]," ").
mode(S)      -> application:set_env(exe,mode,S).
mode()       -> application:get_env(exe,mode,"Exe").

console(S)   -> boot(),
                mad_repl:load(),
                Fold = lists:foldr(fun(I,O) ->
                      R = rev(I),
                      Res = lists:foldl(fun(X,A) -> exe:(atom(X))(A) end,hd(R),tl(R)),
                      io:format("~tp~n",[Res]),
                      []
                      end, [], string:tokens(S,[","])),
                halt(lists:sum(Fold)).

rev(X)           -> lists:reverse(X).
flat(X)          -> lists:flatten(X).
tokens(X,Y)      -> string:tokens(X,Y).
atom(X)          -> list_to_atom(cat([X])).
cat(X)           -> lists:concat(X).
keyget(K,D)      -> proplists:get_value(K,D).
keyget(K,D,I)    -> lists:nth(I+1,proplists:get_all_values(K,D)).

convert(A,S, nt) -> convert(A,S);
convert(A,S, _)  -> A.

convert([],Acc) -> rev(Acc);
convert([$>|T],Acc) -> convert(T,[61502|Acc]);
convert([$<|T],Acc) -> convert(T,[61500|Acc]);
convert([$:|T],Acc) -> convert(T,[61498|Acc]);
convert([$||T],Acc) -> convert(T,[61564|Acc]);
convert([H|T],Acc)  -> convert(T,[H|Acc]).

parse(X)   -> io:format("~tp~n",[macro:parse(bin(X))]).
bin(X)     -> unicode:characters_to_list(X).
display(X) -> io:format("~ts~n",[X]).

file(F) -> case file:read_file(convert(F,[],element(2,os:type()))) of
                {ok,Bin} -> bin(Bin);
                {error,_} -> mad(F) end.

mad(F)  -> case mad_repl:load_file(F) of
                {ok,Bin} -> Bin;
                {error,_} -> erlang:error({"File not found",F}) % <<>>
            end.

pad(D) -> lists:duplicate(D*7," ").

p(X) -> io:format("~ts~n",[unicode:characters_to_list(lists:flatten(pp(X,1)))]).

color(S,gray)   -> ["\e[38;2;187;187;187m",S,"\e[0m"];
color(S,key)    -> ["\e[36;20;52;52;200m",  S,"\e[0m"].

left()     -> color("(",  gray).
right()    -> color(")",  gray).
arrow()    -> color(" → ",gray).
assign()   -> color(":=", gray).
colon()    -> color(":",  gray).
lambda()   -> color(" λ ",  gray).
pi()       -> color(" ∀ ",  gray).
type()     -> color("define ",key).
data()     -> color("data   ",key).
record()   -> color("record ",key).

pp(X,P) when is_list(X) andalso length(X) > 1    -> [left(),string:join([pp(XI,P)||XI<-X]," "),right()];
pp(X,P) when is_list(X)                          -> [string:join([pp(XI,P)||XI<-X]," ")];
pp({assign,L,   {mk,A,B}},P) when is_list(B)     -> [pp(A,P),assign(),string:join([[left(),pp(BI,P),right()]||BI<-B],"")];
pp({assign,L,   {mk,A,B}},P)                     -> [pp(A,P),assign(),pp(B,P)];
pp({preassign,L,{mk_match,[[A]],B}},P)           -> [pp(A,P)];
pp({preassign,L,{mk_type,A}},P)                  -> [type(),[pp(A,P)]];
pp({pretype,L,  {mk,[X],List}},P)                -> [[pp(XI,P)||XI<-X],
                                                     string:join([[left(),pp(I,P),right(),""]||I<-List],"\n"++pad(P))
                                                     ];
pp({id,_,{var,X}},P)                             -> [X];
pp({expr,L,     {mk_new,X}},P)                   -> [pp(XI,P)||XI<-X];
pp({expr,L,     {mk_define,X}},P)                -> [pp(X,P)];
pp({expr,L,     {mk_id,X}},P)                    -> [pp(X,P)];
pp({expr,L,     {mk_forall,Xs,Y}},P)             -> [pi(),string:join([[pad(P-1),left(),pp(X,P),right()]||X<-Xs]," ")," ",pp(Y,P)];
pp({expr,L,     {mk_lambda,X,Y}},P)              -> [lambda(),left(),pp(X,P),right(),arrow(),pp(Y,P)];
pp({expr,L,     {mk_data,Xs}},P)                 -> [data(),string:join([[pad(P-1),left(),pp(X,P),right()]||X<-Xs],"\n"++pad(P))];
pp({expr,L,     {mk_record,Xs}},P)               -> [record(),string:join([[pad(P-1),left(),pp(X,P),right()]||X<-Xs],"\n"++pad(P))];
pp({expr,L,     {mk_arrow,Is,Os}},P)             -> [[pp(I,P+1)||I<-Is],arrow(),pp(Os,P)];
pp({type,L,     {mk,I,List}},P)                  -> [pp(I,P),colon(),pp(List,P)];
pp(Term,P) -> [].

