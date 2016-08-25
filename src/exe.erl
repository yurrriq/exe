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

p(X) -> io:format("~ts~n",[color(unicode:characters_to_binary(lists:flatten(pp(X,1))),[])]).

ansi(S,gray)   -> ["\e[38;2;187;187;187m",S,"\e[0m"];
ansi(S,key)    -> ["\e[36;20;52;52;200m",  S,"\e[0m"];
ansi(S,_  )    -> S.

color(<<>>,Acc) -> lists:reverse(Acc);
color(<<"(",Rest/binary>>,Acc)      -> color(Rest,[ansi("(",gray)|Acc]);
color(<<")",Rest/binary>>,Acc)      -> color(Rest,[ansi(")",gray)|Acc]);
color(<<","/utf8,Rest/binary>>,Acc) -> color(Rest,[ansi(",",gray)|Acc]);
color(<<"→"/utf8,Rest/binary>>,Acc) -> color(Rest,[ansi("→",gray)|Acc]);
color(<<":=",Rest/binary>>,Acc)     -> color(Rest,[ansi(":=",gray)|Acc]);
color(<<"λ"/utf8,Rest/binary>>,Acc) -> color(Rest,[ansi("λ",gray)|Acc]);
color(<<"∀"/utf8,Rest/binary>>,Acc) -> color(Rest,[ansi("∀",gray)|Acc]);
color(<<"record",Rest/binary>>,Acc) -> color(Rest,[ansi("record",key)|Acc]);
color(<<"data",Rest/binary>>,Acc)   -> color(Rest,[ansi("data",key)|Acc]);
color(<<"new",Rest/binary>>,Acc)    -> color(Rest,[ansi("new",key)|Acc]);
color(<<"define",Rest/binary>>,Acc) -> color(Rest,[ansi("define",key)|Acc]);
color(<<C/utf8,Rest/binary>>,Acc)   -> color(Rest,[C|Acc]).

left()     -> ansi("(",    def).
right()    -> ansi(")",    def).
arrow()    -> ansi(" → ",  def).
assign()   -> ansi(" := ", def).
colon()    -> ansi(": ",   def).
lambda()   -> ansi(" λ ",  def).
pi()       -> ansi(" ∀ ",  def).
type()     -> ansi("\ndefine ", def).
data()     -> ansi("\ndata   ", def).
new()      -> ansi("new ",      def).
record()   -> ansi("\nrecord ", def).

-define(WIDTH, 90).

pc(X,P) when is_list(X) andalso length(X) > 1    -> [string:join([pp(XI,P)||XI<-X],".")];
pc(X,P) -> pp(X,P).

pp(X,P) when is_list(X) andalso length(X) > 1    -> [left(),string:join([pp(XI,P)||XI<-X]," "),right()];
pp(X,P) when is_list(X)                          -> [string:join([pp(XI,P)||XI<-X]," ")];
pp({assign,L,   {mk,A,B}},P) when is_list(B)     -> [pp(A,P),assign(),string:join([pp(BI,P)||BI<-B]," ")];
pp({assign,L,   {mk,A,B}},P)                     -> [type(),format_line(pp(A,P),P,?WIDTH),assign(),pp(B,P)];
pp({preassign,L,{mk_match,[[A]],B}},P)           -> [pp(A,P)];
pp({preassign,L,{mk_type,A}},P)                  -> [pp(A,P)];
pp({pretype,L,  {mk,X,List}},P)                  -> [string:join([pp(XI,P)||XI<-X],","),
                                                     string:join([[left(),pp(I,P),right()," "]||I<-List]," ")];
pp({id,_,{var,X}},P)                             -> [X];
pp({expr,L,     {mk_new,X}},P)                   -> [new(),[pp(XI,P)||XI<-X]];
pp({expr,L,     {mk_define,X}},P)                -> [pp(X,P)];
pp({expr,L,     {mk_id,X}},P)                    -> [pc(X,P)];
pp({expr,L,     {mk_forall,Xs,Y}},P)             -> [pi(),string:join([[left(),pp(X,P),right()]||X<-Xs]," "),arrow(),pp(Y,P-1)];
pp({expr,L,     {mk_lambda,X,Y}},P)              -> [lambda(),left(),pp(X,P),right(),arrow(),pp(Y,P)];
pp({expr,L,     {mk_data,Xs}},P)                 -> [data(),string:join([[pad(P-1),left(),pp(X,P),right()]||X<-Xs],"\n"++pad(P)),"\n"];
pp({expr,L,     {mk_record,Xs}},P)               -> [record(),format_line(string:join([[left(),[pp(X,P)],right()]||X<-Xs],"\n"++pad(P)),P+1,?WIDTH),"\n"];
pp({expr,L,     {mk_arrow,Is,Os}},P)             -> [[pp(I,P+1)||I<-Is],arrow(),pp(Os,P)];
pp({type,L,     {mk,I,List}},P)                  -> [pc(I,P),colon(),string:join([pp(L,P)||L<-List]," ")];
pp(Term,P)                                       -> [].

format_line(S,I,P) ->
    SSS=string:tokens(lists:flatten(S),"\n"),
    XXX=string:join(lists:foldr(fun (SS,Acc) ->
        FL= string:tokens(SS,"→"),
        {St,_}=lists:foldr(fun(A,{L,Acc}) ->
               AccA = length(A),
               {String,NewAcc} = case Acc+AccA>=P of true -> {A++"\n"++pad(I),AccA};
                                                    false -> {A,Acc+AccA} end,
               {[String|L],NewAcc} end,{[],0},FL),
        Joined = lists:flatten(unicode:characters_to_list(string:join(St,"→"))),
        [Joined|Acc]
      end,[],SSS),"\n"),
    XXX.
