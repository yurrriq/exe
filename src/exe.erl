-module(exe).
-description('Exe Prover').
-behaviour(supervisor).
-behaviour(application).
-export([init/1, start/2, stop/1]).
-compile(export_all).

% provided functions

a(X)        -> {_,[R]}=exe_parse:expr(flat([exe:str(X)]),[]),R.
main(A)     -> mad:main(A).
start()     -> start(normal,[]).
start(_,_)  -> supervisor:start_link({local,exe},exe,[]).
stop(_)     -> ok.
init([])    -> scan(), {ok, {{one_for_one, 5, 10}, []}}.
type(F)     -> {_,[X]}=parse(lists:concat(["priv/Exe/",F])),X.
parse(F)    -> exe_parse:expr(read(F),[]).
str(F)      -> exe:rev(exe:flat(exe_tok:tokens(unicode:characters_to_binary(F),0,{1,[]},[]))).
read(F)     -> exe:rev(exe:flat(exe_tok:tokens(file(F),0,{1,[]},[]))).
file(F)     -> {ok,Bin} = read_file(F), Bin.
scan()      -> [ show(F) || F <- filelib:wildcard("priv/Exe/**/*"), filelib:is_dir(F) /= true ], ok.
show(F)     -> error("~130p~n~ts~n~130tp~n",[F,file(F),parse(F)]).

% relying function

rev(X)       -> lists:reverse(X).
flat(X)      -> lists:flatten(X).
tokens(X,Y)  -> string:tokens(X,Y).
print(S,A)   -> io_lib:format(S,A).
error(S,A)   -> error_logger:info_msg(S,A).
read_file(F) -> file:read_file(F).
