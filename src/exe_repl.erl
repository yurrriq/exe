-module(exe_repl).
-include("exe_repl.hrl").
-compile(export_all).

color_profile() -> [{string, {dim,yellow,none}},
                    {digits, {dim,green,none}},
                    {prompt, {dim,red,none}},
                    {keyword,{underscore,magenta,none}},
                    {warning,{dim,red,none}},
                    {error,  {underscore,red,none}},
                    {term,   {bright,cyan,none}}].

t(Lines) -> t_a(Lines). % only ANSI, for now.

ctrl_sequence(ansi,Attrs) -> ctrl_sequence(ansi,Attrs,[]).
ctrl_sequence(ansi,[{F,Attr}|T],Acc) -> ctrl_sequence(ansi,T,[apply(exe_pretty,F,[ansi|[Attr]])| Acc]);
ctrl_sequence(ansi,[],Acc) -> lists:concat([ "\e[" , string:join(lists:reverse(Acc),";") , "m"]).

t_a(Lines) -> t_a(Lines,[]).
t_a([Line|T], Acc) -> {Attrs,Str} = Line, t_a(T,[string:concat(ctrl_sequence(ansi,Attrs),Str)|Acc]);
t_a([],Acc) -> lists:flatten(lists:reverse(Acc)).

format_strs(TextAttrs) ->
	F = fun(AttrTuple) ->
			{Class,{TxtAttr,FgColor,BgColor}} = AttrTuple,
			Attrs = lists:filter(fun(A) -> {_,V} = A, V =/= none end,
					[{text_attr,TxtAttr}, {fg_color, FgColor}, {bg_color, BgColor}]),
			FmtStr = t([ { Attrs, "~ts"}, { [{text_attr,reset}], ""}]),
			{Class, FmtStr} end, lists:map(F,TextAttrs).

q(Class,Str) ->
   case proplists:get_value(Class,format_strs(color_profile())) of
        undefined -> Str;
              Fmt -> lists:flatten(io_lib:format(Fmt,[Str])) end.

start()                   -> start(false, false).
start(init)               -> start(false, true);
start(NoCtrlG)            -> start(NoCtrlG, false).
start(NoCtrlG, StartSync) -> spawn(fun() -> server(NoCtrlG) end).

server(NoCtrlG) -> 
    Bs = erl_eval:new_bindings(),
    process_flag(trap_exit, true),
    case NoCtrlG of
         true -> io:fwrite(<<"~s\n">>,[banner(no_control_g)]);
            _ -> io:fwrite(<<"~s\n">>,[banner()]) end,
    ?MODULE:server_loop(0, [], Bs, [], [], 20, 30).

banner() -> "\e[38;2;187;187;187mGroupoid Infinity "
              "\e[38;2;13;13;136mEXE"
            "\e[38;2;187;187;187m Programming Language "
              "\e[38;2;13;13;136mv1.0"
              "\e[0m".

banner(no_control_g) -> banner() ++ " (abort with ^G)".

server_loop(N0, Eval_0, Bs00, RT, Ds00, History0, Results0) ->
    N = N0 + 1,
    {Eval_1,Bs0,Ds0,Prompt} = prompt(N, Eval_0, Bs00, RT, Ds00),
    {Res,Eval0} = get_command(Prompt, Eval_1, Bs0, RT, Ds0),
    case Res of
                  {ok,{ok,[{atom,_,exe}],_},Line} -> io:format("Switching to "++q(term,"EXE")++" mode.~n",[]),
                                        application:set_env(exe,shell,exe),
                                        ?MODULE:server_loop(N, Eval0, Bs0, RT, Ds0, History0, Results0);
                    {ok,S,Line} when S=="\nerl^" orelse S=="erl^" -> io:format("Switching to "++q(term,"Erlang")++" mode.~n",[]),
                                        application:set_env(exe,shell,erl),
                                        ?MODULE:server_loop(N, Eval0, Bs0, RT, Ds0, History0, Results0);
                      {ok,Term,Line} -> case application:get_env(exe,shell,exe) of
                                             erl -> io:format("Erlang Loop: ~tp~n",[Term]);
                                             exe -> R=try macro:parse(strip(Term)) catch _E:_R -> {_E,_R} end,
                                                    case R of
                                                         {error,_} -> io:format("Res: ~tp~n",[Term]);
                                                                 _ -> exe:p(R) end end,
                                        ?MODULE:server_loop(N, Eval0, Bs0, RT, Ds0, History0, Results0);
	{error,{Line,Mod,What},_EndLine} -> ?MODULE:server_loop(N0, Eval0, Bs0, RT, Ds0, History0, Results0);
	              {error,terminated} -> exit(Eval0, kill), terminated;
                 {error,interrupted} -> exit(Eval0, kill),
                                        ?MODULE:server_loop(N0, Eval0, Bs0, RT, Ds0, History0, Results0);
	           {error,until_newline} -> io:format("Key Point Recognizer Error.~n",[]),
                                        ?MODULE:server_loop(N0, Eval0, Bs0, RT, Ds0, History0, Results0);
	                  {eof,_EndLine} -> halt();
	                             eof -> halt();
                                ANY  -> io:format("Unknown Protocol: ~tp~n",[ANY]),
                                        ?MODULE:server_loop(N, Eval0, Bs0, RT, Ds0, History0, Results0) end.


get_command(Prompt, Eval, Bs, RT, Ds) ->
    Parse = case application:get_env(exe,shell,exe) of
                 erl -> fun() -> exit(io:parse_erl_exprs(Prompt)) end;       % Erlang Input
                 exe -> fun() -> exit(?MODULE:wait_command(Prompt)) end end, % EXE Input
    Pid = spawn_link(Parse),
    ?MODULE:get_command1(Pid, Eval, Bs, RT, Ds).

wait_command(Prompt) -> io:request(group_leader(), {get_until,unicode,Prompt,?MODULE,until_newline,[$^]}).

until_newline(_ThisFar,eof,_MyStopCharacter) -> {done,eof,[]};
until_newline(ThisFar,CharList,MyStopCharacter) -> case
        lists:splitwith(fun(X) -> X =/= MyStopCharacter end,  CharList)
    of
  {L,[]} ->
            {more,ThisFar++L};
  {L2,[MyStopCharacter|Rest]} ->
      {done,ThisFar++L2++[MyStopCharacter],Rest}
    end.

strip(CharList) -> string:strip(string:strip(CharList,both,$\n),both,$^).

get_command1(Pid, Eval, Bs, RT, Ds) ->
    receive {'EXIT', Pid, Res}                  -> %io:format("NORM RES: ~tp~n",[{Pid,Res}]),
                                                   {{ok,Res,1}, Eval};
            {'EXIT', Eval, {Reason,Stacktrace}} -> io:format("STACKTRACE: ~tp~n",[{Pid,Reason,Stacktrace}]),
                                                   ?MODULE:get_command1(Pid, Eval, Bs, RT, Ds);
            {'EXIT', Eval, Reason}              -> io:format("EXCEPTION: ~tp~n",[{Pid,Reason}]),
                                                   ?MODULE:get_command1(Pid, Eval, Bs, RT, Ds);
                                          Any   -> io:format("ANY: ~tp~n",[Any]),
                                                   {Any,Eval} end.

prompt(N, Eval0, Bs0, RT, Ds0) ->
    P=io_lib:format(<<"\e[1K\e[~pD~w> ">>, [length(integer_to_list(N))-1, N]),
    {Eval0,Bs0,Ds0,q(prompt,P)}.
