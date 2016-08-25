-module(exe_repl).
-include("exe_repl.hrl").
-compile(export_all).
-define(ANSI_CTRL_CHARS,"\e[").
-define(ANSI_CLEAR,"\e[0m").
-define(LINEMAX, 30).
-define(CHAR_MAX, 60).
-define(DEF_HISTORY, 20).
-define(DEF_RESULTS, 20).
-define(DEF_CATCH_EXCEPTION, false).
-define(DEF_PROMPT_FUNC, default).
-define(RECORDS, shell_records).
-define(MAXSIZE_HEAPBINARY, 64).

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
ctrl_sequence(ansi,[],Acc) -> lists:concat([ ?ANSI_CTRL_CHARS , string:join(lists:reverse(Acc),";") , "m"]).

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
start(NoCtrlG, StartSync) -> code:ensure_loaded(user_default), spawn(fun() -> server(NoCtrlG, StartSync) end).

server(NoCtrlG, StartSync) -> put(no_control_g, NoCtrlG), server(StartSync).
server(StartSync) ->
    %init:wait_until_started(),
    Bs = erl_eval:new_bindings(),
    RT = ets:new(?RECORDS, [public,ordered_set]),
    process_flag(trap_exit, true),
    case get(no_control_g) of
         true -> io:fwrite(<<"~s\n">>,[banner(no_control_g)]);
         _undefined_or_false -> io:fwrite(<<"~s\n">>,[banner()]) end,
    erase(no_control_g),
    {History,Results} = {20,30},
    ?MODULE:server_loop(0, [], Bs, RT, [], History, Results).

banner() -> "\e[38;2;187;187;187mGroupoid Infinity "
              "\e[38;2;13;13;136mEXE"
            "\e[38;2;187;187;187m Programming Language "
              "\e[38;2;13;13;136mv1.0"
              "\e[0m".

banner(no_control_g) -> banner() ++ " (abort with ^G)".

server_loop(N0, Eval_0, Bs00, RT, Ds00, History0, Results0) ->
    N = N0 + 1,
    {Eval_1,Bs0,Ds0,Prompt} = prompt(N, Eval_0, Bs00, RT, Ds00),
    % io:format("SERVER LOOP: ~tp~n",[Eval_1]),
    {Res,Eval0} = get_command(Prompt, Eval_1, Bs0, RT, Ds0),
    case Res of
	{error,{Line,Mod,What},_EndLine} -> ?MODULE:server_loop(N0, Eval0, Bs0, RT, Ds0, History0, Results0);
	              {error,terminated} -> exit(Eval0, kill), terminated;
                 {error,interrupted} -> exit(Eval0, kill),
                                        ?MODULE:server_loop(N0, Eval0, Bs0, RT, Ds0, History0, Results0);
	                  {error,tokens} -> ?MODULE:server_loop(N0, Eval0, Bs0, RT, Ds0, History0, Results0);
	                  {eof,_EndLine} -> halt();
	                             eof -> halt();
                                ANY  -> %io:format("Server Loop Any: ~tp~n",[ANY]),
                                        R=try macro:parse(lists:reverse(tl(lists:reverse(ANY)))) catch _E:_R -> {_E,_R} end,
                                        case R of
                                            {error,_} -> io:format("Res: ~tp~n",[R]);
                                                    _ -> exe:p(R) end,
                                        ?MODULE:server_loop(N, Eval0, Bs0, RT, Ds0, History0, Results0) end.


get_command(Prompt, Eval, Bs, RT, Ds) ->
%    Parse = fun() -> exit(io:parse_erl_exprs(Prompt)) end, % Erlang Input
    Parse = fun() -> exit(?MODULE:wait_command(Prompt)) end, % EXE Input
    Pid = spawn_link(Parse),
    ?MODULE:get_command1(Pid, Eval, Bs, RT, Ds).

wait_command(Prompt) -> io:request(group_leader(), {get_until,unicode,Prompt,?MODULE,until_newline,[$.]}).

until_newline(_ThisFar,eof,_MyStopCharacter) -> {done,eof,[]};
until_newline(ThisFar,CharList,MyStopCharacter) -> case
        lists:splitwith(fun(X) -> X =/= MyStopCharacter end,  CharList)
    of
  {L,[]} ->
            {more,ThisFar++L};
  {L2,[MyStopCharacter|Rest]} ->
      {done,ThisFar++L2++[MyStopCharacter],Rest}
    end.

get_command1(Pid, Eval, Bs, RT, Ds) ->
    receive {'EXIT', Pid, Res}                  -> %io:format("NORM RES: ~tp~n",[{Pid,Res}]),
                                                   {Res, Eval};
            {'EXIT', Eval, {Reason,Stacktrace}} -> io:format("STACKTRACE: ~tp~n",[{Pid,Reason,Stacktrace}]),
                                                   ?MODULE:get_command1(Pid, Eval, Bs, RT, Ds);
            {'EXIT', Eval, Reason}              -> io:format("EXCEPTION: ~tp~n",[{Pid,Reason}]),
                                                   ?MODULE:get_command1(Pid, Eval, Bs, RT, Ds);
                                          Any   -> io:format("ANY: ~tp~n",[Any]),
                                                   {Any,Eval} end.

prompt(N, Eval0, Bs0, RT, Ds0) ->
            {Eval0,Bs0,Ds0,default_prompt(N)}.

default_prompt(N) ->
	P=io_lib:format(<<"\e[1K\e[~pD~w> ">>, [length(integer_to_list(N))-1, N]),
	q(prompt,P).

