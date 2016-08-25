-module(exe_pretty).
-compile(export_all).

q(Class,Str) -> exe_repl:q(Class,Str).

pad(D) -> lists:duplicate(D*7," ").

p(X) -> io:format("~ts~n",[color(unicode:characters_to_binary(lists:flatten(pp(X,1))),[])]).


ansi(S,gray)   -> ["\e[38;2;187;187;187m",S,"\e[0m"];
ansi(S,key)    -> q(keyword,S); %["\e[36;20;52;52;200m",  S,"\e[0m"];
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


text_attr(ansi,reset)-> "0";
text_attr(ansi,bright)-> "1";
text_attr(ansi,dim)-> "2";
text_attr(ansi,underscore)-> "4";
text_attr(ansi,blink)-> "5";
text_attr(ansi,reverse)-> "7";
text_attr(ansi,hidden)-> "8";
text_attr(ansi,alt_font_1)-> "11";
text_attr(ansi,alt_font_2)-> "12";
text_attr(ansi,alt_font_3)-> "13";
text_attr(ansi,alt_font_4)-> "14";
text_attr(ansi,alt_font_5)-> "15";
text_attr(ansi,alt_font_6)-> "16";
text_attr(ansi,alt_font_7)-> "17";
text_attr(ansi,alt_font_8)-> "18";
text_attr(ansi,alt_font_9)-> "19";
text_attr(ansi,framed)-> "51";
text_attr(ansi,encircled)-> "52";
text_attr(ansi,overlined)-> "52".

fg_color(ansi,black) -> "30";   
fg_color(ansi,red) -> "31";
fg_color(ansi,green) -> "32";
fg_color(ansi,yellow) -> "33";
fg_color(ansi,blue) -> "34";
fg_color(ansi,magenta) -> "35";
fg_color(ansi,cyan) -> "36";
fg_color(ansi,white) -> "37";
fg_color(ansi,default_fg) -> "39".

bg_color(ansi,black) ->  "40";
bg_color(ansi,red) ->  "41";
bg_color(ansi,green) ->  "42";
bg_color(ansi,yellow) ->  "43";
bg_color(ansi,blue) ->  "44";
bg_color(ansi,magenta) ->  "45";
bg_color(ansi,cyan) ->  "46";
bg_color(ansi,white) ->  "47";
bg_color(ansi,default_bg) -> "49".
