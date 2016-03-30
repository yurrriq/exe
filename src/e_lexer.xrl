
% Copyright Groupoid Infinity, Inc.

Definitions.

D		= [0-9]
C		= [a-zA-Z_]
A		= [a-zA-Z_0-9]
Type    = (\*.{A}|\*.{A\+1}|\*)
WS		= ([\000-\s]|--.*)

Rules.

{Type}                   : {token,{star,TokenChars,TokenLine}}.
{D}+                     : {token,{int,to_integer(TokenChars),TokenLine}}.
{D}+[lL]                 : {token,{long,to_integer(TokenChars),TokenLine}}.
{D}+\.{D}+([eE]-?{D}+)?  : {token,{float,to_float(TokenChars),TokenLine}}.
{D}+\.{D}+%              : {token,{percent,to_float(TokenChars)/100,TokenLine}}.
{D}++%                   : {token,{percent,to_integer(TokenChars)/100,TokenLine}}.

{C}{A}* : {token,{var,TokenLine,list_to_atom(TokenChars)}}.
{A}+	: {token,{atom,TokenLine,list_to_atom(TokenChars)}}.

[+\-*/]                  : {token,{list_to_atom(TokenChars),TokenLine}}.
(:=|(|)|\:)              : {token,{list_to_atom(TokenChars),TokenLine}}.
(data|record|extend)     : {token,{list_to_atom(TokenChars),TokenLine}}.
(case|of||let|in)        : {token,{list_to_atom(TokenChars),TokenLine}}.
(fun|lambda||forall)     : {token,{list_to_atom(TokenChars),TokenLine}}.
(spawn|send|receive)     : {token,{list_to_atom(TokenChars),TokenLine}}.
(try|do|raise)           : {token,{list_to_atom(TokenChars),TokenLine}}.

"(\\.|[^"])*" : {token,{str2,unquote(TokenChars),TokenLine}}.
'(\\.|[^'])*' : {token,{str1,unquote(TokenChars),TokenLine}}.

"""(x|[^x])*"""     : {token,{docstr,unquote3(TokenChars),TokenLine}}.
{WS}+	            : skip_token.

Erlang code.

to_integer(Cs) -> list_to_integer(lists:reverse(skip_prefix(lists:reverse(Cs)))).
to_float(Cs)   -> list_to_float(lists:reverse(skip_prefix(lists:reverse(Cs)))).

skip_prefix([$f|Cs]) -> skip_prefix(Cs);
skip_prefix([$F|Cs]) -> skip_prefix(Cs);
skip_prefix([$l|Cs]) -> skip_prefix(Cs);
skip_prefix([$L|Cs]) -> skip_prefix(Cs);
skip_prefix([$u|Cs]) -> skip_prefix(Cs);
skip_prefix([$U|Cs]) -> skip_prefix(Cs);
skip_prefix([$%|Cs]) -> skip_prefix(Cs);
skip_prefix(Cs) -> Cs.

unquote3(Doc) -> string:substr(Doc, 4, length(Doc) - 6).

unquote([$'|Cs]) -> unquote(Cs, []);
unquote([$"|Cs]) -> unquote(Cs, []).

unquote([$"], Acc) -> lists:reverse(Acc);
unquote([$'], Acc) -> lists:reverse(Acc);
unquote([$\\,$0|Cs], Acc) -> unquote(Cs, [0|Acc]);
unquote([$\\,$a|Cs], Acc) -> unquote(Cs, [7|Acc]);
unquote([$\\,$b|Cs], Acc) -> unquote(Cs, [8|Acc]);
unquote([$\\,$f|Cs], Acc) -> unquote(Cs, [12|Acc]);
unquote([$\\,$n|Cs], Acc) -> unquote(Cs, [10|Acc]);
unquote([$\\,$r|Cs], Acc) -> unquote(Cs, [13|Acc]);
unquote([$\\,$t|Cs], Acc) -> unquote(Cs, [9|Acc]);
unquote([$\\,$v|Cs], Acc) -> unquote(Cs, [11|Acc]);
unquote([$\\,$"|Cs], Acc) -> unquote(Cs, [$"|Acc]);
unquote([$\\,$'|Cs], Acc) -> unquote(Cs, [$'|Acc]);
unquote([$\\,$\\|Cs], Acc) -> unquote(Cs, [$\\|Acc]);
unquote([$\\,$&|Cs], Acc) -> unquote(Cs, Acc);	%% stop escape
unquote([$\\,D|Cs], Acc) when D >= $0, D =< $9 -> unquote_char(Cs, D -$0, Acc);
unquote([$\\,$x|Cs], Acc) -> unquote_hex(Cs, 0, Acc);
unquote([C|Cs], Acc) -> unquote(Cs, [C|Acc]).

unquote_char([D|Cs], N, Acc) when D >= $0, D =< $9 -> unquote_char(Cs, N *10 +D -$0, Acc);
unquote_char(Cs, N, Acc) -> unquote(Cs, [N|Acc]).

unquote_hex([H|Cs], N, Acc) when H >= $0, H =< $9 -> unquote_hex(Cs, N *16 +H -$0, Acc);
unquote_hex([H|Cs], N, Acc) when H >= $a, H =< $f -> unquote_hex(Cs, N *16 +H -$a +10, Acc);
unquote_hex([H|Cs], N, Acc) when H >= $A, H =< $F -> unquote_hex(Cs, N *16 +H -$A +10, Acc);
unquote_hex(Cs, N, Acc) -> unquote(Cs, [N|Acc]).

%%EOF
