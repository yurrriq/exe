
% Copyright Groupoid Infinity, Inc.

Definitions.

D		= [0-9]
C		= [a-zA-Z_]
A		= [a-zA-Z_0-9]
S		= ([\000-\s]|--.*)
Index   = \*(\.{(.*|[^}])})?
Unit    = \(\)
Slash   = \\
Dot     = \.
Arrow   = (\->|\→)
Curly   = [{,}]
Parens  = [\(\)]
Square  = [\[\]]
Colon   = \:
Define  = :=

Rules.

(data|record|extend)        : {token,{list_to_atom(TokenChars),TokenLine}}.
(case|of||let|in)           : {token,{list_to_atom(TokenChars),TokenLine}}.
(fun|lambda||forall)        : {token,{list_to_atom(TokenChars),TokenLine}}.
(spawn|send|receive)        : {token,{list_to_atom(TokenChars),TokenLine}}.
(try|do|raise)              : {token,{list_to_atom(TokenChars),TokenLine}}.
({Curly}|{Parens}|{Square}) : {token,{list_to_atom(TokenChars),TokenLine}}.

{D}+      : {token,{int,TokenLine,to_integer(TokenChars)}}.
{C}{A}*   : {token,{var,TokenLine,list_to_atom(TokenChars)}}.
{A}+	  : {token,{atom,TokenLine,list_to_atom(TokenChars)}}.

{Dot}     : {token,{'.',TokenLine}}.
{Index}   : {token,{'*',TokenLine,star(TokenChars)}}.
{Unit}    : {token,{'()',TokenLine}}.
{Arrow}   : {token,{'->',TokenLine}}.
{Define}  : {token,{':=',TokenLine}}.
{Colon}   : {token,{':',TokenLine}}.

"(\\.|[^"])*" : {token,TokenLine,{str2,unquote(TokenChars)}}.
'(\\.|[^'])*' : {token,TokenLine,{str1,unquote(TokenChars)}}.

({S}+|.) : skip_token.

Erlang code.

to_integer(Cs) -> list_to_integer(Cs).

unquote([$'|Cs]) -> unquote(Cs, []);
unquote([$"|Cs]) -> unquote(Cs, []).

unquote([$"], Acc)         -> lists:reverse(Acc);
unquote([$'], Acc)         -> lists:reverse(Acc);
unquote([$\\,$0|Cs], Acc)  -> unquote(Cs, [0|Acc]);
unquote([$\\,$a|Cs], Acc)  -> unquote(Cs, [7|Acc]);
unquote([$\\,$b|Cs], Acc)  -> unquote(Cs, [8|Acc]);
unquote([$\\,$f|Cs], Acc)  -> unquote(Cs, [12|Acc]);
unquote([$\\,$n|Cs], Acc)  -> unquote(Cs, [10|Acc]);
unquote([$\\,$r|Cs], Acc)  -> unquote(Cs, [13|Acc]);
unquote([$\\,$t|Cs], Acc)  -> unquote(Cs, [9|Acc]);
unquote([$\\,$v|Cs], Acc)  -> unquote(Cs, [11|Acc]);
unquote([$\\,$"|Cs], Acc)  -> unquote(Cs, [$"|Acc]);
unquote([$\\,$'|Cs], Acc)  -> unquote(Cs, [$'|Acc]);
unquote([$\\,$\\|Cs], Acc) -> unquote(Cs, [$\\|Acc]);
unquote([$\\,$&|Cs], Acc)  -> unquote(Cs, Acc);	%% stop escape
unquote([$\\,D|Cs], Acc) when D >= $0, D =< $9 -> unquote_char(Cs, D -$0, Acc);
unquote([$\\,$x|Cs], Acc)  -> unquote_hex(Cs, 0, Acc);
unquote([C|Cs], Acc)       -> unquote(Cs, [C|Acc]).

unquote_char([D|Cs], N, Acc) when D >= $0, D =< $9 -> unquote_char(Cs, N *10 +D -$0, Acc);
unquote_char(Cs, N, Acc)   -> unquote(Cs, [N|Acc]).

unquote_hex([H|Cs], N, Acc) when H >= $0, H =< $9 -> unquote_hex(Cs, N *16 +H -$0, Acc);
unquote_hex([H|Cs], N, Acc) when H >= $a, H =< $f -> unquote_hex(Cs, N *16 +H -$a +10, Acc);
unquote_hex([H|Cs], N, Acc) when H >= $A, H =< $F -> unquote_hex(Cs, N *16 +H -$A +10, Acc);
unquote_hex(Cs, N, Acc)    -> unquote(Cs, [N|Acc]).

star(X) -> case string:tokens(X,".") of
                ["*"]   -> 1;
                ["*",A] -> hd(string:tokens(A,"{}")) end.

%%EOF
