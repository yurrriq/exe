%%
%% Copyright Groupoid Infinity, Inc.
%%

    % the parser awaits the following tokens:
    %
    % token_id token_digits token_id_etc token_quoted_literal
    % '(' ')' '[' ']' '{' '}' '<' '>'
    % '.' ',' ':' '*' ':=' '#' '|'
    % token_arrow token_forall token_lambda
    % 'packed' 'record' 'new' 'data' 'default'
    % 'let' 'in' 'case' 'of'
    %

Definitions.

D		= [0-9]
C		= [a-zA-Z_]
A		= [a-zA-Z_0-9]
S		= ([\000-\s]|--.*)
Index   = \*(\.{(.*|[^}])})?
Star    = \*
Unit    = \(\)
Slash   = \\
Dot     = \.
Comma   = \,
Arrow   = (\->|\→)
ForAll  = (forall|\∀)
LamBda  = (lambda|\λ)
Curly   = [\{\}]
Angle   = [\<\>]
Parens  = [\(\)]
Square  = [\[\]]
Colon   = \:
Define  = \:\=

Rules.

(data|record|new|default|packed)        : {token,{list_to_atom(TokenChars),TokenLine}}.
(case|of||let|in)                       : {token,{list_to_atom(TokenChars),TokenLine}}.
(spawn|send|receive|try|do|raise)       : {token,{list_to_atom(TokenChars),TokenLine}}.
({Curly}|{Parens}|{Angle}|{Square})     : {token,{list_to_atom(TokenChars),TokenLine}}.
({Dot}|{Comma}|{Star}|{Define}|{Colon}) : {token,{list_to_atom(TokenChars),TokenLine}}.

{D}+            : {token,{ token_digits,    TokenLine,TokenChars}}.
{A}+            : {token,{ token_id,        TokenLine,TokenChars}}.
{Arrow}         : {token,{ token_arrow,     TokenLine}}.
{ForAll}        : {token,{ token_forall,    TokenLine}}.
{LamBda}        : {token,{ token_lambda,    TokenLine}}.

"(\\.|[^"])*" : {token,{token_quoted_literal,TokenLine,unquote(TokenChars)}}.
% '(\\.|[^'])*' : {token,{str1,TokenLine,unquote(TokenChars)}}.

({S}+|.) : skip_token.

Erlang code.

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
