%%
%% Copyright Groupoid Infinity, Inc.
%%

Nonterminals
    level level_seq
    id id_path id_path_seq
    id_type id_type_seq id_assign id_assign_seq
    id_match id_match_seq id_match_comma_seq
    clause clause_seq
    expr expr_ expr_seq
    encoding_instance
    root
.
Terminals
    token_id token_digits token_id_etc token_quoted_literal
    '(' ')' '[' ']' '{' '}' '<' '>' '|'
    '.' ',' ':' '*' ':=' '#'
    token_arrow token_forall token_lambda
    'packed' 'record' 'new' 'data' 'default'
    'let' 'in' 'case' 'of'
.
Rootsymbol      root .


%% universe levels

level -> token_digits : [] .
level -> token_id : [] .
level -> '(' ')' : [] .
level -> '(' level_seq ')' : [] .

level_seq -> level : [] .
level_seq -> level ',' level_seq : [] .


%% identifiers with namespaces

id -> token_digits : [] .
id -> token_id : [] .
id -> token_id_etc : [] .

id_path -> id : [] .
id_path -> '.' id : [] .
id_path -> id_path '.' id : [] .
id_path -> id '.' '{' level_seq '}' : [] .
id_path -> '.' id '.' '{' level_seq '}' : [] .
id_path -> id_path '.' id '.' '{' level_seq '}' : [] .

id_path_seq -> id_path : [] .
id_path_seq -> id_path ',' id_path_seq : [] .


%% fields of records, parameters of functions

id_type -> 'default' id_type : [] .
id_type -> id_path_seq ':' expr : [] .
id_type -> id_path_seq id_type_seq ':' expr : [] .

id_type_seq -> '(' id_type ')' : [] .
id_type_seq -> '(' id_type ')' id_type_seq : [] .

id_assign -> id_path_seq ':=' expr : [] .
id_assign -> id_path_seq ':' expr ':=' expr : [] .
id_assign -> id_path_seq id_match_seq ':=' expr : [] .
id_assign -> id_path_seq id_match_seq ':' expr ':=' expr : [] .

id_assign_seq -> '(' id_assign ')' : [] .
id_assign_seq -> '(' id_assign ')' id_assign_seq : [] .


%% pattern matching

id_match ->    id_path : [] .
id_match ->    '<' id_match_seq '>' : [] .
id_match ->    '{' id_match_comma_seq '}' : [] .
id_match ->    '[' id_match_comma_seq ']' : [] .
id_match ->    '[' id_match_comma_seq '|' id_path ']' : [] .

id_match_seq -> id_match : [] .
id_match_seq -> id_match id_match_seq : [] .

id_match_comma_seq -> '$empty' : [] .
id_match_comma_seq -> id_match : [] .
id_match_comma_seq -> id_match ',' id_match_comma_seq : [] .

clause -> id_match_comma_seq token_arrow expr : [] .

clause_seq -> '$empty' : [] .
clause_seq -> '(' clause ')' clause_seq : [] .


%% expessions (w/o priority)

expr -> expr_ : [] .
expr -> expr_ expr : [] .
expr ->    'let' id_assign_seq 'in' expr : [] .
expr ->    token_forall id_type_seq token_arrow expr : [] .
expr ->    expr token_arrow expr : [] .
expr ->    token_lambda id_type_seq token_arrow expr : [] .
expr ->    token_lambda id_match_seq token_arrow expr : [] .
expr ->    'record' '(' ')' : [] .
expr ->    'record' id_type_seq : [] .
expr ->    'record' id_assign_seq : [] .
expr ->    'record' id_type_seq id_assign_seq : [] .
expr ->    'new' '(' ')' : [] .
expr ->    'new' id_assign_seq : [] .
expr ->    'data' id_type_seq : [] .
expr ->    'case' expr 'of' clause_seq : [] .
expr ->    'packed' encoding_instance expr : [] .

expr_ ->    id_path : [] .
expr_ ->    '#' id_path : [] .
expr_ ->    token_id token_quoted_literal : [] .
expr_ ->    '(' expr ')' : [] .
expr_ ->    '{' expr_seq '}' : [] .
expr_ ->    '[' expr_seq ']' : [] .
expr_ ->    '[' expr_seq '|' expr ']' : [] .
expr_ ->    '*' : [] .
expr_ ->    '*' '.' '{' level_seq '}' : [] .

expr_seq -> '$empty' : [] .
expr_seq -> expr : [] .
expr_seq -> expr ',' expr_seq : [] .


%

root -> id_assign : [] .

encoding_instance -> '(' ')' : [] . %TODO


%%%%%%%%%%%%%%%%%%%%%%%

Erlang       code.

line([T|_])              -> line(T);
line(T) when is_tuple(T) -> element(2, T).

consify([], T)           -> T;
consify([H|Hs], T)       -> {cell,element(2,H),H,consify(Hs, T)}.
