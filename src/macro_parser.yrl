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
    '(' ')' '[' ']' '{' '}' '<' '>'
    '.' ',' ':' '*' ':=' '#' '|'
    token_arrow token_forall token_lambda
    'packed' 'record' 'new' 'data' 'default'
    'let' 'in' 'case' 'of'
.
Rootsymbol      root .


%% universe levels

level ->    token_digits        : mk_level_int('$1') .
level ->    token_id            : mk_level_var('$1') .
level ->    '(' ')'             : mk_level_empty('$1') .
level ->    '(' level_seq ')'   : mk_level_seq('$2') .

level_seq ->    level                   : ['$1'] .
level_seq ->    level ',' level_seq     : ['$1'|'$3'] .


%% identifiers with namespaces

id ->   token_digits        : mk_id_int('$1') .
id ->   token_id            : mk_id_var('$1') .
id ->   token_id_etc        : mk_id_etc('$1') .

id_seq ->  id               : ['$1'] .
id_seq ->  '.' id_seq       : [mk_dot('$1')|'$2'] .
id_seq ->  id '.' id_seq    : ['$1'|'$3'] .

id_path ->  id_seq                              : '$1'
id_path ->  id_seq '.' '{' level_seq '}'        : mk_apply_level('$1','$4') .

id_path_seq -> id_path                          : ['$1'] .
id_path_seq -> id_path ',' id_path_seq          : ['$1'|'$3'] .


%% fields of records, parameters of functions

id_type -> 'default' id_type : {default,'$2'} .
id_type -> id_path_seq ':' expr : {def_type,{_ids,'$1'},{_args,[]},{_type,'$3'}} .
id_type -> id_path_seq id_type_seq ':' expr : {def_args_type,{_ids,'$1'},{_args,'$2'},{_type,'$3'}} .

id_type_seq -> '(' id_type ')' : ['$2'] .
id_type_seq -> '(' id_type ')' id_type_seq : ['$2'|'$4'] .

id_assign -> id_path_seq ':=' expr : \
        {def_assign,{_ids,'$1'},{_val,'$3'}} .
id_assign -> id_path_seq ':' expr ':=' expr : \
        {def_type_assign,{_ids,'$1'},{_type,'$3'},{_val,'$5'}} .
id_assign -> id_path_seq id_match_seq ':=' expr : \
        {def_match_assign,{_ids,'$1'},{_args,'$2'},{_val,'$4'}} .
id_assign -> id_path_seq id_type_seq ':' expr ':=' expr : \
        {decl_args_type_assign,{_ids,'$1'},{_args,'$2'},{_type,'$4'},{_val,'$6'}} .

id_assign_seq -> '(' id_assign ')' : ['$2'] .
id_assign_seq -> '(' id_assign ')' id_assign_seq : ['$2'|'$4'] .


%% pattern matching

id_match ->    id_path : \
        {match_var,{_var,'$1'}} .
id_match ->    '<' id_path '>' : \
        {match_constructor,{_constructor,'$2'},{_args,[]}} .
id_match ->    '<' id_path id_match_seq '>' : \
        {match_constructor,{_constructor,'$2'},{_args,'$3'}} .
id_match ->    '{' id_match_comma_seq '}' : \
        {match_tuple,{_args,'$2'}}.
id_match ->    '[' id_match_comma_seq ']' : \
        {match_list,{_items,'$2'}}.
id_match ->    '[' id_match_comma_seq '|' id_path ']' : \
        {match_list,{_items,'$2'},{_tail,'$4'}}.

id_match_seq -> id_match : [] .
id_match_seq -> id_match id_match_seq : [] .

id_match_comma_seq -> '$empty' : [] .
id_match_comma_seq -> id_match : [] .
id_match_comma_seq -> id_match ',' id_match_comma_seq : [] .

clause -> id_match_comma_seq token_arrow expr : [] .

clause_seq -> '(' clause ')' : [] .
clause_seq -> '(' clause ')' clause_seq : [] .


%% expessions (w/o priority)

expr ->     expr_ : [] .
expr ->     expr_ expr : [] .
expr ->     'let' id_assign_seq 'in' expr : [] .
expr ->     token_forall id_type_seq token_arrow expr : [] .
expr ->     expr token_arrow expr : [] .
expr ->     token_lambda id_type_seq token_arrow expr : [] .
expr ->     token_lambda id_match_seq token_arrow expr : [] .
expr ->     'record' '(' ')' : [] .
expr ->     'record' id_type_seq : [] .
expr ->     'record' id_assign_seq : [] .
expr ->     'record' id_type_seq id_assign_seq : [] .
expr ->     'new' '(' ')' : [] .
expr ->     'new' id_assign_seq : [] .
expr ->     'data' id_type_seq : [] .
expr ->     'case' expr 'of' clause_seq : [] .
expr ->     'packed' encoding_instance expr : [] .

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

%TODO sugar/notation


%%%%%%%%%%%%%%%%%%%%%%%

Erlang       code.

get_line([T|_])              -> get_line(T);
get_line(T) when is_tuple(T) -> element(2, T).

get_data(T) when is_tuple(T) -> element(3, T).

%
% AST node format is {Atom,Args,Attrs}
% Atom - constructor type atom
% Args - constructor args proplist
% Attrs - extended attributes proplist (currently 'line')
%
put_it(Mk,X,Args) -> {Mk,Args,[{line,get_line(X)}]}

% actual AST creation

mk_level_int(X)     -> put_it(mk_level, X, [{_int,list_to_integer(get_data(I))}]}.
mk_level_var(X)     -> put_it(mk_level, X, [{_var,get_data(I)}]).
mk_level_empty(X)   -> put_it(mk_level, X, [{_seq,[]}]).
mk_level_seq(X)     -> put_it(mk_level, X, []}.

mk_id_int(X)    ->  put_it(mk_id, X, [{_int,list_to_integer(get_data(I))}]}.
mk_id_var(X)    ->  put_it(mk_id, X, [{_var,get_data(I)}]}.
mk_id_etc(X)    ->  put_it(mk_id, X, [{_etc,get_data(I)}]}.

mk_dot(X)           ->  put_it(mk_dot, X, []}.
mk_apply_level(X,L) ->  put_it(mk_apply_level, X, [{_id,'$1'},{_level,'$4'}])
