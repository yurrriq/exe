%%
%% Copyright Groupoid Infinity, Inc.
%%

Nonterminals
    level level_comma_seq
    id id_dot_seq path path_comma_seq
    pretype type type_par_seq
    preassign assign assign_par_seq
    id_ta id_ta_par_seq
    match match_seq match_comma_seq
    pattern pattern_comma_seq pattern_arg pattern_arg_seq
    clause clause_par_seq
    expr expr_ expr_comma_seq
    encoding
.
Terminals
    token_id token_digits token_id_etc token_quoted_literal
    '(' ')' '[' ']' '{' '}' '<' '>'
    '.' ',' ':' ':=' '#' '|'
    token_arrow token_forall token_lambda
    'packed' 'record' 'new' 'data' 'default'
    'let' 'in' 'case' 'of'
.
Rootsymbol      assign .

% the actual syntax definition is divided into two parts: (1) concrete; (2) abstract

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% PART 1
%
% The concrete syntax (defined by a grammar)
%
% note: all 'foobar_seq' non-terminals are mapped to erlang lists of 'foobar' nodes
%

%% universe levels

level ->    token_digits                    : mk_level_int('$1',get_data('$1')) .
level ->    token_id                        : mk_level_var('$1',get_data('$1')) .
level ->    '(' ')'                         : mk_level_empty('$1') .
level ->    '(' level_comma_seq ')'         : mk_level_seq('$1','$2') .

level_comma_seq -> level                    : ['$1'] .
level_comma_seq -> level ',' level_seq      : ['$1'|'$3'] .


%% identifiers with namespaces

id ->   token_digits                        : mk_id_int('$1',get_data('$1')) .
id ->   token_id                            : mk_id_var('$1',get_data('$1')) .
id ->   token_id_etc                        : mk_id_etc('$1',get_data('$1')) .

id_dot_seq ->  id                           : ['$1'] .
id_dot_seq ->  '.' id_dot_seq               : [mk_dot('$1')|'$2'] .
id_dot_seq ->  id '.' '{' level_seq '}'     : ['$1'|'$4'] .
id_dot_seq ->  id '.' id_dot_seq            : ['$1'|'$3'] .

path ->  id_dot_seq                         : '$1' .

path_comma_seq -> path                      : ['$1'] .
path_comma_seq -> path ',' path_comma_seq   : ['$1'|'$3'] .


%% fields of records, parameters of functions

pretype -> 'default' pretype                : mk_pretype_default('$1','$2') .
pretype -> path_comma_seq                   : mk_pretype_mk('$1','$1','$3',[]) .
pretype -> path_comma_seq type_par_seq      : mk_pretype_mk('$1','$1','$2','$4').

type -> pretype ':' expr                    : mk_type('$1','$1','$3').

type_par_seq ->  '(' type ')'               : ['$2'] .
type_par_seq ->  '(' type ')' type_seq      : ['$2'|'$4'] .

preassign   ->  path_comma_seq              : mk_preassign_match('$1','$1',[],'$3') .
preassign   ->  path match_seq              : mk_preassign_match('$1','$1','$2','$4') .
preassign   ->  type                        : mk_preassign_type('$1','$1','$3') .

assign  -> preassign ':=' expr              : mk_assign('$1','$1','$3') .

assign_par_seq   ->  '(' assign ')'                  : ['$2'] .
assign_par_seq   ->  '(' assign ')' assign_seq       : ['$2'|'$4'] .

id_ta -> assign :   '$1' .
id_ta -> type   :   '$1' .

id_ta_par_seq -> '(' id_ta ')'                  : ['$2'] .
id_ta_par_seq -> '(' id_ta ')' id_ta_par_seq    : ['$2'|'$4'] .


%% simple pattern matching (in function definition)

match ->    path                                    : mk_match_var('$1','$1') .
match ->    '{' match_comma_seq '}'                 : mk_match_tuple('$1','$2').
match ->    '[' match_comma_seq ']'                 : mk_match_list('$1','$2').
match ->    '[' match_comma_seq '|' path ']'        : mk_match_listt('$1','$2','$4').

match_seq ->     match                              : ['$1'] .
match_seq ->     match match_seq                    : ['$1'|'$2'] .

match_comma_seq ->   '$empty'                       : [] .
match_comma_seq ->   match                          : ['$1'] .
match_comma_seq ->   match ',' match_comma_seq      : ['$1'|'$3'] .

%% full pattern matching (in case statement)

pattern -> pattern_arg                                  : '$1' .
pattern -> id_path pattern_arg_seq                      : mk_pattern_constr('$1','$2') .

pattern_comma_seq -> pattern                            : ['$1'] .
pattern_comma_seq -> pattern ',' pattern_comma_seq      : ['$1'|'$3'] .

pattern_arg -> id_path                                  : mk_pattern_path('$1','$1') .
pattern_arg -> '(' pattern ')'                          : '$2' .
pattern_arg -> '{' pattern_comma_seq '}'                : mk_pattern_tuple('$1','$2') .
pattern_arg -> '[' pattern_comma_seq ']'                : mk_pattern_list('$1','$2') .
pattern_arg -> '[' pattern_comma_seq '|' id_path ']'    : mk_pattern_listt('$1','$2','$4') .

pattern_arg_seq -> pattern_arg                          : ['$1'].
pattern_arg_seq -> pattern_arg pattern_arg_seq          : ['$1'|'$2'].

clause -> pattern_comma_seq token_arrow expr            : mk_clause('$1','$1','$3') .

clause_par_seq -> '(' clause ')'                        : ['$2'] .
clause_par_seq -> '(' clause ')' clause_par_seq         : ['$2'|'$4'] .


%% expessions (w/o priority)

% sequence of application (FIXME priority)
expr ->     expr_                                       : ['$1'] .
expr ->     expr_ expr                                  : ['$1'|'$2'] .

expr_ ->    'let' id_assign_seq 'in' expr               : mk_expr_let('$1','$2','$4') .
expr_ ->    expr token_arrow expr                       : mk_expr_arrow('$1','$1','$3') .
expr_ ->    token_forall id_ta_seq token_arrow expr     : mk_expr_forall('$1','$2','$4').
expr_ ->    token_lambda id_ta_seq token_arrow expr     : mk_expr_lambda_type('$1','$2','$4') .
expr_ ->    token_lambda id_match_seq token_arrow expr  : mk_expr_lambda_match('$1','$2','$4') .
expr_ ->    'record' '(' ')'                            : mk_expr_record('$1',[]) .
expr_ ->    'record' id_ta_seq                          : mk_expr_record('$1','$2') .
expr_ ->    'new' '(' ')'                               : mk_expr_new('$1',[]) .
expr_ ->    'new' id_assign_seq                         : mk_expr_new('$1','$2') .
expr_ ->    'data' id_type_seq                          : mk_expr_data('$1','$2') .
expr_ ->    'case' expr 'of' clause_par_seq             : mk_expr_case('$1','$2','$4') .
expr_ ->    'packed' encoding expr                      : mk_expr_packed('$1','$2','$3') .
expr_ ->    id_path                                     : mk_expr_id('$1','$1') .
expr_ ->    '#' id_path                                 : mk_expr_external('$1','$2') .
expr_ ->    token_id token_quoted_literal               : mk_expr_literal('$1','$1','$2') .
expr_ ->    '(' expr ')'                                : '$2' .
expr_ ->    '{' expr_seq '}'                            : mk_expr_tuple('$1','$2') .
expr_ ->    '[' expr_seq ']'                            : mk_expr_list('$1','$2') .
expr_ ->    '[' expr_seq '|' expr ']'                   : mk_expr_listt('$1','$2','$3') .

expr_comma_seq ->     '$empty'                      : [] .
expr_comma_seq ->     expr                          : ['$1'] .
expr_comma_seq ->     expr ',' expr_comma_seq       : ['$1'|'$3'] .


%

encoding -> '(' ')' : mk_encding('$1') . %TODO

%TODO sugar/notation


%%%%%%%%%%%%%%%%%%%%%%%

Erlang       code.

get_line([T|_])              -> get_line(T);
get_line(T) when is_tuple(T) -> element(2, T).

get_data(T) when is_tuple(T) -> element(3, T).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% PART 2
%
% The abstract syntax (defined by AST constructors)
%

%
% AST node format is {T,Args,Attrs}
% T - atom of type of AST-constructor
% Args - tuple of AST-constructor and args
% Attrs - proplist of extended attributes (currently just 'line')
%

exe_ast(T,L,Args) -> {T,get_line(L),Args}.

% actual AST creation

mk_level_int(L,X)           ->  exe_ast(level, L, {int,X}).
mk_level_var(L,X)           ->  exe_ast(level, L, {var,X}).
mk_level_empty(L)           ->  exe_ast(level, L, {seq,[]}).
mk_level_seq(L,X)           ->  exe_ast(level, L, {seq,X}).

mk_id_int(L,X)              ->  exe_ast(id, L, {int,X}).
mk_id_var(L,X)              ->  exe_ast(id, L, {var,X}).
mk_id_etc(L,X)              ->  exe_ast(id, L, {etc,X}).

mk_dot(L)                   ->  exe_ast(id, L, {dot}). % dummy id

mk_id_type_default(L,X)     ->  exe_ast(id_type, L, {default,X}). % or add custom attribute?
mk_id_type_mk(L,X,Y,Z)      ->  exe_ast(id_type, L, {mk,X,Y,Z}).

mk_assign_type(L,X,Y)       -> exe_ast(id_assign, L, {mk_type,X,Y}).
mk_assign_match(L,X,Y,Z)    -> exe_ast(id_assign, L, {mk_match,X,Y,Z}).

id_match_var(L,X)           -> exe_ast(id_match, L, {mk_var,X}).
id_match_tuple(L,X)         -> exe_ast(id_match, L, {mk_tuple,X}).
id_match_list(L,X)          -> exe_ast(id_match, L, {mk_list,X}).
id_match_listt(L,X,Y)       -> exe_ast(id_match, L, {mk_listt,X,Y}).

mk_clause(L,X,Y)            -> exe_ast(clause, L, {mk,X,Y}).

mk_expr_let(L,X,Y)          -> exe_ast(expr, L, {mk_let,X,Y}).
mk_expr_arrow(L,X,Y)        -> exe_ast(expr, L, {mk_arrow,X,Y}).
mk_expr_forall(L,X,Y)       -> exe_ast(expr, L, {mk_forall,X,Y}).
mk_expr_lambda_type(L,X,Y)  -> exe_ast(expr, L, {mk_lambda_type,X,Y}).
mk_expr_lambda_match(L,X,Y) -> exe_ast(expr, L, {mk_lambda_match,X,Y}).
mk_expr_record(L,X,Y)       -> exe_ast(expr, L, {mk_record,X,Y}).
mk_expr_new(L,X)            -> exe_ast(expr, L, {mk_new,X}).
mk_expr_data(L,X)           -> exe_ast(expr, L, {mk_data,X}).
mk_expr_case(L,X,Y)         -> exe_ast(expr, L, {mk_case,X,Y}).
mk_expr_packed(L,X,Y)       -> exe_ast(expr, L, {mk_packed,X,Y}).
mk_expr_id(L,X)             -> exe_ast(expr, L, {mk_id,X}).
mk_expr_external(L,X)       -> exe_ast(expr, L, {mk_external,X}).
mk_expr_literal(L,X,Y)      -> exe_ast(expr, L, {mk_literal,X,Y}).
mk_expr_tuple(L,X)          -> exe_ast(expr, L, {mk_tuple,X}).
mk_expr_list(L,X)           -> exe_ast(expr, L, {mk_list,X}).
mk_expr_listt(L,X,Y)        -> exe_ast(expr, L, {mk_listt,X,Y}).

mk_encding(L)               -> exe_ast(encoding, L, {mk}).
