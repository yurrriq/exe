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

% the actual syntax definition is divided into two parts: (1) concrete; (2) abstract

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% PART 1
%
% The concrete syntax (defined by a grammar)
%
% all 'foobar_seq' non-terminals are mapped to erlang lists of 'foobar' nodes
%

%% universe levels

level ->    token_digits        : mk_level_int('$1',get_data('$1')) .
level ->    token_id            : mk_level_var('$1',get_data('$1')) .
level ->    '(' ')'             : mk_level_empty('$1') .
level ->    '(' level_seq ')'   : mk_level_seq('$1','$2') .

level_seq ->    level                   : ['$1'] .
level_seq ->    level ',' level_seq     : ['$1'|'$3'] .


%% identifiers with namespaces

id ->   token_digits        : mk_id_int('$1',get_data('$1')) .
id ->   token_id            : mk_id_var('$1',get_data('$1')) .
id ->   token_id_etc        : mk_id_etc('$1',get_data('$1')) .

id_seq ->  id               : ['$1'] .
id_seq ->  '.' id_seq       : [mk_dot('$1')|'$2'] .
id_seq ->  id '.' id_seq    : ['$1'|'$3'] .

id_path ->  id_seq                              : '$1'
id_path ->  id_seq '.' '{' level_seq '}'        : ['$4'|'$1'] .

id_path_seq -> id_path                          : ['$1'] .
id_path_seq -> id_path ',' id_path_seq          : ['$1'|'$3'] .


%% fields of records, parameters of functions

id_type ->  'default' id_type                   : mk_id_type_default('$1','$2') .
id_type ->  id_path_seq ':' expr                : mk_id_type_mk('$1','$1','$3',[]) .
id_type ->  id_path_seq id_type_seq ':' expr    : mk_id_type_mk('$1','$1','$2','$4').

id_type_seq ->  '(' id_type ')'                 : ['$2'] .
id_type_seq ->  '(' id_type ')' id_type_seq     : ['$2'|'$4'] .

id_assign   ->  id_path_seq ':=' expr                      : mk_assign_match('$1','$1',[],'$3') .
id_assign   ->  id_path_seq id_match_seq ':=' expr         : mk_assign_match('$1','$1','$2','$4') .
id_assign   ->  id_path_seq ':' expr ':=' expr             : mk_assign_type('$1','$1',[],'$3','$5') .
id_assign   ->  id_path_seq id_type_seq ':' expr ':=' expr : mk_assign_type('$1','$1','$2','$4','$6') .

id_assign_seq   ->  '(' id_assign ')'                      : ['$2'] .
id_assign_seq   ->  '(' id_assign ')' id_assign_seq        : ['$2'|'$4'] .


%% pattern matching

id_match ->    id_path                                  : id_match_var('$1','$1') .
id_match ->    '<' id_path '>'                          : id_match_constructor('$1','$2',[]) .
id_match ->    '<' id_path id_match_seq '>'             : id_match_constructor('$1','$2','$3') .
id_match ->    '{' id_match_comma_seq '}'               : id_match_tuple('$1','$2').
id_match ->    '[' id_match_comma_seq ']'               : id_match_list('$1','$2').
id_match ->    '[' id_match_comma_seq '|' id_path ']'   : id_match_listt('$1','$2','$4').

id_match_seq ->     id_match                    : ['$1'] .
id_match_seq ->     id_match id_match_seq       : ['$1'|'$3'] .

id_match_comma_seq ->   '$empty'                        : [] .
id_match_comma_seq ->   id_match                        : ['$1'] .
id_match_comma_seq ->   id_match ',' id_match_comma_seq : ['$1'|'$3'] .

clause -> id_match_comma_seq token_arrow expr   : mk_clause('$1','$1','$3') .

clause_seq -> '(' clause ')'                    : ['$2'] .
clause_seq -> '(' clause ')' clause_seq         : ['$2'|'$4'] .


%% expessions (w/o priority)

expr ->     expr_                                       : '$1' .
expr ->     expr_ expr                                  : mk_expr_apply('$1','$1','$2') .
expr ->     'let' id_assign_seq 'in' expr               : mk_expr_let('$1','$2','$4') .
expr ->     token_forall id_type_seq token_arrow expr   : mk_expr_forall('$1','$1','$2','$4').
expr ->     expr token_arrow expr                       : mk_expr_arrow('$1','$1','$3') .
expr ->     token_lambda id_type_seq token_arrow expr   : mk_expr_('$1',) .
expr ->     token_lambda id_match_seq token_arrow expr  : mk_expr_('$1',) .
expr ->     'record' '(' ')'                            : mk_expr_('$1',) .
expr ->     'record' id_type_seq                        : mk_expr_('$1',) .
expr ->     'record' id_assign_seq                      : mk_expr_('$1',) .
expr ->     'record' id_type_seq id_assign_seq          : mk_expr_('$1',) .
expr ->     'new' '(' ')'                               : mk_expr_('$1',) .
expr ->     'new' id_assign_seq                         : mk_expr_('$1',) .
expr ->     'data' id_type_seq                          : mk_expr_('$1',) .
expr ->     'case' expr 'of' clause_seq                 : mk_expr_('$1',) .
expr ->     'packed' encoding expr                      : mk_expr_('$1',) .

expr_ ->    id_path                                     : mk_expr_('$1',) .
expr_ ->    '#' id_path                                 : mk_expr_('$1',) .
expr_ ->    token_id token_quoted_literal               : mk_expr_('$1',) .
expr_ ->    '(' expr ')'                                : mk_expr_('$1',) .
expr_ ->    '{' expr_seq '}'                            : mk_expr_('$1',) .
expr_ ->    '[' expr_seq ']'                            : mk_expr_('$1',) .
expr_ ->    '[' expr_seq '|' expr ']'                   : mk_expr_('$1',) .
expr_ ->    '*'                                         : mk_expr_('$1',) .
expr_ ->    '*' '.' '{' level_seq '}'                   : mk_expr_('$1',) .

expr_seq ->     '$empty'            : [] .
expr_seq ->     expr                : ['$1'] .
expr_seq ->     expr ',' expr_seq   : ['$1'|'$3'] .


%

root -> id_assign : '$1' .

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

exe_ast(T,L,Args) -> {T,Args,get_line(X)}.

% actual AST creation

mk_level_int(L,X)   ->  exe_ast(level, L, {int,X}}.
mk_level_var(L,X)   ->  exe_ast(level, L, {var,X}).
mk_level_empty(L)   ->  exe_ast(level, L, {seq,[]}).
mk_level_seq(L,X)   ->  exe_ast(level, L, {seq,X}}.

mk_id_int(L,X)      ->  exe_ast(id, L, {int,X}}.
mk_id_var(L,X)      ->  exe_ast(id, L, {var,X}}.
mk_id_etc(L,X)      ->  exe_ast(id, L, {etc,X}}.

mk_dot(L)               ->  exe_ast(id, L, {dot}}. % dummy id for projection functions like `.El`

mk_id_type_default(L,X) ->  exe_ast(id_type, L, {default,X}). % or add custom attribute?
mk_id_type_mk(L,X,Y,Z)  ->  exe_ast(id_type, L, {mk,X,Y,Z}).

mk_assign_type(L,X,Y,Z,T)       -> exe_ast(id_assign, L, {mk_type,X,Y,Z,T}).
mk_assign_match(L,X,Y,Z)        -> exe_ast(id_assign, L, {mk_match,X,Y,Z}).

id_match_var('$1','$1') .
id_match_constructor('$1','$2',[]) .
id_match_constructor('$1','$2','$3') .
id_match_tuple('$1','$2').
id_match_list('$1','$2').
id_match_listt('$1','$2','$4').

mk_clause('$1','$1','$3') .

mk_expr_ ...

mk_encding('$1') .
