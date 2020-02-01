#!/usr/bin/env swipl

:- module(logicmoo_nlu,[]).

% ==============================================
% [Required] Load the Logicmoo User System
% ==============================================
:- ensure_loaded(library(logicmoo_lib)).

:- if( \+ exists_source(library('logicmoo_nlu/nl_pipeline.pl'))).
:- add_pack_path(packs_xtra).
:- endif.

:- current_prolog_flag(access_level,WAS),!,
   set_prolog_flag(access_level,user),
   reexport(library('logicmoo_nlu/nl_pipeline.pl')),
   set_prolog_flag(access_level,WAS).


