#!/usr/bin/env swipl

:- module(logicmoo_nlu,[]).

:- current_prolog_flag(access_level,WAS),!,
   set_prolog_flag(access_level,user),
   use_module(library(wamcl_runtime)),
   reexport(library(logicmoo_lib)),
   set_prolog_flag(access_level,WAS).



:- current_prolog_flag(access_level,WAS),!,
   set_prolog_flag(access_level,user),
   reexport(library(parser_all)),
   set_prolog_flag(access_level,WAS).


