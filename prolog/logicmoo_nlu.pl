#!/usr/bin/env swipl

:- module(logicmoo_nlu,[]).


dir_from1(Rel,Y):-
    ((getenv('LOGICMOO_WS',Dir);
      prolog_load_context(directory,Dir);
      'w:/opt/logicmoo_workspace/'=Dir;      
      '~/logicmoo_workspace'=Dir;
      '/opt/logicmoo_workspace/'=Dir;
      fail)),
    absolute_file_name(Rel,Y,[relative_to(Dir),file_type(directory),file_errors(fail)]),
    exists_directory(Y),!.

add_pack_path1(packs_sys):-pack_property(pfc,_),!.
add_pack_path1(Rel):- 
   dir_from1(Rel,Y),
   (( \+ user:file_search_path(pack,Y)) ->asserta(user:file_search_path(pack,Y));true).

:- if( \+ exists_source(library('logicmoo_nlu/nl_pipeline.pl'))).
:- add_pack_path1(packs_xtra).
:- endif.

:- current_prolog_flag(access_level,WAS),!,
   set_prolog_flag(access_level,user),
   use_module(library(wamcl_runtime)),
   reexport(library(logicmoo_lib)),
   set_prolog_flag(access_level,WAS).



:- current_prolog_flag(access_level,WAS),!,
   set_prolog_flag(access_level,user),
   reexport(library('logicmoo_nlu/nl_pipeline.pl')),
   set_prolog_flag(access_level,WAS).


