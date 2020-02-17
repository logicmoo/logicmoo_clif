/*  LogicMOO User Modules Setup
%
%
% Dec 13, 2035
% Douglas Miles

*/
:- module(logicmoo_mud, [ ]).


% ==============================================
% [Required] Load the Logicmoo User System
% ==============================================
:- ensure_loaded(library(logicmoo_lib)).

:- if( \+ exists_source(library(prologmud/mud_startup))).
:- add_pack_path(packs_sys).
:- endif.


:- if( \+ app_argv('--noworld')).
:- baseKB:ensure_loaded(prologmud(mud_loader)).
:- endif.


:- current_prolog_flag(access_level,WAS),!,
   set_prolog_flag(access_level,user),
   baseKB:ensure_loaded(prologmud(mud_startup)),
   set_prolog_flag(access_level,WAS).



:- fixup_exports.



