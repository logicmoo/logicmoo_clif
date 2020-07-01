/*  LogicMOO User Modules Setup
%
%
% Dec 13, 2035
% Douglas Miles

*/
:- module(logicmoo_mud, [ ]).



:- if(\+ exists_source(prologmud(mud_loader))).
:- must((absolute_file_name(library('prologmud/'),Dir,[file_type(directory),access(read)]),
   asserta(user:file_search_path(prologmud,Dir)))).
:- sanity(exists_source(prologmud(mud_loader))).
:- endif.


% ==============================================
% [Required] Load the Logicmoo User System
% ==============================================
:- ensure_loaded(library(logicmoo_lib)).

:- if( \+ exists_source(library(prologmud/mud_startup))).
:- add_pack_path(packs_sys).
:- endif.


:- if( \+ app_argv('--nomud')).
:- baseKB:ensure_loaded(prologmud(mud_loader)).
:- endif.


:- current_prolog_flag(access_level,WAS),!,
   set_prolog_flag(access_level,user),
   baseKB:ensure_loaded(prologmud(mud_startup)),
   set_prolog_flag(access_level,WAS).



:- fixup_exports.



