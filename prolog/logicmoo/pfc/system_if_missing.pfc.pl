:- set_module(class(development)).
:- '$set_source_module'(baseKB).
:- use_module(library(pfc_lib)).
:- mpred_unload_file.
:- ensure_abox(baseKB).
:- file_begin(pfc).
:- set_fileAssertMt(baseKB).
% ensure this file does not get unloaded with mpred_reset
:- prolog_load_context(file,F), ain(mpred_unload_option(F,never)).



pfcControlled(if_missing(ftAskable,ftAssertable)).

% this should have been ok
% (if_missing(Missing,Create) ==> ((\+ Missing/(Missing\==Create), \+ Create , \+ ~(Create)) ==> Create)).
if_missing(Missing,Create) ==> 
 ( ( \+ (Missing/(Missing\=@=Create))) ==> Create).

:- if(baseKB:startup_option(datalog,sanity);baseKB:startup_option(clif,sanity)).

:- ensure_loaded(pack(logicmoo_base/t/examples/pfc/'sanity_foob.pfc')).

:- endif.
