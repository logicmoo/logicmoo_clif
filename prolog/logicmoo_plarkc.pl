/* <module> logicmoo_plarkc - special module hooks into the logicmoo engine allow
%   clif syntax to be recocogized via our CycL/KIF handlers 
% 
% Logicmoo Project: A LarKC Server written in Prolog
% Maintainer: Douglas Miles
% Dec 13, 2035
%
*/
% :- module(logicmoo_plarkc,[]).

:- ensure_loaded(library(logicmoo_engine)).
:- asserta_new(user:file_search_path(pldata,'/opt/cyc/')).
:- asserta_new(user:file_search_path(pldata,library(pldata))).
:- asserta_new(user:file_search_path(logicmoo,library)).

/*
:- (current_prolog_flag(qcompile,PrevValue)->true;PrevValue=false),
   call(assert,on_fin(set_prolog_flag(qcompile,PrevValue))),
   set_prolog_flag(qcompile,large).
*/



:- baseKB:disable_mpred_expansion.
:- set_prolog_flag(lm_expanders,false).
:- if(exists_source(rs)).
:- wdmsg("loading rns").
:- load_files(rs,[if(not_loaded),qcompile(auto)]).
:- wdmsg("done with rns").
:- endif.

:- wdmsg("loading current_renames").
% :- time((user:load_files(library('pldata/kb_7166_current_renames'),[module(baseKB),redefine_module(false),qcompile(auto)]))).
:- retractall(renames(_)).
:- enable_mpred_expansion.
:- set_prolog_flag(lm_expanders,true).
:- wdmsg("done with current_renames").

%:- set_prolog_stack(local, limit(32*10**9)).
%:- set_prolog_stack(global, limit(32*10**9)).
% :- baseKB:ensure_loaded(logicmoo(plarkc/logicmoo_i_cyc_kb)).


:- if(false).
:- baseKB:disable_mpred_expansion.
:- set_prolog_flag(lm_expanders,false).
:- if(exists_source(pldata('kb_7166.qlf'))).
:- wdmsg("loading kb_7166").
:- install_constant_renamer_until_eof.
:- ensure_loaded(pldata('kb_7166.qlf')).
:- else.
:- wdmsg("qcompile kb_7166").
%:- install_constant_renamer_until_eof.
:- load_files(pldata(kb_7166),[if(not_loaded),qcompile(auto)]).
:- endif.
:- wdmsg("done loading kb_7166").
:- set_module(kb_7166:class(library)).
:- set_module(class(library)).
:- enable_mpred_expansion.
:- set_prolog_flag(lm_expanders,true).
:- endif.

:- if(current_predicate(on_fin/1)).
:- forall(call(retract,on_fin(CALL)),call(CALL)).
:- endif.

:- if(current_predicate(setup7166/0)).
:- initialization(setup7166,after_load).
:- initialization(setup7166,restore).
:- endif.


end_of_file.
%
:-in_cmt(listing(cwtdl/3)).
:- dmsg("Loading tinyKB should take under a minute").
:- ltkb1.
:- must((mudSubPart(iExplorer2,Inst),isa(Inst,tHumanNeck))).
:- must((mudSubPart(iExplorer2,Inst),isa(Inst,tHumanHair))).


/*
:- transTiny(Form,(ground(Form),functor(Form,F,1),F\== ~)).

:- set_gui_debug(false).
:- set_no_debug.
:- set_no_debug_thread.

:- transfer_predicate(tinyK8(Form), ( \+ contains_term('$VAR'(_),Form)) , ain((Form))).

:- mpred_trace.

:- set_clause_compile(fwc).

load_later:- quietly((transfer_predicate(tinyK8(Form),writeq(Form),ignore(on_x_log_throw(cwtdl(ain(clif(Form)),500,10)))))).

:- mpred_notrace.

:- in_cmt(listing(cwtdl_failed/1)).

*/
