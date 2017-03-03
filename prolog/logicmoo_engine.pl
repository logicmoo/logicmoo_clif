% #!/usr/bin/env swipl
/*  MUD server startup script in SWI-Prolog

*/

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% LOAD LOGICMOO (entry state)
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- if(\+ current_module(baseKB)).
:- use_module(library(logicmoo_repl)).
:- endif.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% SETUP KB EXTENSIONS
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- '$set_source_module'(baseKB).
:- '$set_typein_module'(baseKB).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% SETUP CYC KB EXTENSIONS
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
loadNewTiny:-
  baseKB:ain((tinyKB(C,_MT,_STR),{tinykb_assertion_recipe(C,CycLOut),delay_rule_eval(CycLOut,tiny_rule,NewAsserts)}
  ==> {dmsg(tiny_clif(NewAsserts))}, tiny_kb(NewAsserts))).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% SETUP SUMO KB EXTENSIONS
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- set_prolog_flag(do_renames,term_expansion).

:- baseKB:ensure_loaded(library('logicmoo/snark/common_logic_sumo.pfc')).

:- during_boot(set_prolog_flag(do_renames,restore)).

sumo_ain('$COMMENT'(_)):- !.
sumo_ain(D):- 
    must(kif_assertion_recipe(D,CycLOut)),
    sumo_ain1(CycLOut).

sumo_ain1(documentation(_, xtChineseLanguage,_)).
sumo_ain1(CycLOut):-
    delay_rule_eval(CycLOut,sumo_rule,NewAsserts),
    dmsg(NewAsserts),
    ain(NewAsserts).


loadSumo1:- 
   with_lisp_translation('./games/ontologyportal_sumo/Merge.kif',sumo_ain),
   with_lisp_translation('./games/ontologyportal_sumo/Mid-level-ontology.kif',sumo_ain),
   !.

loadSumo2:- 
   with_lisp_translation('./games/ontologyportal_sumo/Translations/relations-en.txt',sumo_ain),
   with_lisp_translation('./games/ontologyportal_sumo/english_format.kif',sumo_ain),
   with_lisp_translation('./games/ontologyportal_sumo/domainEnglishFormat.kif',sumo_ain),
   !.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% SAVE SUMO KB EXTENSIONS
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
:- after_boot(loadSumo1).
:- if(current_prolog_flag(logicmoo_qsave,true)).
:- statistics.
:- baseKB:qsave_lm(lm_repl1).
:- endif.

:- after_boot(loadSumo2).
:- if(current_prolog_flag(logicmoo_qsave,true)).
:- statistics.
:- baseKB:qsave_lm(lm_repl2).
:- endif.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% SAVE CYC KB EXTENSIONS
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
:- after_boot(loadTiny1).
:- if(current_prolog_flag(logicmoo_qsave,true)).
:- statistics.
:- baseKB:qsave_lm(lm_repl3).
:- endif.



% 	 	 
%% m1 is semidet.
%
% Hook To [checkkb:m1/0] For Module Logicmoo_snark.
% Module Secondary Helper.
%
%:- add_library_search_path('./mpred_online/',[ '*.pl']).
checkKB:m1:- gripe_time(40,ensure_loaded(logicmoo(mpred_online/xlisting_web))),if_defined(ensure_webserver), make,list_undefined.

% :- hook_message_hook.
% :- set_prolog_flag(verbose_autoload,false).
% :- set_prolog_flag(verbose_load,true).
% m9   :-asserta_if_new((user:term_expansion(I,O):- lmbase_expansion(term,user,I,O))).
%m31 :-   (F = mpred/_),foreach(must(baseKB:mpred_is_impl_file(F)),must_det_l((dmsg(list_file_preds(F)),ensure_loaded(F),export_file_preds(F),list_file_preds(F)))).
%m32:- rtrace(ensure_mpred_system).
% m33:- must(filematch_ext(['',mpred,ocl,moo,plmoo,pl,plt,pro,p,'pl.in',pfc,pfct],logicmoo_user:pfc/mpred,W)),dmsg(W),!.

%:-export(m2/0).
% m2:- ensure_mpred_file_loaded(logicmoo(pfc/relationAllExists)).

% :-ain(((P,Q,z(_))==>(p(P),q(Q)))).
%:-export(m3/0).
% m3:- put_variable_names( ['P'=P,'Q'=Q]), R = (==>((P,Q,z(_)),(p(P),q(Q)))),  renumbervars(write_functor,R,O), writeq(O).
%   put_variable_names( ['P'=P,'Q'=Q]), R = (==>((P,Q,z(_)),(p(P),q(Q)))), write_term(R,[numbervars(true),protray(_)]),renumbervars_prev(R,O).

%:-export(m4/0).

%m5 :- enable_mpred_system(baseKB).


ensure_autoexec:- !. % call_u(consult(logicmoo(pfc/'autoexec.pfc'))).

%:- use_listing_vars.
%:- autoload([verbose(false)]).
%:- use_listing_vars.
%:- nop((autoload,scan_for_varnames)).

mpred_load_restore_file(never):- !,ensure_autoexec,!.
mpred_load_restore_file(File):- absolute_file_name(File,AFN),AFN\=File,!,mpred_load_restore_file(AFN).
mpred_load_restore_file(File):- \+ exists_file(File),
  ensure_autoexec, !,
  mpred_save_restore_file(File),!.

mpred_load_restore_file(File):-
  must_det_l((
  time_file(File,Time),
  qcompile(File),
  ensure_loaded(File),
   ((\+ (baseKB:loaded_file_world_time(N,_,NewTime),NewTime>=Time)) ->true ;
    (
    ignore((baseKB:loaded_file_world_time(N,_,NewTime),NewTime>Time,with_ukb_snark(baseKB,ensure_mpred_file_loaded(N)),fail)),
    mpred_save_restore_file('some_test.pl~'))))),!.

mpred_save_resore_predicate(M:H,AFN):-
   functor(H,F,A),
   format('~N:- multifile(~q:(~q)/~q).~n',[M,F,A]),
   once((prolog_listing:list_declarations(M:H,M))),
   clause(M:H,B,R), 
   once(clause_property(R,file(AFN));\+clause_property(R,file(_))),
   ignore(once(get_clause_vars(H:-B))),
   prolog_listing:portray_clause((H:-B)).


mpred_save_restore_file(File):- 
 must_det_l((   
  absolute_file_name(File,AFN),
   tell(AFN), 
   format('~N:- ~q.~n',['$set_source_module'(basePFC)]),
   format('~N:- style_check(-singleton).'),  
   listing(_),
   flush_output,
   format('~N:- style_check(-singleton).'),
   format('~N:- ~q.~n',['$set_source_module'(baseKB)]),
   ignore((
   cur_predicate(_,baseKB:H),
    mpred_save_resore_predicate(baseKB:H,AFN),
   flush_output,
   fail)),!,
      format('~N:- ~q.~n',['$set_source_module'(baseKB)]),
      format('~N:- style_check(-singleton).~n'),
      listing(baseKB:loaded_file_world_time/3),
      flush_output,
   told)),!.

