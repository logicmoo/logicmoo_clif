% File: /opt/PrologMUD/pack/logicmoo_base/prolog/logicmoo/snark/common_logic_snark.pl
% :- if(( ( \+ ((current_prolog_flag(logicmoo_include,Call),Call))) )).
:- module(common_logic_snark,
          [ add_nesc/2,
            add_poss/2,
            add_poss_to/3,
            add_preconds/2,
            add_preconds2/2,
            adjust_kif/3,
            adjust_kif0/3,
            adjust_kif0/4,
            adjust_kif0/5,
            adjust_kif5/5,
            alt_kif_to_boxlog/4,
            any_to_pfc/2,
            any_to_pfc0/2,
            as_dlog/2,
            baseKB:as_prolog_hook/2,
            as_symlog/2,
            check_is_kb/1,
            kif_to_pfc/2,
            clauses_to_boxlog/4,
            clauses_to_boxlog_0/4,
            clauses_to_boxlog_1/4,
            clauses_to_boxlog_2/4,
            clauses_to_boxlog_5/4,
            convertAndCall/2,
            correct_arities/3,
            % elInverse/2,
            flatten_or_list/3,
            fmtl/1,
            generate_ante/4,
            get_1_var_name/3,
            get_constraints/2,
            get_lits/2,
            get_var_names/3,
            is_clif/1,
          are_clauses_entailed/1,
          is_prolog_entailed/1,
          delistify_last_arg/3,
            kb_incr/2,
            kif/0,
            kif_ask/1,
            kif_ask/2,
            kif_ask_sent/1,
            kif_hook/1,
            kif_io/2,
            kif_process/1,
            kif_process/2,
            kif_read/3,
            (kif_add)/1,
            kif_add_adding_constraints/3,
            kif_add_boxes1/2,
            kif_add_boxes3/3,
            kif_test_string/1,
            kif_to_boxlog/2,
            kif_to_boxlog/3,
            kif_to_boxlog/4,
            kif_to_boxlog_attvars/4,            
            kif_unnumbervars/2,
            lit_cost/3,
            litcost_compare/4,
            local_pterm_to_sterm/2,
            local_pterm_to_sterm2/2,
            local_sterm_to_pterm/2,
            ain_h/3,
            mpred_t_tell_kif/2,
            map_each_clause/3,
            map_each_clause/2,
            mudEquals/2,
            neg_b_if_neg/3,
            neg_h_if_neg/2,
            not_mudEquals/2,
            nots_to/3,
            unnumbervars_with_names/2,
            is_quantifier/1,
            pfc_for_print_left/2,
            pfc_for_print_right/2,
            save_in_code_buffer/2,
            save_wfs/2,
            should_be_poss/1,
            simp_code/2,
            simple_negate_literal/3,
            simplify_bodies/2,
            simplify_list/3,
            skolem_in_code/2,skolem_in_code/3,
            sort_body/3,
            sort_body_0/3,
            subsT_each/3,
            tkif/0,
            to_dlog_ops/1,
            to_nonvars/3,
            to_prolog_ops/1,
            to_symlog_ops/1,
            tsn/0,
            type_of_var/3,
            use_was_isa_h/3,
            var_count_num/4,
            wdmsgl/1,
            wdmsgl_2/2,
            wdmsgl_3/3,
            wdmsgl_4/3,
            why_to_id/3,
            write_list/1,
            (is_entailed_u)/1,
   % op(300,fx,'-'),
   /*op(1150,xfx,'=>'),
   op(1150,xfx,'<=>'),
   op(350,xfx,'xor'),
   op(400,yfx,'&'),
   op(500,yfx,'v')*/
   % if/2,iif/2,   
            is_not_entailed/1
                    
          ]).
/** <module> common_logic_snark
% Provides a specific compilation API for KIF axioms
%

% Logicmoo Project PrologMUD: A MUD server written in Prolog
% Maintainer: Douglas Miles
% Dec 13, 2035
%
*/

:- include('../mpred/mpred_header.pi').
%:- endif.

:-
            op(1150,fx,(was_dynamic)),
            op(1150,fx,(was_multifile)),
            op(1150,fy,(was_module_transparent)).
            

:-
 op(1199,fx,('==>')), 
 op(1190,xfx,('::::')),
 op(1180,xfx,('==>')),
 op(1170,xfx,'<==>'),  
 op(1160,xfx,('<-')),
 op(1150,xfx,'=>'),
 op(1140,xfx,'<='),
 op(1130,xfx,'<=>'), 
 op(600,yfx,'&'), 
 op(600,yfx,'v'),
 op(350,xfx,'xor'),
 op(300,fx,'~'),
 op(300,fx,'-').

%:- baseKB:ensure_loaded(logicmoo('plarkc/logicmoo_i_cyc_rewriting')).


:- module_transparent(( are_clauses_entailed/1,
            is_prolog_entailed/1,
            delistify_last_arg/3)).

:- meta_predicate
   % common_logic_snark
   convertAndCall(*,0),
   % common_logic_snark
   kif_process(*,0),
   % common_logic_snark
   kif_process(0),
   % common_logic_snark
   kif_add_boxes3(2,?,*),
   % common_logic_snark
   ain_h(2,?,*),
   map_each_clause(1,+),
   map_each_clause(2,+,-),

   %'__aux_maplist/3_map_each_clause+1'(*,*,2),
   %'__aux_maplist/2_map_each_clause+1'(*,1),

   % common_logic_snark
   to_nonvars(2,?,?).

%:- meta_predicate '__aux_maplist/2_map_each_clause+1'(*,1).
%:- meta_predicate '__aux_maplist/3_map_each_clause+1'(*,*,2).

/*
:- was_dynamic
        baseKB:as_prolog_hook/2,
        elInverse/2,
        kif_test_string/1,
        mudEquals/2,
        not_mudEquals/2.
        
*/

% :- dynamic(baseKB:(if/2,iif/2)).

:- export(kw_to_vars/2).
kw_to_vars(KW,VARS):-subsT_each(KW,[':ARG1'=_ARG1,':ARG2'=_ARG2,':ARG3'=_ARG3,':ARG4'=_ARG4,':ARG5'=_ARG5,':ARG6'=_ARG6],VARS).



%= 	 	 

%% kif_hook(+TermC) is semidet.
%
% Knowledge Interchange Format Hook.
%
kif_hook(C):- not_ftCompound(C),!,fail.
kif_hook(_H :- _):- !,fail.
kif_hook(_H <- _):- !,fail.
kif_hook(_ ==> _):- !,fail.
kif_hook(_ <==> _):- !,fail.
kif_hook(_=>_).
kif_hook(_<=_).
kif_hook(_<=>_).
kif_hook((_ & _)).
kif_hook((_ /\ _)).
kif_hook((_ \/ _)).
kif_hook((_ v _)).
kif_hook(nesc(_)).
kif_hook(poss(_)).
kif_hook(all(_,_)).
kif_hook(forall(_,_)).
kif_hook(exists(_,_)).
kif_hook(if(_,_)).
kif_hook(iff(_,_)).
% uncommenting these next 3 lines may dbreak sanity_birdt test
kif_hook( ~(H)):- !,nonvar(H),!,kif_hook(H).
kif_hook( \+ H):- !,nonvar(H),!,kif_hook(H).
kif_hook( not(H)):- !,nonvar(H),!,kif_hook(H).
kif_hook(C):- C=..[F,A|_],is_sentence_functor(F),!,kif_hook(A).
  


%= 	 	 

%% are_clauses_entailed( :TermE) is semidet.
%
% Are Clauses Entailed.
%
% 
are_clauses_entailed(E):-var(E),!,fail.
are_clauses_entailed(B):- unnumbervars(B,A),call_u(map_each_clause(is_prolog_entailed,A)).



%% is_prolog_entailed( ?Prolog) is semidet.
%
% True if the "Prolog" clause is asserted
%

is_prolog_entailed(UCL):-clause_asserted(UCL),!.
is_prolog_entailed(UCL):-clause_asserted_i(UCL),!.
is_prolog_entailed(UCL):-show_failure(clause_asserted_u(UCL)),!.
is_prolog_entailed(UCL):-clause(UCL,B),split_attrs(B,A,BB),must(A),BB.
is_prolog_entailed(UCL):-clause(UCL,B,Ref),(B\==true->must(B);(dtrace,clause(HH,BB,Ref),dmsg(BB:-(UCL,HH)))),!.
is_prolog_entailed(UCL):- wdmsg(warn(not_is_prolog_entailed(UCL))),!.


%= 	 	 

%% member_ele( ?E, ?E) is semidet.
%
% Member Ele.
%
member_ele(E,E):- is_ftVar(E),!.
member_ele([],_):-!,fail.
member_ele(E,E):- ( \+ (compound(E))),!.
member_ele([L|List],E):- must(is_list([L|List])),!,member(EE,[L|List]),member_ele(EE,E).
member_ele((H,T),E):- nonvar(H),nonvar(T),!, (member_ele(H,E);member_ele(T,E)).
member_ele(E,E).


%= 	 	 

%% delistify_last_arg( ?Arg, :TermPred, ?Last) is semidet.
%
% Delistify Last Argument.
%
delistify_last_arg(Arg,Pred,Last):-is_list(Arg),!,member(E,Arg),delistify_last_arg(E,Pred,Last).
delistify_last_arg(Arg,M:Pred,Last):- Pred=..[F|ARGS],append([Arg|ARGS],[NEW],NARGS),NEWCALL=..[F|NARGS],show_failure(M:NEWCALL),!,member_ele(NEW,Last).
delistify_last_arg(Arg,Pred,Last):- Pred=..[F|ARGS],append([Arg|ARGS],[NEW],NARGS),NEWCALL=..[F|NARGS],show_failure(NEWCALL),!,member_ele(NEW,Last).

% sanity that mpreds (manage prolog prodicate) are abily to transform

% cwc "code-wise chaining" is always true in Prolog but will throw programming error if evalled in LogicMOO Prover.
% Use this to mark code and not axiomatic prolog


map_each_clause(P,CLIF,Prolog):- is_list(CLIF),!,maplist(map_each_clause(P),CLIF,Prolog).
map_each_clause(P,(H,CLIF),(T,Prolog)):-  sanity(nonvar(H)),!,map_each_clause(P,H,T),map_each_clause(P,CLIF,Prolog).
map_each_clause(P,A,B):- call(P,A,B).

map_each_clause(P,CLIF):-  is_list(CLIF),!,maplist(map_each_clause(P),CLIF).
map_each_clause(P,(H,CLIF)):-  sanity(nonvar(H)),!,map_each_clause(P,H),map_each_clause(P,CLIF).
map_each_clause(P,A):- call(P,A).

%% any_to_pfc( :TermCLIF, ?Prolog) is semidet.
%
% Converted To Prolog.
%
any_to_pfc(B,A):-  must(map_each_clause(any_to_pfc0,B,A)).

any_to_pfc0(B,A):-  is_kif_clause(B),!,kif_to_pfc0(B,A).
any_to_pfc0(B,A):-  is_pfc_clause(B),!,fully_expand(clause(any_to_pfc,any_to_pfc),B,A).
any_to_pfc0(B,A):-  is_prolog_clause(B),!,boxlog_to_pfc(B,A).
any_to_pfc0(B,A):-  !, trace_or_throw(should_never_be_here(any_to_pfc0(B,A))).
any_to_pfc0((H:-B),PrologO):- must((show_failure(why,boxlog_to_pfc((H:-B),Prolog)),!,=(Prolog,PrologO))),!.


%% kif_to_pfc( :TermCLIF, ?Prolog) is semidet.
%
% Ieee Standard Common Logic Interchange Format Version Converted To Prolog.
%
kif_to_pfc(B,A):-  must(map_each_clause(kif_to_pfc0,B,A)).

kif_to_pfc0(CLIF,Prolog):- 
   sanity(is_kif_clause(CLIF)),
  % somehow integrate why_to_id(tell,Wff,Why),
     must_det_l((
      kif_to_boxlog(CLIF,BOXLOG),
      boxlog_to_pfc(BOXLOG,Prolog),
      (BOXLOG=@=Prolog -> true; (pfc_for_print_left(Prolog,PrintPFC),wdmsg(-PrintPFC))))),!.
      


%% pfc_for_print_left( ?Prolog, ?PrintPFC) is semidet.
%
% Prolog Backward Chaining Print.
%
pfc_for_print_left(Prolog,PrintPFC):-is_list(Prolog),!,maplist(pfc_for_print_left,Prolog,PrintPFC).
%pfc_for_print_left(==>(P,if_missing(R,Q)),(Q :- (fwc, naf(R), P))):-!.
%pfc_for_print_left(if_missing(R,Q),(Q :- (fwc, naf(R)))):-!.
pfc_for_print_left(==>(P,Q),(Q:-fwc, P)):-!.
pfc_for_print_left(Prolog,PrintPFC):- =(Prolog,PrintPFC).

%% pfc_for_print_right( ?Prolog, ?PrintPFC) is semidet.
%
% Prolog Forward Chaining Print.
%
pfc_for_print_right(Prolog,PrintPFC):-is_list(Prolog),!,maplist(pfc_for_print_right,Prolog,PrintPFC).
pfc_for_print_right('<-'(Q,P),'->'(P, Q)):-!.
pfc_for_print_right(Prolog,PrintPFC):- =(Prolog,PrintPFC).



%% is_entailed_u( ?CLIF) is semidet.
%
% If Is A Entailed.
%   A good sanity Test for expected side-effect entailments
%   
%
is_entailed_u(CLIF):- 
  mpred_run,
 mpred_nochaining((
   any_to_pfc(CLIF,Prolog),!, \+ \+ are_clauses_entailed(Prolog))),!.


%% is_not_entailed( ?CLIF) is semidet.
%
% If Is A Not Entailed.
%  A good sanity Test for required absence of specific side-effect entailments
%
is_not_entailed(CLIF):-  mpred_nochaining((kif_to_pfc(CLIF,Prolog), \+ are_clauses_entailed(Prolog))).

:- op(1190,xfx,(:-)).
:- op(1200,fy,(is_entailed_u)).

% this defines a recogniser for clif syntax (well stuff that might be safe to send in thru kif_to_boxlog)

%= 	 	 

%% is_clif( :TermCLIF) is semidet.
%
% True if an expression is in ISO Common Logic Interchange Format.
%
is_clif(all(_,X)):-compound(X),!.
is_clif(forall(_,X)):-compound(X),!,is_clif(X).
is_clif(CLIF):-
  VVs = v(if,iff,clif_forall,all,exists), % but not: implies,equiv,forall
   (var(CLIF)-> (arg(_,VVs,F),functor(CLIF,F,2));
     compound(CLIF),functor(CLIF,F,2),arg(_,VVs,F)).


:- style_check(+singleton).


%= 	 	 

%% correct_arities( ?VALUE1, ?FmlO, ?FmlO) is semidet.
%
% Correct Arities.
%
correct_arities(_,FmlO,FmlO):-leave_as_is(FmlO),!.
correct_arities([],Fml,Fml):-!.
correct_arities([H|B],Fml,FmlO):-!,correct_arities(H,Fml,FmlM),correct_arities(B,FmlM,FmlO).
correct_arities(_,Fml,Fml):- \+ compound(Fml),!.
correct_arities(H,Fml,FmlO):- Fml=..[H,A|ARGS], ARGS\=[_],
  (ARGS==[]-> correct_arities(H,A,FmlO);
       (correct_arities(H,A,CA),FmlM=..[H|ARGS],correct_arities(H,FmlM,FmlMC),FmlO=..[H,CA,FmlMC])),!.
correct_arities(H,Fml,FmlM):- Fml=..[F|ARGS],must_maplist(correct_arities(H),ARGS,ARGSM),FmlM =.. [F|ARGSM].


:- public(subsT_each/3).

%= 	 	 

%% subsT_each( ?In, :TermARG2, ?In) is semidet.
%
% Subs True Stucture Each.
%
subsT_each(In,[],In):- !.
% subsT_each(In,[KV|TODO],Out):- !,get_kv(KV,X,Y),subst_except(In,X,Y,Mid),!,subsT_each(Mid,TODO,Out),!.
subsT_each(In,[KV|TODO],Out):- subst_except_l(In,[KV|TODO],Out).


%= 	 	 

%% subst_except_l( :TermVar, ?VALUE2, :TermVar) is semidet.
%
% Subst Except (list Version).
%
subst_except_l(  Var, List, NVar ) :- nonvar(NVar),!,subst_except_l(  Var, List, MVar ),!,must(MVar=NVar).
subst_except_l(  Var, _,Var ) :- is_ftVar(Var),!.
% subst_except_l(  Var, _,Var ) :- leave_as_is(Var),!.
subst_except_l(  N, List,V ) :- member(N=V,List),!.
subst_except_l(   [], _,[] ) :-!.
subst_except_l([H|T],List,[HH|TT]):- !, subst_except_l(H,List,HH), subst_except_l(T,List,TT).
subst_except_l(HT,List,HHTT):- compound(HT),
   compound_name_arguments(HT,F,ARGS0),
   subst_except_l([F|ARGS0],List,[FM|MARGS]),!,
   (atom(FM)->HHTT=..[FM|MARGS];append_termlist(FM,MARGS,HHTT)),!.
subst_except_l(HT,_List,HT).



:- dynamic(mudEquals/2).
:- export(mudEquals/2).

%= 	 	 

%% mudEquals( ?X, ?Y) is semidet.
%
% Application Equals.
%
mudEquals(X,Y):- X=Y.



%= 	 	 

%% skolem_in_code( ?X, ?Y) is semidet.
%
% Skolem In Code.
%
skolem_in_code(X,Y):- ignore(X=Y).

%= 	 	 

%% skolem_in_code( ?X, ?VALUE2, ?Fml) is semidet.
%
% Skolem In Code.
%
skolem_in_code(X,_,Fml):- when('?='(X,_),skolem_in_code(X,Fml)).

:- public(not_mudEquals/2).
:- was_dynamic(not_mudEquals/2).

%= 	 	 

%% not_mudEquals( ?X, ?Y) is semidet.
%
% Not Application Equals.
%
not_mudEquals(X,Y):- dif:dif(X,Y).

:- public(type_of_var/3).

%= 	 	 

%% type_of_var( ?Fml, ?Var, ?Type) is semidet.
%
% Type Of Variable.
%
type_of_var(Fml,Var,Type):- contains_type_lits(Fml,Var,Lits),!,(member(Type,Lits)*->true;Type='Unk').
:- style_check(+singleton).



%= 	 	 

%% to_dlog_ops( ?VALUE1) is semidet.
%
% Converted To Datalog Oper.s.
%
to_dlog_ops([
   '~'='~',
       'theExists'='exists',
       'thereExists'='exists',
       'ex'='exists',
       'forAll'='all',
       'forall'='all',
       ';'='v',
       ','='&',
       'neg'='~',
     % '-'='~',
     
    'not'='~',
     '\\+'='naf',
     'and'='&',
     '^'='&',
     '/\\'='&',
      'or'='v',
      '\\/'='v',
      'V'='v',
      ':-'=':-',
 'implies'='=>',
   'if'='=>',
   'iff'='<=>',
 'implies_fc'='==>',
 'implies_bc'='->',
   'equiv'='<=>',
      '=>'='=>',
     '<=>'='<=>']).


%= 	 	 

%% to_symlog_ops( ?VALUE1) is semidet.
%
% Converted To Symlog Oper.s.
%
to_symlog_ops([
   ';'='v',
   ','='&'
   %'=>'='=>',
   %'<=>'='<=>',
   %'not'='~',
   %':-'=':-'
   ]).


%= 	 	 

%% to_prolog_ops( ?VALUE1) is semidet.
%
% Converted To Prolog Oper.s.
%
to_prolog_ops([
   'v'=';',
   '&'=(',')
   %'=>'='=>',
   %'<=>'='<=>',
   %'~'='~',
   %'naf'='not',
   %'naf'='not',
   %':-'=':-'
   ]).



%= 	 	 

%% to_nonvars( :PRED2Type, ?IN, ?IN) is semidet.
%
% Converted To Nonvars.
%
to_nonvars(_Type,IN,IN):- is_ftVar(IN),!.
to_nonvars(_,Fml,Fml):- leave_as_is(Fml),!.
to_nonvars(Type,IN,OUT):- is_list(IN),!,must_maplist(to_nonvars(Type),IN,OUT),!.
to_nonvars(Type,IN,OUT):- call(Type,IN,OUT),!.



%% convertAndCall( ?Type, :Goal) is semidet.
%
% Convert And Call.
%
convertAndCall(Type,Call):- fail,Call=..[F|IN],must_maplist(to_nonvars(Type),IN,OUT), IN \=@= OUT, !, must(apply(F,OUT)).
convertAndCall(_Type,Call):-call_last_is_var(Call).


%= 	 	 

%% as_dlog( ?Fml, ?Fml) is semidet.
%
% Converted To Datalog.
%
as_dlog(Fml,Fml):- leave_as_is(Fml),!.
as_dlog(Fml,FmlO):- to_dlog_ops(OPS),subsT_each(Fml,OPS,FmlM),!,correct_arities(['v','&'],FmlM,FmlO).





%= 	 	 

%% as_symlog( ?Fml, ?Fml) is semidet.
%
% Converted To Symlog.
%
as_symlog(Fml,Fml):- leave_as_is(Fml),!.
as_symlog(Fml,FmlO):- as_dlog(Fml,FmlM),to_symlog_ops(OPS),subsT_each(FmlM,OPS,FmlM),correct_arities(['v','&'],FmlM,FmlO).


%= 	 	 

%% baseKB:as_prolog_hook( ?Fml, ?Fml) is semidet.
%
% Converted To Prolog.
%
baseKB:as_prolog_hook(Fml,Fml):- is_ftVar(Fml),!.
baseKB:as_prolog_hook(Fml,FmlO):- as_symlog(Fml,FmlM),
  to_prolog_ops(OPS),subsT_each(FmlM,OPS,FmlO).





%= 	 	 

%% adjust_kif( ?KB, ?Kif, ?KifO) is semidet.
%
% Adjust Knowledge Interchange Format.
%
adjust_kif(KB,Kif,KifO):- as_dlog(Kif,KifM),must(adjust_kif0(KB,KifM,KifO)),!.

% Converts to syntax that NNF/DNF/CNF/removeQ like



%= 	 	 

%% adjust_kif0( ?VALUE1, ?V, ?V) is semidet.
%
% Adjust Knowledge Interchange Format Primary Helper.
%

adjust_kif0(KB,I,O):-nonvar(O),!,adjust_kif0(KB,I,M),!,M=O.
adjust_kif0(_,V,V):- is_ftVar(V),!.
adjust_kif0(_,A,A):- \+ compound(A),!.
adjust_kif0(KB,not(Kif),(KifO)):- !,adjust_kif0(KB, ~(Kif),KifO).
adjust_kif0(KB,\+(Kif),(KifO)):- !,adjust_kif0(KB, naf(Kif),KifO).
adjust_kif0(KB,nesc(N,Kif),nesc(N,KifO)):- !,adjust_kif0(KB,Kif,KifO).
adjust_kif0(KB,poss(N,Kif),poss(N,KifO)):- !,adjust_kif0(KB,Kif,KifO).
adjust_kif0(KB, ~(Kif), ~(KifO)):- !,adjust_kif0(KB,Kif,KifO).
adjust_kif0(KB, ~(KB,Kif), ~(KifO)):- !,adjust_kif0(KB,Kif,KifO).
adjust_kif0(KB,t(Kif),t(KifO)):- !,adjust_kif0(KB,Kif,KifO).
adjust_kif0(KB,poss(Kif),poss(b_d(KB,nesc,poss),KifO)):- !,adjust_kif0(KB,Kif,KifO).
adjust_kif0(KB,nesc(Kif),nesc(b_d(KB,nesc,poss),KifO)):- !,adjust_kif0(KB,Kif,KifO).
adjust_kif0(KB,exists(L,Expr),               ExprO):-L==[],!,adjust_kif0(KB,Expr,ExprO).
adjust_kif0(KB,exists(V,Expr),               ExprO):-atom(V),svar_fixvarname(V,L),subst(Expr,V,'$VAR'(L),ExprM),!,adjust_kif0(KB,exists('$VAR'(L),ExprM),ExprO).
adjust_kif0(KB,exists([L|List],Expr),        ExprO):-is_list(List),!,adjust_kif0(KB,exists(L,exists(List,Expr)),ExprO).
adjust_kif0(KB,exists(L,Expr),               ExprO):- \+ contains_var(L,Expr),!,adjust_kif0(KB,Expr,ExprO).
adjust_kif0(KB,exists(L,Expr),exists(L,ExprO)):-!,adjust_kif0(KB,Expr,ExprO).
adjust_kif0(KB,all(L,Expr),               ExprO):-L==[],!,adjust_kif0(KB,Expr,ExprO).
adjust_kif0(KB,all(V,Expr),               ExprO):-atom(V),svar_fixvarname(V,L),subst(Expr,V,'$VAR'(L),ExprM),!,adjust_kif0(KB,all('$VAR'(L),ExprM),ExprO).
adjust_kif0(KB,all([L|List],Expr),all(L,ExprO)):-is_list(List),!,adjust_kif0(KB,exists(List,Expr),ExprO).
adjust_kif0(KB,all(L,Expr),               ExprO):- \+ contains_var(L,Expr),!,adjust_kif0(KB,Expr,ExprO).
adjust_kif0(KB,all(L,Expr),all(L,ExprO)):-!,adjust_kif0(KB,Expr,ExprO).
adjust_kif0(KB,[L|Ist],ConjO):- is_list([L|Ist]),must_maplist(adjust_kif0(KB),[L|Ist],ConjO),!.
adjust_kif0(KB,'&'([L|Ist]),ConjO):- is_list([L|Ist]),list_to_conjuncts('&',[L|Ist],Conj),adjust_kif0(KB,Conj,ConjO).
adjust_kif0(KB,'v'([L|Ist]),ConjO):- is_list([L|Ist]),list_to_conjuncts('v',[L|Ist],Conj),adjust_kif0(KB,Conj,ConjO).
adjust_kif0(KB,(H:-[L|Ist]),(HH:-ConjO)):- adjust_kif(KB,H,HH),is_list([L|Ist]),adjust_kif0(KB,'&'([L|Ist]),ConjO).
adjust_kif0(KB,(H:-B),(HH:-ConjO)):- adjust_kif(KB,H,HH),adjust_kif(KB,B,ConjO),!.
adjust_kif0(_,A,A):-leave_as_is(A),!.
adjust_kif0(KB,Kif,KifO):- Kif=..[F|ARGS],adjust_kif0(KB,F,ARGS,KifO),!.
adjust_kif0(KB,PAB,PABO):- PAB=..[P|AB],must_maplist(adjust_kif0(KB),AB,ABO),PABO=..[P|ABO].


%= 	 	 

%% adjust_kif0( ?KB, ?Not_P, :TermARGS, ?O) is semidet.
%
% Adjust Knowledge Interchange Format Primary Helper.
%
adjust_kif0(KB,call_builtin,ARGS,O):-!,PARGS=..ARGS,adjust_kif0(KB,PARGS,O),!.
adjust_kif0(KB,true_t,[F|LIST],O3):-atom(F),!,PARGS=..[F|LIST],adjust_kif0(KB,(PARGS),O3),!.
adjust_kif0(KB,not_true_t,[F|LIST],O3):-atom(F),!,PARGS=..[F|LIST],adjust_kif0(KB, ~(PARGS),O3),!.
adjust_kif0(KB,~,[A],~(O)):-!,adjust_kif0(KB,A,O),!.
adjust_kif0(KB,not,[A],~(O)):-!,adjust_kif0(KB,A,O),!.
adjust_kif0(KB,possible_t,[A],O):-!,adjust_kif0(KB,poss(A),O),!.
adjust_kif0(KB,possible_t,ARGS,O):-!,PARGS=..ARGS,adjust_kif0(KB,poss(PARGS),O).
adjust_kif0(KB,asserted_t,[A],O):-!,adjust_kif0(KB,t(A),O),!.
adjust_kif0(KB,asserted_t,ARGS,O):-!,PARGS=..ARGS,adjust_kif0(KB,t(PARGS),O).
adjust_kif0(KB,true_t,ARGS,O):-PARGS=..ARGS,adjust_kif0(KB,PARGS,O),!.
adjust_kif0(KB,Not_P,ARGS,O):-atom_concat('not_',P,Not_P),!,PARGS=..[P|ARGS],adjust_kif0(KB, ~(PARGS),O).
adjust_kif0(KB,Int_P,ARGS,O):-atom_concat('int_',P,Int_P),!,append(LARGS,[_, _, _, _, _, _, _ ],ARGS),
   PLARGS=..[P|LARGS],adjust_kif0(KB,PLARGS,O).
adjust_kif0(KB,P,ARGS,O):-atom_concat(_,'_t',P),!,append(LARGS,[_, _, _, _, _, _],ARGS),
   PARGS=..[P|LARGS],adjust_kif0(KB,PARGS,O).

adjust_kif0(KB,W,[P,A,R|GS],O):- call(call_u(is_wrapper_pred(W))),PARGS=..[P,A,R|GS],adjust_kif0(KB,t(PARGS),O).
adjust_kif0(KB,F,ARGS,O):-KIF=..[F|ARGS],length(ARGS,L),L>2,adjust_kif0(KB,KIF,F,ARGS,Conj),KIF\=@=Conj,!,adjust_kif0(KB,Conj,O).
% adjust_kif0(KB,W,[A],O):-is_wrapper_pred(W),adjust_kif(KB,A,O),!.


%= 	 	 

%% adjust_kif0( ?KB, ?KIF, ?OP, ?ARGS, ?Conj) is semidet.
%
% Adjust Knowledge Interchange Format Primary Helper.
%
adjust_kif0(KB,KIF,OP,ARGS,Conj):-must_maplist(adjust_kif(KB),ARGS,ABO),adjust_kif5(KB,KIF,OP,ABO,Conj).


%= 	 	 

%% adjust_kif5( ?KB, ?KIF, ?VALUE3, ?ARGS, ?Conj) is semidet.
%
% Adjust Kif5.
%
adjust_kif5(_KB,_KIF,',',ARGS,Conj):- list_to_conjuncts('&',ARGS,Conj).
adjust_kif5(      _,_,';',ARGS,Conj):-list_to_conjuncts('v',ARGS,Conj).
adjust_kif5(      _,_,'v',ARGS,Conj):-list_to_conjuncts('v',ARGS,Conj).
adjust_kif5(      _,_,'&',ARGS,Conj):-list_to_conjuncts('&',ARGS,Conj).



%= 	 	 

%% local_pterm_to_sterm( ?P, ?S) is semidet.
%
% Local Pterm Converted To Sterm.
%
local_pterm_to_sterm(P,['$VAR'(S)]):- if_defined(mpred_sexp_reader:svar(P,S)),!.
local_pterm_to_sterm(P,['$VAR'(S)]):- if_defined(mpred_sexp_reader:lvar(P,S)),!.
local_pterm_to_sterm(P,[P]):- leave_as_is(P),!.
local_pterm_to_sterm((H:-P),(H:-S)):-!,local_pterm_to_sterm(P,S),!.
local_pterm_to_sterm((P=>Q),[implies,PP,=>,QQ]):-local_pterm_to_sterm(P,PP),local_pterm_to_sterm(Q,QQ).
local_pterm_to_sterm((P<=>Q),[equiv,PP,QQ]):-local_pterm_to_sterm(P,PP),local_pterm_to_sterm(Q,QQ).
local_pterm_to_sterm(all(P,Q),[all(PP),QQ]):-local_pterm_to_sterm(P,PP),local_pterm_to_sterm(Q,QQ).
local_pterm_to_sterm(exists(P,Q),[ex(PP),QQ]):-local_pterm_to_sterm(P,PP),local_pterm_to_sterm(Q,QQ).
local_pterm_to_sterm( ~(Q),[not,QQ]):-local_pterm_to_sterm(Q,QQ).
local_pterm_to_sterm(poss(Q),[pos(QQ)]):-local_pterm_to_sterm(Q,QQ).
local_pterm_to_sterm('&'(P,Q),PPQQ):-local_pterm_to_sterm(P,PP),local_pterm_to_sterm(Q,QQ),flatten([PP,QQ],PPQQ0),list_to_set(PPQQ0,PPQQ).
local_pterm_to_sterm(','(P,Q),PPQQ):-local_pterm_to_sterm(P,PP),local_pterm_to_sterm(Q,QQ),flatten([PP,QQ],PPQQ0),list_to_set(PPQQ0,PPQQ).
local_pterm_to_sterm('v'(P,Q),[or,[PP],[QQ]]):-local_pterm_to_sterm(P,PP),local_pterm_to_sterm(Q,QQ),!.
local_pterm_to_sterm('beliefs'(P,Q),[beliefs(PP),QQ]):-local_pterm_to_sterm2(P,PP),local_pterm_to_sterm(Q,QQ),!.
local_pterm_to_sterm(P,S):-subst_except(P,'&',',',Q),P\=@=Q,!,local_pterm_to_sterm(Q,S),!.
local_pterm_to_sterm(P,S):-subst_except(P,'v',';',Q),P\=@=Q,!,local_pterm_to_sterm(Q,S),!.
local_pterm_to_sterm(P,[Q]):-P=..[F|ARGS],maplist(local_pterm_to_sterm2,ARGS,QARGS),Q=..[F|QARGS].
local_pterm_to_sterm(P,[P]).


%= 	 	 

%% local_pterm_to_sterm2( ?P, ?Q) is semidet.
%
% Local Pterm Converted To Sterm Extended Helper.
%
local_pterm_to_sterm2(P,Q):-local_pterm_to_sterm(P,PP),([Q]=PP;Q=PP),!.






%======  make a sequence out of a disjunction =====

%= 	 	 

%% flatten_or_list( ?A, ?B, ?C) is semidet.
%
% Flatten Or List.
%
flatten_or_list(A,B,C):- convertAndCall(as_symlog,flatten_or_list(A,B,C)).
flatten_or_list(KB,v(X , Y), F):- !,
   flatten_or_list(KB,X,A),
   flatten_or_list(KB,Y,B),
   flatten([A,B],F).
flatten_or_list(_KB,X,[X]).




%= 	 	 

%% fmtl( ?X) is semidet.
%
% Fmtl.
%
fmtl(X):- baseKB:as_prolog_hook(X,XX), fmt(XX).


%= 	 	 

%% write_list( ?F) is semidet.
%
% Write List.
%
write_list([F|R]):- write(F), write('.'), nl, write_list(R).
write_list([]).


%= 	 	 

%% unnumbervars_with_names( ?Term, ?CTerm) is semidet.
%
% Numbervars Using Names.
%

unnumbervars_with_names(Term,CTerm):- !, must(quietly(unnumbervars(Term,CTerm))),!.
unnumbervars_with_names(Term,CTerm):- ground(Term),!,duplicate_term(Term,CTerm).

unnumbervars_with_names(Term,CTerm):-
 must_det_l((
   source_variables_l(NamedVars),
   copy_term(Term:NamedVars,CTerm:CNamedVars),
   b_implode_varnames0(CNamedVars))),!.


 unnumbervars_with_names(Term,CTerm):-
  must_det_l((
   source_variables_l(NamedVars),
   copy_term(Term:NamedVars,CTerm:CNamedVars),
   term_variables(CTerm,Vars),
   call((dtrace,get_var_names(Vars,CNamedVars,Names))),
   b_implode_varnames0(Names),
  % numbervars(CTerm,91,_,[attvar(skip),singletons(false)]),
   append(CNamedVars,NamedVars,NewCNamedVars),
   list_to_set(NewCNamedVars,NewCNamedVarsS),
   remove_grounds(NewCNamedVarsS,NewCNamedVarsSG),
   put_variable_names(NewCNamedVarsSG))),!.


unnumbervars_with_names(Term,CTerm):-
 must_det_l((
   source_variables_l(NamedVars),!,
   copy_term(Term:NamedVars,CTerm:CNamedVars),
   term_variables(CTerm,Vars),
   get_var_names(Vars,CNamedVars,Names),
   b_implode_varnames0(Names),
  %  numbervars(CTerm,91,_,[attvar(skip),singletons(false)]),
   append(CNamedVars,NamedVars,NewCNamedVars),
   list_to_set(NewCNamedVars,NewCNamedVarsS),
   remove_grounds(NewCNamedVarsS,NewCNamedVarsSG),
   put_variable_names(NewCNamedVarsSG))),!.


%= 	 	 

%% get_var_names( :TermV, ?NamedVars, :TermS) is semidet.
%
% Get Variable Names.
%
get_var_names([],_,[]).
get_var_names([V|Vars],NamedVars,[S|SNames]):-
    get_1_var_name(V,NamedVars,S),
    get_var_names(Vars,NamedVars,SNames).


%= 	 	 

%% get_1_var_name( ?Var, :TermNamedVars, ?Name) is semidet.
%
% get  Secondary Helper Variable name.
%
get_1_var_name(_V,[],_S).

get_1_var_name(Var,NamedVars,Name):- compound(Var),arg(1,Var,NV),!,get_1_var_name(NV,NamedVars,Name).
get_1_var_name(Var,NamedVars,Var=NV):-atom(Var),NamedVars=[_|T],nb_setarg(2,NamedVars,[Var=NV|T]),!.
get_1_var_name(Var,[N=V|_NamedVars],Name=V):-
     (Var == V -> Name = N ; (Var==Name -> Name=Var ; fail )),!.
get_1_var_name(Var,[_|NamedVars],Name):- get_1_var_name(Var,NamedVars,Name).



%= 	 	 

%% wdmsgl( ?CNF) is semidet.
%
% Wdmsgl.
%
wdmsgl(CNF):- compound(CNF),CNF=..[NAME,NF],!,must(wdmsgl(NAME:-NF)).
wdmsgl(CNF):- pp_item('',CNF),!.
wdmsgl(NF):- must((get_functor(NF,NAME),!,must(wdmsgl_2(NAME,NF)))).



%= 	 	 

%% wdmsgl_2( ?NAME, ?NF) is semidet.
%
% wdmsgl  Extended Helper.
%
wdmsgl_2(NAME,NF):- functor(NF,_,_),wdmsgl_3(NAME,&,NF).


%= 	 	 

%% wdmsgl_3( ?NAME, ?F, ?NF) is semidet.
%
% Wdmsgl Helper Number 3..
%
wdmsgl_3(NAME,F,NF):-
   unnumbervars_with_names(vv(NAME,F,NF),vv(NAME2,F2,NF2)),
   wdmsgl_4(NAME2,F2,NF2).

%wdmsgl_4(NAME,F,NF):- is_list(NF),!,list_to_set(NF,NS),must_maplist(wdmsgl_4(NAME,F),NS).
%wdmsgl_4(NAME,F,NF):- compound(NF),NF=..[FF,A,B],FF=F,is_ftNonvar(A),is_ftNonvar(B),!,must_maplist(wdmsgl_4(NAME,F),[A,B]).
% wdmsgl_4(NAME,_,NF):- as_symlog(NF,NF2), with_all_dmsg(display_form(KB,NAME:-NF2)).

%= 	 	 

%% wdmsgl_4( ?NAME, ?VALUE2, ?NF) is semidet.
%
% Wdmsgl Helper Number 4..
%
wdmsgl_4(NAME,_,NF):- as_symlog(NF,NF2), with_all_dmsg(display_form(_KB,(NAME:-NF2))).


%% kif_to_boxlog( ?Wff, ?Out) is semidet.
%
% Knowledge Interchange Format Converted To Datalog.
%
%====== kif_to_boxlog(+Wff,-NormalClauses):-
:- public(kif_to_boxlog/2).
% kif_to_boxlog(Wff,Out):- loop_check(kif_to_boxlog(Wff,Out),Out=looped_kb(Wff)).
% kif_to_boxlog('=>'(WffIn,enables(Rule)),'$VAR'('MT2'),complete,Out1), % kif_to_boxlog('=>'(enabled(Rule),WffIn),'$VAR'('KB'),complete,Out).
kif_to_boxlog(Wff,Out):- why_to_id(rule,Wff,Why), kif_to_boxlog(Wff,Why,Out),!.
kif_to_boxlog(WffIn,Out):-  why_to_id(rule,WffIn,Why), kif_to_boxlog(all('$VAR'('KB'),'=>'(asserted_t('$VAR'('KB'),WffIn),WffIn)),'$VAR'('KB'),Why,Out),!.
kif_to_boxlog(WffIn,NormalClauses):- why_to_id(rule,WffIn,Why), kif_to_boxlog(WffIn,'$VAR'('KB'),Why,NormalClauses).


%= 	 	 

%% alt_kif_to_boxlog( ?Wff, ?KB, ?Why, ?Out) is semidet.
%
% Alt Knowledge Interchange Format Converted To Datalog.
%
alt_kif_to_boxlog( ~( Wff),KB,Why,Out):- !, kif_to_boxlog( ~( Wff),KB,Why,Out).
alt_kif_to_boxlog(Wff,KB,Why,Out):- loop_check(kif_to_boxlog(( ~(nesc( ~(Wff)))),KB,Why,Out),Out=looped_kb(Wff)).

:- public(kif_to_boxlog/3).

%= 	 	 

%% kif_to_boxlog( ?WffIn, ?Why, ?Out) is semidet.
%
% Knowledge Interchange Format Converted To Datalog.
%
kif_to_boxlog(WffIn,Why,Out):-  kif_to_boxlog(WffIn,'$VAR'('KB'),Why,Out),!.


:- export(kif_to_boxlog/4).


%= 	 	 

%% kif_to_boxlog( ?I, ?KB, ?Why, ?Flattened) is semidet.
%
% Knowledge Interchange Format Converted To Datalog.
%
kif_to_boxlog(I,KB,Why,Flattened):- % trace,
  convert_if_kif_string( I, PTerm),
  kif_to_boxlog(PTerm,KB,Why,Flattened), !.

% kif_to_boxlog(WffInIn,KB,Why,FlattenedO):-  as_dlog(WffInIn,WffIn),kif_to_boxlog_0(WffIn,KB,Why,FlattenedO),!.

% kif_to_boxlog(Wff,KB,Why,Out):- loop_check(kif_to_boxlog(Wff,KB,Why,Out),alt_kif_to_boxlog(Wff,KB,Why,Out)),!.

%kif_to_boxlog((Wff:- B),KB,Why,Flattened):- is_true(B),!, kif_to_boxlog(Wff,KB,Why,Flattened),!.
%kif_to_boxlog(Wff,KB,Why,Out):- adjust_kif(KB,Wff,M),Wff \=@= M ,!,kif_to_boxlog(M,KB,Why,Out).

kif_to_boxlog(HB,KB,Why,FlattenedO):- 
 unnumbervars((HB,KB,Why),(HB0,KB0,Why0)),
  must(kif_to_boxlog_attvars(HB0,KB0,Why0,FlattenedO)),!.

kif_to_boxlog_attvars(kif(HB),KB,Why,FlattenedO):-!,kif_to_boxlog_attvars(HB,KB,Why,FlattenedO).
kif_to_boxlog_attvars(clif(HB),KB,Why,FlattenedO):-!,kif_to_boxlog_attvars(HB,KB,Why,FlattenedO).
kif_to_boxlog_attvars(HB,KB,Why,FlattenedO):- compound(HB),HB=(HEAD:- BODY),!,
  must_det_l((
   check_is_kb(KB),
   conjuncts_to_list(HEAD,HEADL),
   conjuncts_to_list(BODY,BODYL),
   correct_boxlog([cl(HEADL,BODYL)],KB,Why,FlattenedO))),!.

kif_to_boxlog_attvars(WffIn0,KB0,Why0,FlattenedO):-
  must_det_l((nl,nl,nl,draw_line,draw_line,draw_line,draw_line)),!,
  must_det_l((
   must(unnumbervars_with_names(WffIn0:KB0:Why0,WffIn:KB:Why)),
   ensure_quantifiers(WffIn,Wff),
   wdmsgl(kif(Wff)),!,
   % KB = WffQ,
    check_is_kb(KB),
    must(dif(KB,Why)),
   %locally(t_l:dont_use_mudEquals,defunctionalize('=>',WffQ,Wff)),
   %(WffQ\==Wff-> dmsg(defunctionalize('=>',WffQ,Wff));wdmsgl(kif(Wff))),
   as_dlog(Wff,Wff666),!,
   % kb_nlit(KB,Neg),
   % original(Why)=>Wff666
   add_nesc(Wff666,Wff6667),
   add_preconds(Wff6667,Wff6668),
   adjust_kif(KB,Wff6668,Wff6669),
   wdmsgl(pkif(Wff6669)),
   nnf(KB,Wff6669,NNF),
   %wdmsgl(nnf(NNF)),
   pnf(KB,NNF,PNF),!,
   %wdmsgl(pnf(PNF)),
   %save_wid(Why,kif,Wff),
   %save_wid(Why,pkif,Wff6669),
   cf(Why,KB,Wff6669,PNF,FlattenedO))),!.



%= 	 	 

%% no_rewrites is semidet.
%
% Hook To [baseKB:no_rewrites/0] For Module Common_logic_snark.
% No Rewrites.
%
baseKB:no_rewrites.



%= 	 	 

%% check_is_kb( ?KB) is semidet.
%
% Check If Is A Knowledge Base.
%
check_is_kb(KB):-attvar(KB),!.
check_is_kb(KB):-ignore('$VAR'('KB')=KB).


%= 	 	 

%% add_preconds( ?X, ?X) is semidet.
%
% Add Preconds.
%
add_preconds(X,X):- baseKB:no_rewrites,!.
add_preconds(X,Z):-
 locally(leave_as_is_db('CollectionS666666666666666ubsetFn'(_,_)),
   locally(t_l:dont_use_mudEquals,defunctionalize('=>',X,Y))),add_preconds2(Y,Z).


%= 	 	 

%% add_preconds2( ?Wff6667, ?PreCondPOS) is semidet.
%
% Add Preconds Extended Helper.
%
add_preconds2(Wff6667,PreCondPOS):-
   must_det_l((get_lits(Wff6667,PreCond),list_to_set(PreCond,PreCondS),
     add_poss_to(PreCondS,Wff6667, PreCondPOS))).


%= 	 	 

%% add_poss_to( ?PreCond, ?Wff6667, ?Wff6667) is semidet.
%
% Add Possibility Converted To.
%
add_poss_to([],Wff6667, Wff6667).
add_poss_to([PreCond|S],Wff6667, PreCondPOS):-!,
 add_poss_to(PreCond,Wff6667, PreCondM),
 add_poss_to(S,PreCondM, PreCondPOS).

add_poss_to(PreCond,Wff6667, PreCond=>Wff6667):-prequent(PreCond).
add_poss_to(PreCond,Wff6667, Wff6667):-leave_as_is(PreCond).
add_poss_to( ~(_PreCond),Wff6667, Wff6667).
add_poss_to(PreCond,Wff6667, (poss(PreCond)=>Wff6667)).



%= 	 	 

%% add_nesc( ?X, ?X) is semidet.
%
% Add Necesity.
%
add_nesc(X,X):-!.

add_nesc(IN,OUT):-is_list(IN),must_maplist(add_nesc,IN,OUT),!.
add_nesc(Wff666,Wff666):-leave_as_is(Wff666),!.
add_nesc(P<=>Q,O):-!,add_nesc(((P=>Q) & (Q=>P)),O).
add_nesc(PQ,PQO):- PQ=..[F,V|Q],is_quantifier(F),add_nesc(Q,QQ),PQO=..[F,V|QQ],!.
add_nesc(IN,poss(IN)):-IN=..[F|_],should_be_poss(F),!.
add_nesc(Wff666,Wff666):-is_modal(Wff666,_),!.
add_nesc(P=>Q,((PP & P & QP) =>Q)):-  add_poss(P,PP),add_poss(Q,QP).
add_nesc(IN,OUT):-IN=..[F|INL],logical_functor_pttp(F),!,must_maplist(add_nesc,INL,OUTL),OUT=..[F|OUTL].
add_nesc(Wff666,Wff666):-!.

add_nesc(Q,(PQ & Q)):-  add_poss(Q,PQ),!.
add_nesc((P & Q),(PQ & (P & Q))):-  add_poss(P & Q,PQ),!.
add_nesc(Wff666,Wff666):-!.
add_nesc(IN,OUT):-IN=..[F|INL],logical_functor_pttp(F),!,must_maplist(add_nesc,INL,OUTL),OUT=..[F|OUTL].
add_nesc( ~(IN), ~(IN)).
add_nesc(IN,(IN)).
add_nesc(IN,nesc(IN)).


% add_poss(Wff666,Wff666):-!.
% add_poss(X,X):-!.

%= 	 	 

%% add_poss( ?PQ, ?PQ) is semidet.
%
% Add Possibility.
%
add_poss(PQ,PQ):- var(PQ),!.
add_poss(PQ,PQO):- PQ=..[F,V,Q],is_quantifier(F),add_poss(Q,QQ),PQO=..[F,V,QQ],!.
add_poss(Wff666,true):-leave_as_is(Wff666),!.
add_poss( ~(IN), ~(IN)).
add_poss(INL,OUTC):-is_list(INL),must_maplist(add_poss,INL,OUTL),F='&',OUT=..[F|OUTL],correct_arities(F,OUT,OUTC).
add_poss(IN,OUT):-IN=..[F|INL],logical_functor_pttp(F),!,must_maplist(add_poss,INL,OUTL),OUT=..[F|OUTL].
add_poss(IN,poss(IN)).


% shall X => can X
% shall ~ X => ~ can X
% ~ shall X => can ~ X

%= 	 	 

%% get_lits( ?PQ, ?QQ) is semidet.
%
% Get Literals.
%
get_lits(PQ,[]):- var(PQ),!.
get_lits(PQ,QQ):- PQ=..[F,_Vs,Q],is_quantifier(F),get_lits(Q,QQ).
get_lits(Wff666,[Wff666]):-leave_as_is(Wff666),!.
get_lits( ~(IN),NOUT):-get_lits(IN,OUT),must_maplist(simple_negate_literal(not),OUT,NOUT).
get_lits(knows(WHO,IN),NOUT):-get_lits(IN,OUT),must_maplist(simple_negate_literal(knows(WHO)),OUT,NOUT).
get_lits(beliefs(WHO,IN),NOUT):-get_lits(IN,OUT),must_maplist(simple_negate_literal(beliefs(WHO)),OUT,NOUT).
get_lits(IN,OUTLF):-IN=..[F|INL],logical_functor_pttp(F),!,must_maplist(get_lits,INL,OUTL),flatten(OUTL,OUTLF).
get_lits(IN,[IN]).


%= 	 	 

%% simple_negate_literal( ?F, ?FX, ?X) is semidet.
%
% Simple Negate Literal.
%
simple_negate_literal(F,FX,X):-FX=..FXL,F=..FL,append(FL,[X],FXL),!.
simple_negate_literal(F,X,FX):-append_term(F,X,FX).


%= 	 	 

%% is_quantifier( ?F) is semidet.
%
% If Is A Quantifier.
%
is_quantifier(F):- pttp_nnf_pre_clean_functor(F,(all),[]);pttp_nnf_pre_clean_functor(F,(ex),[]).


%= 	 	 

%% should_be_poss( ?VALUE1) is semidet.
%
% Should Be Possibility.
%
should_be_poss(argInst).

% :- was_dynamic(elInverse/2).


%= 	 	 

%% clauses_to_boxlog( ?KB, ?Why, ?In, ?Prolog) is semidet.
%
% Clauses Converted To Datalog.
%
clauses_to_boxlog(KB,Why,In,Prolog):- clauses_to_boxlog_0(KB,Why,In,Prolog).



%= 	 	 

%% clauses_to_boxlog_0( ?KB, ?Why, ?In, ?Prolog) is semidet.
%
% clauses Converted To Datalog  Primary Helper.
%
clauses_to_boxlog_0(KB,Why,In,Prolog):-loop_check(clauses_to_boxlog_1(KB,Why,In,Prolog),show_call(why,(clauses_to_boxlog_5(KB,Why,In,Prolog)))),!.
clauses_to_boxlog_0(KB,Why,In,Prolog):-correct_cls(KB,In,Mid),!,clauses_to_boxlog_1(KB,Why,Mid,PrologM),!,Prolog=PrologM.


%= 	 	 

%% clauses_to_boxlog_1( ?KB, ?Why, ?In, ?Prolog) is semidet.
%
% clauses Converted To Datalog  Secondary Helper.
%
clauses_to_boxlog_1(KB, Why,In,Prolog):- clauses_to_boxlog_2(KB,Why,In,PrologM),!,must(Prolog=PrologM).


%= 	 	 

%% clauses_to_boxlog_2( ?KB, ?Why, :TermIn, ?Prolog) is semidet.
%
% clauses Converted To Datalog  Extended Helper.
%
clauses_to_boxlog_2(KB, Why,In,Prolog):- is_list(In),!,must_maplist(clauses_to_boxlog_1(KB,Why),In,Prolog).
clauses_to_boxlog_2(KB, Why,cl([],BodyIn),  Prolog):- !, (is_lit_atom(BodyIn) -> clauses_to_boxlog_1(KB,Why,cl([inconsistentKB(KB)],BodyIn),Prolog);  (dtrace,kif_to_boxlog( ~(BodyIn),KB,Why,Prolog))).
clauses_to_boxlog_2(KB, Why,cl([HeadIn],[]),Prolog):- !, (is_lit_atom(HeadIn) -> Prolog=HeadIn ; (kif_to_boxlog(HeadIn,KB,Why,Prolog))).
clauses_to_boxlog_2(KB,_Why,cl([HeadIn],BodyIn),(HeadIn:- BodyOut)):-!, must_maplist(logical_pos(KB),BodyIn,Body), list_to_conjuncts(Body,BodyOut),!.

clauses_to_boxlog_2(KB, Why,cl([H,Head|List],BodyIn),Prolog):- 
  findall(Answer,((member(E,[H,Head|List]),delete_eq([H,Head|List],E,RestHead),
     must_maplist(logical_neg(KB),RestHead,RestHeadS),append(RestHeadS,BodyIn,Body),
       clauses_to_boxlog_1(KB,Why,cl([E],Body),Answer))),Prolog),!.

clauses_to_boxlog_2(_KB,_Why,(H:-B),(H:-B)):- !.


%= 	 	 

%% clauses_to_boxlog_5( ?KB, ?Why, ?In, ?Prolog) is semidet.
%
% Clauses Converted To Datalog Helper Number 5..
%
clauses_to_boxlog_5(KB, Why,In,Prolog):- is_list(In),!,must_maplist(clauses_to_boxlog_5(KB,Why),In,Prolog).
clauses_to_boxlog_5(_KB,_Why,(H:-B),(H:-B)):-!.
clauses_to_boxlog_5(_KB,_Why,cl([HeadIn],[]),HeadIn):-!.
clauses_to_boxlog_5(_KB,_Why,In,Prolog):-dtrace,In=Prolog.


%= 	 	 

%% mpred_t_tell_kif( ?OP2, ?RULE) is semidet.
%
% Managed Predicate True Structure Canonicalize And Store Knowledge Interchange Format.
%
mpred_t_tell_kif(OP2,RULE):-
 locally(t_l:current_pttp_db_oper(mud_call_store_op(OP2)),
   (show_call(why,call((must(kif_add(RULE))))))).


%= 	 	 

%% tsn is semidet.
%
% Tsn.
%
tsn:- with_all_dmsg(forall(clause(kif,C),must(C))).

% kif:- make.
:- dynamic(kif_test_string/1).

%= 	 	 

%% tkif is semidet.
%
% Tkif.
%
tkif:- kif_test_string(TODO),kif_io(string(TODO),current_output).


%= 	 	 

%% regression_test is semidet.
%
% Hook To [baseKB:regression_test/0] For Module Common_logic_snark.
% Regression Test.
%
baseKB:regression_test:- tsn.

:- thread_local(t_l:kif_action_mode/1).
:- asserta_if_new(t_l:kif_action_mode(tell)).

:- thread_local(t_l:kif_reader_mode/1).
:- asserta_if_new(t_l:kif_reader_mode(lisp)).


%= 	 	 

%% kif_read( ?InS, ?Wff, ?Vs) is semidet.
%
% Knowledge Interchange Format Read.
%
kif_read(InS,Wff,Vs):- must(l_open_input(InS,In)),
  must(((t_l:kif_reader_mode(lisp) ,without_must( catch(input_to_forms(In,Wff,Vs),E,(dmsg(E:kif_read_input_to_forms(In,Wff,Vs)),fail)))) *-> true ;
      catch(read_term(In,Wff,[module(user),double_quotes(string),variable_names(Vs)]),E,(dmsg(E:kif_read_term_to_forms(In,Wff,Vs)),fail)))).

%= ===== to test program =====-
% :- ensure_loaded(logicmoo(snark/common_logic_sexpr)).

:- public(kif/0).

%= 	 	 

%% kif is semidet.
%
% Knowledge Interchange Format.
%
kif:- current_input(In),current_output(Out),!,kif_io(In,Out).

%open_input(InS,InS):- is_stream(InS),!.
%open_input(string(InS),In):- text_to_string(InS,Str),string_codes(Str,Codes),open_chars_stream(Codes,In),!.


:- public(kif_io/2).

%= 	 	 

%% kif_io( ?InS, ?Out) is semidet.
%
% Knowledge Interchange Format Input/output.
%
kif_io(InS,Out):-
  l_open_input(InS,In),
   repeat,
      on_x_debug((once((t_l:kif_action_mode(Mode),write(Out,Mode),write(Out,'> '))),
        kif_read(In,Wff,Vs),
         put_variable_names( Vs),
           portray_clause(Out,Wff,[variable_names(Vs),quoted(true)]),
           once(kif_process(Wff)),
           Wff == end_of_file)),!.

:- public(why_to_id/3).

%= 	 	 

%% why_to_id( ?Term, ?Wff, ?IDWhy) is semidet.
%
% Generation Of Proof Converted To Id.
%
why_to_id(Term,Wff,IDWhy):-  \+ atom(Term),term_to_atom(Term,Atom),!,why_to_id(Atom,Wff,IDWhy).
why_to_id(Atom,Wff,IDWhy):- call_u(wid(IDWhy,Atom,Wff)),!.
why_to_id(Atom,Wff,IDWhy):- must(atomic(Atom)),gensym(Atom,IDWhyI),kb_incr(IDWhyI,IDWhy),assertz_if_new(wid(IDWhy,Atom,Wff)).

:- public(kif_process/1).

%= 	 	 

%% kif_process( :GoalAssert) is semidet.
%
% Knowledge Interchange Format Process.
%
kif_process(end_of_file):- !.
kif_process(prolog):- prolog,!.
kif_process(Assert):- atom(Assert),retractall(t_l:kif_action_mode(_)),asserta(t_l:kif_action_mode(Assert)),fmtl(t_l:kif_action_mode(Assert)),!.
kif_process(Wff):- t_l:kif_action_mode(Mode),kif_process(Mode,Wff),!.


%= 	 	 

%% kif_process( ?Other, :GoalWff) is semidet.
%
% Knowledge Interchange Format Process.
%
kif_process(_,':-'(Wff)):- !, kif_process(call,Wff).
kif_process(_,'?-'(Wff)):- !, kif_ask(Wff).
kif_process(_,'ask'(Wff)):- !, kif_ask(Wff).
kif_process(_,'tell'(Wff)):- !, kif_add(Wff).
kif_process(call,Call):- !,call(Call).
kif_process(tell,Wff):- !, kif_add(Wff).
kif_process(ask,Wff):- !, kif_ask(Wff).
kif_process(Other,Wff):- !, wdmsg(error(missing_kif_process(Other,Wff))),!,fail.

:- public(kif_ask_sent/1).

%= 	 	 

%% kif_ask_sent( ?VALUE1) is semidet.
%
% Knowledge Interchange Format Complete Inference Sentence.
%
kif_ask_sent(Wff):-
   why_to_id(ask,Wff,Why),
   term_variables(Wff,Vars),
   gensym(z_q,ZQ),
   Query=..[ZQ,666|Vars],
   why_to_id(rule,'=>'(Wff,Query),Why),
   kif_to_boxlog('=>'(Wff,Query),Why,QueryAsserts),!,
   kif_add_boxes1(Why,QueryAsserts),!,
   call_cleanup(
     kif_ask(Query),
     find_and_call(retractall_wid(Why))).


:- public(kif_ask/1).

%= 	 	 

%% kif_ask( :TermP) is semidet.
%
% Knowledge Interchange Format Complete Inference.
%
kif_ask(P <=> Q):- kif_ask_sent(P <=> Q).
kif_ask(P => Q):- kif_ask_sent(P => Q).
kif_ask((P v Q)):- kif_ask_sent(((P v Q))).
kif_ask((P & Q)):- kif_ask_sent((P & Q)).
kif_ask(Goal0):-  logical_pos(_KB,Goal0,Goal),
    no_repeats(baseKB:(
	if_defined(add_args(Goal0,Goal,_,_,[],_,_,[],[],DepthIn,DepthOut,[PrfEnd|PrfEnd],_ProofOut1,Goal1,_)),!,
        call(call,search(Goal1,60,0,1,3,DepthIn,DepthOut)))).

:- public(kif_ask/2).

%= 	 	 

%% kif_ask( ?VALUE1, ?VALUE2) is semidet.
%
% Knowledge Interchange Format Complete Inference.
%
kif_ask(Goal0,ProofOut):- logical_pos(_KB,Goal0,Goal),
    no_repeats(baseKB:(
	if_defined(add_args(Goal0,Goal,_,_,[],_,_,[],[],DepthIn,DepthOut,[PrfEnd|PrfEnd],ProofOut1,Goal1,_)),!,
        call(call,search(Goal1,60,0,1,3,DepthIn,DepthOut)),
        call(call,contract_output_proof(ProofOut1,ProofOut)))).


%= 	 	 

%% kif_add( ?InS) is semidet.
%
% Knowledge Interchange Format Add.
%
kif_add(InS):- atom(InS),must_det_l((kif_read(string(InS),Wff,Vs),b_implode_varnames0(Vs),local_sterm_to_pterm(Wff,Wff0),kif_add(Wff0))),!.
% kif_add(WffIn):- must_det_l((unnumbervars_with_names(WffIn,Wff),why_to_id(tell,Wff,Why),kif_add(Why,Wff))),!.
kif_add(WffIn):- must_det_l((unnumbervars_with_names(WffIn,Wff),ain(clif(Wff)))),!.



%= 	 	 

%% local_sterm_to_pterm( ?Wff, ?WffO) is semidet.
%
% Local Sterm Converted To Pterm.
%
local_sterm_to_pterm(Wff,WffO):- sexpr_sterm_to_pterm(Wff,WffO),!.



:- op(1000,fy,(kif_add)).

/*
:- public((kif_add)/2).

kif_add(_,[]).
kif_add(Why,[H|T]):- !,must_det_l((kif_add(Why,H),kb_incr(Why,Why2),kif_add(Why2,T))).
kif_add(Why,Wff):-
   must_det_l((kif_to_boxlog(Wff,Why,Asserts),
      kif_add_boxes(assert_wfs_def,Why,Wff,Asserts))),!.


:- thread_local(t_l:assert_wfs/2).
assert_wfs_def(HBINFO,HB):-if_defined(t_l:assert_wfs(HBINFO,HB)),!.
assert_wfs_def(Why,H):-assert_wfs_fallback(Why,H).

assert_wfs_fallback(Why, HB):- subst(HB,(~),(-),HB2),subst(HB2,(not_proven_t),(not_true_t),HB1),subst(HB1,(poss),(possible_t),HBO),assert_wfs_fallback0(Why, HBO).
assert_wfs_fallback0(Why,(H:-B)):- adjust_kif('$VAR'(KB),B,HBK),demodal('$VAR'(KB),HBK,HBKD),
   wdmsg((H:-w_infer_by(Why),HBKD)),pttp_assert_wid(Why,pttp_in,(H:-B)),!.
assert_wfs_fallback0(Why, HB):- adjust_kif('$VAR'(KB),HB,HBK),demodal('$VAR'(KB),HBK,HBKD),
   wdmsg((HBKD:-w_infer_by(Why))),pttp_assert_wid(Why,pttp_in,(HB)),!.

*/

:- public(kb_incr/2).

%= 	 	 

%% kb_incr( ?WffNum1, ?WffNum2) is semidet.
%
% Knowledge Base Incr.
%
kb_incr(WffNum1 ,WffNum2):-is_ftVar(WffNum1),trace_or_throw(kb_incr(WffNum1 ,WffNum2)).
kb_incr(WffNum1 ,WffNum2):-number(WffNum1),WffNum2 is WffNum1 + 1,!.
%kb_incr(WffNum1 ,WffNum2):-atom(WffNum1),WffNum2=..[WffNum1,0],!.
kb_incr(WffNum1 ,WffNum2):-atomic(WffNum1),WffNum2 = WffNum1:0,!.
kb_incr(WffNum1 ,WffNum2):-WffNum1=..[F,P,A|REST],kb_incr(A ,AA),!,WffNum2=..[F,P,AA|REST].
kb_incr(WffNum1 ,WffNum2):-trace_or_throw(kb_incr(WffNum1 ,WffNum2)).
/*
kif_add_boxes(How,Why,Wff0,Asserts0):-
 must_det_l((
  show_failure(why,kif_unnumbervars(Asserts0+Wff0,Asserts+Wff)),
  %fully_expand(Get1,Get),
  get_constraints(Wff,Isas),
  kif_add_adding_constraints(Why,Isas,Asserts))),
   findall(HB-WhyHB,retract(t_l:in_code_Buffer(HB,WhyHB,_)),List),
   list_to_set(List,Set),
   forall(member(HB-WhyHB,Set),
      call(How,WhyHB,HB)).
*/


%= 	 	 

%% kif_add_adding_constraints( ?Why, ?Isas, :TermGet1Get2) is semidet.
%
% Knowledge Interchange Format Add Adding Constraints.
%
kif_add_adding_constraints(Why,Isas,Get1Get2):- var(Get1Get2),!,trace_or_throw(var_kif_add_isa_boxes(Why,Isas,Get1Get2)).
kif_add_adding_constraints(Why,Isas,(Get1,Get2)):- !,kif_add_adding_constraints(Why,Isas,Get1),kb_incr(Why,Why2),kif_add_adding_constraints(Why2,Isas,Get2).
kif_add_adding_constraints(Why,Isas,[Get1|Get2]):- !,kif_add_adding_constraints(Why,Isas,Get1),kb_incr(Why,Why2),kif_add_adding_constraints(Why2,Isas,Get2).
kif_add_adding_constraints(_,_,[]).
kif_add_adding_constraints(_,_,z_unused(_)):-!.
kif_add_adding_constraints(Why,Isas,((H:- B))):- conjoin(Isas,B,BB), kif_add_boxes1(Why,(H:- BB)).
kif_add_adding_constraints(Why,Isas,((H))):- kif_add_boxes1(Why,(H:- Isas)).


%= 	 	 

%% kif_add_boxes1( ?Why, ?List) is semidet.
%
% Knowledge Interchange Format Add Boxes Secondary Helper.
%
kif_add_boxes1(_,[]).
kif_add_boxes1(Why,List):- is_list(List),!,list_to_set(List,[H|T]),must_det_l((kif_add_boxes1(Why,H),kb_incr(Why,Why2),kif_add_boxes1(Why2,T))).
kif_add_boxes1(_,z_unused(_)):-!.
kif_add_boxes1(Why,AssertI):- must_det_l((simplify_bodies(AssertI,AssertO),kif_add_boxes3(save_wfs,Why,AssertO))).

:- thread_local(t_l:in_code_Buffer/3).



%= 	 	 

%% kif_add_boxes3( :PRED2How, ?Why, ?Assert) is semidet.
%
% Knowledge Interchange Format Add Boxes3.
%
kif_add_boxes3(How,Why,Assert):-
  must_det_l((
  boxlog_to_pfc(Assert,Prolog1),
  defunctionalize(Prolog1,Prolog2),
  kif_unnumbervars(Prolog2,PTTP),
  call(How,Why,PTTP))).


%= 	 	 

%% kif_unnumbervars( ?X, ?YY) is semidet.
%
% Knowledge Interchange Format Unnumbervars.
%
kif_unnumbervars(X,YY):-unnumbervars(X,YY),!.
kif_unnumbervars(X,YY):-
 must_det_l((
   with_output_to(string(A),write_term(X,[character_escapes(true),ignore_ops(true),quoted(true)])),
   atom_to_term(A,Y,NamedVars),
   YY=Y,
   add_newvars(NamedVars))).



%= 	 	 

%% simplify_bodies( ?B, ?BC) is semidet.
%
% Simplify Bodies.
%
simplify_bodies((H:- B),(H:- BC)):- must_det_l((conjuncts_to_list(B,RB),simplify_list(_KB,RB,BB),list_to_conjuncts(BB,BC))).
simplify_bodies((B),(BC)):- must_det_l((conjuncts_to_list(B,RB),simplify_list(_KB,RB,BB),list_to_conjuncts(BB,BC))).



%= 	 	 

%% simplify_list( ?KB, ?RB, ?BBS) is semidet.
%
% Simplify List.
%
simplify_list(KB,RB,BBS):- list_to_set(RB,BB),must_maplist(removeQ(KB),BB,BBO),list_to_set(BBO,BBS).


%= 	 	 

%% save_wfs( ?Why, ?PrologI) is semidet.
%
% Save Well-founded Semantics Version.
%
save_wfs(Why,PrologI):- must_det_l((baseKB:as_prolog_hook(PrologI,Prolog),
   locally(t_l:current_local_why(Why,Prolog),
   ain_h(save_in_code_buffer,Why,Prolog)))).


%= 	 	 

%% nots_to( ?H, ?To, ?HH) is semidet.
%
% Negations Converted To.
%
nots_to(H,To,HH):-subst_except(H,not,To,HH),subst_except(H,-,To,HH),subst_except(H,~,To,HH),subst_except(H, \+ ,To,HH),!.

%= 	 	 

%% neg_h_if_neg( ?H, ?HH) is semidet.
%
% Negated Head If Negated.
%
neg_h_if_neg(H,HH):-nots_to(H,'~',HH).

%= 	 	 

%% neg_b_if_neg( ?HBINFO, ?B, ?BBB) is semidet.
%
% Negated Backtackable If Negated.
%
neg_b_if_neg(HBINFO,B,BBB):-nots_to(B,'~',BB),sort_body(HBINFO,BB,BBB),!.



%= 	 	 

%% sort_body( ?HBINFO, ?BB, ?BBB) is semidet.
%
% Sort Body.
%
sort_body(HBINFO,BB,BBB):-sort_body_0(HBINFO,BB,BBB),(BBB=@=BB->true; (expand_to_hb(HBINFO,H,_),nop(dmsg([(H:-BB),'=>',(H:-BBB)])))).


%= 	 	 

%% sort_body_0( ?VALUE1, ?SORTED, ?SORTED) is semidet.
%
% sort body  Primary Helper.
%
sort_body_0(_,SORTED,SORTED):-leave_as_is(SORTED).
sort_body_0(HBINFO,(A,B),SORTED):-!,conjuncts_to_list((A,B),List),
   must_maplist(sort_body_0(HBINFO),List,ListIn),
   predsort(litcost_compare(HBINFO),ListIn,SortedL),
   list_to_conjuncts(SortedL,SORTED).
sort_body_0(HBINFO,(A;B),SORTED):-!,disjuncts_to_list((A;B),List),
   must_maplist(sort_body_0(HBINFO),List,ListIn),
   predsort(litcost_compare(HBINFO),ListIn,SortedL),
   list_to_conjuncts((;),SortedL,SORTED).
sort_body_0(_,SORTED,SORTED).


%= 	 	 

%% litcost_compare( ?HBINFO, ?Comp, ?A, ?B) is semidet.
%
% Litcost Compare.
%
litcost_compare(_,=,A,B):- A=@=B,!.
litcost_compare(HBINFO,Comp,A,B):-lit_cost(HBINFO,A,AC),lit_cost(HBINFO,B,BC),compare(CompC,AC,BC),
  (CompC\== (=) -> CompC = Comp ; Comp = (<)).


%= 	 	 

%% lit_cost( ?HBINFO, ?A, :GoalAC) is semidet.
%
% Literal Cost.
%
lit_cost(_,A,9):-isSlot(A).
lit_cost(_,A,0):- \+ compound(A),!.
lit_cost(HBINFO,A,AC):- A=..[F,ARG], is_log_op(F),!,lit_cost(HBINFO,ARG,AC0),!,
 % this removes the headvar bonus
  term_slots(A,Slots),length(Slots,SC),
  AC is AC0+SC.
lit_cost(HBINFO,A,AC):- expand_to_hb(HBINFO,H,B),
  var_count_num(A,H,SH,UH),
  var_count_num(A,B,VC,Singles),
  AC is Singles*3 + VC + UH - SH.


%= 	 	 

%% simp_code( ?A, ?A) is semidet.
%
% Simp Code.
%
simp_code(HB,(H:-BS)):-expand_to_hb(HB,H,B),conjuncts_to_list(B,BL),sort(BL,BS),!.
simp_code(A,A).



%= 	 	 

%% var_count_num( ?Term, ?SharedTest, ?SharedCount, ?UnsharedCount) is semidet.
%
% Variable Count Num.
%
var_count_num(Term,SharedTest,SharedCount,UnsharedCount):- term_slots(Term,Slots),term_slots(SharedTest,TestSlots),
  subtract(Slots,TestSlots,UnsharedSlots),
  subtract(Slots,UnsharedSlots,SharedSlots),
  length(SharedSlots,SharedCount),
  length(UnsharedSlots,UnsharedCount).


%= 	 	 

%% ain_h( :PRED2How, ?Why, ?H) is semidet.
%
% Assert If New Head.
%
ain_h(How,Why,(H:- B)):- neg_h_if_neg(H,HH), neg_b_if_neg((HH:- B),B,BB),!,call(How,Why,(HH:-BB)).
ain_h(How,Why,(H)):- neg_h_if_neg(H,HH), call(How,Why,(HH)).


%= 	 	 

%% save_in_code_buffer( ?VALUE1, ?HB) is semidet.
%
% Save In Code Buffer.
%
save_in_code_buffer(_ ,HB):- simp_code(HB,SIMP),t_l:in_code_Buffer(HB,_,SIMP),!.
save_in_code_buffer(Why,HB):- simp_code(HB,SIMP),assert(t_l:in_code_Buffer(HB,Why,SIMP)).


%= 	 	 

%% use_was_isa_h( ?I, :TermT, ?ISA) is semidet.
%
% use was  (isa/2) Head.
%
use_was_isa_h(_,ftTerm,true):- !.
use_was_isa_h(_,argi(mudEquals,_),true):- !.
use_was_isa_h(_,argi(skolem,_),true):- !.
use_was_isa_h(I,T,ISA):- to_isa_form0(I,T,ISA),!.

%% to_isa_form( ?I, ?C, ?OUT) is nondet.
%
% Converted To  (isa/2) out.
%
to_isa_form0(I,C,isa(I,C)).
to_isa_form0(I,C,t(C,I)).
to_isa_form0(I,C,OUT):- atom(C)->OUT=..[C,I].

%= 	 	 

%% generate_ante( :TermARG1, :TermARG2, ?InOut, ?InOut) is semidet.
%
% Generate Ante.
%
generate_ante([],[],InOut,InOut).
generate_ante([I|VarsA],[T|VarsB],In,Isas):- use_was_isa_h(I,T,ISA), conjoin(In,ISA,Mid),generate_ante(VarsA,VarsB,Mid,Isas).


%= 	 	 

%% get_constraints( ?ListA, ?Isas) is semidet.
%
% Get Constraints.
%
get_constraints(T,true):- T==true.
get_constraints(_,true):- !.
get_constraints(ListA,Isas):-
     must_det_l((copy_term(ListA,ListB),
      term_variables(ListA,VarsA),
      term_variables(ListB,VarsB),
      attempt_attribute_args(isAnd,ftAskable,ListB),
      attribs_to_atoms(VarsB,VarsB),
      generate_ante(VarsA,VarsB,true,Isas))).



:- source_location(S,_),forall((source_file(H,S),once((clause(H,B),B\=true))),(functor(H,F,A),module_transparent(F/A))).
:- fixup_exports.

