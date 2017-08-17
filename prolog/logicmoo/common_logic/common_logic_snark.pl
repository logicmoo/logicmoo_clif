% File: /opt/PrologMUD/pack/logicmoo_base/prolog/common_logic/snark/common_logic_snark.pl
% :- if(( ( \+ ((current_prolog_flag(logicmoo_include,Call),Call))) )).
:- module(common_logic_snark,
          [ add_nesc/2,
            weaken_to_poss/2,
            add_poss_to/3,
            add_preconds/2,
            add_preconds2/2,
            adjust_kif/3,
            adjust_kif0/3,
            adjust_kif4/4,
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
            kif_ask/1,
            kif_ask/2,
            kif_ask_sent/1,
            kif_hook/1,
            is_gaf/1,
            is_kif_clause/1,
            (kif_add)/1,
            kif_add_adding_constraints/3,
            kif_add_boxes1/2,
            kif_add_boxes3/3,
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
            
            neg_b_if_neg/3,
            neg_h_if_neg/2,
            not_mudEquals/2,
            nots_to/3,
            unnumbervars_with_names/2,
            
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
            to_dlog_ops/1,
            to_nonvars/3,
            to_prolog_ops/1,
            to_symlog_ops/1,
            type_of_var/3,
            use_was_isa_h/3,
            var_count_num/4,
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
            is_not_entailed/1]).

/** <module> common_logic_snark
% Provides a specific compilation API for KIF axioms
%

% Logicmoo Project PrologMUD: A MUD server written in Prolog
% Maintainer: Douglas Miles
% Dec 13, 2035
%
*/

:- reexport(library('logicmoo/common_logic/common_logic_boxlog.pl')).
:- user:reexport(library('logicmoo_pttp')).




:- include(library('pfc2.0/mpred_header.pi')).
%:- endif.

:-
            op(1150,fx,(was_dynamic)),
            op(1150,fx,(was_multifile)),
            op(1150,fy,(was_module_transparent)).

:- load_library_system(library(logicmoo_typesystem)).

:- virtualize_source_file.

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


:- module_transparent(( are_clauses_entailed/1,
            is_prolog_entailed/1,
            delistify_last_arg/3)).

:- meta_predicate
   % common_logic_snark
   convertAndCall(*,0),
   kif_add_boxes3(2,?,*),
   % common_logic_snark
   ain_h(2,?,*),
   map_each_clause(1,+),
   map_each_clause(2,+,-),

   '__aux_maplist/3_map_each_clause+1'(*,*,2),
   % '__aux_maplist/2_map_each_clause+1'(*,1),

   % common_logic_snark
   to_nonvars(2,?,?).

%:- meta_predicate '__aux_maplist/2_map_each_clause+1'(*,1).
%:- meta_predicate '__aux_maplist/3_map_each_clause+1'(*,*,2).

%% delistify_last_arg( ?Arg, :PredMiddleArgs, ?Last) is det.
%
% Delistify Last Argument.
%

delistify_last_arg(Arg,Pred,Last):- no_repeats(Last,must(delistify_last_arg0(Arg,Pred,Last))).

delistify_last_arg0(Arg,Pred,Last):- is_list(Arg),!,member(E,Arg),must(delistify_last_arg0(E,Pred,Last)).
delistify_last_arg0(Arg,M:Pred,Last):- Pred=..[F|ARGS],append([Arg|ARGS],[NEW],NARGS),NEWCALL=..[F|NARGS],maybe_notrace(M:NEWCALL),!,member_ele(NEW,Last).
delistify_last_arg0(Arg,Pred,Last):- Pred=..[F|ARGS],append([Arg|ARGS],[NEW],NARGS),NEWCALL=..[F|NARGS],maybe_notrace(NEWCALL),!,member_ele(NEW,Last).


/*
:- was_dynamic
        baseKB:as_prolog_hook/2,
        elInverse/2,
        
        not_mudEquals/2.
        
*/

% :- dynamic(baseKB:(if/2,iif/2)).

:- export(kw_to_vars/2).
kw_to_vars(KW,VARS):-subsT_each(KW,[':ARG1'=_ARG1,':ARG2'=_ARG2,':ARG3'=_ARG3,':ARG4'=_ARG4,':ARG5'=_ARG5,':ARG6'=_ARG6],VARS).




%% is_gaf( ?Gaf) is det.
%
% If Is A Gaf.
%
is_gaf(Gaf):-when(nonvar(Gaf), \+ (is_kif_clause(Gaf))).

%= %= :- was_export(is_kif_clause/1).



%% is_kif_clause( ?Var) is det.
%
% If Is A Knowledge Interchange Format Rule.
%
is_kif_clause(Var):- is_ftVar(Var),!,fail.
is_kif_clause(R):- kif_hook(R),!.
is_kif_clause(R):- is_clif(R),!.




%% kif_hook(+TermC) is det.
%
% Knowledge Interchange Format Hook.
%
kif_hook(C):- not_ftCompound(C),!,fail.
kif_hook(_H :- _):-  !,fail.
kif_hook(_H <- _):-  !,fail.
kif_hook(_H --> _):- !,fail.
kif_hook(_ ==> _):-  !,fail.
kif_hook(_ <==> _):- !,fail.
% uncommenting these next 3 lines may break sanity_birdt test

 kif_hook(  ~(H)):- !,nonvar(H),kif_hook(H).
 kif_hook(  \+ H):- !,nonvar(H),kif_hook(H).
 kif_hook(not(H)):- !,nonvar(H),kif_hook(H).

kif_hook( naf(H)):- !,nonvar(H),kif_hook(H).
kif_hook(In):- kif_hook_skel(In).
kif_hook(C):- callable(C),functor(C,F,A),kif_hook(C,F,A).

kif_hook(_,F,_):- atom_concat('sk',_,F),atom_concat(_,'Fn',F),!.
kif_hook(C,_,_):- leave_as_is(C),!,fail.
kif_hook(C,F,_):- is_sentence_functor(F),!,arg(_,C,E),kif_hook(E).


%% kif_hook_skel(+TermC) is det.
%
% Knowledge Interchange Format Hook Skelecton.
%

kif_hook_skel(forAll(_,_)).
kif_hook_skel(_=>_).
kif_hook_skel(_<=_).
kif_hook_skel(_<=>_).
kif_hook_skel((_ & _)).
kif_hook_skel((_ /\ _)).
kif_hook_skel((_ \/ _)).
kif_hook_skel((_ v _)).
kif_hook_skel(nesc(_)).
kif_hook_skel(poss(_)).
kif_hook_skel(cir(_)).
kif_hook_skel(all(_,_)).
kif_hook_skel(exactly(_,_,_)).
kif_hook_skel(atmost(_,_,_)).
kif_hook_skel(atleast(_,_,_)).
kif_hook_skel(exists(_,_)).
kif_hook_skel(if(_,_)).
kif_hook_skel(iff(_,_)).
kif_hook_skel(equiv(_,_)).
kif_hook_skel(implies(_,_)).
kif_hook_skel(CLIF):- is_clif(CLIF).
kif_hook_skel( ~(H)):- loop_check(kif_hook(H)).
kif_hook_skel( not(H)):- loop_check(kif_hook(H)).
kif_hook_skel( Compound):- arg(_,v(poss,nesc,until,always,release,cir),F),between(2,3,A),functor( Compound,F,A).
kif_hook_skel( Compound):- compound( Compound),!,functor(Compound,F,_),arg(_,v(and,or,xor),F).
kif_hook_skel( Compound):- var(Compound),!,arg(_,v(and,or,xor),F),between(1,12,A),functor( Compound,F,A).





%% are_clauses_entailed( :TermE) is det.
%
% Are Clauses Entailed.
%
% 
are_clauses_entailed(E):-var(E),!,fail.
are_clauses_entailed(B):- unnumbervars(B,A),map_each_clause(is_prolog_entailed,A).


is_pfc_entailed(B):- unnumbervars(B,A),map_each_clause(mpred_supported(local),A).


%% is_prolog_entailed( ?Prolog) is det.
%
% True if the "Prolog" clause is asserted
%

is_prolog_entailed(UCL):-clause_asserted_u(UCL),!.
is_prolog_entailed(UCL):-show_success(clause_asserted(UCL)),!.
is_prolog_entailed(UCL):-show_success(clause_asserted_i(UCL)),!.
is_prolog_entailed(UCL):-boxlog_to_pfc(UCL,PFC),show_failure(is_pfc_entailed(PFC)),!.
is_prolog_entailed(PFC):-show_failure(is_pfc_entailed(PFC)),!.
is_prolog_entailed(UCL):-clause(UCL,B),split_attrs(B,A,BB),must(A),BB.
is_prolog_entailed(UCL):-clause(UCL,B,Ref),(B\==true->must(B);(dtrace,clause(HH,BB,Ref),dmsg(BB:-(UCL,HH)))),!.
is_prolog_entailed(UCL):-dmsg(warn(not_is_prolog_entailed(UCL))),!,fail.



%% member_ele( ?E, ?E) is det.
%
% Member Ele.
%
member_ele(E,E):- is_ftVar(E),!.
member_ele([],_):-!,fail.
member_ele(E,E):- ( \+ (compound(E))),!.
member_ele([L|List],E):- must(is_list([L|List])),!,member(EE,[L|List]),member_ele(EE,E).
member_ele((H,T),E):- nonvar(H),nonvar(T),!, (member_ele(H,E);member_ele(T,E)).
member_ele(E,E).



% sanity that mpreds (manage prolog prodicate) are abily to transform

% cwc "code-wise chaining" is always true in Prolog but will throw programming error if evalled in LogicMOO Prover.
% Use this to mark code and not axiomatic prolog


map_each_clause(P,CLIF,Prolog):- is_list(CLIF),!,maplist(map_each_clause(P),CLIF,Prolog).
map_each_clause(P,(H,CLIF),(T,Prolog)):-  sanity(nonvar(H)),!,map_each_clause(P,H,T),map_each_clause(P,CLIF,Prolog).
map_each_clause(P,A,B):- call(P,A,B).

map_each_clause(P,CLIF):-  is_list(CLIF),!,maplist(map_each_clause(P),CLIF).
map_each_clause(P,(H,CLIF)):-  sanity(nonvar(H)),!,map_each_clause(P,H),map_each_clause(P,CLIF).
map_each_clause(P,A):- call(P,A).

%% any_to_pfc( :TermCLIF, ?Prolog) is det.
%
% Converted To Prolog.
%
any_to_pfc(B,A):-  sumo_to_pdkb(B,B0),must(map_each_clause(any_to_pfc0,B0,A)).

any_to_pfc0(B,A):-  is_kif_clause(B),!,maybe_notrace(kif_to_pfc0(B,A)).
any_to_pfc0(B,A):-  is_pfc_clause(B),!,maybe_notrace(fully_expand(clause(any_to_pfc,any_to_pfc),B,A)).
any_to_pfc0(B,A):-  is_prolog_clause(B),!,maybe_notrace(boxlog_to_pfc(B,A)).
any_to_pfc0(B,A):-  maybe_notrace(boxlog_to_pfc(B,A)),!.
% any_to_pfc0(B,A):-  \+ \+ lookup_u(B),!,A=B.
any_to_pfc0(B,A):-  !, trace_or_throw(should_never_be_here(any_to_pfc0(B,A))).
any_to_pfc0((H:-B),PrologO):- must((show_failure(why,boxlog_to_pfc((H:-B),Prolog)),!,=(Prolog,PrologO))),!.


%% kif_to_pfc( :TermCLIF, ?Prolog) is det.
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
      


%% pfc_for_print_left( ?Prolog, ?PrintPFC) is det.
%
% Prolog Backward Chaining Print.
%
pfc_for_print_left(Prolog,PrintPFC):-is_list(Prolog),!,maplist(pfc_for_print_left,Prolog,PrintPFC).
%pfc_for_print_left(==>(P,if_missing(R,Q)),(Q :- (fwc, naf(R), P))):-!.
%pfc_for_print_left(if_missing(R,Q),(Q :- (fwc, naf(R)))):-!.
pfc_for_print_left(==>(P,Q),(Q:-fwc, P)):-!.
pfc_for_print_left(Prolog,PrintPFC):- =(Prolog,PrintPFC).

%% pfc_for_print_right( ?Prolog, ?PrintPFC) is det.
%
% Prolog Forward Chaining Print.
%
pfc_for_print_right(Prolog,PrintPFC):-is_list(Prolog),!,maplist(pfc_for_print_right,Prolog,PrintPFC).
pfc_for_print_right('<-'(Q,P),'->'(P, Q)):-!.
pfc_for_print_right(Prolog,PrintPFC):- =(Prolog,PrintPFC).



%% is_entailed_u( ?CLIF) is det.
%
% If Is A Entailed.
%   A good sanity Test for expected side-effect entailments
%   
%
is_entailed_u(CLIF):- 
 mpred_run,
 mpred_nochaining((
   must_det(any_to_pfc(CLIF,Prolog)),!, 
   \+ \+ are_clauses_entailed(Prolog))),!.


%% is_not_entailed( ?CLIF) is det.
%
% If Is A Not Entailed.
%  A good sanity Test for required absence of specific side-effect entailments
%
is_not_entailed(CLIF):-  mpred_nochaining((kif_to_boxlog(CLIF,Prolog), 
  \+ are_clauses_entailed(Prolog))).

:- op(1190,xfx,(:-)).
:- op(1200,fy,(is_entailed_u)).

% this defines a recogniser for clif syntax (well stuff that might be safe to send in thru kif_to_boxlog)



%% is_clif( :TermCLIF) is det.
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




%% correct_arities( ?VALUE1, ?FmlO, ?FmlO) is det.
%
% Correct Arities.
%
correct_arities(_,FmlO,FmlO):-leave_as_is_logically(FmlO),!.
correct_arities([],Fml,Fml):-!.
correct_arities([H|B],Fml,FmlO):-!,correct_arities(H,Fml,FmlM),correct_arities(B,FmlM,FmlO).
correct_arities(_,Fml,Fml):- \+ compound(Fml),!.
correct_arities(H,Fml,FmlO):- Fml=..[H,A|ARGS], ARGS\=[_],
  (ARGS==[]-> correct_arities(H,A,FmlO);
       (correct_arities(H,A,CA),FmlM=..[H|ARGS],correct_arities(H,FmlM,FmlMC),FmlO=..[H,CA,FmlMC])),!.
correct_arities(H,Fml,FmlM):- Fml=..[F|ARGS],must_maplist(correct_arities(H),ARGS,ARGSM),FmlM =.. [F|ARGSM].


:- public(subsT_each/3).



%% subsT_each( ?In, :TermARG2, ?In) is det.
%
% Subs True Stucture Each.
%
subsT_each(In,[],In):- !.
% subsT_each(In,[KV|TODO],Out):- !,get_kv(KV,X,Y),subst_except(In,X,Y,Mid),!,subsT_each(Mid,TODO,Out),!.
subsT_each(In,[KV|TODO],Out):- notrace(subst_except_l(In,[KV|TODO],Out)),!.




%% subst_except_l( :TermVar, ?VALUE2, :TermVar) is det.
%
% Subst Except (list Version).
%
subst_except_l(  Var, List, NVar ) :- nonvar(NVar),!,subst_except_l(  Var, List, MVar ),!,must(MVar=NVar).
subst_except_l(  Var, _,Var ) :- is_ftVar(Var),!.
% subst_except_l(  Var, _,Var ) :- leave_as_is_logically(Var),!.
subst_except_l(  N, List,V ) :- member(N=V,List),!.
subst_except_l(   [], _,[] ) :-!.
subst_except_l([H|T],List,[HH|TT]):- !, subst_except_l(H,List,HH), subst_except_l(T,List,TT).
subst_except_l(HT,List,HHTT):- compound(HT),
   compound_name_arguments(HT,F,ARGS0),
   subst_except_l([F|ARGS0],List,[FM|MARGS]),!,
   (atom(FM)->HHTT=..[FM|MARGS];append_termlist(FM,MARGS,HHTT)),!.
subst_except_l(HT,_List,HT).





%% skolem_in_code( ?X, ?Y) is det.
%
% Skolem In Code.
%
skolem_in_code(X,Y):- ignore(X=Y).



%% skolem_in_code( ?X, ?VALUE2, ?Fml) is det.
%
% Skolem In Code.
%
skolem_in_code(X,_,Fml):- when('?='(X,_),skolem_in_code(X,Fml)).

:- public(not_mudEquals/2).
:- was_dynamic(not_mudEquals/2).



%% not_mudEquals( ?X, ?Y) is det.
%
% Not Application Equals.
%
not_mudEquals(X,Y):- dif:dif(X,Y).

:- public(type_of_var/3).



%% type_of_var( ?Fml, ?Var, ?Type) is det.
%
% Type Of Variable.
%
type_of_var(Fml,Var,Type):- contains_type_lits(Fml,Var,Lits),!,(member(Type,Lits)*->true;Type='Unk').
:- style_check(+singleton).





%% to_dlog_ops( ?VALUE1) is det.
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
    '\\+'='~',
     % '\\+'='naf',
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




%% to_symlog_ops( ?VALUE1) is det.
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




%% to_prolog_ops( ?VALUE1) is det.
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





%% to_nonvars( :PRED2Type, ?IN, ?IN) is det.
%
% Converted To Nonvars.
%
to_nonvars(_Type,IN,IN):- is_ftVar(IN),!.
to_nonvars(_,Fml,Fml):- leave_as_is_logically(Fml),!.
to_nonvars(Type,IN,OUT):- is_list(IN),!,must_maplist(to_nonvars(Type),IN,OUT),!.
to_nonvars(Type,IN,OUT):- call(Type,IN,OUT),!.



%% convertAndCall( ?Type, :Goal) is det.
%
% Convert And Call.
%
convertAndCall(Type,Call):- fail,Call=..[F|IN],must_maplist(to_nonvars(Type),IN,OUT), IN \=@= OUT, !, must(apply(F,OUT)).
convertAndCall(_Type,Call):-call_last_is_var(Call).




%% as_dlog( ?Fml, ?Fml) is det.
%
% Converted To Datalog.
%
as_dlog(Fml,Fml):- leave_as_is_logically(Fml),!.
as_dlog(Fml,FmlO):- to_dlog_ops(OPS),subsT_each(Fml,OPS,FmlM),!,correct_arities(['v','&'],FmlM,FmlO).







%% as_symlog( ?Fml, ?Fml) is det.
%
% Converted To Symlog.
%
as_symlog(Fml,Fml):- leave_as_is_logically(Fml),!.
as_symlog(Fml,FmlO):- notrace((as_dlog(Fml,FmlM),to_symlog_ops(OPS),subsT_each(FmlM,OPS,FmlM),correct_arities(['v','&'],FmlM,FmlO))).




%% baseKB:as_prolog_hook( ?Fml, ?Fml) is det.
%
% Converted To Prolog.
%
baseKB:as_prolog_hook(Fml,Fml):- is_ftVar(Fml),!.
baseKB:as_prolog_hook(Fml,FmlO):- as_symlog(Fml,FmlM),
  to_prolog_ops(OPS),subsT_each(FmlM,OPS,FmlO).







%% adjust_kif( ?KB, ?Kif, ?KifO) is det.
%
% Adjust Knowledge Interchange Format.
%
adjust_kif(KB,Kif,KifO):- as_dlog(Kif,KifM),maybe_notrace(adjust_kif0(KB,KifM,KifO)),!.

% Converts to syntax that NNF/DNF/CNF/removeQ like





%% adjust_kif0( ?VALUE1, ?V, ?V) is det.
%
% Adjust Knowledge Interchange Format Primary Helper.
%

adjust_kif0(KB,I,O):-nonvar(O),!,adjust_kif0(KB,I,M),!,M=O.

adjust_kif0(_,V,V):- is_ftVar(V),!.
adjust_kif0(_,A,A):- \+ compound(A),!.
adjust_kif0(_,A,A):- leave_as_is_logically(A),!.

adjust_kif0(KB,not(Kif),(KifO)):- !,adjust_kif0(KB, ~(Kif),KifO).
% adjust_kif0(KB,\+(Kif),(KifO)):- !,adjust_kif0(KB, naf(Kif),KifO).
adjust_kif0(KB,nesc(N,Kif),nesc(N,KifO)):- !,adjust_kif0(KB,Kif,KifO).
adjust_kif0(KB,poss(N,Kif),poss(N,KifO)):- !,adjust_kif0(KB,Kif,KifO).
adjust_kif0(KB, ~(Kif),    ~(KifO)):- !,adjust_kif0(KB,Kif,KifO).
adjust_kif0(KB, ~(KB2,Kif), KifO):- KB2==KB,!,adjust_kif0(KB,~(Kif),KifO).
adjust_kif0(KB,t(Kif),t(KifO)):- !,adjust_kif0(KB,Kif,KifO).
adjust_kif0(KB,poss(Kif),  poss(b_d(KB,nesc,poss),KifO)):- !,adjust_kif0(KB,Kif,KifO).
adjust_kif0(KB,nesc(Kif),  nesc(b_d(KB,nesc,poss),KifO)):- !,adjust_kif0(KB,Kif,KifO).

adjust_kif0(KB,exists(L,Expr),               ExprO):-L==[],!,adjust_kif0(KB,Expr,ExprO).
adjust_kif0(KB,exists(V,Expr),               ExprO):-atom(V),svar_fixvarname(V,L),subst(Expr,V,'$VAR'(L),ExprM),!,adjust_kif0(KB,exists('$VAR'(L),ExprM),ExprO).
% adjust_kif0(KB,exists([L|List],Expr),        ExprO):-is_list(List),!,adjust_kif0(KB,exists(L,exists(List,Expr)),ExprO).
% adjust_kif0(KB,exists(L,Expr),               ExprO):- is_ftVar(L), \+ contains_var(L,Expr),!,adjust_kif0(KB,Expr,ExprO).
adjust_kif0(KB,exists(L,Expr),exists(L,ExprO)):-!,adjust_kif0(KB,Expr,ExprO).


adjust_kif0(KB,all(L,Expr),               ExprO):-L==[],!,adjust_kif0(KB,Expr,ExprO).
adjust_kif0(KB,all(V,Expr),               ExprO):-atom(V),svar_fixvarname(V,L),subst(Expr,V,'$VAR'(L),ExprM),!,adjust_kif0(KB,all('$VAR'(L),ExprM),ExprO).
adjust_kif0(KB,all([L|List],Expr),all(L,ExprO)):-is_list(List),!,adjust_kif0(KB,all(List,Expr),ExprO).
% adjust_kif0(KB,all(L,Expr),               ExprO):- \+ contains_var(L,Expr),!,adjust_kif0(KB,Expr,ExprO).
adjust_kif0(KB,all(L,Expr),all(L,ExprO)):-!,adjust_kif0(KB,Expr,ExprO).

adjust_kif0(KB,(H & B),(HH & ConjO)):- !, adjust_kif(KB,H,HH),adjust_kif(KB,B,ConjO).
adjust_kif0(KB,(H v B),(HH v ConjO)):- !, adjust_kif(KB,H,HH),adjust_kif(KB,B,ConjO).
adjust_kif0(KB,'&'([L|Ist]),ConjO):- is_list([L|Ist]),list_to_conjuncts('&',[L|Ist],Conj),adjust_kif0(KB,Conj,ConjO).
adjust_kif0(KB,'v'([L|Ist]),ConjO):- is_list([L|Ist]),list_to_conjuncts('v',[L|Ist],Conj),adjust_kif0(KB,Conj,ConjO).

adjust_kif0(KB,[L|Ist],ConjO):- is_list([L|Ist]),!,must_maplist(adjust_kif0(KB),[L|Ist],ConjO),!.
adjust_kif0(KB,(H:-[L|Ist]),(HH:-ConjO)):- nonvar(Ist), adjust_kif(KB,H,HH),is_list([L|Ist]),adjust_kif0(KB,'&'([L|Ist]),ConjO).
adjust_kif0(KB,(H:-B),(HH:-ConjO)):- !, adjust_kif(KB,H,HH),adjust_kif(KB,B,ConjO).

adjust_kif0(KB,PAB,KifO):- PAB=..[F|AB],must_maplist(adjust_kif0(KB),AB,ABO),maybe_notrace(adjust_kif4(KB,F,ABO,KifO)).




%% adjust_kif0( ?KB, ?Not_P, :TermARGS, ?O) is det.
%
% Adjust Knowledge Interchange Format Primary Helper.
%
adjust_kif4(KB,call_builtin,ARGS,O):-!,PARGS=..ARGS,adjust_kif0(KB,PARGS,O),!.

adjust_kif4(KB,'v',[F|LIST],O3):- !, adjust_kif0(KB,'v'([F|LIST]),O3).
adjust_kif4(KB,'&',[F|LIST],O3):- !, adjust_kif0(KB,'&'([F|LIST]),O3).

adjust_kif4(KB,true_t,[F|LIST],O3):-atom(F),!,PARGS=..[F|LIST],adjust_kif0(KB,(PARGS),O3),!.
adjust_kif4(KB,not_true_t,[F|LIST],O3):-atom(F),!,PARGS=..[F|LIST],adjust_kif0(KB, ~(PARGS),O3),!.
adjust_kif4(KB,~,[F|LIST],O3):-atom(F),!,PARGS=..[F|LIST],adjust_kif0(KB, ~(PARGS),O3),!.

/*
adjust_kif4(KB,possible_t,[A],O):-!,adjust_kif0(KB,poss(A),O),!.
adjust_kif4(KB,possible_t,ARGS,O):-!,PARGS=..ARGS,adjust_kif0(KB,poss(PARGS),O).

% adjust_kif0(KB,asserted_t,[A],O):-!,adjust_kif0(KB,t(A),O),!.
% adjust_kif0(KB,asserted_t,[A|RGS],O):- atom(A),PARGS=..[A|RGS],!,adjust_kif0(KB,t(PARGS),O).

adjust_kif4(KB,true_t,[A|RGS],O):- atom(A),PARGS=..[A|RGS],adjust_kif0(KB,PARGS,O),!.
adjust_kif4(KB,Not_P,ARGS,O):-atom_concat('not_',P,Not_P),!,PARGS=..[P|ARGS],adjust_kif0(KB, ~(PARGS),O).
adjust_kif4(KB,Int_P,ARGS,O):-atom_concat('int_',P,Int_P),!,append(LARGS,[_, _, _, _, _, _, _ ],ARGS),
   PLARGS=..[P|LARGS],adjust_kif0(KB,PLARGS,O).

adjust_kif4(KB,P,ARGS,O):- fail, atom_concat(_,'_t',P),!,append(LARGS,[_, _, _, _, _, _],ARGS),
   PARGS=..[P|LARGS],adjust_kif0(KB,PARGS,O).
*/

adjust_kif4(KB,W,[P,A,R|GS],O):- call(clause_b(is_wrapper_pred(W))),PARGS=..[P,A,R|GS],adjust_kif0(KB,t(PARGS),O).

adjust_kif4(KB,F,ARGS,O):-KIF=..[F|ARGS],length(ARGS,L),L>2,adjust_kif0(KB,KIF,F,ARGS,Conj),KIF\=@=Conj,!,adjust_kif0(KB,Conj,O).
% adjust_kif0(KB,W,[A],O):-is_wrapper_pred(W),adjust_kif(KB,A,O),!.

adjust_kif4(_, F,ARGS,P):- P=..[F|ARGS],!.



%% adjust_kif0( ?KB, ?KIF, ?OP, ?ARGS, ?Conj) is det.
%
% Adjust Knowledge Interchange Format Primary Helper.
%
adjust_kif0(KB,KIF,OP,ARGS,Conj):-must_maplist(adjust_kif(KB),ARGS,ABO),adjust_kif5(KB,KIF,OP,ABO,Conj).




%% adjust_kif5( ?KB, ?KIF, ?VALUE3, ?ARGS, ?Conj) is det.
%
% Adjust Kif5.
%
adjust_kif5(_KB,_KIF,',',ARGS,Conj):- list_to_conjuncts('&',ARGS,Conj).
adjust_kif5(      _,_,';',ARGS,Conj):-list_to_conjuncts('v',ARGS,Conj).
adjust_kif5(      _,_,'v',ARGS,Conj):-list_to_conjuncts('v',ARGS,Conj).
adjust_kif5(      _,_,'&',ARGS,Conj):-list_to_conjuncts('&',ARGS,Conj).





%% local_pterm_to_sterm( ?P, ?S) is det.
%
% Local Pterm Converted To Sterm.
%
local_pterm_to_sterm(P,['$VAR'(S)]):- if_defined(mpred_sexp_reader:svar(P,S),fail),!.
local_pterm_to_sterm(P,['$VAR'(S)]):- if_defined(mpred_sexp_reader:lvar(P,S),fail),!.
local_pterm_to_sterm(P,[P]):- leave_as_is_logically(P),!.
local_pterm_to_sterm((H:-P),(H:-S)):-!,local_pterm_to_sterm(P,S),!.
local_pterm_to_sterm((P=>Q),[implies,PP,=>,QQ]):-local_pterm_to_sterm(P,PP),local_pterm_to_sterm(Q,QQ).
local_pterm_to_sterm((P<=>Q),[equiv,PP,QQ]):-local_pterm_to_sterm(P,PP),local_pterm_to_sterm(Q,QQ).
local_pterm_to_sterm(all(P,Q),[all(PP),QQ]):-local_pterm_to_sterm(P,PP),local_pterm_to_sterm(Q,QQ).
local_pterm_to_sterm(exists(P,Q),[ex(PP),QQ]):-local_pterm_to_sterm(P,PP),local_pterm_to_sterm(Q,QQ).
local_pterm_to_sterm( ~(Q),[not,QQ]):-local_pterm_to_sterm(Q,QQ).
local_pterm_to_sterm(poss(Q),[poss(QQ)]):-local_pterm_to_sterm(Q,QQ).
local_pterm_to_sterm('&'(P,Q),PPQQ):-local_pterm_to_sterm(P,PP),local_pterm_to_sterm(Q,QQ),flatten([PP,QQ],PPQQ0),list_to_set(PPQQ0,PPQQ).
local_pterm_to_sterm(','(P,Q),PPQQ):-local_pterm_to_sterm(P,PP),local_pterm_to_sterm(Q,QQ),flatten([PP,QQ],PPQQ0),list_to_set(PPQQ0,PPQQ).
local_pterm_to_sterm('v'(P,Q),[or,[PP],[QQ]]):-local_pterm_to_sterm(P,PP),local_pterm_to_sterm(Q,QQ),!.
local_pterm_to_sterm('beliefs'(P,Q),[beliefs(PP),QQ]):-local_pterm_to_sterm2(P,PP),local_pterm_to_sterm(Q,QQ),!.
local_pterm_to_sterm(P,S):-subst_except(P,'&',',',Q),P\=@=Q,!,local_pterm_to_sterm(Q,S),!.
local_pterm_to_sterm(P,S):-subst_except(P,'v',';',Q),P\=@=Q,!,local_pterm_to_sterm(Q,S),!.
local_pterm_to_sterm(P,[Q]):-P=..[F|ARGS],maplist(local_pterm_to_sterm2,ARGS,QARGS),Q=..[F|QARGS].
local_pterm_to_sterm(P,[P]).




%% local_pterm_to_sterm2( ?P, ?Q) is det.
%
% Local Pterm Converted To Sterm Extended Helper.
%
local_pterm_to_sterm2(P,Q):-local_pterm_to_sterm(P,PP),([Q]=PP;Q=PP),!.






%======  make a sequence out of a disjunction =====



%% flatten_or_list( ?A, ?B, ?C) is det.
%
% Flatten Or List.
%
flatten_or_list(A,B,C):- convertAndCall(as_symlog,flatten_or_list(A,B,C)).
flatten_or_list(KB,v(X , Y), F):- !,
   flatten_or_list(KB,X,A),
   flatten_or_list(KB,Y,B),
   flatten([A,B],F).
flatten_or_list(_KB,X,[X]).






%% fmtl( ?X) is det.
%
% Fmtl.
%
fmtl(X):- baseKB:as_prolog_hook(X,XX), fmt(XX).




%% write_list( ?F) is det.
%
% Write List.
%
write_list([F|R]):- write(F), write('.'), nl, write_list(R).
write_list([]).




%% unnumbervars_with_names( ?Term, ?CTerm) is det.
%
% Numbervars Using Names.
%

% unnumbervars_with_names(X,X):-!.
% unnumbervars_with_names(Term,CTerm):- ground(Term),!,duplicate_term(Term,CTerm).
unnumbervars_with_names(Term,CTerm):- must(quietly(unnumbervars(Term,CTerm))),!.

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




%% get_var_names( :TermV, ?NamedVars, :TermS) is det.
%
% Get Variable Names.
%
get_var_names([],_,[]).
get_var_names([V|Vars],NamedVars,[S|SNames]):-
    get_1_var_name(V,NamedVars,S),
    get_var_names(Vars,NamedVars,SNames).




%% get_1_var_name( ?Var, :TermNamedVars, ?Name) is det.
%
% get  Secondary Helper Variable name.
%
get_1_var_name(_V,[],_S).

get_1_var_name(Var,NamedVars,Name):- compound(Var),arg(1,Var,NV),!,get_1_var_name(NV,NamedVars,Name).
get_1_var_name(Var,NamedVars,Var=NV):-atom(Var),NamedVars=[_|T],nb_setarg(2,NamedVars,[Var=NV|T]),!.
get_1_var_name(Var,[N=V|_NamedVars],Name=V):-
     (Var == V -> Name = N ; (Var==Name -> Name=Var ; fail )),!.
get_1_var_name(Var,[_|NamedVars],Name):- get_1_var_name(Var,NamedVars,Name).



%% kif_to_boxlog( ?Wff, ?Out) is det.
%
% Knowledge Interchange Format Converted To Datalog.
%
%====== kif_to_boxlog(+Wff,-NormalClauses):-
:- public(kif_to_boxlog/2).
% kif_to_boxlog(Wff,Out):- loop_check(kif_to_boxlog(Wff,Out),Out=looped_kb(Wff)).
% kif_to_boxlog('=>'(WffIn,enables(Rule)),'$VAR'('MT2'),complete,Out1), % kif_to_boxlog('=>'(enabled(Rule),WffIn),'$VAR'('KB'),complete,Out).
kif_to_boxlog(Wff,Out):- why_to_id(rule,Wff,Why),!,must(kif_to_boxlog3(Wff,Out,Why)).

kif_to_boxlog3(Wff,Out,Why):- show_failure(kif_to_boxlog(Wff,Why,Out)),!.
kif_to_boxlog3(WffIn,Out,Why):-  kif_to_boxlog(all('$VAR'('KB'),'=>'(kb_in('$VAR'('KB')),WffIn)),'$VAR'('KB'),Why,Out),!.
kif_to_boxlog3(WffIn,NormalClauses,Why):- kif_to_boxlog(WffIn,'$VAR'('KB'),Why,NormalClauses),!.




%% alt_kif_to_boxlog( ?Wff, ?KB, ?Why, ?Out) is det.
%
% Alt Knowledge Interchange Format Converted To Datalog.
%
alt_kif_to_boxlog( ~( Wff),KB,Why,Out):- !, kif_to_boxlog( ~( Wff),KB,Why,Out).
alt_kif_to_boxlog(Wff,KB,Why,Out):- loop_check(kif_to_boxlog(( ~(nesc( ~(Wff)))),KB,Why,Out),Out=looped_kb(Wff)).

:- public(kif_to_boxlog/3).



%% kif_to_boxlog( ?WffIn, ?Why, ?Out) is det.
%
% Knowledge Interchange Format Converted To Datalog.
%
kif_to_boxlog(WffIn,Why,Out):-  kif_to_boxlog(WffIn,'$VAR'('KB'),Why,Out),!.


:- export(kif_to_boxlog/4).




%% kif_to_boxlog( ?I, ?KB, ?Why, ?Flattened) is det.
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
  sumo_to_pdkb(HB,HB00)->
  sumo_to_pdkb(KB,KB00)->
  sumo_to_pdkb(Why,Why00)->
 unnumbervars_with_names((HB00,KB00,Why00),(HB0,KB0,Why0))->
  with_no_kif_var_coroutines(must(kif_to_boxlog_attvars(HB0,KB0,Why0,FlattenedO))),!.

:- meta_predicate(ignore_unless(*,*)).
ignore_unless(A,B):- call(A)->B;true.

kif_to_boxlog_attvars(kif(HB),KB,Why,FlattenedO):-!,kif_to_boxlog_attvars(HB,KB,Why,FlattenedO).
kif_to_boxlog_attvars(clif(HB),KB,Why,FlattenedO):-!,kif_to_boxlog_attvars(HB,KB,Why,FlattenedO).
  
kif_to_boxlog_attvars(HB,KB,Why,FlattenedO):- compound(HB),HB=(HEAD:- BODY),!,
  must_det_l((
   check_is_kb(KB),
   conjuncts_to_list(HEAD,HEADL),
   conjuncts_to_list(BODY,BODYL),
   correct_flattened([cl(HEADL,BODYL)],KB,Why,FlattenedO))),!.

kif_to_boxlog_attvars(WffIn0,KB0,Why0,FlattenedOUTRealOUT):- 
 % flag(skolem_count,_,1),
  maplist(must_det,[
   must_be_unqualified(WffIn0),
   unnumbervars_with_names(WffIn0:KB0:Why0,WffIn:KB:Why),
   ensure_quantifiers(WffIn,Wff),
   
   must_be_unqualified(Wff),
   % KB = WffQ,
   check_is_kb(KB),
   as_dlog(Wff,Wff665),!,
   must_be_unqualified(Wff665),
   to_modal1(KB,Wff665,Wff666),
   must_be_unqualified(Wff666),
   qualify_nesc(Wff666,Wff6667),   
   ignore((Wff666\==Wff6667, sdmsg(kif=(Wff666)),sdmsg(qualify_nesc=(Wff6667)))),
   % add_preconds(Wff6667,Wff6668),
   adjust_kif(KB,Wff6667,Wff6669),
   must_be_unqualified(Wff6669),
   show_call(nnf(KB,Wff6669,NNF)),
   (NNF \== poss(~t)),
   %must_be_unqualified(NNF),
   sdmsg(nnf=(NNF)),
   %save_wid(Why,kif,Wff),
   %save_wid(Why,pkif,Wff6669),
   removeQ(KB,NNF,[], UnQ), 
   ignore_unless(NNF\==UnQ, sdmsg(unq=UnQ)),
   must(kif_to_boxlog_theorist(Wff666,UnQ,KB,Why,FlattenedOUTRealOUT))]).


kif_to_boxlog_theorist(_Wff666,UnQ,KB,Why,FlattenedOUTRealOUT):-
   current_outer_modal_t(HOLDS_T),
   to_tlog(HOLDS_T,KB,UnQ,UnQ666),
   % UnQ=UnQ666,
   as_prolog_hook(UnQ666,THIN0),
   to_tnot(THIN0,THIN),
   must_be_unqualified(THIN),
   ignore_unless(THIN\==UnQ, sdmsg(th_nnf_in=THIN)),
   th_nnf(THIN,even,RULIFY),
   ignore_unless(THIN\== ~ RULIFY, sdmsg(th_nnf_out= ~ RULIFY)),   
   once((rulify(constraint,RULIFY,SideEffectsList),SideEffectsList\==[])),
   list_to_set(SideEffectsList,FlattenedM),
   correct_flattened(KB,Why,FlattenedM,FlattenedIO),
   must_maplist(undess_head,FlattenedIO,FlattenedO),
   defunctionalize_each(FlattenedO,FlattenedOUTY),
   predsort(sort_by_pred_class,FlattenedOUTY,FlattenedOUT),
   =(FlattenedOUT,FlattenedOUTReal),
   must_maplist(from_tlog,FlattenedOUTReal,FlattenedOUTRealOUT),!.


kif_to_boxlog_theorist2(Original,THIN,KB,Why,FlattenedOUTRealOUT):-
   demodal_clauses3(KB,THIN,THIN2),
   as_prolog_hook(THIN2,THIN3),
     
    must(cf(Why,KB,Original,THIN3,FlattenedOUTRealOUT)),!.

correct_flattened(KB,_Why,Flattened,FlattenedO):-
  demodal_clauses3(KB,Flattened,FlattenedO),!.
correct_flattened(_KB,_Why,FlattenedO,FlattenedO):-!.
correct_flattened(KB,Why,FlattenedM,FlattenedO):-
  correct_boxlog(FlattenedM,KB,Why,FlattenedOOO),
  demodal_clauses3(KB,FlattenedOOO,FlattenedO).

:- meta_predicate(to_tlog(+,+,*,-)).
:- meta_predicate(to_tlog_lit(+,+,+,*,-)).

to_tlog(args,_KB,Var, Var):-!.  % for now
to_tlog(_,_KB,Var, Var):- quietly(leave_as_is_logically(Var)),!.
to_tlog(MD,KB,M:H,M:HH):- !, to_tlog(MD,KB,H,HH).
to_tlog(MD,KB,[H|T],[HH|TT]):- !, to_tlog(MD,KB,H,HH),to_tlog(MD,KB,T,TT).

to_tlog(MD,KB, nesc(b_d(KB2,X,_),F), HH):- atom(X),KB\=KB2,XF =..[X,KB2,F],!,to_tlog(MD,KB2,XF, HH).
to_tlog(MD,KB, poss(b_d(KB2,_,X),F), HH):- atom(X),KB\=KB2,XF =..[X,KB2,F],!,to_tlog(MD,KB2,XF, HH).
to_tlog(MD,KB, nesc(b_d(KB,X,_),F),   HH):- atom(X), XF =..[X,F], !,to_tlog(MD,KB,XF, HH).
to_tlog(MD,KB, poss(b_d(KB,_,X),F),   HH):- atom(X), XF =..[X,F], !,to_tlog(MD,KB,XF, HH).
to_tlog(MD,KB, nesc(_,F),   HH):- XF =..[nesc,F], !,to_tlog(MD,KB,XF, HH).
to_tlog(MD,KB, poss(_,F),   HH):- XF =..[poss,F], !,to_tlog(MD,KB,XF, HH).

to_tlog(MD,KB,(X ; Y),(Xp v Yp)) :- to_tlog(MD,KB,X,Xp), to_tlog(MD,KB,Y,Yp).
to_tlog(MD,KB,(X v Y),(Xp v Yp)) :- to_tlog(MD,KB,X,Xp), to_tlog(MD,KB,Y,Yp).
to_tlog(MD,KB,H,HH ):- H=..[F|ARGS],tlog_is_sentence_functor(F),!,must_maplist(to_tlog(MD,KB),ARGS,ARGSO),!,HH=..[F|ARGSO].
to_tlog(MD,KB, ~(XF),  n(HH)):- !,to_tlog(MD,KB,XF, HH).
to_tlog(MD,KB, n(XF),  n(HH)):- !,to_tlog(MD,KB,XF, HH).
to_tlog(MD,KB, nesc(_,XF),(HH)):- !,to_tlog(MD,KB,XF, HH).
to_tlog(MD,KB, nesc(XF),(HH)):- !,to_tlog(MD,KB,XF, HH).
to_tlog(_,KB,H,HH ):- H=..[F,ARG],is_holds_functor(F),!,(is_ftVar(ARG)->HH=H;to_tlog(F,KB,ARG,HH)).
to_tlog(_,KB, poss(XF),  HH):- !, to_tlog(poss_t,KB, XF,  HH).
to_tlog(MD,KB,H,HH):- H=..[F|ARGS],must_maplist(to_tlog(args,KB),ARGS,ARGSO),to_tlog_lit(MD,KB,F,ARGSO,HH).

tlog_is_sentence_functor(F):- \+ atom(F),!,fail.
tlog_is_sentence_functor(F):- upcase_atom(F,F).
tlog_is_sentence_functor(F):- is_sentence_functor(F), \+ is_holds_functor(F).

to_tlog_lit(MD,KB,F,[ARG],HH):- (clause_b(ttExpressionType(F));atom_concat(ft,_,F)),!,to_tlog(MD,KB,quotedIsa(ARG,F ),HH).
to_tlog_lit(MD,KB,F,[ARG],HH):- (clause_b(tSet(F));(atom_concat(t,_,F), \+ atom_concat(_,'_t',F))),!,to_tlog(MD,KB,isa(ARG,F ),HH).
to_tlog_lit(MD,_ ,F,ARGSO,HHH):- is_holds_functor(F),!,HH=..[F|ARGSO],maybe_wrap_modal(MD,HH,HHH).
to_tlog_lit(MD,_ ,F,ARGSO,HHH):- get_holds_wrapper(F,W),(W==h;W==c),!,HH=..[F|ARGSO],maybe_wrap_modal(MD,HH,HHH).
to_tlog_lit(MD,_ ,F,ARGSO,HHH):- get_holds_wrapper(F,W),!,XF=..[F|ARGSO],into_ff(W,XF,HH),maybe_wrap_modal(MD,HH,HHH).
to_tlog_lit(MD,_ ,F,ARGSO,HHH):- XF=..[F|ARGSO],into_ff(MD,XF,HHH).

into_ff(MD,XF,HHH):-into_functor_form(MD,XF,HHH).

current_outer_modal_t(t).

maybe_wrap_modal(MD,HH,HH):- current_outer_modal_t(H_T),MD==H_T,!.
maybe_wrap_modal(MD,HH,HHH):- var_or_atomic(HH),HHH=..[MD,HH],!.
maybe_wrap_modal(MD,M:HH,M:HHH):-!,maybe_wrap_modal(MD,HH,HHH).
maybe_wrap_modal(MD,HH,HH):- functor(HH,MD,_).
maybe_wrap_modal(MD,HH,HHH):- HH=..[F|_],get_holds_wrapper(F,W),W==h,HHH=..[MD,HH].
maybe_wrap_modal(MD,HH,HHH):- HH=..[F|ARGS],get_holds_wrapper(F,W),W==c,atomic_list_concat([F,'_',MD],MF),HHH=..[MF|ARGS].
maybe_wrap_modal(MD,HH,HHH):- HH=..[F|ARGS],is_holds_functor(F),atom_concat(MD,F,MF),HHH=..[MF|ARGS].
maybe_wrap_modal(MD,HH,HHH):-HHH=..[MD,HH].


% get_holds_wrapper(isa,c).
get_holds_wrapper(isa,c).
get_holds_wrapper(arity,c).
get_holds_wrapper(reify,c).
get_holds_wrapper(skolem,c).
get_holds_wrapper(quotedIsa,c).
get_holds_wrapper(resultIsa,c).
get_holds_wrapper(quotedArgIsa,c).
get_holds_wrapper(ISA,c):- tinyKB(isa(ISA,_)).
get_holds_wrapper(IST,c):- atom_contains(IST,ist). % relationAllExists ist etc
get_holds_wrapper(genls,c).
get_holds_wrapper(admittedArgument,c).
get_holds_wrapper(argIsa,c).
get_holds_wrapper(disjointWith,c).
%get_holds_wrapper(_,_):-!,fail.
%get_holds_wrapper(_P,t).

to_tnot(THIN,THIN):- \+ compound(THIN),!.
to_tnot(~ THIN0,NTHIN):- to_tnot( THIN0, THIN),!,to_neg(THIN,NTHIN).
to_tnot(poss_t(C,I),POSCI):- atom(C),CI=..[C,I],!,to_poss(CI,POSCI).
to_tnot(poss(THIN0),NTHIN):- to_poss( THIN0, NTHIN),!.
to_tnot(nesc(THIN0),(NTHIN)):- to_tnot( THIN0, NTHIN),!.
to_tnot((X ; Y),(Xp ; Yp)) :- to_tnot(X,Xp), to_tnot(Y,Yp).
to_tnot((X :- Y),(Xp :- Yp)) :- to_tnot(X,Xp), to_tnot(Y,Yp).
to_tnot((X , Y),(Xp , Yp)) :- to_tnot(X,Xp), to_tnot(Y,Yp).
to_tnot(THIN0,tru(THIN)):- into_mpred_form(THIN0,THIN).

to_neg(THIN,THIN):- \+ compound(THIN),!.
to_neg(neg(THIN),THIN).
to_neg(tru(THIN),neg(THIN)).
to_neg(THIN,neg(THIN)).

to_poss(THIN,poss(THIN)):- \+ compound(THIN),!.
to_poss(poss(THIN),poss(THIN)).
to_poss(tru(THIN),poss(THIN)).
to_poss(neg(THIN),poss(neg(THIN))).
to_poss(THIN,poss(THIN)).

%% no_rewrites is det.
%
% Hook To [baseKB:no_rewrites/0] For Module Common_logic_snark.
% No Rewrites.
%

baseKB:no_rewrites :- fail.




from_tlog(Var, NVar):- \+ compound(Var),!,Var=NVar.
from_tlog(Var, Var):- quietly(leave_as_is_logically(Var)),!.
from_tlog(M:H,M:HH):- !, from_tlog(H,HH).
from_tlog([H|T],[HH|TT]):- !, from_tlog(H,HH),from_tlog(T,TT).
from_tlog( t(XF),  (HH)):- !,from_tlog(XF, HH).
from_tlog( proven_not_holds_t(XF),  ~(HH)):- !,from_tlog(XF, HH).
from_tlog( proven_not_holds_t(F,A,B),  ~(t(F,A,B))):- var(F),!.
from_tlog( proven_not_t(XF),  ~(HH)):- !,from_tlog(XF, HH).
from_tlog( proven_not_t(F,A,B),  ~(t(F,A,B))):- var(F),!.
from_tlog( proven_t(XF),  (HH)):- !,from_tlog(XF, HH).
from_tlog( proven_t(F,A,B),  (t(F,A,B))):- var(F),!.
from_tlog(H,HH):- H=..[F,ARG],is_holds_functor(F),is_ftVar(ARG)->HH=H,!.
% from_tlog(H,HH):- H=..[F|ARGS],tlog_is_sentence_functor(F),!,must_maplist(from_tlog,ARGS,ARGSO),!,HH=..[F|ARGSO].
% from_tlog(H,HH):- H=..[F|ARGS],must_maplist(from_tlog,ARGS,ARGSO),must(from_tlog_lit(F,ARGSO,HH)).
from_tlog(H,HH):- H=..[F|ARGS],from_tlog_lit(F,ARGS,HH),!.

add_modal(t,HH,HH).
add_modal(MD,HH,HHH):- HHH=..[MD,HH].

from_tlog_lit(F,ARGSO,HHH):- F==u,HHH=..[F|ARGSO],!.
from_tlog_lit(F,ARGSO,HHH):- \+ is_holds_functor(F),!,HHH=..[F|ARGSO],!.
from_tlog_lit(F,ARGSO,HHH):- get_holds_unwrapper(F,MD,W),!,XF=..[W|ARGSO],into_mpred_form(XF,HH),from_tlog(HH,HHHH),add_modal(MD,HHHH,HHH).
from_tlog_lit(F,ARGSO,HHH):- XF=..[F|ARGSO],into_mpred_form(XF,HHH).

get_holds_unwrapper(F,t,t):- current_outer_modal_t(F).
get_holds_unwrapper(FIn,MD,F):- modal_prefix(MDF,MD),atom_concat(MDF,F,FIn).


modal_prefix(proven_,t).
modal_prefix(holds_,t).
modal_prefix(not_,~).
modal_prefix(possible_,poss).
modal_prefix(poss_,poss).
modal_prefix(unknown_,unknown).
modal_prefix(false_,~).

% PrologMUD is created to correct the mistakes we made in the projects i worked on that we forgot the funding was to create the platform/OS to run Roger Schank''s outlined software and not Doug Lenat''s software. 
% Additionally to allow it to be taken for granted by current scientists whom were unaware of the breakthroughs we made in those projects due to the fact we where affaid competetors would take our future grant money.


%% check_is_kb( ?KB) is det.
%
% Check If Is A Knowledge Base.
%
check_is_kb(KB):-attvar(KB),!.
check_is_kb(KB):-ignore('$VAR'('KB')=KB).




%% add_preconds( ?X, ?X) is det.
%
% Add Preconds.
%
add_preconds(X,X):- baseKB:no_rewrites,!.
add_preconds(X,Z):-
 locally(leave_as_is_db('CollectionS666666666666666ubsetFn'(_,_)),
   locally(t_l:dont_use_mudEquals,must(defunctionalize('=>',X,Y)))),must(add_preconds2(Y,Z)).




%% add_preconds2( ?Wff6667, ?PreCondPOS) is det.
%
% Add Preconds Extended Helper.
%
add_preconds2(Wff6667,PreCondPOS):-
   must_det_l((get_lits(Wff6667,PreCond),list_to_set(PreCond,PreCondS),
     add_poss_to(PreCondS,Wff6667, PreCondPOS))).




%% add_poss_to( ?PreCond, ?Wff6667, ?Wff6667) is det.
%
% Add Possibility Converted To.
%
add_poss_to([],Wff6667, Wff6667).
add_poss_to([PreCond|S],Wff6667, PreCondPOS):-!,
 add_poss_to(PreCond,Wff6667, PreCondM),
 add_poss_to(S,PreCondM, PreCondPOS).

add_poss_to(PreCond,Wff6667, PreCond=>Wff6667):-prequent(PreCond).
add_poss_to(PreCond,Wff6667, Wff6667):-leave_as_is_logically(PreCond).
add_poss_to( ~(_PreCond),Wff6667, Wff6667).
add_poss_to(PreCond,Wff6667, (poss(PreCond)=>Wff6667)).



%% qualify_nesc( ?P, ?Q) is semidet.
%
%  Q = (poss(P)=>P).
%
:- thread_local(t_l:qualify_modally/0).

% qualify_nesc(Wff666,Wff666):- \+ t_l:qualify_modally,!.
qualify_nesc(Wff666,Wff666):- var(Wff666),!.
qualify_nesc(IN,OUT):-is_list(IN),must_maplist(qualify_nesc,IN,OUT),!.
qualify_nesc(Wff666,Wff666):- leave_as_is(Wff666),!.
qualify_nesc(Wff666,Wff666):- contains_modal(Wff666),!.
% been caught above 
% qualify_nesc(poss(Wff666),poss(Wff666)):-!.
qualify_nesc(PQ,PQO):- PQ=..[F|Q],is_quantifier(F),append(LQ,[RQ],Q),qualify_nesc(RQ,RQQ),append(LQ,[RQQ],QQ),PQO=..[F|QQ],!.

% been caught above 
% qualify_nesc(P=>Q,P=>Q):- (contains_modal(P);contains_modal(Q)),!.

%qualify_nesc(P<=>Q,((nesc(P)<=>nesc(Q)) & (poss(P)<=>poss(Q)))):-!.
%qualify_nesc(P=>Q,((nesc(P)=>nesc(Q)) & (poss(P)=>poss(Q)))):-!.

qualify_nesc( ~(IN), nesc(~(IN))):-!.
% qualify_nesc( ~(IN), ~(poss(IN))):-!.

% qualify_nesc(P=>Q,(poss(Q)&P)=>Q):-!.
% qualify_nesc(P,(poss(P)=>(P))):-!.

qualify_nesc(P,(~nesc(P)=>nesc(P))):- \+ \+ (P = (_ & _) ; P = (_ v _)).

%qualify_nesc(P=>Q,nesc(P=>Q)):-!.
%qualify_nesc(P<=>Q,nesc(P<=>Q)):-!.
qualify_nesc(P,nesc(P)):-!.


% never seen
qualify_nesc(IN,  nesc(IN)):-!.
qualify_nesc(nesc(Wff666),(poss(Wff666)=>nesc(Wff666))):-!.
qualify_nesc(   IN,  nesc(IN)).
qualify_nesc(P<=>Q,PQ & QP):- !,qualify_nesc(P=>Q,PQ),qualify_nesc(Q=>P,QP).
qualify_nesc(P=>Q,(PP => (NP & QP =>NQ))):-!, weaken_to_poss(P,PP),weaken_to_poss(Q,QP),add_nesc(P,NP),add_nesc(Q,NQ).

/*
qualify_nesc(IN,poss(IN)):- IN=..[F|_],should_be_poss(F),!.
qualify_nesc(Wff,(poss(Wff) => nesc(Wff))):- quietly(var_or_atomic(Var)),!.
qualify_nesc(Wff,(poss(Wff) => nesc(Wff))):- leave_as_is_logically(Wff),!.
qualify_nesc((P & Q),(PQ & (P & Q))):-  weaken_to_poss(P & Q,PQ),!.
qualify_nesc(Q,(PQ & Q)):-  weaken_to_poss(Q,PQ),!.
qualify_nesc(Wff666,Wff666):-!.
% qualify_nesc(IN,OUT):-IN=..[F|INL],logical_functor_pttp(F),!,must_maplist(qualify_nesc,INL,OUTL),OUT=..[F|OUTL].
*/


%% add_nesc( ?X, ?X) is semidet.
%
% Add Necesity.
%

add_nesc(IN,OUT):-is_list(IN),must_maplist(add_nesc,IN,OUT),!.
add_nesc(Wff666,Wff666):- is_ftVar(Wff666),!.
add_nesc(Wff666,Wff666):-leave_as_is(Wff666),!.
add_nesc(Wff666,Wff666):-contains_modal(Wff666),!.
add_nesc( ~(IN), nesc(~(IN))).
add_nesc(IN,OUT):-IN=..[F|INL],logical_functor_pttp(F),!,must_maplist(add_nesc,INL,OUTL),OUT=..[F|OUTL].
add_nesc(IN,nesc(IN)).
/*
add_nesc(nesc(Wff666),nesc(Wff666)):-!.
add_nesc(poss(Wff666),poss(Wff666)):-!.
add_nesc(P<=>Q,O):-!,add_nesc(((P=>Q) & (Q=>P)),O).
add_nesc(PQ,PQO):- PQ=..[F|Q],is_quantifier(F),append(LQ,[RQ],Q),add_nesc(RQ,RQQ),append(LQ,[RQQ],QQ),PQO=..[F|QQ],!.
add_nesc(IN,poss(IN)):-IN=..[F|_],should_be_poss(F),!.
add_nesc(P=>Q,((PP & P & QP) =>Q)):-  weaken_to_poss(P,PP),weaken_to_poss(Q,QP).

add_nesc(Q,(PQ & Q)):-  weaken_to_poss(Q,PQ),!.
add_nesc((P & Q),(PQ & (P & Q))):-  weaken_to_poss(P & Q,PQ),!.
add_nesc(Wff666,Wff666):-!.
*/


% weaken_to_poss(Wff666,Wff666):-!.
% weaken_to_poss(X,X):-!.



%% weaken_to_poss( ?PQ, ?PQ) is det.
%
% Weaken statments from meaning Nesc to meaning Possibility.
%
weaken_to_poss(PQ,poss(PQ)):- var(PQ),!.
weaken_to_poss(poss(PQ),poss(PQ)):-!.
weaken_to_poss(nesc(PQ),poss(PQ)):-!.
weaken_to_poss(INL,OUTC):-is_list(INL),must_maplist(weaken_to_poss,INL,OUTL),F='&',OUT=..[F|OUTL],correct_arities(F,OUT,OUTC).
%weaken_to_poss(PQ,PQO):- PQ=..[F,V,Q],is_quantifier(F),weaken_to_poss(Q,QQ),PQO=..[F,V,QQ],!.
weaken_to_poss(Wff666,poss(Wff666)):- leave_as_is_logically(Wff666),!.
weaken_to_poss( ~(IN), poss(~(IN))):-!.
weaken_to_poss(IN,OUT):-IN=..[F|INL],logical_functor_pttp(F),!,must_maplist(weaken_to_poss,INL,OUTL),OUT=..[F|OUTL].
weaken_to_poss(IN,poss(IN)).


% shall X => can X
% shall ~ X => ~ can X
% ~ shall X => can ~ X



%% get_lits( ?PQ, ?QQ) is det.
%
% Get Literals.
%
get_lits(PQ,[]):- var(PQ),!.
get_lits(PQ,QQ):- PQ=..[F,_Vs,Q],is_quantifier(F),get_lits(Q,QQ).
get_lits(Wff666,[Wff666]):-leave_as_is_logically(Wff666),!.
get_lits( ~(IN),NOUT):-get_lits(IN,OUT),must_maplist(simple_negate_literal(not),OUT,NOUT).
get_lits(knows(WHO,IN),NOUT):-get_lits(IN,OUT),must_maplist(simple_negate_literal(knows(WHO)),OUT,NOUT).
get_lits(beliefs(WHO,IN),NOUT):-get_lits(IN,OUT),must_maplist(simple_negate_literal(beliefs(WHO)),OUT,NOUT).
get_lits(IN,OUTLF):-IN=..[F|INL],logical_functor_pttp(F),!,must_maplist(get_lits,INL,OUTL),flatten(OUTL,OUTLF).
get_lits(IN,[IN]).




%% simple_negate_literal( ?F, ?FX, ?X) is det.
%
% Simple Negate Literal.
%
simple_negate_literal(F,FX,X):-FX=..FXL,F=..FL,append(FL,[X],FXL),!.
simple_negate_literal(F,X,FX):-append_term(F,X,FX).



%% should_be_poss( ?VALUE1) is det.
%
% Should Be Possibility.
%
should_be_poss(argInst).

% :- was_dynamic(elInverse/2).




%% clauses_to_boxlog( ?KB, ?Why, ?In, ?Prolog) is det.
%
% Clauses Converted To Datalog.
%
clauses_to_boxlog(KB,Why,In,Prolog):- clauses_to_boxlog_0(KB,Why,In,Prolog),!.





%% clauses_to_boxlog_0( ?KB, ?Why, ?In, ?Prolog) is det.
%
% clauses Converted To Datalog  Primary Helper.
%
clauses_to_boxlog_0(KB,Why,In,Prolog):-
 loop_check(clauses_to_boxlog_1(KB,Why,In,Prolog),
    show_call(why,(clauses_to_boxlog_5(KB,Why,In,Prolog)))),!.
clauses_to_boxlog_0(KB,Why,In,Prolog):-correct_cls(KB,In,Mid),!,clauses_to_boxlog_1(KB,Why,Mid,PrologM),!,Prolog=PrologM.




%% clauses_to_boxlog_1( ?KB, ?Why, ?In, ?Prolog) is det.
%
% clauses Converted To Datalog  Secondary Helper.
%
clauses_to_boxlog_1(KB, Why,In,Prolog):- clauses_to_boxlog_2(KB,Why,In,PrologM),!,must(Prolog=PrologM).




%% clauses_to_boxlog_2( ?KB, ?Why, :TermIn, ?Prolog) is det.
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




%% clauses_to_boxlog_5( ?KB, ?Why, ?In, ?Prolog) is det.
%
% Clauses Converted To Datalog Helper Number 5..
%
clauses_to_boxlog_5(KB, Why,In,Prolog):- is_list(In),!,must_maplist(clauses_to_boxlog_5(KB,Why),In,Prolog).
clauses_to_boxlog_5(_KB,_Why,(H:-B),(H:-B)):-!.
clauses_to_boxlog_5(_KB,_Why,cl([HeadIn],[]),HeadIn):-!.
clauses_to_boxlog_5(_KB,_Why,In,Prolog):-dtrace,In=Prolog.






%% mpred_t_tell_kif( ?OP2, ?RULE) is det.
%
% Managed Predicate True Structure Canonicalize And Store Knowledge Interchange Format.
%
mpred_t_tell_kif(OP2,RULE):-
 locally(t_l:current_pttp_db_oper(mud_call_store_op(OP2)),
   (show_call(why,call((must(kif_add(RULE))))))).


:- public(why_to_id/3).



%% why_to_id( ?Term, ?Wff, ?IDWhy) is det.
%
% Generation Of Proof Converted To Id.
%
why_to_id(Term,Wff,IDWhy):-  \+ atom(Term),term_to_atom(Term,Atom),!,why_to_id(Atom,Wff,IDWhy),!.
why_to_id(Atom,Wff,IDWhy):- clause_asserted(wid(IDWhy,Atom,Wff)),!.
why_to_id(Atom,Wff,IDWhy):- must(atomic(Atom)),gensym(Atom,IDWhyI),kb_incr(IDWhyI,IDWhy),assertz_if_new(wid(IDWhy,Atom,Wff)),!.



%% kif_ask_sent( ?VALUE1) is det.
%
% Knowledge Interchange Format Complete Inference Sentence.
%
:- public(kif_ask_sent/1).
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


%% kif_ask( :TermP) is det.
%
% Knowledge Interchange Format Complete Inference.
%
kif_ask(Goal0):-  call_unwrap(Goal0,Goal),!,kif_ask(Goal).
%kif_ask(P <=> Q):- kif_ask_sent(P <=> Q).
%kif_ask(P => Q):- kif_ask_sent(P => Q).
%kif_ask((P v Q)):- kif_ask_sent(((P v Q))).
%kif_ask((P & Q)):- kif_ask_sent((P & Q)).
kif_ask((PQ)):- kif_hook_skel(PQ),kif_ask_sent((PQ)).
kif_ask(Goal0):-  logical_pos(_KB,Goal0,Goal),
    no_repeats(baseKB:(
	if_defined(add_args(Goal0,Goal,_,_,[],_,_,[],[],DepthIn,DepthOut,[PrfEnd|PrfEnd],_ProofOut1,Goal1,_)),!,
        call(call,search(Goal1,60,0,1,3,DepthIn,DepthOut)))).

:- public(kif_ask/2).



%% kif_ask( ?VALUE1, ?VALUE2) is det.
%
% Knowledge Interchange Format Complete Inference.
%
kif_ask(Goal0,ProofOut):- logical_pos(_KB,Goal0,Goal),
    no_repeats(baseKB:(
	if_defined(add_args(Goal0,Goal,_,_,[],_,_,[],[],DepthIn,DepthOut,[PrfEnd|PrfEnd],ProofOut1,Goal1,_)),!,
        call(call,search(Goal1,60,0,1,3,DepthIn,DepthOut)),
        call(call,contract_output_proof(ProofOut1,ProofOut)))).





call_unwrap(WffIn,OUT):- call_unwrap0(WffIn,OUT),!,WffIn\==OUT.

call_unwrap0(WffIn,WffIn):- is_ftVar(WffIn),!.
call_unwrap0(==>WffIn,OUT):-!,call_unwrap0(WffIn,OUT).
call_unwrap0(clif(WffIn),OUT):-!,call_unwrap0(WffIn,OUT).
call_unwrap0(WffIn,WffIn).




%% local_sterm_to_pterm( ?Wff, ?WffO) is det.
%
% Local Sterm Converted To Pterm.
%
local_sterm_to_pterm(Wff,WffO):- sexpr_sterm_to_pterm(Wff,WffO),!.



:- op(1000,fy,(kif_add)).
%% kif_add( ?InS) is det.
%
% Knowledge Interchange Format Add.
%
kif_add(InS):-
 sanity( \+ is_ftVar(InS)),
 string(InS),!,
 must_det_l((
  input_to_forms(string(InS),Wff,Vs),
  nop(b_implode_varnames0(Vs)),
  local_sterm_to_pterm(Wff,Wff0))),
  InS \== Wff0,
  kif_add(Wff0),!.
kif_add(Goal0):-  call_unwrap(Goal0,Goal),!,kif_add(Goal).
kif_add([]).
kif_add([H|T]):- !,kif_add(H),kif_add(T).
%kif_add((H <- B)):- !, ain((H <- B)).
%kif_add((H :- B)):- !, ain((H :- B)).
%kif_add((P ==> Q)):- !, ain((P ==> Q)). 

kif_add(WffIn):- kif_hook(WffIn),!,show_call(ain(clif(WffIn))). 

kif_add(WffIn):- show_call(ain(WffIn)),!.
% unnumbervars_with_names(WffIn,Wff),
%kif_add(WffIn):- show_call(ain(clif(WffIn))),!.

kif_ain(InS):-kif_add(InS).
kif_assert(InS):-kif_add(InS).

/*
:- public((kif_add)/2).

kif_add(_,[]).
kif_add(Why,[H|T]):- !,must_det_l((kif_add(Why,H),kb_incr(Why,Why2),kif_add(Why2,T))).
kif_add(Why,P):- !, mpred_ain(P,Why). 
kif_add(Why,(H <- B)):- !, mpred_ain((H <- B),Why).
%kif_add(Why,(P ==> Q)):- !, ain((P ==> Q),Why). 


kif_add(Why,Wff):-
   must_det_l((kif_to_boxlog(Wff,Why,Asserts),
      kif_add_boxes(assert_wfs_def,Why,Wff,Asserts))),!.


:- thread_local(t_l:assert_wfs/2).
assert_wfs_def(HBINFO,HB):-if_defined(t_l:assert_wfs(HBINFO,HB)),!.
assert_wfs_def(Why,H):-assert_wfs_fallback(Why,H).

assert_wfs_fallback(Why, HB):- subst(HB,(~),(-),HB2),subst(HB2,(not_proven_t),(not_true_t),HB1),subst(HB1,(poss),(possible_t),HBO),assert_wfs_fallback0(Why, HBO).
assert_wfs_fallback0(Why,(H:-B)):- adjust_kif('$VAR'(KB),B,HBK),to_modal1('$VAR'(KB),HBK,HBKD),
   wdmsg((H:-w_infer_by(Why),HBKD)),pttp_assert_wid(Why,pttp_in,(H:-B)),!.
assert_wfs_fallback0(Why, HB):- adjust_kif('$VAR'(KB),HB,HBK),to_modal1('$VAR'(KB),HBK,HBKD),
   wdmsg((HBKD:-w_infer_by(Why))),pttp_assert_wid(Why,pttp_in,(HB)),!.

*/

:- public(kb_incr/2).



%% kb_incr( ?WffNum1, ?WffNum2) is det.
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




%% kif_add_adding_constraints( ?Why, ?Isas, :TermGet1Get2) is det.
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




%% kif_add_boxes1( ?Why, ?List) is det.
%
% Knowledge Interchange Format Add Boxes Secondary Helper.
%
kif_add_boxes1(_,[]).
kif_add_boxes1(Why,List):- is_list(List),!,list_to_set(List,[H|T]),must_det_l((kif_add_boxes1(Why,H),kb_incr(Why,Why2),kif_add_boxes1(Why2,T))).
kif_add_boxes1(_,z_unused(_)):-!.
kif_add_boxes1(Why,AssertI):- must_det_l((simplify_bodies(AssertI,AssertO),kif_add_boxes3(save_wfs,Why,AssertO))).

:- thread_local(t_l:in_code_Buffer/3).





%% kif_add_boxes3( :PRED2How, ?Why, ?Assert) is det.
%
% Knowledge Interchange Format Add Boxes3.
%
kif_add_boxes3(How,Why,Assert):-
  must_det_l((
  boxlog_to_pfc(Assert,Prolog1),
  defunctionalize(Prolog1,Prolog2),
  kif_unnumbervars(Prolog2,PTTP),
  call(How,Why,PTTP))).




%% kif_unnumbervars( ?X, ?YY) is det.
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





%% simplify_bodies( ?B, ?BC) is det.
%
% Simplify Bodies.
%
simplify_bodies((H:- B),(H:- BC)):- must_det_l((conjuncts_to_list(B,RB),simplify_list(_KB,RB,BB),list_to_conjuncts(BB,BC))).
simplify_bodies((B),(BC)):- must_det_l((conjuncts_to_list(B,RB),simplify_list(_KB,RB,BB),list_to_conjuncts(BB,BC))).





%% simplify_list( ?KB, ?RB, ?BBS) is det.
%
% Simplify List.
%
simplify_list(KB,RB,BBS):- list_to_set(RB,BB),must_maplist(removeQ(KB),BB,BBO),list_to_set(BBO,BBS).




%% save_wfs( ?Why, ?PrologI) is det.
%
% Save Well-founded Semantics Version.
%
save_wfs(Why,PrologI):- must_det_l((baseKB:as_prolog_hook(PrologI,Prolog),
   locally(t_l:current_local_why(Why,Prolog),
   ain_h(save_in_code_buffer,Why,Prolog)))).




%% nots_to( ?H, ?To, ?HH) is det.
%
% Negations Converted To.
%
nots_to(H,To,HH):-subst_except(H,not,To,HH),subst_except(H,-,To,HH),subst_except(H,~,To,HH),subst_except(H, \+ ,To,HH),!.



%% neg_h_if_neg( ?H, ?HH) is det.
%
% Negated Head If Negated.
%
neg_h_if_neg(H,HH):-nots_to(H,'~',HH).



%% neg_b_if_neg( ?HBINFO, ?B, ?BBB) is det.
%
% Negated Backtackable If Negated.
%
neg_b_if_neg(HBINFO,B,BBB):-nots_to(B,'~',BB),sort_body(HBINFO,BB,BBB),!.





%% sort_body( ?HBINFO, ?BB, ?BBB) is det.
%
% Sort Body.
%
sort_body(HBINFO,BB,BBB):-sort_body_0(HBINFO,BB,BBB),(BBB=@=BB->true; (expand_to_hb(HBINFO,H,_),nop(dmsg([(H:-BB),'=>',(H:-BBB)])))).




%% sort_body_0( ?VALUE1, ?SORTED, ?SORTED) is det.
%
% sort body  Primary Helper.
%
sort_body_0(_,SORTED,SORTED):-leave_as_is_logically(SORTED).
sort_body_0(HBINFO,(A,B),SORTED):-!,conjuncts_to_list((A,B),List),
   must_maplist(sort_body_0(HBINFO),List,ListIn),
   predsort(litcost_compare(HBINFO),ListIn,SortedL),
   list_to_conjuncts(SortedL,SORTED).
sort_body_0(HBINFO,(A;B),SORTED):-!,disjuncts_to_list((A;B),List),
   must_maplist(sort_body_0(HBINFO),List,ListIn),
   predsort(litcost_compare(HBINFO),ListIn,SortedL),
   list_to_conjuncts((;),SortedL,SORTED).
sort_body_0(_,SORTED,SORTED).




%% litcost_compare( ?HBINFO, ?Comp, ?A, ?B) is det.
%
% Litcost Compare.
%
litcost_compare(_,=,A,B):- A=@=B,!.
litcost_compare(HBINFO,Comp,A,B):-lit_cost(HBINFO,A,AC),lit_cost(HBINFO,B,BC),compare(CompC,AC,BC),
  (CompC\== (=) -> CompC = Comp ; Comp = (<)).




%% lit_cost( ?HBINFO, ?A, :GoalAC) is det.
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




%% simp_code( ?A, ?A) is det.
%
% Simp Code.
%
simp_code(HB,(H:-BS)):-expand_to_hb(HB,H,B),conjuncts_to_list(B,BL),sort(BL,BS),!.
simp_code(A,A).





%% var_count_num( ?Term, ?SharedTest, ?SharedCount, ?UnsharedCount) is det.
%
% Variable Count Num.
%
var_count_num(Term,SharedTest,SharedCount,UnsharedCount):- term_slots(Term,Slots),term_slots(SharedTest,TestSlots),
  subtract(Slots,TestSlots,UnsharedSlots),
  subtract(Slots,UnsharedSlots,SharedSlots),
  length(SharedSlots,SharedCount),
  length(UnsharedSlots,UnsharedCount).




%% ain_h( :PRED2How, ?Why, ?H) is det.
%
% Assert If New Head.
%
ain_h(How,Why,(H:- B)):- neg_h_if_neg(H,HH), neg_b_if_neg((HH:- B),B,BB),!,call(How,Why,(HH:-BB)).
ain_h(How,Why,(H)):- neg_h_if_neg(H,HH), call(How,Why,(HH)).




%% save_in_code_buffer( ?VALUE1, ?HB) is det.
%
% Save In Code Buffer.
%
save_in_code_buffer(_ ,HB):- simp_code(HB,SIMP),t_l:in_code_Buffer(HB,_,SIMP),!.
save_in_code_buffer(Why,HB):- simp_code(HB,SIMP),assert(t_l:in_code_Buffer(HB,Why,SIMP)).




%% use_was_isa_h( ?I, :TermT, ?ISA) is det.
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



%% generate_ante( :TermARG1, :TermARG2, ?InOut, ?InOut) is det.
%
% Generate Ante.
%
generate_ante([],[],InOut,InOut).
generate_ante([I|VarsA],[T|VarsB],In,Isas):- use_was_isa_h(I,T,ISA), conjoin(In,ISA,Mid),generate_ante(VarsA,VarsB,Mid,Isas).




%% get_constraints( ?ListA, ?Isas) is det.
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

