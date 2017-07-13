/*  
% ===================================================================
% File 'mpred_type_constraints.pl'
% Purpose: For Emulation of OpenCyc for SWI-Prolog
% Maintainer: Douglas Miles
% Contact: $Author: dmiles $@users.sourceforge.net ;
% Version: 'interface' 1.0.0
% Revision:  $Revision: 1.9 $
% Revised At:   $Date: 2002/06/27 14:13:20 $
% ===================================================================
% File used as storage place for all predicates which change as
% the world is run.
%
%
% Dec 13, 2035
% Douglas Miles
*/
:- if(current_prolog_flag(lm_pfc_lean,false)).

% File: /opt/PrologMUD/pack/logicmoo_base/prolog/logicmoo/mpred/mpred_type_constraints.pl
%:- if(( ( \+ ((current_prolog_flag(logicmoo_include,Call),Call))) )).
:- module(mpred_type_constraints,
          [ add_dom/2,           
            arg_to_var/3,
            attempt_attribute_args/3,
            attempt_attribute_args/5,
            attempt_attribute_one_arg/4,
            attribs_to_atoms/2,
            attribs_to_atoms0/2,
            cmp_memberchk/2,
            cmp_memberchk0/2,
            comp_type/3,
            iz/2,
            extend_iz/2,
            extend_iz_member/2,
            init_iz/2,
            inst_dom/2,
            isa_pred_l/3,
            isa_pred_l/4,
            dom_chk/2,
            dom_call/2,
            domz_to_isa/2,
            map_subterms/3,
            max_dom/3,
            max_dom_l/2,
            mdif/2,
            min_dom/3,
            min_dom_l/2,
            promp_yn/2,
            same/2,
            same_arg/3,
            samef/2,
            to_functor/2,
            type_size/2,
            extract_conditions/2,
            
            unrelax/1, iz_member/1,

            lazy/1,lazy/2,

            constrain/1,enforce/1,mpred_functor/3,

            relax/1,relax_goal/2,thaw/1,
            mpred_type_constraints_file/0
          ]).

:- set_prolog_flag(generate_debug_info, true).
%:- include('mpred_header.pi').

% :- endif.



:- if(exists_source(library(multivar))).
:- use_module(library(multivar)).
:- endif.


:- meta_predicate 
   isa_pred_l(+,*,*),
   isa_pred_l(+,*,*,*),
   map_subterms(+,?,?),
   iz_member(*),
   constrain(*),
   map_lits(1,+),
   boxlog_goal_expansion(*,*),
   map_each_argnum(?,4,?,?,*),
   map_argnums(?,4,*),
   thaw(?),
   lazy(0),
   unrelax(*),
   relax_goal(*,+),
   lazy(+,0).

:- meta_predicate relax(*),relaxing(*).

:- kb_shared(baseKB:admittedArgument/3).

:- thread_local(t_l:no_kif_var_coroutines/1).

:- meta_predicate relaxed_call(0).

% ?- G=(loves(X,Y),~knows(Y,tHuman(X))),relax_goals(G,Out),writeq(Out).

:- meta_predicate map_plits(1,*).
map_lits(P1,Lit):- 
 locally($('$outer_stack')=[],once(map_plits(P1,Lit))),!.

map_plits(P1,Lit):- \+ compound(Lit),!,call(P1,Lit).
map_plits(P1,[Lit1 |  Lit2]):- !,map_plits(P1,Lit1),map_plits(P1,Lit2).
map_plits(P1,(Lit1 ,  Lit2)):- !,map_plits(P1,Lit1),map_plits(P1,Lit2).
map_plits(P1,(Lit1 ;  Lit2)):- !,map_plits(P1,Lit1),map_plits(P1,Lit2).
map_plits(P1,(Lit1 :- Lit2)):- !,map_lits(P1,Lit1),with_outer(Lit1,0,map_plits(P1,Lit2)).
map_plits(P1, Expr) :- demodalfy_outermost(+,Expr,MExpr,_Outer),!,
   with_outer(Expr,1,map_plits(P1, MExpr)).
map_plits(P1, Expr) :- Expr=..[C,I], tCol(C),!,map_plits(P1, isa(I,C)).
map_plits(P1, Expr) :- functor(Expr,F,A),mappable_sentence_functor(F,A), !, Expr =.. [F|Args],
  map_meta_lit(F,1,P1,Args).
map_plits(P1,Lit):- call(P1,Lit).

map_meta_lit(F,N,P1,[Arg|Args]):- !,
  with_outer(F,N,map_plits(P1, Arg)),
  N2 is N + 1,
  map_meta_lit(F,N2,P1,Args).
map_meta_lit(_,_,_,[]):-!.

with_outer(ExprF,N,Goal):- nb_current('$outer_stack',Was),
  locally($('$outer_stack')=[ExprF-N|Was],Goal).

closure_push(Closure,Data):- var(Closure),!,add_dom(Closure,Data).
closure_push(Closure,Data):- Closure=[true|_Rest],!,setarg(1,Closure,Data).
closure_push(Closure,Data):- Closure=[_First|Rest],!,setarg(2,Closure,[Data|Rest]).

constrain_arg_var(Closure,Arg,FA):- closure_push(Closure,add_dom(Arg,FA)).


%push_modal(neg(_)):- nb_current('$modal_stack',[neg(_)|Was]),!, b_setval('$modal_stack',Was).
%push_modal(Modal):- nb_current('$modal_stack',Was)->b_setval('$modal_stack',[Modal|Was]);b_setval('$modal_stack',[Modal,call]).
%last_modal(Modal):- nb_current('$modal_stack',[Modal|_])-> true; Modal=call.

map_argnums(_,_,Lit):- \+ compound(Lit), !.
map_argnums(Modal,P4,[Lit1 |  Lit2]):- !,map_argnums(Modal,P4,Lit1),map_argnums(Modal,P4,Lit2).
map_argnums(Modal,P4,isa(I,C)):- !,call(P4,Modal,C,0,I).
map_argnums(Modal,P4,Expr) :- demodalfy_outermost(Modal,Expr,MExpr,ModalValue),!,map_argnums(ModalValue,P4, MExpr).
map_argnums(Modal,P4,Expr) :- Expr=..[C,I], \+ (clause_b(argIsa(C,1,CC)),CC==C), clause_b(tCol(C)), !,map_argnums(Modal,P4,isa(I,C)).
map_argnums(Modal,P4,Expr) :- compound_name_arguments(Expr,F,Args),functor(Expr,F,A),
   (mappable_sentence_functor(F,A) -> map_argnums(Modal,P4,Args); map_each_argnum(Modal,P4,F,1,Args)).


map_each_argnum(Modal,P4,F,N,[Arg|Args]):- !,
   call(P4,Modal,F,N,Arg),
   N2 is N + 1,
   map_each_argnum(Modal,P4,F,N2,Args).
map_each_argnum(_Modal,_,_,_,_).


demodalfy_outermost(ModalIn,MExpr, Expr, ModalValue):-  MExpr=..[Modal,Expr], modal_value(ModalIn,Modal,ModalValue).
modal_value(neg(_), Neg , true):- arg(_,v( ( \+ ),'~','-','not'),Neg).
modal_value(_, Neg , neg(Neg)):- arg(_,v( ( \+ ),'~','-','not'),Neg).

mappable_sentence_functor(call,1).
mappable_sentence_functor(=,2):-!,fail.
mappable_sentence_functor(call_u,1).
mappable_sentence_functor(F,_):- downcase_atom(F,DC),upcase_atom(F,DC).
%mappable_sentence_functor(F,1):- \+ tCol(F).
%mappable_sentence_functor(F,A):- \+ argIsa(F,A,_).


compound_lit(Arg):- compound(Arg).

% ========================================================================
% enforce_bound(G)  = check constraints
% ========================================================================
:- export(enforce_bound/1).
enforce_bound(G):-args_enforce_bound(G,Closure),maplist(call,Closure).

:- during_boot(add_history(( 
  G=(loves(X,Y),~knows(Y,tHuman(X))),must(args_enforce_bound(G,Out)),writeq(Out)
   ))).

:- export(args_enforce_bound/2).
args_enforce_bound(G,Closure):- ignore(Closure=[true]),map_argnums(pos(_),args_enforce_bound3(Closure),G).

args_enforce_bound3(Closure,Modal,C,0,I):- !, ignore(( nonvar(I),
   (Modal\=pos(_)  -> closure_push(Closure,modal_isa(I,C)) ; closure_push(Closure,isa(I,C))))).
args_enforce_bound3(Closure,Modal,_F,_A,Arg):- compound_lit(Arg),!,map_argnums(Modal,args_enforce_bound3(Closure),Arg).
args_enforce_bound3(_Closure,_Modal,_F,_A,Arg):- var(Arg),!.
args_enforce_bound3(Closure,Modal,F,A,Arg):-args_enforce_nonvar(Closure,Modal,F,A,Arg).


% ========================================================================
% constrain(G)  = add constraints to free args
% ========================================================================
:- export(constrain/1).
constrain(G):-ground(G),!.
constrain(G):-args_constrain(G,Closure),maplist(call,Closure).

:- export(args_constrain/2).
:- during_boot(add_history(( 
  G=(loves(X,Y),~knows(Y,tHuman(X))),must(args_constrain(G,Out)),writeq(Out)
   ))).

args_constrain(G,Closure):- ignore(Closure=[true]),map_argnums(pos(_),args_constrains3(Closure),G).


args_constrains3(Closure,Modal,C,0,I):- !,
   (Modal\=pos(_)  -> constrain_arg_var(Closure,I,does_exist(I)) ; constrain_arg_var(Closure,I,isa(I,C))).
args_constrains3(Closure,Modal,_F,_A,Arg):- compound_lit(Arg),!,map_argnums(Modal,args_constrains3(Closure),Arg).
args_constrains3(_Closure,_Modal,_F,_A,Arg):- nonvar(Arg),!.
args_constrains3(Closure,Modal,F,A,Arg):-args_constrain_var(Closure,Modal,F,A,Arg).
   
:- export(does_exist/1).
does_exist(_).
modal_admittedArgument(F,1,V):-!,admittedArgument(F,1,V).
modal_admittedArgument(_,_,_).
% ========================================================================
% enforce(G)  = enforce_bound/1 + constrain/1
% ========================================================================
:- export(enforce/1).
enforce(G):-args_enforce(G,Closure),maplist(call,Closure).


:- during_boot(add_history(( 
  G=(loves(X,Y),~knows(Y,tHuman(X))),must(args_enforce(G,Out)),writeq(Out)
   ))).

:- export(args_enforce/2).
args_enforce(G,Closure):- ignore(Closure=[true]),map_argnums(pos(_),args_enforces3(Closure),G).

args_enforces3(Closure,Modal,C,0,I):- !,
   (Modal\=pos(_)  -> constrain_arg_var(Closure,I,does_exist(I)) ; constrain_arg_var(Closure,I,isa(I,C))).
args_enforces3(Closure,Modal,_F,_A,Arg):- compound_lit(Arg),!,map_argnums(Modal,args_enforces3(Closure),Arg).
args_enforces3(Closure,Modal,F,A,Arg):- var(Arg),!, args_constrain_var(Closure,Modal,F,A,Arg).
args_enforces3(Closure,Modal,F,A,Arg):- args_enforce_nonvar(Closure,Modal,F,A,Arg).
 


% ========================================================================
% remove_constraints(G)  = remove constraints 
% ========================================================================
remove_constraints(G):-args_remove_constraints(G,Closures),maplist(ignore,Closures).

:- export(args_remove_constraints/2).
:- during_boot(add_history(( 
                            G=(loves(X,Y),~knows(Y,tHuman(X))),args_enforce(G,Out),writeq(Out),
                            args_remove_constraints(G,Out2),writeq(Out2)
  
   ))).

args_remove_constraints(G,Closure):- ignore(Closure=[true]),map_argnums(pos(_),args_remove_constraints3(Closure),G).

args_remove_constraints3(Closure,_Modal,C,0,I):- !, transfer_constraints(Closure,I),transfer_constraints(Closure,C).
args_remove_constraints3(Closure,Modal,_F,_A,Arg):- compound_lit(Arg),!,map_argnums(Modal,args_remove_constraints3(Closure),Arg).
args_remove_constraints3(Closure,_Modal,_F,_A,Arg):- transfer_constraints(Arg,Closure).

transfer_constraints(Arg,Closure):- ignore((var(Arg),get_attr(Arg,iza,ToDo),del_attr(Arg,iza),
   maplist(constrain_arg_var(Closure,Arg),ToDo))).



%% args_constrain_var(?Closure, +Modal, +F, +A, +Arg) is det.
%
% Datalog Preconditional Expansion.
%
args_constrain_var(Closure,Modal,F,A,Arg):- (A==1 ; Modal=pos(_)),
    argIsa(F,A,Type),!,constrain_arg_var(Closure,Arg,isa(Arg,Type)).

args_constrain_var(Closure,Modal,F,A,Arg):- 
   (Modal\=pos(_)  ->
       constrain_arg_var(Closure,Arg,modal_admittedArgument(F,A,Arg)) ;
       constrain_arg_var(Closure,Arg,    admittedArgument(F,A,Arg))).

%% args_enforce_nonvar(?Closure, +Modal, +F, +A, +Arg) is det.
%
% Datalog Preconditional Expansion.
%
args_enforce_nonvar(Closure,Modal,F,A,Arg):-
   (Modal\=pos(_)  ->
       closure_push(Closure,modal_admittedArgument(F,A,Arg)) ;
       closure_push(Closure,    admittedArgument(F,A,Arg))).


%% extract_conditions( +PFCSentence, -Conds) is semidet.
%
% Datalog Preconditional Expansion.
%
extract_conditions(Sentence,Conds):- 
 copy_term(Sentence,Sentence,Goals),
 list_to_set(Goals,GoalSet),
 (Goals\==GoalSet-> dmsg(cons_odd) ; true),
 list_to_conjuncts(GoalSet,Conds),!.

%% boxlog_goal_expansion( ?G, ?GG) is semidet.
%
% Datalog Goal Expansion.
%
boxlog_goal_expansion(relax(G),GG):-!,relax_goal(G,GG).
%boxlog_goal_expansion(G,GG):-!,relax_goal(G,GG).
/* 
boxlog_goal_expansion(G,_):- % \+ source_location(_,_),
  wdmsg(g_s(G)),fail.
*/


is_iz_or_iza(Var):- get_attr(Var,iz,_);get_attr(Var,iza,_).

%% relax( :GoalG) is det.
%
% Relaxen.
%
relax(G):- map_lits(relax_lit,G).

relaxing(G):- term_attvars(G,Gs),notrace(relax(G)),term_attvars(G,Gs0),!,Gs0\==Gs.

relax_lit(G):- var(G),!.
relax_lit(_:G):-!,relax_lit(G).
relax_lit(G):- G=..[_|ARGS],relax_args(G,1,ARGS).


%% relaxed_call( :GoalG) is nondet.
%
%
relaxed_call(G):- relax(G), (G *-> unrelax(G) ; (unrelax(G),!,fail)).


%% relax_goal( :GoalG ) is det.
%
% Relaxen Goal.
%

relax_goal(G,GG):- copy_term(G,GG),relax(GG).


relax_goal_alt_old(G,GGG):-
  copy_term(G,GG,Gs),G=GG,G=..[_|ARGS],relax_args(GG,1,ARGS),   
  GGG=(GG,maplist(iz_member,Gs)).


%  ?- G=loves(a,b),relax_lit(G).
  




%% relax_N( ?G, ?N, ?A) is semidet.
%
% Relaxen Argument.
%
% % relax_N(G,N,Val):- var(Val),!,setarg(N,G,Val).
% % relax_N(G,N,Val):- iz(AA,[Val]),!,nb_setarg(N,G,AA).
relax_N(_,_,Val):- var(Val),!, ((get_attr(Val,iz,_);get_attr(Val,iza,_))->true;put_attr(Val,iz,[_])).
relax_N(G,N,Val):- dont_relax(Val)->true;(nb_setarg(N,G,NewVar),put_value(NewVar,Val)).

:- if(exists_source(library(multivar))).
% put_value(Var,Value):- multivar(Var),iz(Var,[Value]),mv_set1(Var,Value).

% put_value(Var,Value):- Var==Value,!.
put_value(Var,Value):- is_dict(Value,Tag),!,
     (Tag==Var->true;put_value(Var,Tag)),
     dict_pairs(Value,_Tag2,Pairs),
     maplist(put_value_attr(Var),Pairs).
put_value(Var,Value):- iz(Var,[Value]).

put_value_attr(Var,N-V):- put_attr_value(Var,N,V).
put_attr_value(Var,iza,V):- !, add_dom(Var,V).
put_attr_value(Var,iz,V):- !, iz(Var,V).
put_attr_value(Arg,Name,FA):- as_constraint_for(Arg,FA,Constraint),!,put_attr_value0(Arg,Name,Constraint).

put_attr_value0(Var,Name,HintE):- 
  (get_attr(Var,Name,HintL) -> min_dom(HintE,HintL,Hint); Hint=[HintE]), !,
   put_attr(Var,Name,Hint).



:- else.
 put_value(Var,Value):- iz(Var,[Value]).
:- endif.

dont_relax(A):- var(A),!,is_iz_or_iza(A).
dont_relax(A):- \+ compound(A), \+ atom(A), \+ string(A).

%% relax_args( ?G, ?N, :TermA) is semidet.
%
% Relaxen Arguments.
%
relax_args(G,N,[A|RGS]):-relax_N(G,N,A),!,N2 is N + 1,relax_args(G,N2,RGS).
relax_args(_,_,[]).


:- use_module(user:library(clpfd)).		% Make predicates defined
:- use_module(user:library(clpr),except([{}/1])).		% Make predicates defined
:- use_module(user:library(simplex)).		% Make predicates defined

:- meta_predicate lazy_pfa(0,+,*).
:- meta_predicate #(0).
'#'(G):- map_lits(lazy,G).

%% lazy( :GoalG) is semidet.
%
% Lazy.
%
lazy(G):- var(G),!,freeze(G,lazy(G)).
lazy(G):- ground(G),!,call(G).
lazy(is(X,G)):- !,clpr:{X =:= G}.
% lazy(is(X,G)):-!,term_variables(G,Vs),lazy(Vs,is(X,G)).
lazy(G):- functor(G,F,A),lazy_pfa(G,F,A).

arithmetic_compare(=<).
arithmetic_compare(=:=).
arithmetic_compare(:=).
arithmetic_compare(<).
arithmetic_compare(>=).
arithmetic_compare(>).

lazy_pfa(G,F,2):- arithmetic_compare(F),!,clpr:{G}.
lazy_pfa(G,_,1):- term_variables(G,[V1|Vs1]),!,
      (Vs1 = [V2|Vs0] -> lazy([V1,V2|Vs0],G)
                      ; freeze(V1,G)).
lazy_pfa(G,_,_):- term_variables(G,[V1|Vs1]),
      (Vs1 = [V2|Vs0] -> lazy([V1,V2|Vs0],G)
                      ; freeze(V1,G)).

%% lazy( ?V, :GoalG) is semidet.
%
% Lazy.
%
lazy([V],G):- !, freeze(V,G).
%lazy([V|Vs],G):- or_any_var([V|Vs],C)->when(C,lazy(G)).
lazy([V|Vs],G):- !, lazy(Vs,freeze(V,G)).
lazy(_,G):- call(G).


or_any_var([V],nonvar(V)).
or_any_var([V|Vs],(nonvar(V);C)):-or_any_var(Vs,C).

% test  lazy(isa(X,Y)),!,X=tCol,melt(Y).

%% thaw( ?G) is semidet.
%
% Thaw.
%
thaw(G):- call_residue_vars(G,Vs),maplist(melt,Vs).


%% melt( ?G) is semidet.
%
% melt.
%
melt(V):-frozen(V,G),call(G).


%% inst_dom( ?X, ?List) is semidet.
%
% Inst Isac.
%
inst_dom(X, List):- predsort(comp_type,List,SList),dom_call(X,SList).

% An attributed variable with attribute value DVar has been
% assigned the value Y

iza:attr_unify_hook(DVar, Y):-
   ( get_attr(Y, iza, Dom2)
   -> ord_union(DVar, Dom2, NewDomain),
   ( (fail,NewDomain == [])
   -> fail
   ; (fail,NewDomain = [Value])
   -> Y = Value
   ; put_attr(Y, iza, NewDomain)
   )
   ; var(Y)
   -> put_attr( Y, iza, DVar )
   ;  dom_chk(Y,DVar)).

iza:attr_unify_hook(ArgIsas,Value):- dom_chk(Value,ArgIsas).


% Translate attributes from this module to residual goals
iza:attribute_goals(X) -->
      { get_attr(X, iza, List) },!,
      [add_dom(X, List)].

%% add_dom( ?Var, ?HintE) is semidet.
%
% Add Iza.
%
as_constraint_for(Arg,isa(AArg,FA),FA):- atom(FA),AArg==Arg,!.
as_constraint_for(Arg,ISA,FA):- ISA=..[FA,AArg],AArg==Arg,!.
as_constraint_for(_,FA,FA).



add_dom(Arg,FA):- as_constraint_for(Arg,FA,Constraint),!,add_dom0(Arg,Constraint).
add_dom0(Var,HintE):- var(Var),
  (get_attr(Var,iza,HintL) ->min_dom(HintE,HintL,Hint);Hint=[HintE]), !,
   put_attr(Var,iza,Hint).
add_dom0(Var,Hint):- ignore(show_failure(why,dom_call(Var,Hint))).



%% dom_chk( ?E, ?Cs) is semidet.
%
% Isac Checking.
%
dom_chk(_,_):- t_l:no_kif_var_coroutines(G),!,call(G).
dom_chk(E,Cs):- once(dom_call(E,Cs)).


%% dom_call( ?VALUE1, :TermARG2) is semidet.
%
% Isac Gen.
%
dom_call(Y, [H|List]):- !,dom_call0(Y,H),dom_call(Y, List).
dom_call(_, _).

dom_call0(Y,H):- atom(H),!,isa(Y,H).
dom_call0(Y,H):- arg(_,H,E),Y==E,!,call_u(H),!.
dom_call0(Y,H):- ereq(props(Y,H)).

/*
enforce_fa_unify_hook([Goal|ArgIsas],Value):- !,
  enforce_fa_call(Goal,Value),
  enforce_fa_unify_hook(ArgIsas,Value).
enforce_fa_unify_hook(_,_).

enforce_fa_call(Goal,Value):- atom(Goal),!,call(Goal,Value).
enforce_fa_call(Goal,Value):- arg(_,Goal,Var),Var==Value,!,call(Goal).
enforce_fa_call(Goal,Value):- prepend_arg(Goal,Value,GVoal),!,call(GVoal).

prepend_arg(M:Goal,Value,M:GVoal):- !, prepend_arg(Goal,Value,GVoal).
prepend_arg(Goal,Value,GVoal):- Goal=..[F|ARGS],GVoal=..[F,Value|ARGS].
*/

/*

 G=(loves(X,Y),~knows(Y,tHuman(X))),args_enforce(G,Out),maplist(call,Out).

*/


%% attribs_to_atoms( ?ListA, ?List) is semidet.
%
% Attribs Converted To Atoms.
%
attribs_to_atoms(ListA,List):-map_subterms(attribs_to_atoms0,ListA,List).




%% map_subterms( :PRED2Pred, ?I, ?O) is semidet.
%
% Map Subterms.
%
map_subterms(Pred,I,O):-is_list(I),!,maplist(map_subterms(Pred),I,O).
map_subterms(Pred,I,O):-call(Pred,I,O),!.
map_subterms(Pred,I,O):-compound(I),!,I=..IL,maplist(map_subterms(Pred),IL,OL),O=..OL.
map_subterms(_Pred,IO,IO).




%% domz_to_isa( :TermAA, :TermAB) is semidet.
%
% iza Converted To  (iprops/2).
%
domz_to_isa(Iza,ftTerm):-var(Iza),!.
domz_to_isa((A,B),isAnd(ListO)):-!,conjuncts_to_list((A,B),List),list_to_set(List,Set),min_dom_l(Set,ListO).
domz_to_isa((A;B),isOr(Set)):-!,conjuncts_to_list((A,B),List),list_to_set(List,Set).
domz_to_isa(AA,AB):-must(AA=AB).




%% attribs_to_atoms0( ?Var, ?Isa) is semidet.
%
% Attribs Converted To Atoms Primary Helper.
%
attribs_to_atoms0(Var,Isa):-get_attr(Var,iza,Iza),!,must(domz_to_isa(Iza,Isa)).
attribs_to_atoms0(O,O):- \+ (compound(O)).


%% min_dom_l( ?List, ?ListO) is semidet.
%
% min  (sub_super/2) (List version).
%
min_dom_l(List,ListO):-isa_pred_l(lambda(Y,X,sub_super(X,Y)),List,ListO).



%% max_dom_l( ?List, ?ListO) is semidet.
%
% max  (sub_super/2) (List version).
%
max_dom_l(List,ListO):-isa_pred_l(sub_super,List,ListO).



%% isa_pred_l( :PRED2Pred, ?List, ?ListO) is semidet.
%
%  (iprops/2) Predicate (List version).
%
isa_pred_l(Pred,List,ListO):-isa_pred_l(Pred,List,List,ListO).




%% isa_pred_l( :PRED2Pred, ?UPARAM2, ?List, ?UPARAM4) is semidet.
%
%  (iprops/2) Predicate (List version).
%
isa_pred_l(_Pred,[],_List,[]).
isa_pred_l(Pred,[X|L],List,O):-member(Y,List),X\=Y,call_u(call(Pred,X,Y)),!,isa_pred_l(Pred,L,List,O).
isa_pred_l(Pred,[X|L],List,[X|O]):-isa_pred_l(Pred,L,List,O).




%% min_dom( :TermHintA, ?HintE, ?HintE) is semidet.
%
% min  (sub_super/2).
%
min_dom([H],In,Out):- !, min_dom0(H,In,Out).
min_dom([H|T],In,Out):- !, min_dom0(H,In,Mid),min_dom(T,Mid,Out).
min_dom(E,In,Out):- min_dom0(E,In,Out).

min_dom0(HintA,[],[HintA]).
min_dom0(HintA,[HintB|HintL],[HintB|HintL]):- HintA==HintB,!.
min_dom0(HintA,[HintB|HintL],[HintA,HintB|HintL]):- functor(HintA,_,A),functor(HintB,_,B),B>A,!.
min_dom0(HintA,[HintB|HintL],[HintA|HintL]):- sub_super(HintA,HintB),!.
min_dom0(HintA,[HintB|HintL],[HintB|HintL]):- sub_super(HintB,HintA),!.
min_dom0(HintA,[HintB|HintL],[HintB|HintS]):- !,min_dom0(HintA,HintL,HintS).



sub_super(Col1,Col2):- tCol(Col1),!,genls(Col1,Col2).

%% max_dom( :TermHintA, ?HintE, ?HintE) is semidet.
%
% max  (sub_super/2).
%
max_dom([H],In,Out):- !, max_dom0(H,In,Out).
max_dom([H|T],In,Out):- !, max_dom0(H,In,Mid),max_dom(T,Mid,Out).
max_dom(E,In,Out):- max_dom0(E,In,Out).

max_dom0(HintA,[],[HintA]).
max_dom0(HintA,[HintB|HintL],[HintB|HintL]):- HintA==HintB,!.
max_dom0(HintA,[HintB|HintL],[HintA,HintB|HintL]):- functor(HintA,_,A),functor(HintB,_,B),B>A,!.
max_dom0(HintA,[HintB|HintL],[HintA|HintL]):- sub_super(HintB,HintA),!.
max_dom0(HintA,[HintB|HintL],[HintB|HintL]):- sub_super(HintA,HintB),!.
max_dom0(HintA,[HintB|HintL],[HintB|HintS]):- !,max_dom0(HintA,HintL,HintS).





:- style_check(-singleton).




%% unrelax( ?X) is semidet.
%
% Domain Labeling (residuals).
%
unrelax(X):-copy_term(X,X,Gs),maplist(iz_member,Gs).




%% iz_member( :GoalG) is semidet.
%
% Domain Member.
%
iz_member(iz(X,List)):-!,member(X,List).
iz_member(G):-G.


:- style_check(-singleton).

%% attempt_attribute_args( ?AndOr, ?Hint, :TermVar) is semidet.
%
% Attempt Attribute Arguments.
%

attempt_attribute_args(_AndOr,Hint,Var):- var(Var),add_dom(Var,Hint),!.
attempt_attribute_args(_AndOr,_Hint,Grnd):-ground(Grnd),!.
attempt_attribute_args(_AndOr,_Hint,Term):- \+ (compound(Term)),!.
attempt_attribute_args(AndOr,Hint,+(A)):-!,attempt_attribute_args(AndOr,Hint,A).
attempt_attribute_args(AndOr,Hint,-(A)):-!,attempt_attribute_args(AndOr,Hint,A).
attempt_attribute_args(AndOr,Hint,?(A)):-!,attempt_attribute_args(AndOr,Hint,A).
attempt_attribute_args(AndOr,Hint,(A,B)):-!,attempt_attribute_args(AndOr,Hint,A),attempt_attribute_args(AndOr,Hint,B).
attempt_attribute_args(AndOr,Hint,[A|B]):-!,attempt_attribute_args(AndOr,Hint,A),attempt_attribute_args(AndOr,Hint,B).
attempt_attribute_args(AndOr,Hint,(A;B)):-!,attempt_attribute_args(';'(AndOr),Hint,A),attempt_attribute_args(';'(AndOr),Hint,B).
attempt_attribute_args(_AndOr,_Hint,Term):- use_was_isa(Term,I,C), add_dom(I,C).
attempt_attribute_args(AndOr,_Hint,Term):- Term=..[F,A],tCol(F),!,attempt_attribute_args(AndOr,F,A).
attempt_attribute_args(AndOr,Hint,Term):- Term=..[F|ARGS],!,attempt_attribute_args(AndOr,Hint,F,1,ARGS).




%% attempt_attribute_args( ?AndOr, ?Hint, ?F, ?N, :TermARG5) is semidet.
%
% Attempt Attribute Arguments.
%
attempt_attribute_args(_AndOr,_Hint,_F,_N,[]):-!.
attempt_attribute_args(AndOr,_Hint,t,1,[A]):-attempt_attribute_args(AndOr,callable,A).
attempt_attribute_args(AndOr,Hint,t,N,[A|ARGS]):-atom(A),!,attempt_attribute_args(AndOr,Hint,A,N,ARGS).
attempt_attribute_args(_AndOr,_Hint,t,_N,[A|_ARGS]):- \+ (atom(A)),!.
attempt_attribute_args(AndOr,Hint,F,N,[A|ARGS]):-attempt_attribute_one_arg(Hint,F,N,A),N2 is N+1,attempt_attribute_args(AndOr,Hint,F,N2,ARGS).




%% attempt_attribute_one_arg( ?Hint, ?F, ?N, ?A) is semidet.
%
% Attempt Attribute One Argument.
%
attempt_attribute_one_arg(_Hint,F,N,A):-call_u(argIsa(F,N,Type)),Type\=ftTerm, \+ (compound(Type)),!,attempt_attribute_args(and,Type,A).
attempt_attribute_one_arg(_Hint,F,N,A):-call_u(argQuotedIsa(F,N,Type)),Type\=ftTerm, \+ (compound(Type)),!,attempt_attribute_args(and,Type,A).
attempt_attribute_one_arg(_Hint,F,N,A):-call_u(argIsa(F,N,Type)),Type\=ftTerm,!,attempt_attribute_args(and,Type,A).
attempt_attribute_one_arg(_Hint,F,N,A):-attempt_attribute_args(and,argi(F,N),A).



% mdif(A,B):- tlbugger:attributedVars,!,dif(A,B).



%% mdif( ?A, ?B) is semidet.
%
% Mdif.
%
mdif(A,B):-A\==B.

:- was_export((samef/2,same/2)).



%% same( ?X, ?Y) is semidet.
%
% Same.
%
same(X,Y):- samef(X,Y),!.
same(X,Y):- compound(X),arg(1,X,XX)->same(XX,Y),!.
same(Y,X):- compound(X),arg(1,X,XX),!,same(XX,Y).




%% samef( ?X, ?Y) is semidet.
%
% Samef.
%
samef(X,Y):- quietly(((to_functor(X,XF),to_functor(Y,YF),(XF=YF->true;string_equal_ci(XF,YF))))).




%% to_functor( ?A, ?O) is semidet.
%
% Converted To Functor.
%
to_functor(A,O):-is_ftVar(A),!,A=O.
to_functor(A,O):-compound(A),get_functor(A,O),!. % ,to_functor(F,O).
to_functor(A,A).

:- was_export(arg_to_var/3).



%% arg_to_var( ?Type, ?String, ?Var) is semidet.
%
% Argument Converted To Variable.
%
arg_to_var(_Type,_String,_Var).

:- was_export(same_arg/3).




%% same_arg( ?How, ?X, ?Y) is semidet.
%
% Same Argument.
%
same_arg(_How,X,Y):-var(X),var(Y),!,X=Y.
same_arg(equals,X,Y):-!,equals_call(X,Y).
same_arg(tCol(_Type),X,Y):-!, unify_with_occurs_check(X,Y).

same_arg(ftText,X,Y):-(var(X);var(Y)),!,X=Y.
same_arg(ftText,X,Y):-!, string_equal_ci(X,Y).

same_arg(same_or(equals),X,Y):- same_arg(equals,X,Y).
same_arg(same_or(sub_super),X,Y):- same_arg(equals,X,Y).
same_arg(same_or(sub_super),Sub,Sup):- holds_t(sub_super,Sub,Sup),!.
same_arg(same_or(isa),X,Y):- same_arg(equals,X,Y).
same_arg(same_or(isa),I,Sup):- !, holds_t(Sup,I),!.

same_arg(same_or(_Pred),X,Y):- same_arg(equals,X,Y).
same_arg(same_or(Pred),I,Sup):- holds_t(Pred,I,Sup),!.

% same_arg(I,X):- promp_yn('~nSame Objects: ~q== ~q ?',[I,X]).



%% promp_yn( ?Fmt, ?A) is semidet.
%
% Promp Yn.
%
promp_yn(Fmt,A):- format(Fmt,A),get_single_char(C),C=121.



:- export(mpred_functor/3).
mpred_functor(Pred,Pred,A):-var(Pred),!,between(1,9,A).
mpred_functor(F/A,F,A):-!,probably_arity(F,A).
mpred_functor(_:Pred,F,A):-!,mpred_functor(Pred,F,A).
mpred_functor(F,F,A):-atom(F),!,probably_arity(F,A).
mpred_functor(Pred,F,A):-functor_safe(Pred,F,A).

probably_arity(F,A):-(integer(A)->true;(arity(F,A)*->true;between(1,9,A))).



% :-swi_module(iz, [ iz/2  ]). % Var, ?Domain
:- use_module(library(ordsets)).

%% iz( ?X, ?Dom) is semidet.
%
% Domain.
%
:- was_export(iz/2).

iz(X, Dom) :-
      var(Dom), !,
      get_attr(X, iz, Dom).
iz(X, List) :- 
      listify(List,List0),
      list_to_ord_set(List0, Domain),
      put_attr(Y, iz, Domain),
      X = Y.

:- was_export(extend_iz_member/2).



%% extend_iz_member( ?X, ?DomL) is semidet.
%
% Extend Domain.
%
extend_iz_member(X, DomL):- init_iz(X, Dom2), ord_union(Dom2, DomL, NewDomain),put_attr( X, iz, NewDomain ).

:- was_export(extend_iz/2).



%% extend_iz( ?X, ?DomE) is semidet.
%
% Extend Domain.
%
extend_iz(X, DomE):-  init_iz(X, Dom2),ord_add_element(Dom2, DomE, NewDomain),put_attr( X, iz, NewDomain ).

:- was_export(init_iz/2).



%% init_iz( ?X, ?Dom) is semidet.
%
% Init Domain.
%
init_iz(X,Dom):-get_attr(X, iz, Dom),!.
init_iz(X,Dom):-Dom =[_], put_attr(X, iz, Dom),!.

% An attributed variable with attribute value Domain has been
% assigned the value Y

iz:attr_unify_hook([Y], Value) :-  same(Y , Value),!.
iz:attr_unify_hook(Domain, Y) :-
   ( get_attr(Y, iz, Dom2)
   -> ord_intersection(Domain, Dom2, NewDomain),
         ( NewDomain == []
         -> fail
         ; NewDomain = [Value]
          -> same(Y , Value)
             ; put_attr(Y, iz, NewDomain)
           )
   ; var(Y)
   -> put_attr( Y, iz, Domain )
   ; (\+ \+ (cmp_memberchk(Y, Domain)))
).



% Translate attributes from this module to residual goals
iz:attribute_goals(X) --> { get_attr(X, iz, List) },!,[iz(X, List)].



%iz:attr_portray_hook(Val, _) :- write('iz:'), write(Val),!.

%iza:attr_portray_hook(Val, _) :- write('iza:'), write(Val),!.


%% cmp_memberchk( ?X, ?Y) is semidet.
%
% Cmp Memberchk.
%
cmp_memberchk(X,Y):-numbervars(X,0,_,[attvars(skip)]),member(X,Y),!.



%% cmp_memberchk0( ?Item, :TermX1) is semidet.
%
% Cmp Memberchk Primary Helper.
%
cmp_memberchk0(Item, [X1,X2,X3,X4|Xs]) :- !,
	compare(R4, Item, X4),
	(   R4 = (>) -> cmp_memberchk0(Item, Xs)
	;   R4 = (<) ->
	    compare(R2, Item, X2),
	    (   R2 = (>) -> Item = X3
	    ;   R2 = (<) -> Item = X1
	    ;/* R2 = (=),   Item = X2 */ true
	    )
	;/* R4 = (=) */ true
	).
cmp_memberchk0(Item, [X1,X2|Xs]) :- !,
	compare(R2, Item, X2),
	(   R2 = (>) -> cmp_memberchk0(Item, Xs)
	;   R2 = (<) -> Item = X1
	;/* R2 = (=) */ true
	).
cmp_memberchk0(Item, [X1]) :-
	Item = X1.



%% type_size( ?VALUE1, :PRED1000VALUE2) is semidet.
%
% Type Size.
%
type_size(C,S):-a(completeExtentEnumerable,C),!,setof(E,t(C,E),L),length(L,S).
type_size(C,1000000):-a(ttExpressionType,C),!.
type_size(_,1000).

/*

?-  Z #=:= 2 + X, Z #< 2 .

succ(succ(0)).

S2I
I2E

2
2
2
E2S

S = succ/1.
I = integer
E = 2

a:p(1).

a:p(X):-b:p(X).
b:p(X):-c:p(X).

b:p(2).

*/ 


%% comp_type( ?Comp, ?Col1, ?Col2) is semidet.
%
% Comp Type.
%
comp_type(Comp,Col1,Col2):-type_size(Col1,S1),type_size(Col2,S2),compare(Comp,S1,S2).


:- fixup_exports.

mpred_type_constraints_file.


%% goal_expansion( ?LC, ?LCOO) is semidet.
%
% Hook To [system:goal_expansion/2] For Module Mpred_type_constraints.
% Goal Expansion.
%
% system:goal_expansion(G,O):- \+ current_prolog_flag(xref,true),\+ pldoc_loading, nonvar(G),boxlog_goal_expansion(G,O).

:- endif.

