/* <module>
% =============================================
% File 'system_common.pfc'
% Purpose: Agent Reactivity for SWI-Prolog
% Maintainer: Douglas Miles
% Contact: $Author: dmiles $@users.sourceforge.net ;
% Version: 'interface' 1.0.0
% Revision: $Revision: 1.9 $
% Revised At: $Date: 2002/06/27 14:13:20 $
% =============================================
%
%  PFC is a language extension for prolog.. there is so much that can be done in this language extension to Prolog
%
%
% props(Obj,[height(ObjHt)]) == t(height,Obj,ObjHt) == rdf(Obj,height,ObjHt) == t(height(Obj,ObjHt)).
% pain(Obj,[height(ObjHt)]) == prop_set(height,Obj,ObjHt,...) == ain(height(Obj,ObjHt))
% [pdel/pclr](Obj,[height(ObjHt)]) == [del/clr](height,Obj,ObjHt) == [del/clr]svo(Obj,height,ObjHt) == [del/clr](height(Obj,ObjHt))
% keraseall(AnyTerm).
%
%                      ANTECEEDANT                                   CONSEQUENT
%
%         P =         test nesc true                         assert(P),retract(~P) , enable(P).
%       ~ P =         test nesc false                        assert(~P),retract(P), disable(P)
%
%   ~ ~(P) =         test possible (via not impossible)      retract( ~(P)), enable(P).
%  \+ ~(P) =         test impossiblity is unknown            retract( ~(P))
%   ~ \+(P) =        same as P                               same as P
%     \+(P) =        test naf(P)                             retract(P)
%
% Dec 13, 2035
% Douglas Miles
*/

% :- require('system_base.pfc').

:- use_module(library(rtrace)).
:- mpred_unload_file.
:- begin_pfc.
:- '$set_source_module'(baseKB).
:- prolog_load_context(module,Mod),sanity(Mod==baseKB),writeq(prolog_load_context(module,Mod)),nl.


:- % better stack traces..
 set_prolog_flag(access_level,system).

arity(genlPreds,2).

:- dynamic(mpred_undo_sys/3).
pfcControlled(mpred_undo_sys(ftAssertion, ftCallable, ftCallable)).
mpred_undo_sys(P, WhenAdded, WhenRemoved) ==> (P ==> {WhenAdded}), mpred_do_and_undo_method(WhenAdded,WhenRemoved).

% DONT mpred_undo_sys(added(P),ain(P),mpred_retract(P)).
% mpred_undo_sys(asserted(P),assert_eq_quitely(PE),retract_eq_quitely(PE)):-expand_goal(P,PE).

% 
comment(isa,"Instance of").

~(tCol(genlPreds)).

~(singleValuedInArg(arity,2)).
~(prologSingleValued(arity)).
~(prologSingleValued(support_hilog)).

~(arity(argIsa,1)).
arity(pddlObjects,2).

prologHybrid(genls/2).


/*
:- 
 With = kb_shared, % [multifile,kb_shared,discontiguous],
 with_pfa(With,((logical_functor_pttp/1, pfcControlled/1, pfcRHS/1,  conflict/1,   argsQuoted/1,     add_args/15,argIsa_known/3,call_mt_t/11))),

% with_pfa(With,((( call_which_t/9,constrain_args_pttp/2,contract_output_proof/2,get_clause_vars_for_print/2,holds_f_p2/2,input_to_forms/2,is_wrapper_pred/1,lambda/5,mpred_f/1,
%          pp_i2tml_now/1,pp_item_html/2,pttp1a_wid/3,pttp_builtin/2,pttp_nnf_pre_clean_functor/3,quasiQuote/1,relax_term/6,retractall_wid/1,ruleRewrite/2,search/7,support_hilog/2,svar_fixvarname/2)))),

% with_pfa(With,((pfcControlled/1,pfcRHS/1,logical_functor_pttp/1,          add_args/15,argIsa_known/3,call_mt_t/11,call_which_t/9,constrain_args_pttp/2,contract_output_proof/2,get_clause_vars_for_print/2,holds_f_p2/2,input_to_forms/2,is_wrapper_pred/1,lambda/5,mpred_f/1,pp_i2tml_now/1,pp_item_html/2,pttp1a_wid/3,pttp_builtin/2,pttp_nnf_pre_clean_functor/3,
%          quasiQuote/1,relax_term/6,retractall_wid/1,ruleRewrite/2,search/7,support_hilog/2,svar_fixvarname/2,rtNotForUnboundPredicates/1))),
 with_pfa(With,(((bt/2),(nt/3),(pk/3),(pt/2),(spft/3),(tms/1),(hs/1),(que/2),(pm/1),
          (('==>')/1),(('::::')/2),(('<-')/2),(('<==>')/2),(('==>')/2),(('~')/1),(('nesc')/1),
 ((mpred_action)/1),
          (mpred_do_and_undo_method/2), 
*/
/*
	  prologMultiValued/1,prologOrdered/1,prologNegByFailure/1,prologPTTP/1,prologKIF/1,pfcControlled/1,ttRelationType/1,
           prologHybrid/1,predCanHaveSingletons/1,prologDynamic/1,prologBuiltin/1,functorIsMacro/1,prologListValued/1,prologSingleValued/1,
          (hs/1),(pfcControlled/1),(prologDynamic/2),(prologSideEffects/1),(prologSingleValued/1),(singleValuedInArg/2),(prologSideEffects/1,
          functorIsMacro/1,pfcControlled/1,
           resolveConflict/1,resolverConflict_robot/1)))),
 with_pfa(With,((mpred_isa/2,arity/2,predicateConventionMt/2))),
 with_pfa(With,((vtColor/1))).
 */

:-  multifile((disjointWith/2,genls/2,isa/2,argIsa/3)).
:-  dynamic((disjointWith/2,genls/2,isa/2,argIsa/3)).
:- discontiguous((disjointWith/2,genls/2,isa/2,argIsa/3,typeGenls/2)).

% :- autoload.



/*
 %  % :- debug_logicmoo(_).
:- nodebug_logicmoo(http(_)).
:- debug_logicmoo(logicmoo(_)).
:- mpred_trace_exec.
:- begin_pfc.

*/

% remove conflicts early 
% (~(P)/mpred_non_neg_literal(P) ==> ( {mpred_remove(P)}, (\+P ))).


/*
Unneeded yet

% These next 2 might be best as builtins?
((~(P)/(mpred_non_neg_literal(P),copy_term(P,PP))) ==> \+ PP ).
% (P/mpred_non_neg_literal(P) ==> (\+ ~(P))).
% ((P/(mpred_non_neg_literal(P),copy_term(P,PP))) ==> (~ ~ PP )).

% :- nortrace,quietly.
% a pretty basic conflict (disabled for now)
%(~(P)/mpred_non_neg_literal(P), P) ==> conflict(~(P)).
(~(P)/mpred_non_neg_literal(P), P) ==> conflict(~(P)).
%(P/mpred_non_neg_literal(P), ~(P)) ==> conflict(P).

*/

%:- rtrace,dtrace.
%==>(prologBuiltin(mpred_select_hook/1)).
% :- nortrace,quietly.

:- kb_shared(conflict/1).
% a conflict triggers a Prolog action to resolve it.
conflict(C) ==> {must(with_mpred_trace_exec((resolveConflict(C),\+conflict(C))))}.

:- kb_shared(ttTypeType/1).

% meta rules to schedule inferencing.
% resolve conflicts asap
mpred_select_hook(conflict(X)) :- que(conflict(X),_Why).

:- dynamic(rtUnaryPredicate/1).
:- dynamic(ttExpressionType/1).

tSet(completelyAssertedCollection).


%% prologBuiltin( ?ARG1, ?ARG2) is semidet.
%
% Prolog Builtin.
%
%WRONG prologBuiltin(resolveConflict/1,predicateConventionMt(baseKB)).
%WRONG prologBuiltin(mpred_select_hook/1,predicateConventionMt(baseKB)).
%:-rtrace.



% IN =@=> OUT  ==> 

==>prologBuiltin(agent_text_command/4,prologDynamic).

%tPred(t,prologDynamic).

% tPred(member/2,prologBuiltin).

tSet(rtNotForUnboundPredicates).


tCol(vtVerb).

:- sanity(fileAssertMt(baseKB)).
:- sanity(defaultAssertMt(baseKB)).

ttRelationType(rtNotForUnboundPredicates).
rtNotForUnboundPredicates(member/2).

%and(A,B):- cwc, call_u((A,B)).
%or(A,B):- cwc, call_u((A;B)).


:- fully_expand(==>pkif("
(=> 
    (and 
      (typeGenls ?COLTYPE1 ?COL1) 
      (typeGenls ?COLTYPE2 ?COL2) 
      (disjointWith ?COL1 ?COL2)) 
    (disjointWith ?COLTYPE1 ?COLTYPE2))"
),
O),dmsg(O).

==>pkif("
(=> 
    (and 
      (typeGenls ?COLTYPE1 ?COL1) 
      (typeGenls ?COLTYPE2 ?COL2) 
      (disjointWith ?COL1 ?COL2)) 
    (disjointWith ?COLTYPE1 ?COLTYPE2)) "
).


/*
?- isa(iExplorer2,W),
*/

% ===================================================================
% Type checker system / Never Assert / Retraction checks
% ===================================================================

(sometimesTypeCheck, typeCheckDecl(Each,Must), Each, {\+ Must}) ==> failed_typeCheckDecl(Each,Must).

failed_typeCheckDecl(Each,Must)==>{trace_or_throw(failed_typeCheckDecl(Each,Must))}.

never_assert_u(vtVerb(BAD),vtVerbError):-fail,BAD=='[|]'.
never_assert_u(prologSingleValued(BAD),var_prologSingleValued(BAD)):-is_ftVar(BAD).

never_assert_u(baseKB:mtProlog(baseKB),must(mtCycL(baseKB))).
never_assert_u(meta_argtypes(tSet(ftAssertable)),badRules).


never_assert_u(A,test_sanity(A)):- never_assert_u(A).



:- kb_shared(never_retract_u/2).
never_retract_u(~(X),is_ftVar(X)):- cwc, is_ftVar(X).
never_retract_u(A,test_sanity(A)):- cwc, never_retract_u(A).
never_retract_u(X,is_ftVar(X)):- cwc, is_ftVar(X).
never_retract_u(human(trudy),sanity_test).
never_retract_u(tHumanHair(skRelationAllExistsFn(mudSubPart, skRelationAllExistsFn(mudSubPart, skRelationAllExistsFn(mudSubPart, iExplorer1, tHumanBody), tHumanHead), tHumanHair)),sanity_test).
never_retract_u((father(skArg1ofFatherFn(trudy), trudy)),sanity_test).
never_retract_u(argQuotedIsa(thereExistAtLeast, 1, ftPositiveInteger),sanity_test).
% P/never_assert_u(P,Why) ==> conflict(never_assert_u(P,Why))

prologHybrid(arity/2).
prologDynamic(is_never_type/1).
prologDynamic(term_expansion/2).
prologBuiltin(var/1).

completelyAssertedCollection(completelyAssertedCollection).
completelyAssertedCollection(C)==>tCol(C).

% A Type Specification
completelyAssertedCollection(tCol).  % a type is a type
completelyDecidableCollection(ftSpec). % A specification is sort of a type
completelyDecidableCollection(ftTerm).

:- multifile ftSpec/1.
:- dynamic ftSpec/1.
:- discontiguous ftSpec/1.
tCol(ftSpec).
ttExpressionType(ftSpec).
~meta_argtypes(ftSpec(ftString)). % A string may not be considered a legal specification
functorForFtSpec(prologEquality).

resultIsa(_F,C)/ground(C)==>ftSpec(C).
argsQuoted(argsQuoted).
argsQuoted(ftSpec).
ftSpec(vtActionTemplate).
argsQuoted(vtActionTemplate).

% ftSpec(ftSpec).
% meta_argtypes(ftSpec)
meta_argtypes(ftSpec(ftSpec)).  % An argtype specification is considered to be a legal specification

genls(ttExpressionType, ftSpec).

genls(tCol, ftSpec).
probablyRedundant ==> meta_argtypes(ftSpec(tCol)).  % A typeclass is considered to be a legal specification

~tIndividual(tIndividual).

pfcControlled(P),arity(P,A)==>hybrid_support(P,A).

ttRelationType(X)==>tCol(X).
ttRelationType(X)/atom(X)==>(arity(X,1),pfcControlled(X)).

tSet(ttExpressionType).


% tCols are either syntactic or existential
completelyAssertedCollection(ttExpressionType).  % syntactic
completelyAssertedCollection(tSet). % existential

%ttExpressionType(T)==>completelyDecidableCollection(T).

% relations are predsor functions
completelyAssertedCollection(tRelation).
completelyAssertedCollection(tPred).
completelyAssertedCollection(tFunction).

completelyAssertedCollection(functorIsMacro).  % Items read from a file might be a special Macro Head
completelyAssertedCollection(ttRelationType).  % Or they might be a predciate declarer
% completelyAssertedCollection(functorDeclares).  % or they might declare other things
% completelyAssertedCollection(functorIsMacro).  % or they might declare other things



completelyAssertedCollection(functorIsMacro).

completelyAssertedCollection(tPred).
~completelyAssertedCollection(meta_argtypes).
completelyAssertedCollection(tTemporalThing).
completelyAssertedCollection(tInferInstanceFromArgType).
completelyAssertedCollection(ttNotTemporalType).
completelyAssertedCollection(ttSpatialType).
completelyAssertedCollection(ttTemporalType).
completelyAssertedCollection(ttTypeType).
completelyAssertedCollection(ttUnverifiableType).


%% prologNegByFailure( ?VALUE1) is semidet.
%
% Prolog Negated By Failure.
%
prologNegByFailure(prologNegByFailure).
prologNegByFailure(quotedIsa/3).
~prologNegByFailure(isa/2).

:- listing( ~ / 1).

:- dynamic(baseKB:ttTypeType/1).

ttTypeType(C)==>completelyAssertedCollection(C).


someTimesBuggy2ndOrder ==>
((someTimesBuggy2ndOrder,genlPreds(C1,C2),arity(C1,2)) ==>
  {P1 =.. [C1,X,Y],
    P2 =.. [C2,X,Y]},
  clif(P1 => P2)).

someTimesBuggy2ndOrder ==>
((genlPreds(C1,C2),arity(C1,3)) ==>
  {P1 =.. [C1,X,Y,Z],
    P2 =.. [C2,X,Y,Z]},
  clif(P1 => P2)).

tCol(tCol).  % = isa(tCol,tCol).
tCol(tSet).

(genls(C,SC)==>(tCol(C),tCol(SC))).

% tSet(C)/(atom(C),TCI=..[C,I]) ==> (arity(C,1),mpred_univ(C,I,TCI), ... )


% :- prolog.
% tPred


==>
completelyAssertedCollection(isEach(tCol,tPred,pfcControlled)).
ttRelationType(C)==>completelyAssertedCollection(C).

% ~genls(meta_argtypes,ftSpec).

:- dynamic(baseKB:mudWielding/2).

prologMultiValued(P)==> \+ prologSingleValued(P).
prologSingleValued(P)==> \+ prologMultiValued(P).

~(ttExpressionType(prologEquality)).
ttRelationType(prologEquality).
prologEquality(mudEquals/2).
prologEquality(('=')/2).
prologEquality(('==')/2).

arity(',',2).

~(isa((','), prologEquality)).

==>tSet(isEach(tCol,tPred,pfcControlled)).

rtQuotedPred(meta_argtypes).
rtQuotedPred(functorIsMacro).
rtQuotedPred(functorDeclares).

pfcControlled(genlPreds).
pfcControlled(isa).
pfcControlled(argIsa).


%tCol(X) ==> isa(X,tCol).
%tCol(X) ==> ruleRewrite(t(X,I),isa(I,X)).

(~tCol(T),tCol(T))==> conflict(~tCol(T)).

%typeProps(tCoffeeCup,[mudColor(vBlack),mudColor(isEach(vBrown,vBlack)),mudSize(vSmall),mudShape(vCuplike),mudMaterial(vGlass),mudTexture(vSmooth)]).
%props(iCoffeeCup7,[mudColor(vBlack),mudColor(isEach(vBrown,vBlack)),mudSize(vSmall),mudShape(vCuplike),mudMaterial(vGlass),mudTexture(vSmooth)]).

:- sanity(get_lang(pfc)).

% tCol(C)/(\+ never_isa_syntax(C))==>{decl_as_isa(C)}.

%underkill - Though it is making bad things happen 
ttExpressionType(C)==> \+ completelyAssertedCollection(C).

tSet(rtNotForUnboundPredicates).
tSet(tPred).
tSet(prologBuiltin).
tSet(tFunction).
tSet(tRelation).
tSet(ttTemporalType).
tSet(functorIsMacro).

:- install_constant_renamer_until_eof.

==>ttModule(tSourceCode,mudToCyc('ComputerCode'),comment("Source code files containing callable features")).
==>ttModule(tSourceData,mudToCyc('PropositionalInformationThing'),comment("Source data files containing world state information")).

==> prologHybrid(isLoadedType(ttModule),pfcControlled).
==> prologHybrid(isLoaded(tMicrotheory),pfcControlled).

isLoaded(Thing),isa(Thing,ModType), \+ ttExpressionType(ModType) ==> isLoadedType(ModType).

pfcControlled(prologArity(tRelation,ftInt)).
pfcControlled(isa(ftTerm,tCol)).

tSet(tSet).
tSet(tCol).
tSet(ttModule).
tFixedArityRelation(tSet).
tFixedArityRelation(tCol).
ttRelationType(prologHybrid).

:- check_clause_counts.

%:- rtrace,trace.
%:- notrace, nortrace.



prologHybrid(mudToCyc(ftTerm,ftTerm)).

:- must(arity(mudToCyc,2)).

% col_as_isa(X)==>tFixedArityRelation(X),arity(X,1).
col_as_unary(X)==>tFixedArityRelation(X),arity(X,1).

tSet(ttExpressionType).
tSet(completelyAssertedCollection).


ttExpressionType(C) ==> ( \+ completelyAssertedCollection(C), ~ tSet(C), tCol(C)).


:- sanity(get_lang(pfc)).
%WEIRD ~(tCol(C))/completelyAssertedCollection(C)==> \+ completelyAssertedCollection(C).
% EASIER
% ~tCol(C) ==> ~completelyAssertedCollection(C).
% (tCol(C),\+ ttExpressionType(C)) ==> tSet(C).
% ((tCol(P), \+ ttExpressionType(P)) <==> tSet(P)).

tSet(C) ==>
({((
  % 
  % dynamic(C/1),
  % wdmsg(c_tSet(C)),  
  %call((shouldnt_be_set(C) -> (show_failure(mpred_why(tSet(C))),
  %   show_failure(mpred_why(tCol(C))),break) ; true)),
  atom(C),
  %\+ ttExpressionType(C),
  ( \+ is_static_predicate(C/1)),
  functor(Head,C,1),
  call(BHead=baseKB:Head),
  ( \+(predicate_property(BHead,_))-> kb_shared(C/1); true),
  baseKB:export(baseKB:C/1),
  mpred_type_isa:import(baseKB:C/1),
  nop(predicate_property(BHead,dynamic)->true;show_pred_info(BHead))))},
  functorDeclares(C),
  pfcControlled(C),
  \+ ttExpressionType(C),
  tCol(C),
  arity(C,1)).



/*
tSet(C)==>
 ( {atom(C), functor(Head,C,1), call(BHead=baseKB:Head),
   ( \+(predicate_property(BHead,_))-> kb_shared(C/1); true),
    nop(predicate_property(BHead,dynamic)->true;show_pred_info(BHead))},
   functorDeclares(C),
   pfcControlled(C),
   arity(C,1)).
*/


/*
tSet(C)/(atom(C),TCI=..[C,I]) ==> (arity(C,1),
 % mpred_univ(C,I,TCI),
 {call_u((decl_type(C), 
  ignore((
   \+ is_static_predicate(C/1),
   kb_shared(C/1),
   \+ completelyAssertedCollection(C),
   call_u(ain((
   ((TCI :- 
    ((cwc, call_u((
      predicate_property(TCI,number_of_rules(1)),
    lazy(( \+ call_u(~(TCI)))),
    isa_backchaing(I,C))))))))))))))}).


*/
/*
ttExpressionType(P) ==> 
 {get_functor(P,F), functor(Head,F,1), call(BHead=baseKB:Head),
  call((\+ predicate_property(BHead,defined) -> kb_shared(F/1); true)),
  call((predicate_property(BHead,dynamic)->(ain(Head==>{ignore(retract(Head))}));show_pred_info(BHead)))},
  ~functorIsMacro(F),
  ~functorDeclares(F),
  ~tSet(F),
  notAssertibleCollection(F),
  tCol(F),
  completelyDecidableCollection(F),
  arity(F,1).
*/

%:- mpred_trace_exec.

tSet(tKnownID).
% :- xlisting(tKnownID).
%?- isa(tKnownID,W).
%:- break.

:- mpred_notrace_exec.

% (tInferInstanceFromArgType(Col),tCol(Col)/i_name('',Col,ColName),tPred(Prop)/i_name('',Prop,PropName),{ColName=PropName}==> tInferInstanceFromArgType(Prop)).

% (tInferInstanceFromArgType(Prop),tPred(Prop),arity(Prop,N)/(N>1) ==> ({i_name('vt',Prop,FinalType)},tCol(FinalType),tInferInstanceFromArgType(FinalType),argIsa(Prop,N,FinalType))).

prologSideEffects(write/1).
prologSideEffects(resolveConflict/1).



/*
((hybrid_support(F,A)/(is_ftNameArity(F,A), \+ prologDynamic(F),\+ is_static_predicate(F/A))) ==>
  ({    
    functor(G,F,A),
     (var(M)->must(defaultAssertMt(M));true),
     (var(M)->ignore(( current_predicate(F,M:G), \+ predicate_property(M:G,imported_from(_))));true),
     (var(M)->predicate_property(M:G,exported);true),
     % must(rebuild_pred_into(G,G,ain,[+dynamic,+multifile,+discontiguous])),         
     % (predicate_property(M:G,dynamic)->true;must(convert_to_dynamic(M,F,A))),
     kb_shared(M:F/A),
     show_failure(hybrid_support, \+ is_static_predicate(F/A))}),
     prologHybrid(F),
    arity(F,A)).
*/


arity(functorIsMacro,1).

functorIsMacro(functorIsMacro).
ttRelationType(X)==>functorDeclares(X).
% tCol(X)==>functorDeclares(X).
% functorDeclares(X)==>tCol(X).
% functorIsMacro(X)==>functorDeclares(X).
functorIsMacro(pddlSomethingIsa/2).
tPred(pddlSomethingIsa(ftTerm,ftListFn(tCol))).

/*
prologBuiltin(A) :- cwc,head_to_functor_name(A, B),prologBuiltin(B).
prologBuiltin(P) :- cwc,is_ftCompound(P),!,get_functor(P,F,A),functor(C,F,A),(predicate_property(C,built_in)). % predicate_property(P,static)).
ttRelationType(PT)==> {atom(PT),H=..[PT,I]}, (H:-cwc,head_to_functor_name(I,F),call_u(call(PT,F))).
*/


tCol(iExplorer4)==>{trace_or_throw(never_tCol(iExplorer4))}.

==> isa(pddlSomethingIsa/2, prologHybrid).

arity(argIsa,3).


% prologHybrid(F/A)/(atom(F),number(A)) ==> arity(F,A),{must(dynamic_safe(F/A))}.

%:-mpred_trace_exec.

% Functions
hardCodedExpansion ==> ((tFunction(ArgTypes)/is_declarations(ArgTypes)) ==> meta_argtypes(ArgTypes),{get_functor(ArgTypes,F)}, tFunction(F)).
% FormatTypes
hardCodedExpansion ==> (ttExpressionType(ArgTypes)/is_declarations(ArgTypes) ==> meta_argtypes(ArgTypes)).

argIsa(completeExtentAsserted,1,tPred).

((meta_argtypes(ArgTypes)/(is_ftCompound(ArgTypes))) ==> 
   ({get_functor(ArgTypes,F,A),A>1},arity(F,A),{arg(N,ArgTypes,Type)},argIsa(F,N,Type))).


meta_argtypes(predicateConventionMt(tPred,tMicrotheory)).
meta_argtypes(argIsa(tRelation,ftInt,tCol)).

:- mpred_run.
:- mpred_notrace_exec.

:- must(argIsa(predicateConventionMt,1,tPred)).
:- must(argIsa(predicateConventionMt,2,tMicrotheory)).

functorIsMacro(tCol).


tCol(tCol).
tCol(tSet).

rtQuotedPred(meta_argtypes).
rtQuotedPred(functorIsMacro).
rtQuotedPred(functorDeclares).
tCol(prologMultiValued).
tCol(prologSingleValued).
tCol(tFunction).
tCol(tInferInstanceFromArgType).
tCol(tPred).
tCol(tRelation).
tCol(ttSpatialType).
ttTypeType(ttTypeType).
ttTypeType(C)==>tSet(C).
ttTypeType(ttAgentType).

:- must(tSet(ttAgentType)).

tCol(tWorld).

completelyAssertedCollection(prologSingleValued).
completelyAssertedCollection(tCol).
completelyAssertedCollection(ttExpressionType).
completelyAssertedCollection(ttValueType).
completelyAssertedCollection(ttTemporalType).
completelyAssertedCollection(tRelation).
completelyAssertedCollection(tPred).

% completelyAssertedCollection(C)==>completeExtentAsserted(C).

completelyAssertedCollection(completeExtentAsserted).
completeExtentAsserted(completelyAssertedCollection).
completelyAssertedCollection(completelyAssertedCollection).
completeExtentAsserted(functorDeclares).
completeExtentAsserted(completeExtentAsserted).
arity(completeExtentAsserted,1).

% tSet(completeExtentAsserted).
argIsa(completeExtentAsserted,1,tPred).
meta_argtypes(genlPreds(tPred,tPred)).
:- must_det(argIsa(genlPreds,2,_)).
completeExtentAsserted(defnSufficient).


:- kb_shared(ttNotTemporalType/1).
ttNotTemporalType(ftInt).
%ttNotTemporalType(ftTerm).
ttNotTemporalType(tCol).
ttNotTemporalType(ttExpressionType).
ttNotTemporalType(ttValueType).

==>ttNotTemporalType(tCol).
ttNotTemporalType(T)==>tCol(T).
==>ttTemporalType(tTemporalThing).
ttTemporalType(T)==>tCol(T).

arity(argQuoted,1).





% (isa(Inst,Type), tCol(Inst)) ==> isa(Type,ttTypeType).


(ttExpressionType(FT),{is_ftCompound(FT)})==>meta_argtypes(FT).

tSet(vtDirection).

:- sanity(get_lang(pfc)).

disjointWith(tPred,tFunction).

disjointWith(ttTemporalType,ttAbstractType).
disjointWith(Sub, Super) ==> disjointWith( Super, Sub).

(rtSymmetric(Pred) ==> ({atom(Pred),G1=..[Pred,X,Y],G2=..[Pred,Y,X]}, (G1==>G2), (~(G1)==> ~(G2)))).


tSet(rtNotForUnboundPredicates).

prologSideEffects(P)==>rtNotForUnboundPredicates(P).

isa(tRelation,ttAbstractType).




:- if(baseKB:startup_option(datalog,sanity);baseKB:startup_option(clif,sanity)).

:- reconsult(pack(logicmoo_base/t/examples/pfc/'neg_sanity.pfc')).


:- endif. % load_time_sanity


%P/(is_ftNonvar(P),get_functor(P,F)),afterAdding(F,Do)/is_ftNonvar(Do)==>{call(Do,P)}.
%~P/(is_ftNonvar(P),get_functor(P,F)),afterRemoving(F,Do)/is_ftNonvar(Do)==>{call(Do,P)}.




%:-rtrace.
% (tCol(Inst), {isa_from_morphology(Inst,Type)}) ==> (isa(Inst,Type)).

% HOW TO MAKE THIS FAST?  isa(Inst,Type) <= {isa_from_morphology(Inst,Type)}.

%((disjointWith(P1,P2) , genls(C1,P1), {dif:dif(C1,P1)}) ==>    disjointWith(C1,P2)).
% (disjointWith(C1,P2) <= (genls(C1,P1), {dif:dif(C1,P1)}, disjointWith(P1,P2))).

tSet(completelyAssertedCollection).
rtQuotedPred(completeIsaAsserted/1).
% genls(completeIsaAsserted,tTemporalThing).
genls(A,B)==>(arity(A,1),arity(B,1)).
genls(completelyAssertedCollection,tCol).
completelyAssertedCollection(completelyAssertedCollection).
completelyAssertedCollection(tPred).
completelyAssertedCollection(tRelation).
completelyAssertedCollection(ttExpressionType).
completelyAssertedCollection(tCol).
completelyAssertedCollection(functorIsMacro).
% completelyAssertedCollection(functorDeclares).
completelyAssertedCollection(ttRelationType).
completelyAssertedCollection(completelyAssertedCollection).

% dividesBetween(S,C1,C2) ==> (disjointWith(C1,C2) , genls(C1,S) ,genls(C2,S)).

% disjointWith(P1,P2) ==> ((~(isa(C,P1))) <==> isa(C,P2)).

% isa(Col1, ttObjectType) ==> ~(isa(Col1, ttExpressionType)).


% tCol(ArgsIsa):-ttRelationType(ArgsIsa).
% TODO decide if OK
%tCol(F):-t(functorDeclares,F).
tSet(ttExpressionType).


:- install_constant_renamer_until_eof.

genls(ttSpatialType,ttTemporalType).
genls(tSpatialThing,tTemporalThing).




% remove conflicts early 
% (~(P)/mpred_non_neg_literal(P) ==> ( {mpred_remove(P)}, (\+P ))).

tSet(ttTypeFacet).
==>tCol(rtAvoidForwardChain, comment("rtAvoidForwardChain means that backchain is required for subclasses 
     to gain membership TODO: Give example "
     )).

tCol('tThing').
arity('tThing',1).
% genls(ttExpressionType,rtAvoidForwardChain).
isa('tThing',rtAvoidForwardChain).

%isa('CycLTerm',rtAvoidForwardChain).
prologHybrid(quotedIsa(ftTerm,ttExpressionType)).

:- kb_shared(quotedIsa/2).

/*
  ftSpec
  tCol
 ttFormatType | tCol
*/

mainClass(I,C)==>isa(I,C).

not_isa(I,C):- cwc, mainClass(I,MC),disjointWith(MC,DC),genls(C,DC).

% isa(I,C):- cwc, is_ftNonvar(C),ttExpressionType(C),!,quotedIsa(I,C).
%isa(I,C):- cwc, tCol(C),(ttExpressionType(C)*->quotedIsa(I,C);loop_check(isa_backchaing(I,C))).
%isa(I,C):- cwc, tSet(C),(ttExpressionType(C)*->quotedIsa(I,C)).
% isa(I,C):- cwc, when(?=(I,C),\+ clause_b(isa(I,C))), (loop_check(visit_pred(I,C))*->true;loop_check(no_repeats(isa_backchaing(I,C)))).
%isa(I,C):- cwc, loop_check(visit_pred(I,C)).
%isa(I,C):- cwc, loop_check(visit_isa(I,C)).

isa([tIndividual(tSack)],C):-C==ftListFn(ftAskable),!.
isa(iExplorer2,C):- C==argsQuoted,!,fail.
:- asserta((isa(I,C):- ground(I:C),not_isa(I,C),!,fail)).
% isa(I,C):- cwc, no_repeats(loop_check(isa_backchaing(I,C))).
% isa(_,C):- nonvar(C),\+ tSet(C),!,fail.

quotedIsa(_,C):- nonvar(C), tSet(C),!,fail.
quotedIsa(I,C):- cwc, loop_check(term_is_ft(I,C)).

dif_in_arg(P,N,Q):- cwc, ground(P),P=..[F|ARGS],arg(N,P,B),Q=..[F|ARGS],nb_setarg(N,Q,A),dif(A,B).

tSet(ttSpatialType).
tSet(tSpatialThing).
completelyAssertedCollection(ttTypeType).
completelyAssertedCollection(tCol).



:- kb_shared(isa/2).

ttRelationType(Prop)==>tCol(Prop).



%:-baseKB:agenda_slow_op_enqueue(ain(((arity(Pred,2),argIsa(Pred,1,Col)/(is_ftNonvar(Pred),Col\=ftTerm,tCol(Col)), \+prologSideEffects(Pred), t(Pred,Arg,_)/is_ftNonvar(Arg)) ==> t(Col,Arg)))).
%:-baseKB:agenda_slow_op_enqueue(ain(((arity(Pred,2),argIsa(Pred,2,Col)/(is_ftNonvar(Pred),Col\=ftTerm,tCol(Col)), \+prologSideEffects(Pred), t(Pred,_,Arg)/is_ftNonvar(Arg)) ==> t(Col,Arg)))).
%:-add_slow(((arity(Pred,2),argIsa(Pred,2,Col)/(is_ftNonvar(Pred),Col\=ftTerm,tCol(Col)),t(Pred,_,Arg)/is_ftNonvar(Arg)) ==> t(Col,Arg))).
%(((P/(has_functor(P),get_functor(P,F,A),A\=2,\+prologSideEffects(F),mpred_literal(P)) ==> {baseKB:agenda_slow_op_enqueue(deduceEachArgType(P))}))).

% :-rtrace.

%((((P/(nonvar(P),is_ftNonvar(P),functor(P,F,A), \+ mpred_connective(F), A>1) ==> 
%   {baseKB:agenda_slow_op_enqueue(must(ignore(deduceEachArgType(P))))})))).


% tCol(Col) <==> isa(Col,tCol).


%(disjointWith(P1,P2) , genls(C1,P1)) ==>    disjointWith(C1,P2).
disjointWith(Sub, Super) ==> disjointWith( Super, Sub).
disjointWith(ttTemporalType,ttAbstractType).

prologHybrid(typeGenls/2).
:- ain(meta_argtypes(typeGenls(ttTypeType,tCol))).
%(isa(COLTYPEINST,COLTYPE) , typeGenls(COLTYPE,COL)) ==> genls(COLTYPEINST,COL).

typeGenls(ttRelationType,tPred).


prologHybrid(argIsa/3).

:- asserta(t_l:pfcExpansion).





%% argIsa( ?F, ?N, ?Type) is semidet.
%
% asserted Argument  (isa/2) known.
%
argIsa(F/_,N,Type):- nonvar(F),!,argIsa(F,N,Type).
argIsa(F,N,Type):- var(F),!,tRelation(F),argIsa(F,N,Type).
argIsa(F,N,Type):- var(N),arity_no_bc(F,A),!,system_between(1,A,N),argIsa(F,N,Type).
argIsa(F,1,F):- tCol(F), arity_no_bc(F,1),!.
% Managed Arity Predicates.
argIsa(Pred,N,ftVoprop) :- number(N),arity_no_bc(Pred,A),N>A,!.

==>argIsa(isEach(arity,arityMax,arityMin),2,ftInt).

/*
argIsa(F,_,ftTerm):-member(F/_, [argIsa/3,predProxyAssert/2,negate_wrapper0/2,mudFacing/_,registered_module_type/2,       
                                ruleBackward/2,formatted_resultIsa/2, pt/_,rhs/_,nt/_,bt/_,bracket/3]),!.
argIsa(Prop,N1,Type):- is_2nd_order_holds(Prop),dmsg(todo(define(argIsa(Prop,N1,'Second_Order_TYPE')))),dumpST,dtrace,Type=argIsaFn(Prop,N1),!.
*/
/*
$mycont.set({V1=$a.value,V2=$b.value}/(VarIn)>>writeln(my_cont(V1,V2,VarIn))).
writeln($mycont).
*/

:- kb_shared(mpred_f/5).
:- kb_shared(mpred_f/6).
:- kb_shared(mpred_f/4).
:- kb_shared(mpred_f/7).

% :- rtrace.
%% argQuotedIsa( ?F, ?N, ?FTO) is semidet.
%
% Argument  (isa/2) Format Type.
%
:- kb_shared(argQuotedIsa/3).
prologHybrid(argQuotedIsa(tRelation,ftInt,ttExpressionType)).

((prologHybrid(F),arity(F,A))==>{kb_shared(F/A)}).
:- listing(argQuotedIsa/3).
%:- break.
% argQuotedIsa(F/_,N,Type):-nonvar(F),!,argQuotedIsa(F,N,Type).
argQuotedIsa(F,N,FTO):- argIsa(F,N,FT), must(to_format_type(FT,FTO)),!.
:- nortrace.

:- was_export(argIsa/3).

%= 	 	 

%% argIsa( ?F, ?N, ?Type) is semidet.
%
% Argument  (isa/2) call  Primary Helper.
%
argIsa(argIsa,1,tRelation).
argIsa(argIsa,2,ftInt).
argIsa(argIsa,3,tCol).  
argIsa(comment,2,ftString).
argIsa(isKappaFn,1,ftVar).
argIsa(isKappaFn,2,ftAskable).
%argIsa(isInstFn,1,tCol).


argIsa(quotedDefnIff,1,ftSpec).
argIsa(quotedDefnIff,2,ftCallable).
argIsa(meta_argtypes,1,ftSpec).


argIsa(isa,2,tCol).
argIsa(mpred_isa,1,tPred).
argIsa(mpred_isa,2,ftVoprop).
% argIsa(mpred_isa,3,ftVoprop).

argIsa(formatted_resultIsa,1,ttExpressionType).
argIsa(formatted_resultIsa,2,tCol).

argIsa(predicates,1,ftListFn(ftTerm)).
argIsa(resultIsa,2,tCol).

argIsa(predTypeMax,1,tPred).
argIsa(predTypeMax,2,tCol).
argIsa(predTypeMax,3,ftInt).

argIsa(predInstMax,1,tObj).
argIsa(predInstMax,2,tPred).
argIsa(predInstMax,3,ftInt).

argQuotedIsa(props,1,ftID).
argIsa(props,N,ftVoprop):- integer(N), system_between(2,31,N).

argIsa(apathFn,1,tRegion).
argIsa(apathFn,2,vtDirection).
argIsa(localityOfObject,1,tObj).
argIsa(localityOfObject,2,tSpatialThing).

argIsa(typeProps,1,tCol).
argIsa(typeProps,N,ftVoprop):-system_between(2,31,N).

argIsa(instTypeProps,1,ftProlog).
argIsa(instTypeProps,2,tCol).
argIsa(instTypeProps,N,ftVoprop):-system_between(3,31,N).


argIsa(must,1,ftCallable).

argsIsa(F,Type),arity(F,A),{system_between(1,A,N)}==>argIsa(F,N,Type).

argIsa(predicateConventionMt,1,tPred).
argIsa(predicateConventionMt,2,ftAtom).
% argIsa(baseKB:agent_text_command,_,ftTerm).
argIsa('<=>',_,ftTerm).
argIsa(class_template,N,Type):- (N=1 -> Type=tCol;Type=ftVoprop).
==>argIsa(isEach(descriptionHere,mudDescription,nameString,mudKeyword),2,ftString).

% argQuotedIsa(F,N,Type)==>argIsa(F,N,Type).

% argQuotedIsa(F,N,Type):- functorDeclares(F),(N=1 -> Type=F ; Type=ftVoprop).
%argIsa(F,N,Type):- t(tCol,F),!,(N=1 -> Type=F ; Type=ftVoprop).
:- sanity(listing(argQuotedIsa/3)).

/*
{source_file(M:P,_),functor(P,F,A),
  \+ predicate_property(M:P,imported_from(_))} 
   ==> functor_module(M,F,A).
:- show_count(functor_module/3).
*/

:- dynamic(functor_module/3).
argsQuoted(functor_module).

({current_module(M),
 (predicate_property(functor_module(_,_,_),
   clause_count(N)),N<1000),current_predicate(M:F/A),functor(P,F,A), 
  \+ predicate_property(M:P,imported_from(_))}) 
   ==> functor_module(M,F,A).

functor_module(_,F,A)==> arity(F,A).


:- show_count(arity/2).

(functor_module(M,F,A),
  {functor(P,F,A),predicate_property(M:P,static)})==>
  (predicateConventionMt(F,M),mpred_prop(F,A,prologBuiltin)).

(functor_module(M,F,A),
  {functor(P,F,A), predicate_property(M:P,meta_predicate(P)), 
  system_between(1,A,N),arg(N,P,Number),number(Number)}) 
       ==> argIsa(F,N,ftAskable).

(functor_module(M,F,A),
  {functor(P,F,A), predicate_property(M:P,meta_predicate(P)), 
  system_between(1,A,N),arg(N,P,0)}) 
       ==> argIsa(F,N,ftAskable).



%= 	 	 

%% argsIsa( ?WP, ?VALUE2) is semidet.
%
% Argument  (isa/2) call Helper number 3..
%
==>argsIsa(isEach(predProxyRetract,predProxyAssert,predProxyQuery,genlInverse),tPred).
argsIsa(disjointWith,tCol).
argsIsa(ftFormFn,ftTerm).
argsIsa(mudTermAnglify,ftTerm).
argsIsa(genls,tCol).
argsIsa(subFormat,ttExpressionType).










/*
:- ain(((vtActionTemplate(ArgTypes)/is_declarations(ArgTypes) ==> vtActionTemplate(ArgTypes)))).
:- ain(((baseKB:action_info(ArgTypes,_)/is_declarations(ArgTypes) ==> vtActionTemplate(ArgTypes)))).
:- ain(((functorIsMacro(Compound)/compound_functor(Compound,F)) ==> functorDeclares(F))).
hardCodedExpansion ==> ((ttExpressionType(FT)/is_declarations(FT))==>meta_argtypes(FT)).


*/

disjointWith(tCol,tIndividual).
% :- noguitracer.
%:- rtrace.

codeTooSlow,
  arity(F,A)/(atom(F),\+ is_sentence_functor(F),number(A),A>1,A<10,functor(P,F,A),\+ rtLogicalConnective(F)), 
  \+ meta_argtypes_guessed(P),   
   (argIsa(F,A,NOTFT)/NOTFT\==ftTerm),
   (argIsa(F,1,NOTFT2)/NOTFT2\==ftTerm),
 {generateArgVars(P, argIsa(F), '='(_))}
==> meta_argtypes_guessed(P).

meta_argtypes_guessed(P)==>meta_argtypes(P).
   
:- if(baseKB:startup_option(datalog,sanity);baseKB:startup_option(clif,sanity)).


% :- if_startup_script(locally(t_l:pfcExpansion,ensure_loaded(mpred_i_mpred_mpred_testing))).

% :-asserta(baseKB:isa_pred_now_locked).


% :-loadTinyAssertions1.

%:-prolog_repl.
%:-showTinyAssertions.
%:-prolog_repl.
%:-loadTinyAssertions2.


:- endif.

:- meta_predicate(~(0)).
:- kb_shared(~(0)).

:- kb_shared(predicateConventionMt/2).
:- decl_mpred(predicateConventionMt/2).

meta_argtypes(predicateConventionMt(tPred,tMicrotheory)).


prologHybrid(predicateConventionMt, 2).
prologMultiValued(predicateConventionMt(tRelation,ftAtom)).

hardCodedExpansion ==> (prologHybrid(Compound)/get_arity(Compound,F,A)==>{kb_shared(F/A)}).

% pddlObjects(Type,EList)==>  isa(isEach(EList),Type).
% pddlSorts(Type,EList)==> genls(isEach(EList),Type).


:- kb_shared(argIsa/3).

:- decl_mpred(argIsa/3).

/*
prologBuiltin(col_arity/2).
col_arity(Spec,A):-arity(Spec,A),!.
col_arity(Spec,A):-atom(Spec),!,A=1.
col_arity(Spec,A):-compound(Spec),functor(Spec,_,A).
isa(Spec,tCol)/col_arity(Spec,A) ==> arity(Spec,A).
*/

% :-ain((mpred_isa(I,C)==>{ain((isa(I,tPred),mpred_isa(I,C),props(I,[C])))})).
% :-ain((t(C,I)==>{ /* retract(hasInstance_dyn(C,I)), */ ain((isa(I,C))) , ain((props(I,C)))})).


% :-include('mpred_header.pi').
tSet(tPred).

:- must(assert_argIsa(tPred,1,tPred)).


/*
% reflexive equality
equal(A,B) ==> equal(B,A).
equal(A,B),{ \+ (A=B}),equal(B,C),{ \+ (A=C)} ==> equal(A,C).

notequal(A,B) ==> notequal(B,A).
equal(A,C),notequal(A,B) ==> notequal(C,B).
*/

:- dynamic(either/2).
% is this how to define constraints?
% either(P,Q) ==> (~(P) ==> Q), (~(Q) ==> P).
(either(P,Q) ==> ((~(P) <==> Q), (~(Q) <==> P))).
% ((P,Q ==> false) ==> (P ==> ~(Q)), (Q ==> ~(P))).


:-  /**/ export(member/2).
:-  /**/ export(arg/3).
%:-  /**/ export(call_u/1).
% prologDynamic(cycAssert/2).
:-  /**/ export(integer/1).
% :-  /**/ export(makeConstant/1).
% :-  /**/ export(naf/1).
:-  /**/ export(number/1).
:-  /**/ export(string/1).
:-  /**/ export(var/1).



tSet(completeExtentAsserted).
tSet(ttExpressionType).

rtQuotedPred(functorIsMacro).
rtQuotedPred(functorDeclares).

%((prologHybrid(C),{get_functor(C,F,A),C\=F}) ==> arity(F,A)).
prologHybrid(typeProps/2).


arity(typeProps,2).

% :- decl_mpred_pfc ~/1.


:- ignore(show_failure(why,arity(typeProps,2))).
:- must(call_u(arity(typeProps,2))).

% ==> (==>(argIsa(isEach(tPred,prologMultiValued,prologOrdered,prologNegByFailure,meta_argtypes,prologHybrid,prologPTTP,prologDynamic,functorIsMacro,prologListValued,prologSingleValued),2,ftListFn(ftVoprop)))).
% :- ain_expanded(==>(isa(isEach(prologMultiValued,prologOrdered,prologNegByFailure,meta_argtypes,prologPTTP,prologHybrid,predCanHaveSingletons,prologDynamic,prologBuiltin,functorIsMacro,prologListValued,prologSingleValued),functorDeclares))).
% ==>(genls(isEach(prologMultiValued,prologOrdered,prologNegByFailure,prologHybrid,prologPTTP,prologDynamic,prologBuiltin,prologKIF,functorIsMacro,prologListValued,prologSingleValued),tPred)).
:- assert_hasInstance(tCol,tCol).
:- file_begin(pfc).

 
% FIXXXXXXXXXXXXXXXXXXXXXXXXXXXXXxxx
% FIXX 
==> prologHybrid(isEach( tCol/1, disjointWith/2, genls/2,genlPreds/2, meta_argtypes/1)).
% FIXXXXXXXXXXXXXXXXXXXXXXXXXXXXXxxx

% FIXXXXXXXXXXXXXXXXXXXXXXXXXXXXXxxx
% FIXX 
==> prologHybrid(isEach( ttNotTemporalType/1,ttTemporalType/1 )).
% TODO FIX 
% :- decl_mpred(tDeleted(ftID),[prologIsFlag]).
prologIsFlag(tDeleted(ftID)).
% FIXXXXXXXXXXXXXXXXXXXXXXXXXXXXXxxx

prologHybrid(genlInverse/2).
prologHybrid(genlPreds/2).
prologHybrid(argIsa/3).
prologHybrid(predProxyAssert,2).
prologHybrid(predProxyQuery, 2).
prologHybrid(predProxyRetract, 2).

prologHybrid(disjointWith/2).
prologHybrid(instTypeProps/3).
prologHybrid(predTypeMax/3).
prologHybrid(prologSingleValued/1).
prologHybrid(prologSideEffects).
prologHybrid(resultIsa/2).
prologHybrid(genls/2).
prologHybrid(isa/2).
prologHybrid(genls/2).
prologDynamic(arg/3).
~tSet(meta_argtypes).
tSet(prologMultiValued).
tSet(prologSingleValued).
tSet(tCol).
tSet(tFunction).
tSet(tInferInstanceFromArgType).
tSet(tPred).
tSet(tRelation).
tSet(ttTemporalType).
tSet(ttTypeType).
% tCol(tPathway).
genls(tFunction,tRelation).

tSet(ttValueType).

ttExpressionType(ftString).
ttExpressionType(ftVar).


ttExpressionType(ftCallable).
ttExpressionType(ftPercent).

:- dynamic(vtColor/1).
isa(vRed,vtColor).

completelyAssertedCollection(vtValue).

:- system:op(1199,fx,('==>')).
:- system:op(1190,xfx,('::::')).
:- system:op(1180,xfx,('==>')).
:- system:op(1170,xfx,('<==>')).
:- system:op(1160,xfx,('<-')).

:- system:op(1150,xfx,('=>')).
:- system:op(1140,xfx,('<=')).
:- system:op(1130,xfx,('<=>')).


:-  system:op(600,yfx,('&')).
:-  system:op(600,yfx,('v')).
:-  system:op(350,xfx,('xor')).
:-  system:op(300,fx,('~')).
:-  system:op(300,fx,('-')).

isa(vtColor,ttValueType).

isa(X,ttValueType) ==> genls(X,vtValue).
isa(X,ttValueType) ==> completelyAssertedCollection(X).

isa(vtValue,ttValueType).

typeGenls(ttValueType,vtValue).

% :- must((vtColor(vRed))).


%argIsa(Prop,N,Type) :- cwc,number(N),loop_check(argIsa_known(Prop,N,Type)),must(ground(argIsa(Prop,N,Type))).
%argIsa(Prop,N,Type) <- {cwc,number(N),argIsa_known(Prop,N,Type),must(ground(argIsa(Prop,N,Type)))}.

ttExpressionType(Type) ==> (argIsa(Prop,N,Type),{number(N)} ==> argQuotedIsa(Prop,N,Type)).

:- discontiguous(prologSingleValued/1).


:- do_gc.

:- kb_shared(mudLabelTypeProps/3).
:- kb_shared(mudLabelTypeProps/3).
%:- listing(ttRelationType).
% :- rtrace.
:- forall(ttRelationType(F),must((decl_type(F),ain(functorDeclares(F)),ain(genls(F,tPred))))).
:- nortrace.
% :-  /**/ export(mtForPred/2).

/*
:- rtrace.
:- debug,dtrace,(kb_shared((argIsa/3, formatted_resultIsa/2, localityOfObject/2, subFormat/2, 
    isa/2,  genls/2, pddlSomethingIsa/2, ttSpatialType/1, 
    resultIsa/2, subFormat/2, tCol/1, tRegion/1, completelyAssertedCollection/1, 
    ttExpressionType/1, typeProps/2))).

:- prolog. 
*/
/*
:- kb_shared((argIsa/3, formatted_resultIsa/2, localityOfObject/2, subFormat/2, 
    isa/2,  genls/2, pddlSomethingIsa/2, 
    resultIsa/2, subFormat/2, tCol/1, tRegion/1, completelyAssertedCollection/1, 
    ttExpressionType/1, typeProps/2)).
*/
/* FIX
==>
*/
prologHybrid(isEach(argIsa/3, formatted_resultIsa/2, localityOfObject/2, subFormat/2, isa/2, 
   genls/2, pddlSomethingIsa/2, resultIsa/2, subFormat/2, tCol/1, tRegion/1, 
   completelyAssertedCollection/1, ttExpressionType/1, typeProps/2)).


:- ain(isa(ttExpressionType,ttAbstractType)).
:- discontiguous(subFormat/2).
:- kb_shared(tChannel/1).
:- kb_shared(tChannel/1).

% ain((I/(mpred_literal(I),fully_expand(_,I,O),I \=@=O )==> ({format('~q~n',[fully_expand(I->O)])},O))).

/* subFormat(ftDeplictsFn(tCol),ftSpec). */
/* subFormat(ftDeplictsFn(meta_argtypes),ftSpec). */
subFormat(ftVoprop,ftSpec).

==> tFunction(opQuote(isEach(ftRest(ftTerm)))).
==> tFunction(isRandom(tCol)).
==> tFunction(isAnd(ftRest(ftSpec))).
==> tFunction(isMost(ftRest(ftSpec))).
==> tFunction(isOneOf(ftRest(ftSpec))).
==> tFunction(isNot(ftSpec)).
==> tFunction(isOptional(ftSpec,ftTerm)).
==> tFunction(isOptionalStr(ftString)).
==> tFunction(exactStr(ftString)).

resultIsa(ftDeplictsFn,ftSpec).

==> prologHybrid(quotedDefnIff/2).


isa(argIsa,prologHybrid).
isa(determinerString/2, prologMultiValued).
isa(quotedDefnIff, completeExtentAsserted).
isa(ftInt,ttExpressionType).
isa(ftNumber,ttExpressionType).
isa(ftString,ttExpressionType).
isa(isInstFn,tFunction).
isa(isKappaFn,tFunction).
isa(prologMultiValued, tCol).
arity(ftListFn,1).
arity(isLikeFn,2).
arity(ftDeplictsFn,1).

arity(tFunction,1).
==> tFunction(ftDiceFn(ftInt,ftInt,ftInt)).
==> tFunction(ftListFn(tCol)).
==> tFunction(ftDeplictsFn).

completelyAssertedCollection(rtAvoidForwardChain).
completelyAssertedCollection('SententialOperator').


tSet(rtAvoidForwardChain).
tSet('SententialOperator').
%TODO rtAvoidForwardChain('$VAR'('FUNC')).

==>rtAvoidForwardChain(isEach('FunctionToArg',holds,equals,different,evaluate,trueSentence,'TINYKB-ASSERTION',termOfUnit)).
genls('rtSententialRelation','rtSententialOperator').
genls('rtSententialOperator',rtAvoidForwardChain).
genls('rtVariableArityRelation',rtAvoidForwardChain).
genls('rtCommutativeRelation',rtAvoidForwardChain).
genls('tFunction',rtAvoidForwardChain).
genls('rtEvaluatableRelation',rtAvoidForwardChain).

tSet('rtCommutativeRelation').
tSet('rtEvaluatableRelation').
tSet('rtSententialRelation').
tSet('rtVariableArityRelation').


rtQuotedPred(completeIsaAsserted).
%completelyAssertedCollection(Ext):- fwc, arg(_,vv(tCol,vtDirection,ttExpressionType,tRegion,ftString, genlPreds),Ext).
completeExtentAsserted(formatted_resultIsa).
completeExtentAsserted(quotedDefnIff).
completelyAssertedCollection(completelyAssertedCollection).

ttExpressionType(ftVar).
ttExpressionType(ftVoprop).


ttStringType('CharacterString').
ttStringType('SubLString').
ttStringType('ControlCharacterFreeString').
ttStringType('SubLListOfStrings').
% ttStringType(['ListOfTypeFn', X]):-atom(X),ttStringType(X).


% resultIsa(F,C)==>(ftSpec(C),'tFunction'(F)).
% ( meta_argtypes(FT)/dif(FT,COL), genls(FT, COL),tCol(COL),{\+ (isa(COL,ttExpressionType))}) ==> formatted_resultIsa(FT,COL).

%:- mpred_trace.
%:- pfcWatch.
%:- mpred_warn.
% next_test :- sleep(1),pfcReset.


% :- kb_shared((disjointWith/2,genls/2)).

argsQuoted(mudAreaConnected).

prologHybrid(argIsa(tRelation,ftInt,tCol)).
prologHybrid(formatted_resultIsa(ttExpressionType,tCol)).

:- sanity(argIsa(genlPreds,2,_)).
:- must(tCol(vtVerb)).
:- must(isa(vtVerb,tCol)).
:- must(t(tCol,vtVerb)).



prologHybrid(quotedDefnIff(ttExpressionType,ftTerm)).
prologHybrid(defnNecessary(ttExpressionType,ftTerm)).
prologHybrid(quotedDefnIff(ttExpressionType,ftTerm)).


tFuncton(isLikeFn(tPred,tCol)).
tRelation('==>'(ftAskable,ftAssertable)).
prologHybrid(subFormat(ttExpressionType,ttExpressionType)).
prologMultiValued(comment(ftTerm,ftString)).
prologMultiValued(genlInverse(tPred,tPred)).
prologMultiValued(genlPreds(tPred,tPred)).
prologMultiValued(predProxyAssert(prologMultiValued,ftTerm)).
prologMultiValued(predProxyQuery(prologMultiValued,ftTerm)).

:- if(true).
prologHybrid(instTypeProps(ftID,tCol,ftRest(ftVoprop))).
functorIsMacro(macroSomethingDescription(ftTerm,ftListFn(ftString))).
functorIsMacro(pddlObjects(tCol,ftListFn(ftID))).
functorIsMacro(pddlDescription(ftID,ftListFn(ftString))).
functorIsMacro(pddlPredicates(ftListFn(ftVoprop))).
functorIsMacro(pddlSorts(tCol,ftListFn(tCol))).
functorIsMacro(pddlTypes(ftListFn(tCol))).
:- endif.


% prologMultiValued('<==>'(ftTerm,ftTerm)).
prologMultiValued('<-'(ftAssertable,ftAskable)).
prologMultiValued('==>'(ftAskable,ftAssertable)).
prologNegByFailure(predArgMulti(prologMultiValued,ftInt)).
prologNegByFailure(tDeleted(ftID)).

%= 	 	 

%% prologSingleValued( ?ARG1, ?ARG2) is semidet.
%
% Prolog Single Valued.
%
==>prologSingleValued(predInstMax(ftID,prologSingleValued,ftInt),prologHybrid).
props(predTypeMax(prologSingleValued,tCol,ftInt),[prologHybrid,prologSingleValued]).
resultIsa(txtFormatFn,ftText).
%'<==>'(prologMultiValued(CallSig,[predProxyAssert(aina),predProxyRetract(del),predProxyQuery(call)]),prologDynamic(CallSig)).
%'<==>'(prologMultiValued(CallSig,[predProxyAssert(pttp_tell),predProxyRetract(pttp_retract),predProxyQuery(pttp_ask)]),prologPTTP(CallSig)).
subFormat(ftAtom,ftTerm).
subFormat(ftCallable,ftProlog).
resultIsa(ftDiceFn,ftInt).
% subFormat(ftID,ftTerm).
subFormat(ftInt,ftNumber).
subFormat(ftInteger,ftNumber).
subFormat(ftNumber,ftPercent).
subFormat(ftPercent,ftNumber).
subFormat(ftString,ftTerm).
subFormat(ftString,ftText).
subFormat(ftTerm,ftProlog).
subFormat(ftText,ftTerm).
subFormat(ftVar,ftProlog).
subFormat(ftVoprop,ftRest(ftVoprop)).
subFormat(ftVoprop,ftTerm).

subFormat(COL1,COL2)/(atom(COL1);atom(COL2))==>(ttExpressionType(COL1),ttExpressionType(COL2)).
% tCol(W)==>{quietly(guess_supertypes(W))}.


tSet(tNewlyCreated).
tSet(ttTypeFacet).

:- dynamic(tNewlyCreated/1).
tNewlyCreated(W)==>{guess_types(W)}.

ttTypeFacet(ttTypeFacet).
ttTypeFacet(ttUnverifiableType).


%typeGenls(tPred,ttRelationType).
typeGenls(ttExpressionTypeType,ttExpressionType).
typeGenls(ttTypeFacet,tCol).
typeGenls(ttTypeType,tCol).

typeGenls(ttAgentType,tAgent).


(typeGenls(TT,ST) ==> 
 (isa(Inst,TT) ==> genls(Inst,ST))).


:-kb_shared(rtUnaryPredicate/1).
:-kb_shared(ttSpatialType/1).


ttTypeFacet(ttUnverifiableType).
ttUnverifiableType(ftID).
% ttUnverifiableType(ftListFn(ftTerm)).
% ttUnverifiableType(ftListFn).
% ttUnverifiableType(ftDiceFn(ftInt,ftInt,ftInt)).

ttUnverifiableFormatType(C) <==> ttExpressionType(C),ttUnverifiableType(C).

ttUnverifiableFormatType(ftDice).
ttUnverifiableFormatType(ftString).
ttUnverifiableFormatType(ftTerm).
ttUnverifiableFormatType(ftText).
ttUnverifiableFormatType(ftVoprop).

ttUnverifiableType(tCol).
ttUnverifiableType(tFunction).
ttUnverifiableType(tPred).
ttUnverifiableType(ttExpressionType).
ttUnverifiableType(vtDirection).


%ttRelationType(ArgsIsa)==>tPred(ArgsIsa).
%TODO isa(_,ArgsIsa)==>tCol(ArgsIsa).

:- set_prolog_flag(report_error,true),set_prolog_flag(debug_on_error,true),set_prolog_flag(debug, true).


/*
disjointWith(A,B):- A=B,!,fail.
disjointWith(A,B):- disjointWithT(A,B).
disjointWith(A,B):- disjointWithT(AS,BS),transitive_subclass_or_same(A,AS),transitive_subclass_or_same(B,BS).
disjointWith(A,B):- once((type_isa(A,AT),type_isa(B,BT))),AT \= BT.
*/
disjointWith(Sub, Super) ==> disjointWith( Super, Sub).


disjointWith(ttTemporalType,ttAbstractType).

prologHybrid(dividesBetween(tCol,tCol,tCol)).

quotedDefnIff(X,_)==>ttExpressionType(X).


quotedDefnIff(ftInt,integer).
quotedDefnIff(ftFloat,float).
quotedDefnIff(ftAtom,atom).
quotedDefnIff(ftString,is_ftString2).
quotedDefnIff(ftSimpleString,string).
quotedDefnIff(ftCallable,is_callable).
quotedDefnIff(ftCompound,is_ftCompound).
quotedDefnIff(ftGround,ground).
quotedDefnIff(ftID,is_id).
quotedDefnIff(ftTerm,is_ftNonvar).
quotedDefnIff(ftVar,is_ftVar).
quotedDefnIff(ftNonvar,is_ftNonvar).
quotedDefnIff(ftNumber,number).
quotedDefnIff(ftList,is_list).
% quotedDefnIff(ftRest,is_rest).
quotedDefnIff(ftBoolean,is_boolean).
quotedDefnIff(ftText,is_ftText).
quotedDefnIff(ftRest(Type),is_rest_of(Type)):- cwc, is_ftNonvar(Type).
quotedDefnIff(ftListFn(Type),is_list_of(Type)):- cwc, is_ftNonvar(Type).
quotedDefnIff(ftCodeIs(SomeCode),SomeCode):- cwc, is_ftNonvar(SomeCode).
:- listing(quotedDefnIff).

(ttExpressionType(FT)/append_term(FT,Arg,Head) ==> 
    ((Head:- !, term_is_ft(Arg,FT)))).

% tCol(Type),(rtBinaryPredicate(Pred)/(functor(G,Pred,2),G=..[Pred,isInstFn(Type),Value])), G ==> relationMostInstance(Pred,Type,Value).


%((genlPreds(Col1,Col2),(arity(Col1,1);arity(Col2,1)))==>genls(Col1,Col2)).
%((genls(Col1,Col2),(tPred(Col1);tPred(Col2)))==>genlPreds(Col1,Col2)).

tSet(rtBinaryPredicate).
ttRelationType(rtBinaryPredicate).

isa(arity,rtBinaryPredicate).

% (arity(Pred,2),tPred(Pred)) <==> isa(Pred,rtBinaryPredicate).

ttRelationType('rtUnaryPredicate').

isa(arity,rtBinaryPredicate).



specialFunctor('\\+').
specialFunctor('/').


:- if(baseKB:startup_option(datalog,sanity);baseKB:startup_option(clif,sanity)).
/*
:- must((expand_props(_,==>props(iCrackers666,[mudColor(vTan),isa(tBread),mudShape(isEach(vCircular,vFlat)),mudSize(vSmall),mudTexture(isEach(vDry,vCoarse))]),O),ain(mdefault(O)))).

:- must((fully_expand(_,props(iCrackers666,[mudColor(vTan),isa(tBread),mudShape(isEach(vCircular,vFlat)),mudSize(vSmall),mudTexture(isEach(vDry,vCoarse))]),O),mpred_why(mdefault(O)))).
*/
:- endif.

arity(Pred,2),tPred(Pred) <==> rtBinaryPredicate(Pred).

% if arity is ever greater than 1 it can never become 1
% arity(F,A)/(number(A),A>1) ==> ~(arity(F,1)).

completelyAssertedCollection(rtBinaryPredicate).


% TODO ADD THIS 
%(tCol(Super),completelyAssertedCollection(Super),genls(Sub, Super), isa(I,Sub), {ground(I:Sub:Super),\==(Sub, Super)}) ==> isa(I,Super).

:- mpred_trace_exec.

/*

(implies 
    (and 
      (isa ?PRED ReflexiveBinaryPredicate) 
      (arg1Isa ?PRED ?CONSTRAINT1) 
      (isa ?OBJ1 ?CONSTRAINT1) 
      (equals ?OBJ1 ?OBJ2)) 
    (?PRED ?OBJ1 ?OBJ2))

*/
% ((genlPreds(equals,P),argIsa(P,1,Col)) ==>  (t(P,A,B):- (nonvar(A),A==B,isa(A,Col)))).
% genlPreds(genls,equals).
:- mpred_notrace_exec.
rtReflexiveBinaryPredicate(TB)==>genlPreds(equals,TB).

% (isa(TypeType,ttTypeType) , isa(Inst,TypeType), genls(SubInst,Inst)) ==> isa(SubInst,TypeType).

ttExpressionType(ftAction).
{type_prefix(_Prefix,Type),atom(Type),atom_concat(ft,_,Type)}==>ttExpressionType(Type).
{type_suffix(_Suffix,Type),atom(Type),atom_concat(ft,_,Type)}==>ttExpressionType(Type).


{type_prefix(_Prefix,Type)}==>tCol(Type).
{type_suffix(_Suffix,Type)}==>tCol(Type).

((tCol(C)/( \+ ttExpressionType(C))) ==> tSet(C)).



tSet(tPred).
prologHybrid(isa/2).

%mpred_online:semweb_startup:- with_no_term_expansions(if_file_exists(use_module(logicmoo(dbase/mpred_i_rdf_store)))).

% :- with_no_term_expansions(if_file_exists(use_module(logicmoo(mobs/planner/mpred_i_hyhtn)))).
tSet(prologIsFlag).
tSet(prologDynamic).
prologHybrid(formatted_resultIsa/2).

:- sanity(argIsa(genlPreds,2,_)).
:- must(tCol(vtVerb)).
:- must(t(tCol,vtVerb)).
:- must(isa(vtVerb,tCol)).


ttAgentType(mobPhilosopher).


%:- mpred_trace_all.
isa(iPlato,mobPhilosopher).

:-must(isa(iPlato,mobPhilosopher)).

:- mpred_test(\+ isa(iPlato,ftAtom)).

%:- mpred_test(\+ isa(iPlato,ftAtom)).
%:- sanity(mpred_test(~quotedIsa(iPlato,mobPhilosopher))).
:- sanity(mpred_test(quotedIsa(iPlato,ftAtom))).
:- mpred_notrace_all.

ttBarrierStr(A)/(atomic_list_concat([A,"Type"],AType0),
  atomic_list_concat([A,''],Type0),
  do_renames(Type0,Type),
  do_renames(AType0,TypeType)) ==> barrierSpindle(TypeType,Type).



barrierSpindle(TypeType,Type)==> 
   generatesAsFirstOrder(Type), isa(TypeType,ttBarrierType),isa(Type,ttBarrier),typeGenls(TypeType,Type).

ttBarrier(C)==>tSet(C).
(ttBarrierType(C)==>(tSet(C),ttTypeType(C))).

/*

@ TODO RE-ENABLE WHEN NEEDED
ttBarrier(C)==>(isa(I,C)==>mainClass(I,C)).

ttBarrier(A)/dif(A,B),ttBarrier(B)==> disjointWith(A,B).
% ttBarrierType(A)/dif(A,B),ttBarrierType(B)==> disjointWith(A,B).

*/

tCol(ttAbstractType).
disjointWith(C,D)==> tCol(C),tCol(D).

cycBetween(A,B,N):-
  (number(A) -> 
     ((number(B);number(N)),system_between(A,B,N));
     ((number(B),number(N))->system_between(A,B,N))).

:- install_constant_renamer_until_eof.

  
ttBarrierStr("Action").
ttBarrierStr("Agent").
ttBarrierStr("Artifact").
barrierSpindle('ttSpecifiedPartTypeCollection','tPartTypePhysicalPartOfObject').
ttBarrierStr("Capability").
ttBarrierStr("Event").
ttBarrierStr("FormulaTemplate").
ttBarrierStr("Goal").
ttBarrierStr("Group").
ttBarrierStr("LinguisticObject").
ttBarrierStr("Microtheory").
ttBarrierStr("PersonTypeByActivity").
ttBarrierStr("Place").
ttBarrierStr("Quantity").
ttBarrierStr("Relation").
ttBarrierStr("ScalarInterval").
ttBarrierStr("Situation").
ttBarrierStr("ExpressionType").
ttBarrierStr("TimeParameter").
ttBarrierStr("Topic").
% ttBarrierStr("Collection").

:- listing(disjointWith/2).

genlsFwd(tItem,'Artifact').
genlsFwd(tRegion,'Place').

:- set_prolog_flag(do_renames,restore).


