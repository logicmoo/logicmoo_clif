
/*
:- ensure_loaded(plarkc(mpred_sexpr_reader)).

:- parse_to_source(
  "(documentation instance EnglishLanguage \"An object is an &%instance of a &%SetOrClass if it is included in that &%SetOrClass. 
  An individual may be an instance of many classes, some of which may be subclasses of others. 
  Thus, there is no assumption in the meaning of &%instance about specificity or uniqueness.\")",
  Out),writeq(Out).
*/


% KIF BASED
:- export((
         must_map_preds/3, 
         sumo_to_clif/2,
         is_kif_string/1,
         from_kif_string/2,
         convert_if_kif_string/2,
         kif_assertion_recipe/2)).



delay_rule_eval(InOut,_Wrap,InOut):-ground(InOut),!.
delay_rule_eval(In,Wrap,WIn):- WIn=..[Wrap,In].

% for SUMO
rename_sumo('Collection','ttSumoCollection').
rename_sumo(format,formatSumo).
% rename_sumo(documentation,comment).
rename_sumo('instance', isa).
rename_sumo('subclass', genls).
rename_sumo('inverse', genlInverse).
rename_sumo('domain', 'argIsa').
rename_sumo('disjoint', 'disjointWith').

rename_sumo('Atom', 'tSumoAtomMolecule').

rename_sumo('range', 'resultIsa').
rename_sumo('domainSubclass', 'argGenl').
rename_sumo('rangeSubclass', 'resultGenl').
rename_sumo(immediateInstance,nearestIsa).
rename_sumo('partition', 'sumo_partition').
rename_sumo('Entity','tThing').
rename_sumo('ListFn',vTheListFn).
rename_sumo('ListOrderFn',vSumoListOrderFn).
rename_sumo('AssignmentFn',uFn).
rename_sumo('SymbolicString',ftString).
rename_sumo('property','sumoProperty').
rename_sumo('attribute','sumoAttribute').
rename_sumo('Attribute','vtSumoAttribute').
rename_sumo('EnglishLanguage','vEnglishLanguage').
rename_sumo('Formula','ftFormula').
rename_sumo('Function','tFunction').
rename_sumo(forall,all).
rename_sumo(subrelation,genlPreds).
rename_sumo('Class','tSet').
rename_sumo('SetOrClass', 'tCol').
rename_sumo(I,O):- if_defined(builtin_rn_or_rn_new(I,O)),!.



%% is_kif_string( ?String) is det.
%
% If Is A Knowledge Interchange Format String.
%
is_kif_string([]):- !,fail.
is_kif_string(String):-atomic(String),name(String,Codes), memberchk(40,Codes),memberchk(41,Codes).




%% convert_if_kif_string( ?I, ?O) is det.
%
% Convert If Knowledge Interchange Format String.
%
convert_if_kif_string(I, O):-is_kif_string(I),kif_assertion_recipe(I,O),!, \+ is_list(O).


last_chance_doc(Wff0,WffO):- atomic(Wff0),atom_contains(Wff0,' '),string_to_mws(Wff0,MWS),last_chance_doc(MWS,WffO),!.
last_chance_doc(Wff0,comment(Atom,NewStr)):- 
   Wff0=..[s,"(", "documentation",AntisymmetricRelation, "EnglishLanguage", "\""|REST],
         append(NOQUOTES,[_,_],REST),
         string_to_atom(AntisymmetricRelation,Atom),
         NewStr =..[s|NOQUOTES],!.
last_chance_doc(IO,IO).


%% from_kif_string( ?String, ?Forms) is det.
%
% Converted From Knowledge Interchange Format String.
%
from_kif_string(I,Wff) :- input_to_forms(I,Wff,Vs)->must(put_variable_names(Vs)),!.
from_kif_string(String,Forms) :- codelist_to_forms(String,Forms),!.
from_kif_string(Wff,Wff).


:- module_transparent(must_map_preds/3).
must_map_preds([],IO,IO):-!.
must_map_preds([one(Pred)|ListOfPreds],IO,Out):- break, must(call(Pred,IO)),!,
   must_map_preds(ListOfPreds,IO,Out).
must_map_preds([Pred|ListOfPreds],In,Out):- must(call(Pred,In,Mid)),!,
   must_map_preds(ListOfPreds,Mid,Out),!.


:- thread_local(t_l:no_db_expand_props/0).

fully_expand_always(C0,C1):- locally(t_l:no_db_expand_props,fully_expand('==>'(C0),C1)),!.

kif_assertion_recipe(D,CycLOut):-
         must_det_l((must_map_preds([
          %  from_kif_string,
           sexpr_sterm_to_pterm,
           sumo_to_clif,
           %cyc_to_clif,
           fully_expand_always,
           % unnumbervars_and_save,
           sumo_last_pass],D,CycLOut))).

sumo_last_pass(O,O):- \+ compound(O),!.
% sumo_last_pass((tPred(A),IO),IO):-atom(A),!.
sumo_last_pass(SENT,SENTO):- is_list(SENT),!,must_maplist(sumo_last_pass,SENT,SENTO).
sumo_last_pass([P|List],OUT):- atom(P), op_type_head(P,TYPE),make_var_arg(TYPE,P,List,OUT),!.
sumo_last_pass([P|List],[P|List]):-!.
sumo_last_pass(SENT,SENTO):- SENT=..[CONNECTIVE|ARGS],must_maplist(sumo_last_pass,ARGS,ARGSO),SENTO=..[CONNECTIVE|ARGSO],!.
sumo_last_pass(IO,IO).

op_type_head(P,uN):-atom(P), atom_concat(_,'Fn',P).
op_type_head(P,tN):-atom(P).


make_var_arg(TYPE,P,List,OUT):- is_ftVar(List),!,OUT=..[TYPE,P,List].
make_var_arg(TYPE,P,List,OUT):- is_list(List),!,must_maplist(sumo_last_pass,List,ListO),OUT=..[TYPE,P|ListO].
make_var_arg(TYPE,P,[A0|List],OUT):- sumo_last_pass(A0,A),!,
 (is_ftVar(List) -> OUT=..[TYPE,P,A,List];
    (append(Left,Var,List),is_ftVar(Var),!,
    must_maplist(sumo_last_pass,Left,NewLeft),
    append(NewLeft,[Var],NewList),
    OUT=..[TYPE,P,A|NewList])),!.


sumo_to_clif(O,O):-is_ftVar(O),!.
sumo_to_clif(documentation(C,'vEnglishLanguage',S),comment(C,S)):-!.
sumo_to_clif(Const,NConst):-atom(Const),rename_sumo(Const,NConst),!.
sumo_to_clif(Const,NConst):-string(Const),string_to_mws(Const,NConst),!.
sumo_to_clif(O,O):- \+ compound(O),!.
sumo_to_clif(I,O):-clause_b(ruleRewrite(I,O))->I\==O,!.
% sumo_to_clif((tPred(_),I),O):-!,sumo_to_clif(I,O).
sumo_to_clif(SENT,SENTO):- is_list(SENT),!,must_maplist(sumo_to_clif,SENT,SENTO).
sumo_to_clif(SENT,SENTO):- SENT=..[CONNECTIVE|ARGS],must_maplist(sumo_to_clif,[CONNECTIVE|ARGS],ARGSO),SENTO=..ARGSO,!.
sumo_to_clif(IO,IO).


:- use_module(library(logicmoo_motel)).


