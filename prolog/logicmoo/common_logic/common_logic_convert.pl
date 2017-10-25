
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
         sumo_to_pdkb_p5/2,
         is_kif_string/1,
         from_kif_string/2,
         convert_if_kif_string/2,
         sumo_to_pdkb/2)).



delay_rule_eval(InOut,_Wrap,InOut):-ground(InOut),!.
delay_rule_eval(In,Wrap,WIn):- WIn=..[Wrap,In].

% for SUMO
sumo_to_pdkb_const('Collection','ttSumoCollection').
sumo_to_pdkb_const(format,formatSumo).
% sumo_to_pdkb_const(documentation,comment).
sumo_to_pdkb_const('instance', isa).
sumo_to_pdkb_const('subclass', genls).
sumo_to_pdkb_const('inverse', genlInverse).
sumo_to_pdkb_const('domain', 'argIsa').
sumo_to_pdkb_const('disjoint', 'disjointWith').

sumo_to_pdkb_const('Atom', 'tSumoAtomMolecule').

sumo_to_pdkb_const('range', 'resultIsa').
sumo_to_pdkb_const('domainSubclass', 'argGenl').
sumo_to_pdkb_const('rangeSubclass', 'resultGenl').
sumo_to_pdkb_const(immediateInstance,nearestIsa).
sumo_to_pdkb_const('partition', 'sumo_partition').
sumo_to_pdkb_const('Entity','tThing').
sumo_to_pdkb_const('ListFn',vTheListFn).
sumo_to_pdkb_const('ListOrderFn',vSumoListOrderFn).
sumo_to_pdkb_const('AssignmentFn',uFn).
sumo_to_pdkb_const('SymbolicString',ftString).
sumo_to_pdkb_const('property','sumoProperty').
sumo_to_pdkb_const('attribute','sumoAttribute').
sumo_to_pdkb_const('Attribute','vtSumoAttribute').
sumo_to_pdkb_const('EnglishLanguage','vEnglishLanguage').
sumo_to_pdkb_const('Formula','ftFormula').
sumo_to_pdkb_const('Function','tFunction').
sumo_to_pdkb_const(forall,all).
sumo_to_pdkb_const(subrelation,genlPreds).
sumo_to_pdkb_const('Class','tSet').
sumo_to_pdkb_const('baseKB','baseKB').
sumo_to_pdkb_const('SetOrClass', 'tCol').
sumo_to_pdkb_const(v,v).
sumo_to_pdkb_const(&,&).
sumo_to_pdkb_const(~,~).
sumo_to_pdkb_const(=>,=>).
sumo_to_pdkb_const(U,U):- downcase_atom(U,U).
sumo_to_pdkb_const(U,U):- upcase_atom(U,U).
sumo_to_pdkb_const(I,O):- if_defined(builtin_rn_or_rn_new(I,O)),!.




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
convert_if_kif_string(I, O):-is_kif_string(I),sumo_to_pdkb(I,O),!, \+ is_list(O).


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
convert_1_kif_string(I,Wff):- input_to_forms(I,Wff,Vs)->must(put_variable_names(Vs)),!.

from_kif_string(Wff,Wff):- \+ atomic(Wff), \+ is_list(Wff),!.
from_kif_string(I,Wff) :- string(I),convert_1_kif_string(string(I),Wff),!.
from_kif_string(I,Wff) :- atom(I),atom_contains(I,' '),convert_1_kif_string(atom(I),Wff),!.
from_kif_string([C|String],Wff) :- is_list(String),text_to_string_safe([C|String],Text),one_must(convert_1_kif_string(string(Text),Wff),codelist_to_forms(string(Text),Wff)),!.
from_kif_string(Wff,Wff).


:- module_transparent(must_map_preds/3).
must_map_preds([],IO,IO):-!.
must_map_preds([one(Pred)|ListOfPreds],IO,Out):- !, quietly(call(Pred,IO)),!,must_map_preds(ListOfPreds,IO,Out).
must_map_preds([Pred|ListOfPreds],In,Out):- quietly(call(Pred,In,Mid)),!,must_map_preds(ListOfPreds,Mid,Out),!.


:- thread_local(t_l:no_db_expand_props/0).

fully_expand_always(C0,C1):- locally_tl(no_db_expand_props,fully_expand('==>'(C0),C1)),!.


sumo_to_pdkb(CycL,CycL):- is_ftVar(CycL).
sumo_to_pdkb('$COMMENT'(A),'$COMMENT'(A)):- !.
sumo_to_pdkb(D,CycLOut):-
         must_det_l((must_map_preds([
           from_kif_string,
           sexpr_sterm_to_pterm,
           sumo_to_pdkb_extra(sumo_to_pdkb_p5),
           cyc_to_pdkb_maybe,
           fully_expand_always,
           unnumbervars_with_names,
           sumo_to_pdkb_p9,
           =],D,CycLOut))).

cyc_to_pdkb_maybe(I,O):- if_defined(cyc_to_pdkb(I,O),I=O),!.

sumo_to_pdkb_p9(I,O):-sumo_to_pdkb_extra(sumo_to_pdkb_p9_e,I,O).

:- meta_predicate(sumo_to_pdkb_extra(2,?,?)).

sumo_to_pdkb_extra(_ ,O,O):- is_ftVar(O),!.
sumo_to_pdkb_extra(Ex,I,O):- call(Ex,I,O),!.
sumo_to_pdkb_extra(_ ,O,O):- \+ compound(O),!.
sumo_to_pdkb_extra(Ex,(H,T),(HH,TT)):- !,sumo_to_pdkb_extra(Ex,H,HH),sumo_to_pdkb_extra(Ex,T,TT).
sumo_to_pdkb_extra(Ex,[H|T],[HH|TT]):- !,sumo_to_pdkb_extra(Ex,H,HH),sumo_to_pdkb_extra(Ex,T,TT).
sumo_to_pdkb_extra(Ex,SENT,SENTO):- SENT=..[CONNECTIVE|ARGS],sumo_to_pdkb_extra(Ex,[CONNECTIVE|ARGS],ARGSO),
  (is_list(ARGSO)->SENTO=..ARGSO;SENTO=ARGSO),!.
sumo_to_pdkb_extra(_ ,IO,IO).

sumo_to_pdkb_p5(documentation(C,'vEnglishLanguage',S),comment(C,S)):-!.
sumo_to_pdkb_p5(Const,NConst):-atom(Const),(sumo_to_pdkb_const(Const,NConst)->true;Const=NConst),!.
sumo_to_pdkb_p5(Const,NConst):-string(Const),string_to_mws(Const,NConst),!.
sumo_to_pdkb_p5(I,O):-clause_b(ruleRewrite(I,O))->I\==O,!.

sumo_to_pdkb_p9_e([P|List],OUT):- atom(P),\+ is_list(List),op_type_head(P,TYPE),make_var_arg(TYPE,P,List,OUT),!.

op_type_head(P,uN):-atom(P), atom_concat(_,'Fn',P).
op_type_head(P,tN):-atom(P).


make_var_arg(TYPE,P,List,OUT):- is_ftVar(List),!,OUT=..[TYPE,P,List].
make_var_arg(TYPE,P,List,OUT):- is_list(List),!,must_maplist(sumo_to_pdkb_p9,List,ListO),OUT=..[TYPE,P|ListO].
make_var_arg(TYPE,P,[A0|List],OUT):- sumo_to_pdkb_p9(A0,A),!,
 (is_ftVar(List) -> OUT=..[TYPE,P,A,List];
    (append(Left,Var,List),is_ftVar(Var),!,
    must_maplist(sumo_to_pdkb_p9,Left,NewLeft),
    append(NewLeft,[Var],NewList),
    OUT=..[TYPE,P,A|NewList])),!.



:- use_module(library(logicmoo_motel)).


:- fixup_exports.
