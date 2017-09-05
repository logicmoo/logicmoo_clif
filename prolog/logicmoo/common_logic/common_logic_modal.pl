:- module(common_logic_modalization,[qualify_nesc/2]).

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


/*


  qualify_modality( +FmlIn, -FmlOut, [options...]).


   converts terms like...

         loves(joe,mary)

   Into...

         poss(loves(joe,mary)) => nesc(loves(joe,mary)).

   settings are...


*/



:- thread_local(t_l:qualify_modally/0).
%% qualify_modality( ?P, ?Q) is det.
qualify_modality(OuterQuantKIF,OuterQuantKIF):- current_prolog_flag(logicmoo_modality,none),!.
qualify_modality(PQ,PQO):- qualify_nesc(PQ,PQO).




%% qualify_nesc( ?P, ?Q) is det.
%
%  Q = (poss(P)=>P).
%

% qualify_nesc(OuterQuantKIF,OuterQuantKIF):- \+ t_l:qualify_modally,!.
qualify_nesc(OuterQuantKIF,OuterQuantKIF):- var(OuterQuantKIF),!.
qualify_nesc(IN,OUT):-is_list(IN),must_maplist_det(qualify_nesc,IN,OUT),!.
qualify_nesc(OuterQuantKIF,OuterQuantKIF):- leave_as_is(OuterQuantKIF),!.
qualify_nesc(OuterQuantKIF,OuterQuantKIF):- contains_modal(OuterQuantKIF),!.
qualify_nesc(PQ,PQO):- PQ=..[F|Q],is_quantifier(F),append(LQ,[RQ],Q),qualify_nesc(RQ,RQQ),append(LQ,[RQQ],QQ),PQO=..[F|QQ],!.
% qualify_nesc(P<=>Q,PQ & QP):- !,qualify_nesc(P=>Q,PQ),qualify_nesc(Q=>P,QP).

% full modality
qualify_nesc(P,(poss(P)=>nesc(P))):- current_prolog_flag(logicmoo_modality,full), !.

% late modality
qualify_nesc(P,nesc(P)):- current_prolog_flag(logicmoo_modality,late), !.


% part modality
qualify_nesc( ~(IN), ~(poss(IN))):- current_prolog_flag(logicmoo_modality,part), !.
%qualify_nesc(P<=>Q,((nesc(P)<=>nesc(Q)) & (poss(P)<=>poss(Q)))):-!.
qualify_nesc(P=>Q,((poss(Q)&nesc(P))=>nesc(Q))):-  current_prolog_flag(logicmoo_modality,part), !.
%qualify_nesc(P=>Q,((nesc(P)=>nesc(Q)) & (poss(P)=>poss(Q)))):-!.
%qualify_nesc(P,(~nesc(P)=>nesc(P))):- \+ \+ (P = (_ & _) ; P = (_ v _)).
qualify_nesc(P,nesc(P)):- \+ current_prolog_flag(logicmoo_modality,full), !.

% fallback
qualify_nesc(P,nesc(P)):- !.

% never seen (but realistic)
qualify_nesc(P=>Q,(PP => (NP & QP =>NQ))):-!, weaken_to_poss(P,PP),weaken_to_poss(Q,QP),add_nesc(P,NP),add_nesc(Q,NQ).
qualify_nesc((P & Q),(PossPQ => (P & Q))):-  weaken_to_poss(P & Q, PossPQ),!.

/*
qualify_nesc(IN,poss(IN)):- IN=..[F|_],should_be_poss(F),!.
qualify_nesc(Wff,(poss(Wff) => nesc(Wff))):- quietly(var_or_atomic(Var)),!.
qualify_nesc(Wff,(poss(Wff) => nesc(Wff))):- leave_as_is_logically(Wff),!.
qualify_nesc(Q,(PQ & Q)):-  weaken_to_poss(Q,PQ),!.
qualify_nesc(OuterQuantKIF,OuterQuantKIF):-!.
% qualify_nesc(IN,OUT):-IN=..[F|INL],logical_functor_pttp(F),!,must_maplist_det(qualify_nesc,INL,OUTL),OUT=..[F|OUTL].
*/


%% add_nesc( ?X, ?X) is det.
%
% Add Necesity.
%

add_nesc(IN,OUT):-is_list(IN),must_maplist_det(add_nesc,IN,OUT),!.
add_nesc(OuterQuantKIF,OuterQuantKIF):- is_ftVar(OuterQuantKIF),!.
add_nesc(OuterQuantKIF,OuterQuantKIF):-leave_as_is(OuterQuantKIF),!.
add_nesc(OuterQuantKIF,OuterQuantKIF):-contains_modal(OuterQuantKIF),!.
add_nesc( ~(IN), nesc(~(IN))).
add_nesc(IN,OUT):-IN=..[F|INL],logical_functor_pttp(F),!,must_maplist_det(add_nesc,INL,OUTL),OUT=..[F|OUTL].
add_nesc(IN,nesc(IN)).
/*
add_nesc(nesc(OuterQuantKIF),nesc(OuterQuantKIF)):-!.
add_nesc(poss(OuterQuantKIF),poss(OuterQuantKIF)):-!.
add_nesc(P<=>Q,O):-!,add_nesc(((P=>Q) & (Q=>P)),O).
add_nesc(PQ,PQO):- PQ=..[F|Q],is_quantifier(F),append(LQ,[RQ],Q),add_nesc(RQ,RQQ),append(LQ,[RQQ],QQ),PQO=..[F|QQ],!.
add_nesc(IN,poss(IN)):-IN=..[F|_],should_be_poss(F),!.
add_nesc(P=>Q,((PP & P & QP) =>Q)):-  weaken_to_poss(P,PP),weaken_to_poss(Q,QP).

add_nesc(Q,(PQ & Q)):-  weaken_to_poss(Q,PQ),!.
add_nesc((P & Q),(PQ & (P & Q))):-  weaken_to_poss(P & Q,PQ),!.
add_nesc(OuterQuantKIF,OuterQuantKIF):-!.
*/



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


% weaken_to_poss(OuterQuantKIF,OuterQuantKIF):-!.
% weaken_to_poss(X,X):-!.
                            


%% weaken_to_poss( ?PQ, ?PQ) is det.
%
% Weaken statments from meaning Nesc to meaning Possibility.
%
weaken_to_poss(PQ,poss(PQ)):- var(PQ),!.
weaken_to_poss(poss(PQ),poss(PQ)):-!.
weaken_to_poss(nesc(PQ),poss(PQ)):-!.
weaken_to_poss(INL,OUTC):-is_list(INL),must_maplist_det(weaken_to_poss,INL,OUTL),F='&',OUT=..[F|OUTL],correct_arities(F,OUT,OUTC).
%weaken_to_poss(PQ,PQO):- PQ=..[F,V,Q],is_quantifier(F),weaken_to_poss(Q,QQ),PQO=..[F,V,QQ],!.
weaken_to_poss(OuterQuantKIF,poss(OuterQuantKIF)):- leave_as_is_logically(OuterQuantKIF),!.
weaken_to_poss( ~(IN), poss(~(IN))):-!.
weaken_to_poss(IN,OUT):-IN=..[F|INL],logical_functor_pttp(F),!,must_maplist_det(weaken_to_poss,INL,OUTL),OUT=..[F|OUTL].
weaken_to_poss(IN,poss(IN)).


% shall X => can X
% shall ~ X => ~ can X
% ~ shall X => can ~ X
















undess_head(H,H):- current_prolog_flag(logicmoo_propagation, modal),!.

undess_head((H:-B),(HH:-B)):-!,undess_head(H,HH).
undess_head(proven_tru(H),H):- !.
undess_head(H,H).

demodal_clauses3(KB,FlattenedO1,FlattenedOO):-
        demodal_clauses(KB,FlattenedO1,FlattenedO2),
        demodal_clauses1(KB,FlattenedO2,FlattenedO3),
        demodal_clauses1(KB,FlattenedO3,FlattenedO4),
        demodal_clauses1(KB,FlattenedO4,FlattenedO5),
      remove_unused_clauses(FlattenedO5,FlattenedOO).


demodal_clauses1(_,FlattenedO,FlattenedO):-!.
demodal_clauses1(KB,FlattenedO4,FlattenedO5):- demodal_clauses(KB,FlattenedO4,FlattenedO5).

demodal_clauses(_KB,Var, Var):- quietly(var_or_atomic(Var)),!.
demodal_clauses(KB,List,ListO):- is_list(List),!,must_maplist_det(demodal_clauses(KB),List,ListO),!.
demodal_clauses(KB,(Head:-Body),HeadOBodyO):- !, demodal_head_body(KB,Head,Body,HeadOBodyO),!.
demodal_clauses(KB,Head,HeadOBodyO):- demodal_head_body(KB,Head,true,HeadOBodyO),!.


/*
demodal_head_body(KB,Head,Body,(Head:-BodyO)):- term_attvars(Head,AttVars),include(AttVars,is_skolem,HeadAttVars),
  term_attvars(Body,BodyAttVars),subtract_eq(HeadAttVars,BodyAttVars,SKList),
    transform_skolem_forms(SKList,HeadExtra),
    conjoin(HeadExtra,Body,BodyM),
    demodal_body(KB,Head,BodyM,BodyO),!.
*/
demodal_head_body(KB,Head,Body,HeadBodyO):-
   demodal_head(KB,Head,HeadM,Body,HeadExtra),
   (HeadM\==Head ; HeadExtra\==true),
   conjoin(HeadExtra,Body,BodyM),
   demodal_head_body(KB,HeadM,BodyM,HeadBodyO),!.

demodal_head_body(_KB,'$unused'(Head),Body,('$unused'(Head):-Body)):-!.
demodal_head_body(_KB,Head,Body,('$unused'(Head):-Body)):- Body = fail_cause(_,_),!.
demodal_head_body(_KB,Head,Body,('$unused'(Head):-fail_cause(unusable_body,Body))):-
   unusable_body(Head,Body),!.
demodal_head_body(KB,Head,Body,OUT):-
   demodal_body(KB,Head,Body,BodyM),
   (Body=@=BodyM -> OUT= (Head :- Body) ; 
     demodal_head_body(KB,Head,BodyM,OUT)),!.


unusable_body(_,Var):- \+ compound(Var),!,fail.
unusable_body(_,fail_cause(_,_)).
unusable_body(_,fail_cause(_)).
unusable_body(_,(proven_not_reify(XX),_)):- !,nonvar(XX).
unusable_body(_,(A,B,_)):- negations_of_each_other(A,B).
unusable_body(Head,(A,B)):- !,(unusable_body(Head,A);unusable_body(Head,B)).
unusable_body(Head,(A;B)):- !,(unusable_body(Head,A);unusable_body(Head,B)).
unusable_body(_,\+ needs(_)).
unusable_body(_,fail).
% unusable_body(_,proven_neg(needs(_))).

negations_of_each_other(A,B):- A == ~B.
negations_of_each_other(A,B):- ~A == B.


gen_possible_varnames(IO):-gen_possible_varnames(IO,_).
gen_possible_varnames(I,O):-gen_possible_varnames(add_var_to_env,I,O).

gen_possible_varnames(_Each,G,G):- \+ compound(G),!.
gen_possible_varnames(Each, nameOf(V,N), nameOf(V,N)):- var(V), \+ variable_name(V,_), atomic(N),call(Each,N,V),!.
gen_possible_varnames(Each, nameOf(V,H), nameOf(V,H)):- var(V), \+ variable_name(V,_),
   compound(H),functor(H,F,_),
   flag(skolem_count,SKN,SKN+1),
   toCamelcase(F,UF),atom_concat(UF,SKN,UF1),
   call(Each,UF1,V),!.
gen_possible_varnames(Each,H,H ):- H=..[F,V],var(V),
  \+ variable_name(V,_), 
  \+ atom_concat('sk',_,F), 
  \+ atom_concat(_,'Of',F), 
  \+ atom_concat(_,'Fn',F),
  flag(skolem_count,SKN,SKN+1),
  toCamelcase(F,UF),atom_concat(UF,SKN,UF1),
  call(Each,UF1,V),!.
gen_possible_varnames(Each,H,HH ):- H=..[F|ARGS],!,must_maplist_det(gen_possible_varnames(Each),ARGS,ARGSO),!,HH=..[F|ARGSO].
gen_possible_varnames(_Each, (G), (G)):- !.

/*
LEM asserts (A v ~A) is nesisarily true.. But what if we rejected this? 
We still need to prove things.. like "prove A" or even "prove ~A" thus we are better of with:  <>(A v ~A)

"not possibly all x" can be negated to "nesc all x" without the need to invert to existential quantification

all x: ~P(x)

all x: ~P(x) === all x: ~<>P(x)  

which can be negated to    all x: <>P(x)  without switching to existental quantification

negates to  <> all P()



meaning a new rule can make something that was once not possible to prove, become provable
<>~P or <>P can become either []P or []~P later (but afterwards will not change)
this doesnt nesc imply defeasably, but implies elaboration tollerance






(A v ~A) in order to deal with   ?(A v ~A)   ?A ? ~<>A
[]A v ~<>A
*/
body_contains(B,Cont):- sub_term(SK,B),compound(SK),SK=Cont.


% demodal_head(_KB,proven_not_tru(skolem(A,B)),unused_skolem(A,B,KB),true):- nonvar(B),!.
% demodal_head(_KB,proven_not_reify(A),'$unused'(proven_not_reify(A)),_Body,true):- nonvar(A),!.
% demodal_head(_KB,proven_neg(needs(Head)),'$unused'(proven_neg(needs(Head))),_Body,true):- !.

demodal_head(KB,proven_tru(skolem(X,Y,KB)),make_existential(X,Y,KB),_Body,true).
demodal_head(KB,proven_neg(skolem(X,Y,KB)),'$unused'(unmake_existential(X,Y,KB)),_Body,true).
demodal_head(KB,proven_tru(H),deduce_tru(H),Body,true):- body_contains(Body,skolem(_,_,KB)).
demodal_head(KB,proven_neg(H),never_any(H),Body,true):- body_contains(Body,skolem(_,_,KB)).
demodal_head(_KB,proven_tru(H),pro_tru(H),_Body,true).
demodal_head(_KB,proven_neg(H),con_neg(H),_Body,true).

demodal_head(KB,Head,HeadM,_Body,HeadExtra):- demodal_any(KB,Head,HeadM,HeadExtra).


sharing_vars_vars(A,B):- term_variables(A,AV),term_variables(B,BV),member(VB,BV),member(VA,AV),VB==VA.



% demodal_any(_KB,different(A,B),not_equals(A,B),true):-!.
demodal_any(_KB,proven_not_tru(different(A,B)),proven_tru(equals(A,B)),true):-!.
demodal_any(_KB,proven_not_tru(equals(A,B)),proven_tru(different(A,B)),true):-!.
demodal_any(_KB,proven_not_tru(mudEquals(A,B)), proven_tru(different(A,B)),true):-!.
demodal_any(_KB, not_nesc(b_d(_7B2, nesc, poss), A v ~B), (~A & B),true) :-!.
demodal_any(_KB,proven_not_tru(isa(A,B)),not_isa(A,B),true):- nonvar(B),!.
demodal_any(_KB,naf(proven_not_tru(Head)),poss(Head),true):- !.
% demodal_any(_KB,Head,Head,true):- current_prolog_flag(logicmoo_propagation, modal),!.
demodal_any(KB,nesc(Head),Head,Out):- !,demodal_any(KB,Head,Head,Out).
demodal_any(_KB,Head,Head,true):- !.
% demodal_any(KB,Head,HeadO,true):-  demodal_clauses(KB,Head,HeadO).


demodal_body(_KB,_Head,Var, Var):- \+compound(Var),!.  
% DISABLER demodal_body(_KB,_Head,Var, Var):-!.

% demodal_body(KB, Head, Body, _):- dmsg(demodal_body(KB, Head, Body)),fail.

demodal_body(KB, Head, (Var, Rest), NEW):- var(Var),!,demodal_body(KB, Head,  Rest, NewRest),conjoin(NewRest,Var,NEW).
demodal_body(_KB,_Head, poss([infer_by(_)],G), poss(G)).
demodal_body(_KB,_Head, nesc([infer_by(_)],G), nsec(G)).

demodal_body(_KB, _Head, ((A , B) , C), (A , B , C)):- nonvar(A),!.
demodal_body(_KB, _Head, (A , B , C), (A , B)):- A==C,!.
demodal_body(_KB, _Head, (A , B , C), (A , C)):- A==B,!.
demodal_body(_KB, _Head, (A , B , C), (A , C)):- B==C,!.

demodal_body(_KB,_Head, poss(poss( G)), poss(G)):- nonvar(G),!.

demodal_body(KB,  Head, proven_not_neg(skolem(X,Y,KB)), OUT):- !, demodal_body(KB,  Head, (skolem(X,Y,KB)), OUT).

demodal_body(KB,  (make_existential(X,_,KB)), proven_not_neg(G), ensure_dom(X,G)):- term_variables(G,Vars),memberchk(V,Vars),X==V.
demodal_body(KB,  (make_existential(X,_,KB)), proven_not_tru(G), never_dom(X,G)):- term_variables(G,Vars),memberchk(V,Vars),X==V.
demodal_body(KB,  (make_existential(X,_,KB)), proven_not_neg(G), require_xdoms(G)):-  contains_var(X,G).
demodal_body(KB,  (make_existential(X,_,KB)), proven_not_tru(G), never_xdoms(Vars,G)):- term_variables(G,Vars),contains_var(X,G).
demodal_body(KB,  (make_existential(_,SK,KB)), proven_not_neg(G), require_tru(G)):- sharing_vars_vars(SK,G).
demodal_body(KB,  (make_existential(_,SK,KB)), proven_not_tru(G), never_v(G)):- sharing_vars_vars(SK,G).




demodal_body(_KB,_Head,(H,T),(T,H)) :-  \+ poss_or_skolem(H),poss_or_skolem(T).

demodal_body(KB,Head,(A;B),BodyOut):- disjuncts_to_list((A;B),List),list_to_set(List,SET),List\==SET,!,must_maplist_det(demodal_body(KB,Head),SET,SET2),list_to_conjuncts((;),SET2,BodyOut).
demodal_body(KB,Head,(A,B),BodyOut):- conjuncts_to_list((A,B),List),list_to_set(List,SET),List\==SET,!,must_maplist_det(demodal_body(KB,Head),SET,SET2),list_to_conjuncts(SET2,BodyOut).

demodal_body(KB,Head,[H|T],[HH|TT]):- !, must(( demodal_body(KB,Head,H,HH),demodal_body(KB,Head,T,TT))),!.
demodal_body(KB,Head,(H;T),(HH;TT)):- !, must(( demodal_body(KB,Head,H,HH),demodal_body(KB,Head,T,TT))),!.
demodal_body(KB,Head,(H,T),(HH,TT)):- T\=(_,_),!, must(( demodal_body(KB,Head,H,HH),demodal_body(KB,Head,T,TT))),!.
demodal_body(KB,Head,(H,T),(HH,TT)):- !, must(( demodal_body(KB,Head,H,HH),demodal_body(KB,Head,T,TT))),!.


% demodal_body(_KB,  _Head, proven_neg(skolem(_,_,_)), fail_cause(naf_sk,proven_neg(skolem(_,_,_)))):-!.
% demodal_body(_KB,  _Head, proven_not_tru(skolem(_,_,_)), fail_cause(naf_neg_sk,proven_not_tru(skolem(_,_,_)))):-!.
% demodal_body(_KB,  never_any(_) , Body ,  fail_cause(naf_sk,Body)) :- body_contains(Body,never_any(skolem(_,_,_))).

demodal_body(_KB,  _ , Body ,  fail_cause(naf_sk,Body)) :- body_contains(Body,never_any(skolem(_,_,_))).
demodal_body(_KB,  _ , Body ,  fail_cause(naf_sk,Body)) :- body_contains(Body,never_deduce(skolem(_,_,_))).
demodal_body(_KB,  _ , Body ,  fail_cause(naf_sk,Body)) :- body_contains(Body,falsify(skolem(_,_,_))).

demodal_body(_KB,  deduce_tru(_Head), proven_not_neg(X), pro_tru(X)):-!.
demodal_body(_KB,  deduce_tru(_Head), proven_not_tru(X), never_deduce(X)):-!.

demodal_body(_KB,  never_any(_Head), proven_not_neg(X), induce_tru(X)):-!.
demodal_body(_KB,  never_any(_Head), proven_not_tru(X), never_any(X)):-!.

demodal_body(KB,  never_any(Head), skolem(X,_SK, KB), true):- \+ sharing_vars_vars(Head,X).
% demodal_body(_KB,  never_any(Head), skolem(X,_SK, KB), var(X)):- \+ sharing_vars_vars(Head,X).



demodal_body(_KB,  pro_tru(_Head), proven_not_neg(X), pro_tru(X)):-!.
demodal_body(_KB,  pro_tru(_Head), proven_not_tru(X), deduce_neg(X)):-!.

demodal_body(_KB,  con_neg(_Head), proven_not_neg(X), induce_tru(X)):-!.
demodal_body(_KB,  con_neg(_Head), proven_not_tru(X), con_neg(X)):-!.


demodal_body(_KB,   (_Head), proven_not_neg(X), tru(X)):-!.
demodal_body(_KB,   (_Head), proven_not_tru(X), falsify(X)):-!.


demodal_body(KB, _Head, Body,BodyO):- demodal_any(KB,Body,BodyM,Conj), (BodyM\==Body;Conj\==true),  conjoin(Conj,BodyM,BodyO).
demodal_body(KB,Head,H,HH ):- H=..[F|ARGS],!,must_maplist_det(demodal_body(KB,Head),ARGS,ARGSO),!,HH=..[F|ARGSO].
demodal_body(_KB,_Head, (G), (G)):- !.


:- if(false).
demodal_body(_KB, _Head, ((A , B) ; (C , D)), (A , (B ; D))):- A==C,!.
demodal_body(_KB, _Head, proven_tru(X),  X).
demodal_body(_KB, _Head, proven_neg(X), ~ X).
% demodal_body(_KB, _Head, proven_not_tru(X), \+ X).
demodal_body(_KB, proven_neg(_Head), \+ ~ CMP, true):- compound(CMP),CMP=(skolem(_,_,_)).
% demodal_body(_KB, _Head, ((A ; B), C), (C, once(B ; A))).
% demodal_body(_KB, _Head, (C, (A ; B)), ((B ; A), C)).
demodal_body(_KB, proven_neg(Head), (Other,(\+ BHead ; ~Other1)),naf(BHead)):- BHead == Head,Other=Other1.
demodal_body(_KB, proven_neg(Head), (Other,( ~Other1 ; \+ BHead )),naf(BHead)):- BHead == Head,Other=Other1.
demodal_body(_KB, _Head, (A, proven_isa(I, C)), (proven_isa(I, C), A)):- A \= proven_isa(_, _).
% demodal_clauses(KB,G,O):- G=..[F,H], \+ leave_as_is(H), H=..[HF,HH], atom_compat(F,HF,HHF),!, GG=..[HHF,HH], demodal_clauses(KB,GG,O).
demodal_body(_KB,_Head,naf(~(CMP)),CMP):- poss_or_skolem(CMP).
demodal_body(_KB,Head, v(A, ~(B)), ~(B)):- A==Head,!.
demodal_body(_KB,Head, v(~(B), A), ~(B)):- A==Head,!.
demodal_body(_KB,Head, v(A, B), B):- A==Head,!.
demodal_body(_KB,Head, v(B, A), B):- A==Head,!.
demodal_body(_KB, _Head, poss(A & B), (poss(A) , poss(B))):-nonvar(A),!.
%demodal_body(_KB, ~(_Head),(G1,G2), (G1 , \+ GG2)):- G2 \= (_,_), G2 == ~(GG2).
%demodal_body(_KB,_Head,(G1,G2), (G1, poss(GG2) )):- G2 \= (_,_), G2 == ~(GG2), nonvar(GG2).
demodal_body(KB,Head,(H & T),(HH,TT)):- !, must(( demodal_body(KB,Head,H,HH),demodal_body(KB,Head,T,TT))),!.
demodal_body(KB,Head,(H,T),(HH,TT)):- !, must(( demodal_body(KB,Head,H,HH),demodal_body(KB,Head,T,TT))),!.
demodal_body(KB,Head,(H v T),(HH v TT)):- !, must(( demodal_body(KB,Head,H,HH),demodal_body(KB,Head,T,TT))),!.
% demodal_body(_KB, _Head, G, G):- !.
demodal_body(_KB, Head, G, true):- G==Head, unusual_body,!.
% demodal_body(_KB,_Head, poss(isa(I,C)), isa(I,C)):- !.
demodal_body(_KB,_Head, naf(~(G)), poss(G)):- nonvar(G),!.
demodal_body(_KB,_Head, ~(~(G)), (G)):- nonvar(G), unusual_body,!.
demodal_body(_KB, _Head, not_nesc(b_d(_KB2, nesc, poss), A v ~B), (~A , B)) :-!.
demodal_body(KB,Head, v(~(A), B), BB):- demodal_body(KB,Head,A,AA),AA==Head,!,demodal_body(KB,Head,B,BB).
%demodal_body(KB,Head, v(~(B), A), BB):- demodal_body(KB,Head,A,AA),AA==Head,!,demodal_body(KB,Head,B,BB).
demodal_body(KB,Head, v(~(A), B), (AA *-> BB)):- nonvar(A),!,demodal_body(KB,Head,A,AA),demodal_body(KB,Head,B,BB).
%demodal_body(_KB,_Head, \+ (~(G)), proven(G)):- nonvar(G),!.
demodal_body(_KB,_Head, \+ (~(G)), poss(G)):- nonvar(G),!.
demodal_body(_KB, _Head, ( H, poss(G) ) , poss(G)):- H==G , unusual_body.
demodal_body(_KB, _Head, ( H, (G) ) , (G)):- H==G, unusual_body.
demodal_body(_KB, _Head, ( H, G ) , G):- H==true, unusual_body.
demodal_body(_KB, _Head, ( G, H ) , G):- H==true, unusual_body.
demodal_body(_KB, _Head, ( G *-> H ) , G):- H==true, unusual_body.
demodal_body(_KB, _Head, ( H *-> G ) , G):- H==true, unusual_body.
%demodal_body(_KB, Head, ( H, poss(G) ) , (H, G)):- pos_or_isa(H), pred_of(Head,GHead)-> G \= GHead,!.
%demodal_body(_KB, Head, ( poss(G) , H) , (G, H)):-  pos_or_isa(H), pred_of(Head,GHead)-> G \= GHead,!.
%demodal_body(_KB, Head, ( poss(G) ) , (G)):-  shared_vars(Head,G,SVG),SVG==[].
%demodal_body(_KB, Head, ( poss(G) ) , (G)):- Head \= ~(_),!.
demodal_body(_KB,_Head, poss(poss( G)), poss(G)):- nonvar(G),!.
demodal_body(KB,Head,[H|T],[HH|TT]):- !, must(( demodal_body(KB,Head,H,HH),demodal_body(KB,Head,T,TT))),!.
demodal_body(KB,Head,(H;T),(HH;TT)):- !, must(( demodal_body(KB,Head,H,HH),demodal_body(KB,Head,T,TT))),!.
demodal_body(KB,Head,(H,T),(HH,TT)):- current_prolog_flag(logicmoo_propagation, modal),
   T\=(_,_),!, must(( demodal_body(KB,Head,H,HH),demodal_body(KB,Head,T,TT))),!.
% demodal_body(_KB,_Head, (G), (G)):- current_prolog_flag(logicmoo_propagation, modal),!.
demodal_body(KB,Head,H,HH ):- H=..[F|ARGS],!,must_maplist_det(demodal_body(KB,Head),ARGS,ARGSO),!,HH=..[F|ARGSO].
:- endif.






:- fixup_exports.
