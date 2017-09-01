%:- if(( ( \+ ((current_prolog_flag(logicmoo_include,Call),Call))) )).
:- module(common_logic_exists,[existentialize/2,

         nnf_shared/5,
         skolem_bad/4,
         skolem_f/5,
         skolem_fn/6,
         skolem_fn_shared/6,
         mk_skolem/5,mk_skolem_name/5,nnf_label/5,
         nnf_ex/5,
         form_sk/2,
         sk_form/2,
         push_skolem/2,push_skolem/3,
         push_dom/2,
         annote/4,
         annote/3,
         skolem_unify/2,
         show_attrs/1,            
         isaDom/2,
         push_cond/2,
         is_value/1,
         skolem_test/1,
         destructive_replace/3,
         mpred_constrain_w_proxy/1,
         mpred_constrain_w_proxy_enter/3,
         mpred_set_arg_isa/4,
         with_no_kif_var_coroutines/1
	  ]).
/** <module> common_logic_skolem
% Provides a prolog database replacement that uses an interpretation of KIF
%
%  t/N
%  hybridRule/2
%  
%
% Logicmoo Project PrologMUD: A MUD server written in Prolog
% Maintainer: Douglas Miles
% Dec 13, 2035
%
*/
% NEW
:- include(library('pfc2.0/mpred_header.pi')).
%:- endif.
:- use_module(library(dictoo)).
:- meta_predicate skolem_test(0).
:- meta_predicate skolem_unify(*,0).

:- ensure_loaded(library(attvar_reader)).
:- reexport(library(dictoo)).

:- module_transparent with_no_kif_var_coroutines/1.

with_no_kif_var_coroutines(Goal):- locally_each(t_l:no_kif_var_coroutines(true),Goal).

/* module Form Prolog sks (debugging)
*/

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

/*

  existentialize( +FmlIn, -FmlOut, [options...]).


      converts terms like...

         loves(joe,mary)

      Into...

         exists([R,X,Y,T], 
            ((subRelation(R,loves), is_a(T,time), is_a(T,context),
              exists_durring(X,T),exists_durring(Y,T),
              ~different(joe,X),~different(mary,Y)) 
                  => trueIn(T,holds(R,X,Y)))).


      options are...


*/

existentialize(P,NewPIn):- 
 get_named_objects(P,Names),
  (Names\==[]-> existsentialize_objects(Names,P,NewP) ; P=NewP),!,
  NewP = NewPIn.

existentialize_v2(exists(X,P),exists(X,P)):-nonvar(P),!.
existentialize_v2(P,NewPIn):- get_named_objects(P,Names),
  (Names\==[]-> existsentialize_objects(Names,P,NewP) ; P=NewP),!,
  NewP = NewPIn.


already_existentialized(Term,Str):-  sub_term(NameOf,Term), compound(NameOf), NameOf=nameOf(_,StrW), name(Str,StrW) .
already_existentialized(Term,Str):-  sub_term(NameOf,Term), compound(NameOf), NameOf=exists(X,_),Str==X.

should_existentialize(Term,~ Sub,Str):-!,compound(Sub), should_existentialize(Term,Sub,Str).
should_existentialize(Term,Sub,Str) :- compound(Sub),functor(Sub,F,A),
  \+ dont_existentialize_args(Term,F,A),
  arg(_N,Sub,Text),
  (string(Text);(existentialize_args(Term,F,A),atom(Text))),
  text_to_string(Text,Str).

existentialize_args(Term,F,A):- 
  \+ dont_existentialize_args(Term,F,A),
  do_existentialize_f(F).

do_existentialize_f(loves).
do_existentialize_f(man).

dont_existentialize_args(_Term,F,_A):- dont_existentialize_f(F).

dont_existentialize_f(skolem).
dont_existentialize_f(nameOf).
dont_existentialize_f(equals).
dont_existentialize_f(different).

get_named_objects(Term,Names):- 
   findall(Str,
    (sub_term(Sub,Term),
      should_existentialize(Term,Sub,Str),
      \+ already_existentialized(Term,Str)),
     NamesL),
   list_to_set(NamesL,Names).

existsentialize_objects([],P,P).
existsentialize_objects([Name|TODO],P,exists(X,(nameOf(X,Name),NewP))):-
   name(Atom,Name),
   subst(P,Atom,X,NextPM),
   subst(NextPM,Name,X,NextP),
   existsentialize_objects(TODO,NextP,NewP).
                                    



/*

  rejiggle_quants( +FmlIn, -FmlOut, [options...]).


      converts terms like...

         forall(P,exists(M, person(P) => mother(P,M))).

      Into...

         forall(P, person(P) => exists(M, mother(P,M))).


      options are...


*/
% =================================
% Quanitifier Expansions
% =================================

rejiggle_quants(KB,In,Out2):-
  expandQuants(KB,In,Mid1),
  moveInwardQuants([],elim(all),KB,Mid1,Mid2),
  un_quant3(KB,Mid2,Out),
  Out2 = Out.

expandQuants(_,Fml,Fml):- is_leave_alone(Fml),!.
expandQuants(_,[],[]):- !.
expandQuants(KB,[A|B],[AO|BO]):- expandQuants(KB,A,AO),expandQuants(KB,B,BO),!.

expandQuants(KB,all(XL,NNF),FmlO):- is_list(XL),
    (get_quantifier_isa(XL,X,Col) -> 
      expandQuants(KB,all(X,isa(X,Col) => NNF),FmlO);
      (XL=[X|MORE],!,
      (MORE==[] -> 
            expandQuants(KB,all(X,NNF),FmlO);
            expandQuants(KB,all(X,all(MORE,NNF)),FmlO)))).

expandQuants(KB,exactly(N,X,NNF),FmlO):- expandQuants(KB,quant(exactly(N),X,NNF),FmlO).
expandQuants(KB,atleast(N,X,NNF),FmlO):- expandQuants(KB,quant(atleast(N),X,NNF),FmlO).
expandQuants(KB,atmost(N,X,NNF),FmlO):- expandQuants(KB,quant(atmost(N),X,NNF),FmlO).
expandQuants(KB,exists(X,NNF),FmlO):- expandQuants(KB,quant(exists,X,NNF),FmlO).
expandQuants(KB,some(X,NNF),FmlO):- expandQuants(KB,quant(exactly(1),X,NNF),FmlO).
expandQuants(KB,quant(Quant,XL,NNF),FmlO):- is_list(XL),
    (get_quantifier_isa(XL,X,Col) -> 
      expandQuants(KB,quant(Quant,X,quant(isa(Col),X, NNF)),FmlO);
      (XL=[X|MORE],!,
      (MORE==[] -> 
            expandQuants(KB,quant(Quant,X,NNF),FmlO);
            expandQuants(KB,quant(Quant,X,quant(Quant,MORE,NNF)),FmlO)))).

expandQuants(KB,PAB,FmlO):- PAB=..[F|AB], must_maplist_det(expandQuants(KB),AB,ABO), FmlO=..[F|ABO].

un_quant3(_,Fml,Fml):- is_leave_alone(Fml),!.
un_quant3(KB,all(X,NNF),all(X,FmlO)):- !,un_quant3(KB,NNF,FmlO).
un_quant3(KB,quant(isa(K),X,NNF),FmlO):- un_quant3(KB,NNF,NNFO),un_quant3(KB,isa(X,K) & NNFO,FmlO).
un_quant3(KB,quant(Quant,X,NNF),FmlO):- un_quant3(KB,NNF,NNFO),Quant=..[Q|AUNT],append([Q|AUNT],[X,NNFO],STERM),FmlO=..STERM.
un_quant3(KB,PAB,FmlO):- PAB=..[F|AB], must_maplist_det(un_quant3(KB),AB,ABO), FmlO=..[F|ABO].

contains_compound(IN,CMP):-
 \+ ((sub_term(SUB,IN),compound(SUB),SUB=CMP)).

term_each_slot(IN,SUB):- sub_term(SUB,IN),is_ftVar(SUB).


%% moveInwardQuants(VarsQ,MayElimAll, ?KB, ?Kif, ?FmlO) is det.
%
% Move Existential Quantifiers Inward
%
moveInwardQuants(_,_,_,Fml,Fml):- is_leave_alone(Fml),!.
moveInwardQuants(_,_,_,[],[]):- !.
moveInwardQuants(_,_,_,~(NNF),~(FmlO)):-!,NNF=FmlO.
moveInwardQuants(VarsQ,MayElimAll,KB,[A|B],[AO|BO]):- moveInwardQuants(VarsQ,MayElimAll,KB,A,AO),moveInwardQuants(VarsQ,MayElimAll,KB,B,BO),!.
moveInwardQuants(VarsQ,cant(May),KB,all(X,NNF),all(X,FmlO)):-!,moveInwardQuants([X|VarsQ],cant(May),KB,NNF,FmlO).
moveInwardQuants(VarsQ,MayElimAll,KB,all(X,NNF),all(X,FmlO)):-!,moveInwardQuants([X|VarsQ],MayElimAll,KB,NNF,FmlO).


moveInwardQuants(VarsQ,MayElimAll,KB,quant(Quant,X,all(Y,FmlAB)),quant(Quant,X,FmlABM)):- !,
  moveInwardQuants([X|VarsQ],cant(MayElimAll),KB,all(Y,FmlAB),FmlABM).

moveInwardQuants(VarsQ,MayElimAll,KB,quant(Quant,X,quant(Q2,Y,FmlAB)),quant(Quant,X,FmlABM)):- !,
  moveInwardQuants([X|VarsQ],cant(MayElimAll),KB,quant(Q2,Y,FmlAB),FmlABM).

/*
moveInwardQuants(VarsQ,MayElimAll,KB,quant(Quant,X,FmlAB),quant(Quant,X,FmlABM)):- 
  (term_each_slot(FmlAB,Var),Var\==X,\+ member_eq(Var,VarsQ)),!,
  moveInwardQuants([Var,X|VarsQ],cant(MayElimAll),KB,FmlAB,FmlABM).
*/

moveInwardQuants(VarsQ,MayElimAll,KB,quant(Quant,X,FmlAB),FmlABO):- split_dlog_formula(FmlAB,OP,FmlA,FmlB),
   (((not_contains_var(X,FmlB)-> (moveInwardQuants(VarsQ,cant(MayElimAll),KB,quant(Quant,X,FmlA),FmlAO),unsplit_dlog_formula(OP,FmlAO,FmlB,FmlABO)));
   ((not_contains_var(X,FmlA)-> (moveInwardQuants([X|VarsQ],cant(MayElimAll),KB,quant(Quant,X,FmlB),FmlBO),unsplit_dlog_formula(OP,FmlA,FmlBO,FmlABO)));
    fail))),!.

moveInwardQuants(VarsQ,MayElimAll,KB,quant(Quant,X,FmlAB),quant(Quant,X,FmlABM)):- 
   moveInwardQuants([X|VarsQ],cant(MayElimAll),KB,FmlAB,FmlABM).


moveInwardQuants(VarsQ,MayElimAll,KB,PAB,FmlO):- PAB=..[F|AB], must_maplist_det(moveInwardQuants(VarsQ,MayElimAll,KB),AB,ABO), FmlO=..[F|ABO].



% =================================
% Typed (Exactly/AtMost/AtLeast 2 ((?x Man)(?y Woman)(?z Child)) ...                     )
% =================================

nnf_ex(KB,exactly(N,XL,NNF),FreeV,FmlO,Paths):- is_list(XL),
    (get_quantifier_isa(XL,X,Col) -> 
      nnf(KB,exactly(N,X,isa(X,Col) & NNF),FreeV,FmlO,Paths);
      (XL=[X|MORE],!,
      (MORE==[] -> 
            nnf(KB,exactly(N,X,NNF),FreeV,FmlO,Paths);
            nnf(KB,exactly(N,X,exactly(N,MORE,NNF)),FreeV,FmlO,Paths)))).

nnf_ex(KB,atleast(N,XL,NNF),FreeV,FmlO,Paths):- is_list(XL),
    (get_quantifier_isa(XL,X,Col) -> 
      nnf(KB,atleast(N,X,isa(X,Col) & NNF),FreeV,FmlO,Paths);
      (XL=[X|MORE],!,
      (MORE==[] -> 
            nnf(KB,atleast(N,X,NNF),FreeV,FmlO,Paths);
            nnf(KB,atleast(N,X,atleast(N,MORE,NNF)),FreeV,FmlO,Paths)))).

nnf_ex(KB,atmost(N,XL,NNF),FreeV,FmlO,Paths):- is_list(XL),
    (get_quantifier_isa(XL,X,Col) -> 
      nnf(KB,atmost(N,X,isa(X,Col) & NNF),FreeV,FmlO,Paths);
      (XL=[X|MORE],!,
      (MORE==[] -> 
            nnf(KB,atmost(N,X,NNF),FreeV,FmlO,Paths);
            nnf(KB,atmost(N,X,atmost(N,MORE,NNF)),FreeV,FmlO,Paths)))).

% =================================
% Typed (Exists ((?x Man)(?y Woman)) ... )
% =================================

nnf_ex(KB,exists(TypedX,NNF),FreeV,FmlO,Paths):- get_quantifier_isa(TypedX,X,Col),!,
    nnf(KB,exists(X, NNF & isa(X,Col)),FreeV,FmlO,Paths).
nnf_ex(KB,exists(XL,NNF),FreeV,FmlO,Paths):- is_list(XL),XL=[X],!,
    nnf(KB,exists(X,NNF),FreeV,FmlO,Paths).
nnf_ex(KB,exists(XL,NNF),FreeV,FmlO,Paths):- is_list(XL),XL=[X|MORE],!,
    nnf(KB,exists(X,exists(MORE,NNF)),FreeV,FmlO,Paths).



% nnf_ex(KB,exists(X,Fml),FreeV,NNF,Paths):-  \+ contains_var(X,Fml),!, trace_or_throw(bad_nnf(KB,exists(X,Fml),FreeV,NNF,Paths)).
% maybe this instead ? 
nnf_ex(KB,exists(X,Fml),FreeV,NNF,Paths):-  \+ contains_var(X,Fml),dmsg(( \+ contains_var(X,Fml))),!,nnf(KB,Fml,FreeV,NNF,Paths).


% ATTVAR WAY
nnf_ex(KB,exists(X,Fml),FreeV,NNF1,Paths):- is_skolem_setting(in_nnf_implies),!,
 must_det_l((
    term_slots(FreeV+X,Slots),
    % add_dom(X,extensional(X)),
    skolem_f(KB, Fml, X, Slots, SkF),    
    nnf(KB, Fml <=> skolem(X,SkF),Slots,NNF1,Paths)
   )),!.

% NEW NORMAL WAY
nnf_ex(KB,exists(X,Fml),FreeV,NNF1,Paths):- is_skolem_setting(in_nnf_implies),!,
 must_det_l((
    term_slots(FreeV,Slots),
    skolem_f(KB, Fml, X, Slots, SkF),
    subst(Fml,X,SkF,FmlSk),
        nnf(KB, (  ~(  ~skolem(X,SkF) v FmlSk )=> Fml),Slots,NNF1,Paths)
   )),!.

% OLD NORMAL WAY
nnf_ex(KB,exists(X,Fml),FreeV,NNF,Paths):- is_skolem_setting(in_nnf_implies),!,
 must_det_l((
    term_slots(FreeV,Slots),
    skolem_f(KB, Fml, X, Slots, SkF),
    subst(Fml,X,SkF,FmlSk),
        nnf(KB,FmlSk,Slots,NNF,Paths)
   )),!.


%  one interesting trick i started to take  all P and convert to  <>P=[_]P  


% NEEDS WAY
% disabled
nnf_ex(KB,exists(X,Fml),FreeV,NNF1NNF2,Paths):- fail, is_skolem_setting(in_nnf_implies),!,
 must_det_l((
    term_slots(Fml+FreeV+X,Slots),
       delete_eq(Slots,X,SlotsV1),delete_eq(SlotsV1,KB,SlotsV2),    
    skolem_f(KB, Fml, X, SlotsV2, SkF),
    subst(Fml,X,SkF,FmlSk),
    nnf(KB,(~ poss(b_d(KB,nesc,poss),Fml) => needs(SkF)),SlotsV2,NNF1,_Paths1),    
    nnf(KB,((needs(SkF) => FmlSk)),SlotsV2,NNF2,_Paths2),
    nnf(KB,(NNF1 & NNF2),[X|FreeV],NNF1NNF2,Paths)
       )),!.

% NEW NORMAL WAY
% disabled
nnf_ex(KB,exists(X,Fml),FreeV,NNF,Paths):-  fail, is_skolem_setting(in_nnf_implies),!,
 must_det_l((
    term_slots(Fml+FreeV+X,Slots),delete_eq(Slots,X,SlotsV1),delete_eq(SlotsV1,KB,SlotsV2),
    nnf(KB,~(~(Fml)),SlotsV2,NNFInner1,_),
    nnf(KB,NNFInner1,SlotsV2,NNFInner,_),
    removeQ(KB,NNFInner,UQ),
    cnf(KB, (UQ),Inner),
    removeQ(KB,Inner,UInnerQ),
    skolem_f(KB, Fml, X, SlotsV2, SkF),
    subst(Fml,X,SkF,FmlSk),
    nnf(KB, (UInnerQ) => ~poss(b_d(KB,nesc,poss),~FmlSk),SlotsV2,NNF,Paths)
   )),!.


% "NEEDS" based WAY
nnf_ex(KB,exists(X,FmlIn),FreeV,NNF1NNF2,Paths):- is_skolem_setting(in_nnf_implies),!,
 must_det_l((
    term_slots(FmlIn+FreeV+X,Slots),
       delete_eq(Slots,X,SlotsV1),delete_eq(SlotsV1,KB,SlotsV2),
    
    nnf(KB,FmlIn,SlotsV2,Fml,_Paths),
    subst(Fml,X,SkF,FmlSk),
    skolem_f(KB, Fml, X, SlotsV2, SkF),
    nnf(KB,(~ nesc(b_d(KB,nesc,poss),Fml) => needs(SkF)),SlotsV2,NNF1,_Paths1),    
    nnf(KB,((needs(SkF) => FmlSk)),SlotsV2,NNF2,_Paths2),
    nnf(KB,(NNF1 & NNF2),FreeV,NNF1NNF2,Paths)
   )),!.


nnf_ex(KB,exists(X,Fml),FreeV,NNF,Paths):- is_skolem_setting(in_nnf_implies),!,
 must_det_l((
       term_slots(Fml+FreeV+X,Slots),
       delete_eq(Slots,X,SlotsV1),delete_eq(SlotsV1,KB,SlotsV2),
    skolem_f(KB, Fml, X, SlotsV2, SkF),
    push_skolem(X,SkF),
    nnf(KB,(~(skolem(X,SkF)) v Fml),SlotsV2,NNF,Paths)
   )),!.

% disabled
nnf_ex(KB,exists(X,Ante=>FmlIn),FreeV,NNF,Paths):- fail, is_skolem_setting(in_nnf_implies),!,
 nnf(KB,FmlIn,FreeV,Fml,_Paths),
 must_det_l((
    term_slots(Fml+FreeV+X,Slots),
    delete_eq(Slots,X,SlotsV1),delete_eq(SlotsV1,KB,SlotsV2),
    skolem_f(KB, Fml, X, SlotsV2, SkF),
    subst(Fml,X,SkF,FmlSk),
    % push_skolem(X,SkF),
    nnf(KB,~ Ante v (FmlSk v Fml),SlotsV2,NNF,Paths)
   )),!.

nnf_ex(KB,exists(X,FmlIn),FreeV,NNF,Paths):- is_skolem_setting(in_nnf_implies),!,
 nnf(KB,FmlIn,FreeV,Fml,_Paths),
 must_det_l((
    term_slots(Fml+FreeV+X,Slots),
    delete_eq(Slots,X,SlotsV1),delete_eq(SlotsV1,KB,SlotsV2),
    skolem_f(KB, Fml, X, SlotsV2, SkF),
    subst(Fml,X,SkF,FmlSk),
    % push_skolem(X,SkF),
    nnf(KB,(FmlSk v Fml),SlotsV2,NNF,Paths)
   )),!.

nnf_ex(KB,exists(X,Fml),FreeV,NNF,Paths):- is_skolem_setting(in_nnf_implies),!,
 must_det_l((
    term_slots(Fml+FreeV+X,Slots),
    delete_eq(Slots,X,SlotsV1),delete_eq(SlotsV1,KB,SlotsV2),
    skolem_f(KB, Fml, X, SlotsV2, SkF),
    subst(Fml,X,SkF,FmlSk),
    % push_skolem(X,SkF),
    nnf(KB,(FmlSk v Fml),SlotsV2,NNF,Paths)
   )),!.

nnf_ex(KB,exists(X,Fml),FreeV,NNF,Paths):- is_skolem_setting(in_nnf_implies),!,
 must_det_l((
   nnf(KB,Fml,FreeV,NNF1,_Paths),
   term_slots(Fml+FreeV+NNF1,Slots),
    delete_eq(Slots,X,SlotsV1),delete_eq(SlotsV1,KB,SlotsV2),
    skolem_f(KB, Fml, X, SlotsV2, SkF),    
    subst(NNF1,X,SkF,FmlSk),
   nnf(KB, (~(nesc(NNF1)) => nesc(FmlSk)),[X|Slots],NNF,Paths))),!.

/*
nnf_ex(KB,exists(X,Fml),FreeV,NNF,Paths):- is_skolem_setting(in_nnf_implies),!,
 must_det_l((
   nnf(KB,Fml,FreeV,NNF1,_Paths),
   term_slots(Fml+FreeV+NNF1,Slots),
    delete_eq(Slots,X,SlotsV1),delete_eq(SlotsV1,KB,SlotsV2),
    skolem_f(KB, Fml, X, SlotsV2, SkF),
    subst(NNF1,X,SkF,FmlSk),
    % copy_term(NNF1+X,NNF2+Y),
   nnf(KB, 
    ((~(reify)(SkF) => NNF1) & 
     (reify(SkF) => FmlSk)),
     [X|Slots],NNF,Paths))),!.

*/
/*
Maybe
nnf_ex(KB,exists(X,Fml),FreeV,NNF,Paths):- is_skolem_setting(in_nnf_implies),!,
 must_det_l((
   nnf(KB,Fml,FreeV,NNF1,_Paths),
   term_slots(Fml+FreeV+NNF1,Slots),
    delete_eq(Slots,X,SlotsV1),delete_eq(SlotsV1,KB,SlotsV2),
    skolem_f(KB, Fml, X, SlotsV2, SkF),    
    subst(NNF1,X,SkF,FmlSk),
   nnf(KB, (~(nesc(NNF1)) => nesc(FmlSk)),[X|Slots],NNF,Paths))),!.

% disabled
nnf_ex(KB,exists(X,Fml),FreeV,NNF,Paths):- is_skolem_setting(in_nnf_implies),!,
 must_det_l((
   nnf(KB,Fml,FreeV,NNF1,_Paths),
   term_slots(Fml+FreeV+NNF1,Slots),
    delete_eq(Slots,X,SlotsV1),
    delete_eq(SlotsV1,KB,SlotsV2),
    skolem_f(KB, Fml, X, SlotsV2, SkF),
   subst(NNF1,X,SkF,FmlSk),nnf(KB, FmlSk ,[X|Slots],NNF,Paths))),!.

% disabled
nnf_ex(KB,exists(X,Fml),FreeV,NNF,Paths):- is_skolem_setting(in_nnf_implies),!,
 must_det_l((
   add_to_vars(X,FreeV,NewVars),
    term_slots(NewVars,Slots),
    delete_eq(Slots,X,SlotsV1),
    delete_eq(SlotsV1,KB,SlotsV2),
    skolem_f(KB, Fml, X, SlotsV2, SkF),
    push_skolem(X,SkF),
    nnf(KB,(~(skolem(X,SkF)) v Fml),NewVars,NNF,Paths)
   )),!.

% disabled
nnf_ex(KB,exists(X,Fml),FreeV,exists(X,NNF),Paths):- (is_skolem_setting(removeQ);is_skolem_setting(attvar)),
   add_to_vars(X,FreeV,NewVars),
   nnf(KB,Fml,NewVars,NNF,Paths),!.

% disabled
nnf_ex(KB,exists(X,Fml),FreeV,NNF,Paths):- is_skolem_setting(in_nnf),!,
 must_det_l((
   add_to_vars(X,FreeV,NewVars),
    term_slots(NewVars,Slots),
    delete_eq(Slots,X,SlotsV1),
    delete_eq(SlotsV1,KB,SlotsV2),
    skolem_f(KB, Fml, X, SlotsV2, SkF),
    push_skolem(X,SkF),
   nnf(KB,Fml,NewVars,NNF,Paths))),!.

% disabled
nnf_ex(KB,exists(X,Fml),FreeV,NNF,Paths):- is_skolem_setting(push_skolem),!, wdmsg(nnf_ex(skolemizing(push_skolem,exists(X,Fml)))),
   push_skolem(X,true),
   nnf(KB,Fml,FreeV,NNF,Paths).

% disabled
nnf_ex(KB,exists(X,Fml),FreeV,NNF,Paths):- is_skolem_setting(old_mk_skolem),!, wdmsg(nnf_ex(skolemizing(exists(X,Fml),with(FreeV)))),
   must(mk_skolem(KB,Fml,X,FreeV,FmlSk)),
   nnf(KB,FmlSk,FreeV,NNF,Paths).

% exists(X,nesc(f(X)))  ->  exists(X, ~( poss( ~( f(X))))) ->   ~( poss( ~( f(X))))
% disabled
nnf_ex(KB,exists(_X,Fml),FreeV,NNF,Paths):- fail, nnf(KB, ~( poss(b_d(KB,nesc,poss), ~( Fml))),FreeV,NNF,Paths).

% disabled
nnf_ex(KB,exists(X,Fml),FreeV,NNF,Paths):- is_skolem_setting(label),
   nnf_label(KB,exists(X,Fml),FreeV,NNF,Paths),!.

% disabled
nnf_ex(KB,exists(X,Fml),FreeV,NNF,Paths):- is_skolem_setting(shared),
   nnf_shared(KB,exists(X,Fml),FreeV,NNF,Paths),!.

% disabled
nnf_ex(KB,exists(X,Fml),FreeV,NNF,Paths):- is_skolem_setting(ignore),
   add_to_vars(X,FreeV,NewVars),
   nnf(KB,Fml,NewVars,NNF,Paths).
*/


% =================================
% ==== AtLeast N ========
% ==== Cardinality (quantifier macros) ========
% =================================

% AtLeast 1:  We simply create the existence of 1
nnf_ex(KB,atleast(N,X,Fml),FreeV,NNF,Paths):- N==1, !,
   nnf(KB,exists(X,Fml),FreeV,NNF,Paths).

nnf_ex(KB,thereExistsAtLeast(N,X,Fml),FreeV,NNF,Paths):-!, nnf_ex(KB,atleast(N,X,Fml),FreeV,NNF,Paths).

% AtLeast 2: (This is just to confirm code .. thus, will comment out to use "AtLeast X:" rule)
nnf_ex(KB,atleast(N,X,Fml),FreeV,NNF,Paths):-  N==2, !,  
  subst_except(Fml,X,Y,FmlY),
  %  Would this work?             
  %      NEWFORM = ((exists(X,Fml) & exists(Y,FmlY) & different(X,Y))),
  %  or does it reify to be implication?
  NEWFORM =  ~  ( ~ different(X,Y) v exists(X,Fml)) v exists(Y,FmlY),
  nnf(KB,NEWFORM,FreeV,NNF,Paths).


% AtLeast N:  If AtLeast 4 above is correct than AtLeast N is correcT?
nnf_ex(KB,atleast(N,X,Fml),FreeV,NNF,Paths):-  is_using_feature(list_macros),!,
   length(SET,N),
   NEWFORM = (~skolem(X,skFn({onlyId(_Id,X,SET)}&Fml)) v Fml),
   nnf(KB,NEWFORM,[X|FreeV],NNF,Paths).


% AtLeast 3: (This is just to confirm code .. thus, will comment out to use "AtLeast X:" rule)
nnf_ex(KB,atleast(N,X,Fml),FreeV,NNF,Paths):-  N==3, !,
  subst_except(Fml,X,Y,FmlY),subst_except(Fml,X,Z,FmlZ),
  NEWFORM = ( ~(( ~((  ~(different(X,Y) & different(X,Z) & different(Y,Z)) v (exists(X,Fml)))) v exists(Y,FmlY))) v exists(Z,FmlZ)),
  nnf(KB,NEWFORM,FreeV,NNF,Paths).

% AtLeast 4: (This is just to confirm code .. thus, will comment out to use "AtLeast X:" rule)
nnf_ex(KB,atleast(N,X,Fml),FreeV,NNF,Paths):-   N =4, fail, is_using_feature(list_macros),!,
 NEWFORM =  exists([A,B,C,D],(different(A,B) & different(A,C) & different(A,D) & different(B,C) & different(B,D) & different(C,D) 
    & {memberOf(X,[A,B,C,D])} => Fml)),
    nnf(KB,NEWFORM,FreeV,NNF,Paths).



% AtLeast N:  If AtLeast 4 above is correct than AtLeast N is correcT?
nnf_ex(KB,atleast(N,X,Fml),FreeV,NNF,Paths):- % is_using_feature(list_macros),!,
   length(SET,N),!,
      nnf_ex(KB,atleastInSet(N,X,Fml,N,SET),FreeV,NNF,Paths).

nnf_ex(_KB,atleastInSet(0,_X,_Fml,_S,_Set),_FreeV,true,1):- !.

nnf_ex(KB,atleastInSet(N,X,Fml,S,SET),FreeV,NNF,Paths):- % is_using_feature(list_macros),!,
   nth1(N,SET,X),
   NEWFORM = (~skolem(X,skFn(onlyId(N,X,SET)&Fml)) v Fml),
   N2 is N - 1, subst_except(Fml,X,X2,Fml2),
   nnf_ex(KB, ( NEWFORM & atleastInSet(N2,X2,Fml2,S,SET)),[X|FreeV],NNF,Paths).


% AtLeast N:  If AtLeast 4 above is correct than AtLeast N is correcT?
nnf_ex(KB,atleast(N,X,Fml),FreeV,NNF,Paths):- % is_using_feature(list_macros),!,
   length(SET,N),numbervars(SET,0,_),
   NEWFORM = (~skolem(X,skFn({onlyId(_Id,X,SET)}&Fml)) v Fml),
   nnf(KB,NEWFORM,[X|FreeV],NNF,Paths).

/*

% AtLeast N:  This constructs N separate Skolems.. but did i name them the same?
nnf_ex(KB,atleast(N,X,Fml),FreeV,NNF,Paths):- NewN is N - 1, !,
    subst_except(Fml,X,Y,FmlY),        
    NEWFORM =  ~ (~ (different(X,Y) v ( ~ skId(Y,N) v ((exists(Y, FmlY )))))) v atleast(NewN,X,Fml),
    nnf(KB,NEWFORM,FreeV,NNF,Paths),!.


% AtLeast N:  If AtLeast 4 above is correct than AtLeast N is correcT?
nnf_ex(KB,atleast(N,X,Fml),FreeV,NNF,Paths):- %%  is_using_feature(list_macros),!,
   length(SET,N),
   NEWFORM = (~skolem(X,skFn({allDifferent(SET) & memberOf(X,SET)}&Fml)) v Fml),
   nnf(KB,NEWFORM,[X|FreeV],NNF,Paths).

% AtLeast N:  Non list macro PFCLog version (Might prefer this?)
nnf_ex(KB,atleast(N,X,Fml),FreeV,NNF,Paths):- is_using_feature(inline_prolog),!,
    X= Skolem,
    NEWFORM =  
       ({between(1,N,Id)} => equals(Skolem, skolemIDAndFormFN(Id,Fml))),
    nnf(KB,NEWFORM,FreeV,NNF,Paths).

*/


% AtLeast N:  This constructs N separate Skolems.. but did i name them the same?
nnf_ex(KB,atleast(N,X,Fml),FreeV,NNF,Paths):- fail, NewN is N - 1, !,
    subst_except(Fml,X,Y,FmlY),             
     NEWFORM =  ( ~(different(X,Y) & exists(Y, ~skolem(Y,skIDFn(Y,N)) v FmlY)) v atleast(NewN,X,Fml)),
    % NEWFORM =  ( ~different(X,Y) v exists(Y, FmlY & atleast(NewN,X,Fml))),
    nnf(KB,NEWFORM,[X,Y|FreeV],NNF,Paths),!.

% AtLeast N:  "Non list macro version (Might prefer this?)"
nnf_ex(KB,atleast(N,X,Fml),FreeV,NNF,Paths):- NewN is N - 1, !,
    subst_except(Fml,X,Y,FmlY),        
    NEWFORM = exists(Y, (FmlY & different(X,Y) & atleast(NewN,X,Fml))),
    nnf(KB,NEWFORM,FreeV,NNF,Paths),!.

% =================================
% ==== AtMost N ========
% ==== Cardinality (quantifier macros) ========
% =================================

% AtMost 0: "There may never be even 1 and have Fml be true"
nnf_ex(KB,atmost(N,X,FmlIn),FreeV,NNF,Paths):- N==0, !, 
   nnf(KB,FmlIn,FreeV,Fml,_),
   NEWFORM = ( ~( exists(X,Fml) )),
   nnf(KB,NEWFORM,FreeV,NNF,Paths).

% AtMost 1: "There may never be 2 (that is X, Y are different) and have Fml be true"
nnf_ex(KB,atmost(N,X,FmlIn),FreeV,NNF,Paths):- N==1, !, 
   nnf(KB,FmlIn,FreeV,Fml,_),
    subst_except(Fml,X,Y,FmlY),
  %  NEWFORM = (( exists(X,Fml)) => ~( exists(Y,FmlY)  & different(X,Y) )),
   NEWFORM = ~(( Fml & FmlY & different(X,Y))),
   nnf(KB,NEWFORM,[X,Y|FreeV],NNF,Paths).

% AtMost N: "If there are AtLeast N then  There Exists No More"
nnf_ex(KB,atmost(N,X,Fml),FreeV,NNF,Paths):- fail,  % wont work due to ~(atleast) = atmost (creating a loop (when in NNF))
   subst_except(Fml,X,Y,FmlY),
   NEWFORM = (atleast(N,X,Fml) => ~(exists(Y, FmlY & different(X,Y)))),
  nnf(KB,NEWFORM,FreeV,NNF,Paths).

% AtMost N: "If there exists 1 then there exists at most N-1"
nnf_ex(KB,atmost(N,X,Fml),FreeV,NNF,Paths):- NewN is N - 1, !,
   subst_except(Fml,X,Y,FmlY),
   NEWFORM = (exists(Y, FmlY) => atmost(NewN,X,Fml)),
  nnf(KB,~different(X,Y) v NEWFORM,FreeV,NNF,Paths).


% =================================
% ==== Exactly N ========
% ==== Cardinality (quantifier macros) ========
% =================================

% Exactly 0: "There may never be even 1 and have Fml be true"
nnf_ex(KB,exactly(N,X,FmlIn),FreeV,NNF,Paths):- N==0, !, 
   nnf(KB,FmlIn,FreeV,Fml,_),
   NEWFORM = ( ~( exists(X,Fml) )),
   nnf(KB,NEWFORM,FreeV,NNF,Paths).


% Exactly 1: states "There is AtMost and AtLeast 1"
nnf_ex(KB,exactly(N,X,Fml),FreeV,NNF,Paths):- N==1, !,
     subst_except(Fml,X,Y,FmlY),
    call(=,NEWFORM ,((exists(X,Fml) & exists(Y,FmlY))=>equals(X,Y))),
    nnf(KB,NEWFORM,FreeV,NNF,Paths).

% Exactly N: states "There is AtMost N /\ AtLeast N"
nnf_ex(KB,exactly(N,X,Fml),FreeV,NNF,Paths):-           !,
   NEWFORM = (atleast(N,X,Fml) & atmost(N,X,Fml)),
   nnf(KB,NEWFORM,FreeV,NNF,Paths).


% Exactly N: "There exists 1 more than the exact 1 smaller group"
nnf_ex(KB,exactly(N,X,Fml),FreeV,NNF,Paths):- number(X), N>1, NewN is N - 1, !,
    subst_except(Fml,X,Y,FmlY),      
    NEWFORM = exists(Y, (FmlY & (different(X,Y) =>  exactly(NewN,X,Fml)))),
    nnf(KB,NEWFORM,FreeV,NNF,Paths).


% =================================
% ==== basic macros ========
% ==== Cardinality (quantifier macros) ========
% =================================

% AllDifferent 4: "All 4 members are different"
nnf_ex(KB,allDifferent([A,B,C,D]),FreeV,NNF,Paths):- 
  NEWFORM =  (different(A,B) & different(A,C) & different(A,D) & different(B,C) & different(B,D) & different(C,D)),
  nnf(KB,NEWFORM,FreeV,NNF,Paths).

% AllDifferent SET: "All members are different"
nnf_ex(KB,allDifferent(SET),FreeV,NNF,Paths):- is_using_feature(list_macros),is_using_feature(inline_prolog),!,
  NEWFORM =  (
    {member(X,SET),member(Y,SET),X\==Y} 
       =>different(X,Y) ),
   nnf(KB,NEWFORM,FreeV,NNF,Paths).




%% nnf_shared( ?KB, :TermX, ?FreeV, ?NNF, ?Paths) is det.
%
% Negated Normal Form Shared.
%
nnf_shared(KB,exists(X,Fml),FreeV,NNF,Paths):-
   must_det_l((
         add_to_vars(X,FreeV,NewVars),
         nnf(KB,Fml,NewVars,NNFMid,_Paths),
         skolem_fn_shared(KB, NNFMid, X, FreeV, Fun, SkVars),
         SKF =.. [Fun|SkVars],
         % subst_except(NNFMid,X,SKF,FmlSk),
         nnf(KB, skolem(X,SKF) => NNFMid ,NewVars,NNF,Paths))).


%=%  Skolemizing : method 1

% Usage: mk_skolem(+Fml,+X,+FreeV,?FmlSk)
% Replaces existentially quantified variable with the formula
% VARIABLES MUST BE PROLOG VARIABLES
% exists(X,p(X)) ==> p(p(exists))


%= 	 	 

%% skolem_bad( ?Fml, ?X, ?FreeV, ?FmlSk) is det.
%
% Skolem Bad.
%
skolem_bad(Fml,X,FreeV,FmlSk):- 
	copy_term((X,Fml,FreeV),(Fml,Fml1,FreeV)),
	copy_term((X,Fml1,FreeV),(exists,FmlSk,FreeV)).

%=%  Skolemizing : method 2

% Usage: mk_skolem(KB, +Fml, +X, +FreeV, ?FmlSk )
% Replaces existentially quantified variable with a unique function
% fN(Vars) N=1,...
% VARIABLES MAYBE EITHER PROLOG VARIABLES OR TERMS



%= 	 	 

%% mk_skolem( ?KB, ?F, ?X, ?FreeV, ?Out) is det.
%
% Make Skolem.
%

mk_skolem(KB, Fml, X, FreeV, FmlOut):-  
   must(skolem_f(KB, Fml, X, FreeV, Sk)),   
   must(FmlOut= Fml),
   !,show_call(why, asserta((constraintRules(X,Sk,Fml)))),
   form_sk(X,Sk).

mk_skolem(KB, F, X, FreeV, FmlSk):- 
    must(skolem_f(KB, F, X, FreeV, Sk)), 
    must(subst_except(F, X, Sk, FmlSk)),!.


  	 

%% skolem_f( ?KB, ?F, ?X, ?FreeVIn, ?Sk) is det.
%
% Skolem Function.
%

skolem_f(KB, F, X, FreeVIn, SkF):- 
       must_det_l((
        delete_eq(FreeVIn,KB,FreeV0),
        delete_eq(FreeV0,X,FreeV),
        list_to_set(FreeV,FreeVSet),
	contains_var_lits(F,X,LitsList),
        (get_var_name(X,VN)->true;VN='Exists'),
        mk_skolem_name(KB,X,LitsList,VN,SK),
        flag(skolem_count,SKN,SKN+1),
        concat_atom(['sk',SK,'_',SKN,'FnSk'],Fun),
	SkF =..[Fun|FreeVSet])),
       % @TODO  maybye use sk again
        nop(oo_put_attr(X,sk,SkF)).


%= 	 	 

%% skolem_fn( ?KB, ?F, ?X, ?FreeVIn, ?Fun, ?FreeVSet) is det.
%
% Skolem Function.
%
skolem_fn(KB, F, X, FreeVIn,Fun, FreeVSet):- % dtrace,
       must_det_l((
         delete_eq(FreeVIn,KB,FreeV0),
         delete_eq(FreeV0,X,FreeV),
         list_to_set(FreeV,FreeVSet),
	contains_var_lits(F,X,LitsList),
        (get_var_name(X,VN)->true;VN='Exists'),
        mk_skolem_name(KB,X,LitsList,VN,SK),
        concat_atom(['sk',SK,'Fn'],Fun))).


%= 	 	 

%% skolem_fn_shared( ?KB, ?F, ?X, ?FreeVIn, ?Fun, ?Slots) is det.
%
% Skolem Function Shared.
%
skolem_fn_shared(KB, F, X, _FreeVIn,Fun, Slots):- 
       must_det_l((
	contains_var_lits(F,X,LitsList),
        term_slots(LitsList,FreeV0),
        delete_eq(FreeV0,X,Slots),
        mk_skolem_name(KB,X,LitsList,'',SK),
        concat_atom(['sk',SK,'Fn'],Fun))).

:- fixup_exports.


%%	form_sk(+Var, +Skolem) is det.
%
%	Assign a Skolem to a Var. Succeeds   silently if Sk is not a
%	sk (anymore).


is_value(Term):-atomic(Term).

% ?- A = a(1) mpred_constrain_w_proxy(A).
mpred_constrain_w_proxy(Goal):- \+ compound(Goal),!.
mpred_constrain_w_proxy(Goal):- functor(Goal,F,_),  mpred_constrain_w_proxy_enter(1,F,Goal),
  term_attvars(Goal,Vars),
  maplist(show_attrs,Vars),
  wdmsg(mpred_constrain_w_proxy(Goal)).

show_attrs(Var):- oo_get_attrs(Var,Atts),wdmsg(Var=Atts).

% todo use: push_dom(X,Dom)
mpred_set_arg_isa(Pred,N,Term,_Outer):- holds_attrs(Term),push_dom(Term,argIsaFn(Pred,N)),!.
mpred_set_arg_isa(Pred,N,Term,Outer):- 
  (is_value(Term);is_function_expr('=>',Term)),!,
  must(( setarg(N,Outer,NewVar),
   % destructive_replace(Outer,Term,NewVar),   
   push_cond(NewVar,mudEquals(NewVar,Term)))),
   push_dom(NewVar,argIsaFn(Pred,N)),!.
mpred_set_arg_isa(_Pred,_N,Term,_Outer):- compound(Term),!,must(mpred_constrain_w_proxy(Term)),!.
mpred_set_arg_isa(_Pred,_N,_Term,_Outer).

mpred_constrain_w_proxy_enter(N,Pred,Outer):- arg(N,Outer,Term),!,
 must(mpred_set_arg_isa(Pred,N,Term,Outer)),
 N2 is N+1,
 mpred_constrain_w_proxy_enter(N2,Pred,Outer).
mpred_constrain_w_proxy_enter(_,_,_).

% ?- A=a(1,1),destructive_replace(A,1,one),A=a(one,one).
destructive_replace(Outer,Term,NewVar):-arg(N,Outer,Value) ,Value==Term,setarg(N,Outer,NewVar),destructive_replace(Outer,Term,NewVar),!.
destructive_replace(Outer,Term,NewVar):- Outer=..[_|ARGS],maplist(destructive_replace,ARGS,Term,NewVar),!.   
destructive_replace(_Outer,_Term,_NewVar).


form_sk(OtherValue, Skolem):- sk:attr_unify_hook(Skolem, OtherValue),!.
% form_sk(OtherValue, Skolem):- nonvar(OtherValue).


% push_dom(_,_):- \+ is_skolem_setting(push_skolem),!.
% push_dom(X,Form2):-annote(dom, X,Form2,_Merged).
push_dom(X,Dom):- push_cond(X,isaDom(X,Dom)).

isaDom(X,[Y|Z]):- !,maplist(isaDom(X),[Y|Z]).
isaDom(X,Y):- ((call_u(isa(X,Y)) *-> true; true)).

annote(Dom,X,Form2):- must(annote(Dom,X,Form2,_)).

% annote(_,_,IO,IO):- \+ is_skolem_setting(push_skolem),!.
% annote(_,X,Form2,Form2):- var(X), freeze(X,(ground(X)->show_call(for(X),lazy(call_u(Form2)));true)).
annote(Dom,X,Form2,SK_FINAL):- oo_get_attr(X,Dom,Form1),merge_forms(Form1,Form2,SK_FINAL),oo_put_attr(X,Dom,SK_FINAL),!.
annote(_,X,IO,IO):- is_ftNonvar(X),!.
annote(Dom,X,Form2,Form2):- oo_put_attr(X,Dom,Form2).

is_skolem(Sk):-get_skolem(Sk,_Form).
get_skolem(Sk,Form):-oo_get_attr(Sk, sk, Form),!.

x_skolem(Sk,skolem(Sk,Form)):-get_skolem(Sk,Form),del_attr(Sk,sk).

transform_skolem_forms(Sk,Form):- x_skolem(Sk,Form),!.
transform_skolem_forms(Var,true):- var(Var),!.
transform_skolem_forms(Head,HeadExtra):- term_attvars(Head,AttVars),include(AttVars,is_skolem,HeadAttVars),
  transform_skolem_forms_l(HeadAttVars,HeadExtra).

transform_skolem_forms_l([Sk],Form):- x_skolem(Sk,Form),!.
transform_skolem_forms_l([Sk|Head],(Form,HeadExtra)):-  x_skolem(Sk,Form), transform_skolem_forms_l(Head,HeadExtra).


%%	sk_form(+Sk, -Form) is semidet.
%
%	True if Sk has been assigned Form or is a Free variable.

sk_form(Sk, Form) :- oo_get_attr(Sk, sk, Form),!.
sk_form(Var,Form):- var(Var),!,gensym(sk_other_,Form), dtrace, oo_put_attr(Var, sk, Form).
sk_form(sk(Value),Value):-!.

push_cond(X,Form):- annote(cond,X,Form,_Merged).

cond:attr_unify_hook(Cond,Value):- var(Value),!,push_cond(Value,Cond),!. 
% ?- A=a(1),mpred_constrain_w_proxy(A),trace,A=a(Z),Z=1.0.
cond:attr_unify_hook([X|Cond],_Value):- !, maplist(call_u,[X|Cond]).
cond:attr_unify_hook(Cond,_Value):- call_u(Cond).

%push_skolem(Onto,SK_ADD):- var(Onto), \+ attvar(Onto), nop(dmsg(warn(var_not_push_skolem(Onto,SK_ADD)))),!.
push_skolem(Onto,SK_ADD):-push_skolem(Onto,SK_ADD,_).

push_skolem(Onto,SK_ADD,SK_FINAL):- oo_get_attr(Onto,sk,SLPREV),!,merge_forms(SLPREV,SK_ADD,SK_FINAL),sk_replace(Onto,SK_FINAL),!.

push_skolem(Onto,SK_ADD,SK_FINAL):- var(Onto),!,SK_FINAL=SK_ADD,sk_replace(Onto,SK_FINAL),!.
push_skolem(Onto,SK_ADD,SK_FINAL):- sk_form(Onto,SLPREV),!,merge_forms(SLPREV,SK_ADD,SK_FINAL),sk_replace(Onto,SK_FINAL),!.
push_skolem(Onto,SK_ADD,SK_ADD):- sk_replace(Onto,SK_ADD).

sk_replace(Onto,SK_FINAL):-var(Onto),!,annote(sk,Onto,SK_FINAL).
sk_replace(_Into,_SKFINAL):-!,fail.


sk:attr_unify_hook(Form, OtherValue):-OtherValue==Form,!.
sk:attr_unify_hook(_Form, _OtherValue):- t_l:no_kif_var_coroutines(G),!,call(G).
sk:attr_unify_hook(Form, OtherValue):- var(OtherValue),!,push_skolem(OtherValue,Form),!.
%sk:attr_unify_hook(Form, OtherValue):- contains_var(OtherValue,Form),!.
%sk:attr_unify_hook(Form, OtherValue):- contains_var(Form,OtherValue),!.
% sk:attr_unify_hook(Form, OtherValue):- skolem_unify(OtherValue,Form).


%sk:attr_portray_hook(Form, SkVar) :- writeq(sk(SkVar,Form)).

%sk:project_attributes(QueryVars, ResidualVars):- fail,nop(wdmsg(sk:proj_attrs(skolem,QueryVars, ResidualVars))).

:- module_transparent(portray_sk/1).
portray_sk(Sk) :- dictoo:oo_get_attr(Sk, sk, Form),!, printable_variable_name(Sk,Name), format('sk_avar(~w,~p)',[Name,Form]).

:- system:import(portray_sk/1).



%=

%% attr_portray_hook( ?Value, ?Var) is semidet.
%
% Attr Portray Hook.
%
 % vn:attr_portray_hook(Name, _) :- write('???'), write(Name),!.
%vn:attr_portray_hook(_, _) :- !.
%sk:attr_portray_hook(_, _) :- !.

:- multifile(user:portray/1).
:- dynamic(user:portray/1).
% user:portray(Sk):- get_attr(Sk, vn, Name), get_attrs(Sk,att(vn,Name,[])),write(Name),!,write('{}').

/*

%% portray_attvar( ?Var) is semidet.
%
% Hook To [portray_attvar/1] For Module Logicmoo_varnames.
% Portray Attribute Variable.
%
:- if(false).

:- abolish('$attvar':portray_attvar/1). 
:- public('$attvar':portray_attvar/1).

'$attvar':portray_attvar(Sk) :- get_attr(Sk, vn, Name),atomic(Name), write('_'),write(Name),get_attrs(Sk,att(vn,Name,[])),!.

'$attvar':portray_attvar(Sk) :-
   get_attr(Sk, sk, _), write('_sk'),!. % get_attrs(Sk,att(vn,Name,att(sk,Name,[]))),!.

'$attvar':portray_attvar(Var) :-
   write('{'),
   get_attrs(Var, Attr),
   '$attvar':portray_attrs(Attr, Var),
   write('}'),!.

'$attvar':portray_attvar(Var) :-
	write('{<'),
        ((get_attr(Var,vn, VarName))->true;sformat(VarName,'~w',[Var])),
	get_attrs(Var, Attr),
	catch(writeq('??'(VarName,Attr)),_,'$attvar':portray_attrs(Attr, Var)),
	write('>}').

:- endif.
*/

:- multifile(user:portray/1).
:- dynamic(user:portray/1).
% user:portray(Sk):- get_attr(Sk, sk, _Form) , loop_check(common_logic_skolem:portray_sk(Sk)),!.

%% sk_form:attribute_goals(@V)// is det.
%	copy_term/3, which also determines  the   toplevel  printing  of
%	residual constraints.

% % % sk:attribute_goals(Sk) --> {sk_form(Sk, Form)},!,[form_sk(Sk,Form)].

skolem_test(_):- !.
skolem_test(Form):- show_call(call_u(Form)).

skolem_unify(_Var,Form):- skolem_test(Form).


member_eqz(E, [H|T]) :-
    (   E == H
    ->  true
    ;   member_eqz(E, T)
    ).

merge_forms(A,B,A):- A==B,!.
merge_forms(A,B,B):- member_eqz(A,B),!.
merge_forms(A,B,A):- member_eqz(B,A),!.
merge_forms(A,B,A):- A=B,!,wdmsg(seeeeeeeeeeeee_merge_forms(A,B)),!.
merge_forms(A,B,C):- flatten([A,B],AB),must(list_to_set(AB,C)),!.






atom_concat_new(SIn,CU,SIn):- atom_length(CU,L),L>1,atom_contains(SIn,CU),!.
atom_concat_new(CU,SIn,SIn):- atom_length(CU,L),L>1,atom_contains(SIn,CU),!.
atom_concat_new(SIn,CU,SOut):- atom_concat(SIn,CU,SOut).


%% mk_skolem_name(KB, +Var, +TermFml, +SuggestionIn, -NameSuggestion) is det.
%
%  generate a skolem name..
%
mk_skolem_name(_KB,Var,Fml,SIn,SOut):- is_ftVar(Fml),same_var(Var,Fml),!,atom_concat_new('VFml',SIn,SOut).
mk_skolem_name(_KB,_V, Fml,SIn,SOut):- is_ftVar(Fml),!,atom_concat_new('VaR',SIn,SOut).

mk_skolem_name(_KB,_V,[],SIn,SIn):- !.
mk_skolem_name(_KB,_V, OP,SIn,SIn):- is_log_op(OP),!.
mk_skolem_name(_KB,_V, OP,SIn,SIn):- atom(OP),atom_concat('sk',_,OP),!.
mk_skolem_name(_KB,_V,Fml,SIn,SOut):- atomic(Fml),!,must((i_name(Fml,N),toPropercase(N,CU))),!,atom_concat_new(SIn,CU,SOut).
mk_skolem_name(KB,Var,[H|T],SIn,SOut):- !,mk_skolem_name(KB,Var,H,SIn,M),!,mk_skolem_name(KB,Var,T,M,SOut).
mk_skolem_name(KB,Var,isa(VX,Lit),SIn,SOut):- same_var(Var,VX),is_ftNonvar(Lit),!,mk_skolem_name(KB,Var,['Isa',Lit],'',Mid),atom_concat_new(Mid,SIn,SOut).
mk_skolem_name(KB,Var,inst(VX,Lit),SIn,SOut):- same_var(Var,VX),is_ftNonvar(Lit),!,mk_skolem_name(KB,Var,['Inst',Lit],'',Mid),atom_concat_new(Mid,SIn,SOut).
mk_skolem_name(KB,Var,Fml,SIn,SOut):- Fml=..[F,VX],same_var(Var,VX),!,mk_skolem_name(KB,Var,['Is',F],'',Mid),atom_concat_new(Mid,SIn,SOut).

mk_skolem_name(KB,Var,Fml,SIn,SOut):- fail, Fml=..[F,Other,VX|_],same_var(Var,VX),!,(type_of_var(KB,Other,OtherType0),
   (OtherType0=='Unk'->OtherType='';OtherType=OtherType0)),
   mk_skolem_name(KB,Var,[OtherType,'Arg2Of',F],SIn,SOut).

mk_skolem_name(_KB,Var,Fml,SIn,SOut):- Fml=..[F,VX|_],same_var(Var,VX),!,i_name(F,Lit), atomic_list_concat([Lit],Added),atom_concat_new(SIn,Added,SOut).
mk_skolem_name(_KB,Var,Fml,SIn,SOut):- arg(N,Fml,VX),functor(Fml,F,_),number_string(N,NStr),same_var(Var,VX),!,
  i_name(F,Lit), atomic_list_concat(['Arg',NStr,Lit],Added),atom_concat_new(SIn,Added,SOut).
  
mk_skolem_name(_KB,_Var,_Fml,SIn,SIn).

% same_var(Var,Fml):-  ~(  ~( Var=Fml)),!.



% skolem_fn


%= 	 	 

%% nnf_label( ?KB, :TermX, ?FreeV, ?NNF, ?Paths) is det.
%
% Negated Normal Form Label.
%
nnf_label(KB,exists(X,Fml),FreeV,NNF,Paths):-
   must_det_l((
         add_to_vars(X,FreeV,NewVars),
         nnf(KB,Fml,NewVars,NNFMid,_Paths),
         skolem_fn(KB, NNFMid, X, FreeV, Fun, SkVars),
         SKF =.. [Fun|SkVars],
        % subst_except(NNFMid,X,SKF,FmlSk),
         % MAYBE CLOSE nnf(KB,((mudEquals(X,SKF) => ~(FmlSk)) v Fml),NewVars,NNF,Paths).
         %nnf1(KB,  (((skolem(X,SKF))=>NNFMid) & FmlSk) ,NewVars,NNF,Paths))).
        % GOOD nnf(KB, isa(X,SKF) => (skolem(X,SKF)=>(NNFMid)) ,NewVars,NNF,Paths))).
         nnf(KB, skolem(X,SKF) => NNFMid ,NewVars,NNF,Paths))).


:- fixup_exports.

