
% :- module(kbi,[]).
% :- use_module(library(pfc)).
% :- include(test_header).
% :- set_prolog_flag(write_attributes,portray).

:- listing(ls).
:- '$set_source_module'(kbi).
:- use_module(library(retry_undefined)).


 :- meta_predicate query_ex(*).
 :- meta_predicate body_call(*).
 :- meta_predicate bless_ex(*,*).
 :- meta_predicate add_constraint_ex(*,*,*).
 :- meta_predicate reify(*).
 :- meta_predicate add_constraint_ex(*,*,*).
 :- meta_predicate test_count(0,*).
 :- meta_predicate undo(0).


:- use_module(library(must_trace)).
% :- use_module(library(loop_check)).
:- use_module(library(logicmoo_typesystem)).
:- use_module(library(logicmoo_clif)).

kbi:real_static.
kbi:real.
%:- module(kbi).
:- '$set_source_module'(kbi).

:- fav_debug.

% =================
% Cute and Lazy
% =================


memberchk_eq(X, [Y|Ys]) :- (   X == Y ->  true ;   memberchk_eq(X, Ys)).
subtract_eq([],_,[],[]).
subtract_eq([X|Xs],Ys,L,[X|Intersect]) :-   memberchk_eq(X,Ys),subtract_eq(Xs,Ys,L,Intersect).
subtract_eq([X|Xs],Ys,[X|T],Intersect) :-   subtract_eq(Xs,Ys,T,Intersect).

% :- abolish(user:portray/1).
:- dynamic(user:portray/1).
:- multifile(user:portray/1).


%:- dynamic(identityPred/1).
make_identity(_):-!.
make_identity(I):- make_type(identityPred:I/2).

make_type(_):-!.
make_type(Info):- make_type0(Info).
make_type0(T:F/A):-!,functor(P,F,A),make_type0(T:P).
make_type0(T:FA):- functor(FA,F,A),functor(P,F,A), 
   asserta_if_new( ((kbi:P):- kbi:call(T,P))),
   asserta_if_new(baseKB:safe_wrap(baseKB,F,A,T)),
   kbi:export(kbi:F/A),
   kbi:import(kbi:F/A).

make_type0(F):- atom(F),!,make_type0(head_call:F/1).
make_type0(P):-make_type0(head_call:P).

kbi_define(G):- strip_module(G,_,P),make_type0(P).





exists:attr_portray_hook(Attr,Var):- one_portray_hook(Var,exists(Var,Attr)).


:- module_transparent(user:portray_var_hook/1).
:- multifile(user:portray_var_hook/1).
:- dynamic(user:portray_var_hook/1).

user:portray_var_hook(Var) :- 
 current_prolog_flag(write_attributes,portray),
 attvar(Var),
 get_attr(Var,exists,Val),
  current_prolog_flag(write_attributes,Was),
  setup_call_cleanup(set_prolog_flag(write_attributes,ignore),
    writeq({exists(Var,Val)}),
    set_prolog_flag(write_attributes,Was)),!.


add_dom_differentFromAll(Ex,DisjExs):- add_dom_list_val(dif,differentFromAll,Ex,DisjExs).


add_dom_list_val(_,_,_,[]):- !.
add_dom_list_val(Pred1,_,X,[Y]):- atom(Pred1), X==Y -> true;P=..[Pred1,X,Y],add_dom(X,P). 
add_dom_list_val(Pred1,Pred,X,FreeVars):- list_to_set(FreeVars,FreeVarSet),FreeVars\==FreeVarSet,!,
  add_dom_list_val(Pred1,Pred,X,FreeVarSet).
add_dom_list_val(_Pred,Pred,X,FreeVars):- P=..[Pred,X,FreeVars],add_dom(X,P).

one_portray_hook(Var,Attr):-
  locally(set_prolog_flag(write_attributes,ignore),
  ((setup_call_cleanup(set_prolog_flag(write_attributes,ignore),
  ((subst(Attr,Var,SName,Disp),!,
  get_var_name(Var,Name),
   (atomic(Name)->SName=Name;SName=self),
   format('~p',[Disp]))),
   set_prolog_flag(write_attributes,portray))))).


visit_exs(P,P,_,In,In):- \+ compound(P),!.

visit_exs(ex(X,P),InnerP,FreeVars,In,Out):- append(In,[X],Mid),   
 add_dom_list_val(skFArg,skFArgs,X,FreeVars),
 visit_exs(P,InnerP,[X|FreeVars],Mid,Out),!,
 add_dom(X,exists(X,InnerP)).
visit_exs(all(X,P),InnerP,FreeVars,In,Out):- append(In,[X],Mid),
  visit_exs(P,InnerP,[X|FreeVars],Mid,Out),!.
visit_exs(P,POut,FreeVars,In,Rest):-arg(_,P,PP),compound(PP),!,P=..[F|ARGS],get_ex_quants_l(FreeVars,ARGS,ARGSO,In,Rest),POut=..[F|ARGSO].
visit_exs(P,P,_,In,In).

assert_kbi(P):- must(kbi:assert_if_new(P)).

get_ex_quants_l(_,[],[],IO,IO).  
get_ex_quants_l(FreeVars,[X|ARGS],[Y|ARGSO],In,Rest):-
  visit_exs(X,Y,FreeVars,In,M),
  get_ex_quants_l(FreeVars,ARGS,ARGSO,M,Rest).

unify_two(AN,AttrX,V):- nonvar(V),!, (V='$VAR'(_)->true;throw(unify_two(AN,AttrX,V))).
unify_two(AN,AttrX,V):- get_attr(V,AN,OAttr),!,OAttr=@=AttrX,!. % ,show_call(OAttr=@=AttrX).
unify_two(AN,AttrX,V):- put_attr(V,AN,AttrX).

exists:attr_unify_hook(Ex,V):- unify_two(exists,Ex,V).

require_dom(NonVar,Closure):- nonvar(NonVar),!,call_tru(NonVar,Closure).
require_dom(Var,Closure):- attvar(Var),!,add_dom(Var,Closure).
require_dom(Var,Closure):- add_dom(Var,Closure).

not_nameOf(Ex,V):- \+ nameOf1(Ex,V).

nameOf(Ex,V):- atomic(Ex),!,text_to_string(Ex,V).
nameOf(Ex,V):- nonvar(Ex),!,term_string(Ex,V).
nameOf(Ex,V):- nonvar(V),has_dom(Ex,nameOf(Ex,V0)),!,text_to_string(V0,V).
nameOf(Ex,V):- nonvar(V),!,add_dom(Ex,nameOf(Ex,V)),!,add_var_to_env(V,Ex).
nameOf(Ex,V):- var(V),has_dom(Ex,nameOf(Ex,V)),!,(nonvar(V)->add_var_to_env(V,Ex);true).

nameOf(Ex,V):- producer(nameOf(Ex,V)).
% nameOf(Ex,V):- var(V),!,add_dom(Ex,nameOf(Ex,V)),!.



assign_ex(Ex,V):- kbi:nameOf(Ex,V).

reify((P,Q)):-!,reify(P),reify(Q).
reify(P):- query_ex(P).



% ex(P):- compound(P),P=..[_,I], (var(I)-> freeze(I,from_ex(P)) ; fail).

existential_var(Var,_):- nonvar(Var),!.
existential_var(Var,_):- attvar(Var),!.
existential_var(Var,P):- put_attr(Var,exists,P),!.


solve_ex(Var,_Vs,_Head,P,BodyList):- 
  existential_var(Var,P), 
  maplist(kbi:bless_with,BodyList), maplist(kbi:body_call,BodyList).

bless_with(P):- ground(P),!.
bless_with(P):- bless(P).

% body_call(P):- recorded(kbi,P).
body_call(P):- ground(P),!,kbi:loop_check(P).
body_call(P):- bless(P).


is_recorded(A):- recorded(kbi,A)*->nop(sanity(\+cyclic_term(A)));body_call(A).

% WORDED head_call(P):- (kbi:clause(can_bless(P),Body)*->Body; ((fail,kbi:bless(P)))),is_recorded(P).

head_call(P):- is_recorded(P).
% head_call(P):- bless(P),(kbi:clause(existing(P),Body)*->Body; true),ignore(is_recorded(P)).

bless(P):-ground(P),!.
bless(P):- 
 (get_ev(P,Attvars,Univ)),
   (Univ == [] -> true ;
       maplist(add_constraint_ex(bless_ex,P),Univ)),
   (Attvars == [] -> true ;
        maplist(add_constraint_ex(bless_ex,P),Attvars)),
 nop(Attvars == [] -> true ;
      maplist(add_constraint_ex(bless_ex2,P),Attvars)).

% add_constraint_ex(_Call,_P,_V):-!,fail.
add_constraint_ex(_,P,V):- \+ contains_var(V,P),!.
add_constraint_ex(_,P,V):- add_dom(V,P),!.
add_constraint_ex(Call,P,V):-freeze(V,call(Call,V,P)).

get_ev(P,Annotated,Plain):- 
    term_variables(P,Vars),
    term_attvars(P,Annotated),
    subtract_eq(Vars,Annotated,Plain).

labling_ex(P):- copy_term(P,PP,Residuals),maplist(call,Residuals),P=PP.


bless_ex2(_X,P):- \+ ground(P).
bless_ex(X, P):- nonvar(X)->call(P); true.


query_tru(Qry) :- nrlc((proven_tru(Qry))).

query_ex(PQ):-   update_changed_files1,
  existentialize(PQ,P),
   wdmsg(query_ex(P)),
   sanity(((existentialize(P,PEx), ignore((PEx\==P,wdmsg(query_ex(PEx))))))),
   gensym(skTrue,QryF),
   gensym(skFalse,NotQryF),
   term_variables(P,Vars),
   Qry=..[QryF|Vars],
   NotQry=..[NotQryF|Vars],
   assert_ex((P => Qry)),
   subst(P,exists,all,PA),
   assert_ex(((~(PA)) => NotQry)),!,
   (query_tru(Qry) *-> wdmsg(Qry); 
     (query_tru(NotQry)*-> wdmsg(NotQry); wdmsg(unknown(Qry)))).
        

% query_ex(P):-  ignore(show_failure(P)).
% query_ex(P):- is_recorded(P),recorded(complete,P).

minus_vars(Head,Minus,Dif):-
   term_variables(Head,HeadVars),
   term_variables(Minus,BodyVars),
   subtract_eq(HeadVars,BodyVars,Dif).


%===
%do_create_cl(_,Lit1,_):- ground(Lit1),!.
%===
do_create_cl(Lit1,BodyLits,Prop):-   
   (current_predicate(_,Lit1)->true;make_type(Lit1)),   
   term_variables(Lit1,AllHeadVars),
   maplist(add_dom_rev(Lit1),AllHeadVars),
   term_variables(BodyLits,AllBodyVars),
   subtract_eq(AllHeadVars,AllBodyVars,UniqeHead,Intersect),
   subtract_eq(AllBodyVars,AllHeadVars,UniqeBody,_BodyIntersect),
   create_ex(Lit1,Prop,UniqeHead,Intersect,UniqeBody,BodyLits),
   recorda_if_new(Lit1).


%create_ex(X,Lit1,BodyLits,Prop,DisjExs):- \+ contains_var(X,Lit1),assert_if_new((gen_out(Lit1):- ensure_sneezed(X,Lit1,BodyLits,Prop,[]))),fail.
create_ex(Lit1,Prop,UniqeHead,Intersect,UniqeBody,BodyLits):-
   recorda_if_new(Lit1,head_body(Lit1,BodyLits,UniqeHead,Intersect,UniqeBody,Prop)).


comingle_vars(QuantsList,NewP):- 
   maplist(add_all_differnt(QuantsList,NewP),QuantsList).

add_all_differnt(QuantsList,_NewP,Ex):-
    delete_eq(QuantsList,Ex,DisjExs),
    add_dom_differentFromAll(Ex,DisjExs).

recorda_if_new(K,Lit1):- functor(Lit1,F,A),functor(Lit0,F,A),recorded(K,Lit0),Lit0=@=Lit1,!,wdmsg(skip_recorda(Lit0=@=Lit1)).
recorda_if_new(K,Lit1):- show_call(recorda(K,Lit1)).

recorda_if_new(Lit1):- recorda_if_new(kbi,Lit1). 

assert_ex2(P):- 
  flag(skolem_count,_,0),
  existentialize(P,PE),
  kif_to_boxlog(PE,BLU),
  sort(BLU,BL),
  must_maplist_det(assert_ex3,BL).

assert_ex3('$unused'(_):-_).
assert_ex3(proven_tru(H):- B):- !,assert_ex3((H:- B)).
assert_ex3(skolem(V,Sk):- B):- !,
  xform_body(sk_head,V,Sk,B,BO),
  assert_ex4((make_skolem(V,Sk):- BO)).

assert_ex3(proven_neg(H):- B):- !,assert_ex4((proven_neg(H):- B)).
assert_ex3((Head:- (skolem(V,Sk)))):- !,
  assert_ex4((producer(Head):- ((call_skolem(V,Sk))))).

assert_ex3((Head:- (skolem(V,Sk),B))):- !,    
  xform_body(post_sk,V,Sk,B,BO),
  assert_ex4((producer(Head):- (call_skolem(V,Sk),BO))).

assert_ex3(P):- assert_ex4(P).

assert_ex4(P):- ain(P),assert_ex5(P).

assert_ex5(P):- dmsg(P).


new_sk_dict( _:{vs:_,sks:_,more:_}).
get_sk_props(X,Dict):- attvar(X),get_attr(X,skp,Dict).
ensure_sk_props(X,Dict):- sanity(var(X)),(get_sk_props(X,Dict)->true;((new_sk_dict(Dict),put_attr(X,skp,Dict)))).

made_skolem(_,_).
skolem(X,SK):- var(X),!, \+ has_dom(X,made_skolem(X,SK)), add_dom(X,made_skolem(X,SK)),!,make_skolem(X,SK).
skolem(E,SK):- nameOf(E,Named),!,(make_skolem(X,SK)*->nameOf(X,Named)).
    
xform_body(_ALL,_V,_Sk,B,B):- \+ compound(B),!.
xform_body(_ALL,_V,_Sk,proven_tru(A),A).
xform_body(ALL,V,Sk,[A|B],[AA|BB]):- !, xform_body(ALL,V,Sk,A,AA),xform_body(ALL,V,Sk,B,BB).
xform_body(ALL,V,Sk,(A,B),(AA,BB)):- !, xform_body(ALL,V,Sk,A,AA),xform_body(ALL,V,Sk,B,BB).
xform_body(ALL,V,Sk,(A;B),(AA;BB)):- !, xform_body(ALL,V,Sk,A,AA),xform_body(ALL,V,Sk,B,BB).
xform_body(ALL,V,Sk,A,B):- !, A=..[F|AL],xform_body(ALL,V,Sk,AL,BL),B=..[F|BL].
xform_body(post_sk,_V,_Sk,B,B).
xform_body(sk_head,_V,_Sk,B,B):-!.


call_skolem(X,Y):- skolem(X,Y).

assert_ex(P):-!,assert_ex2(P).


assert_ex(P):- 
  existentialize(P,PE)->P\==PE,!,
  assert_ex(PE).
  
assert_ex((P -> Q)):- !, assert_kbi(Q:-head_call(P)).

assert_ex(reduced(P)):- !, recorda_if_new(P).


assert_ex(quanted(QuantsList,NewP)):-
  comingle_vars(QuantsList,NewP),
  conjuncts_to_list(NewP,Lits),!,
  forall(select(Lit1,Lits,BodyLits),
   (nop(recorda_if_new(Lit1)),
     assert_ex(create_cl(Lit1,BodyLits,NewP)))).

assert_ex(create_cl(Lit1,BodyLits,NewP)):- !,  
  do_create_cl(Lit1,BodyLits,NewP).

assert_ex(P):- visit_exs(P,NewP,[],[],QuantsList),   
    (QuantsList \== [] 
     -> assert_ex(quanted(QuantsList,NewP));
     NewP\==P -> assert_ex(reduced(NewP));
     assert_ex(reduced(NewP))).
                                    
% import_ex(F/A):-kbi:current_predicate(_,kbi:F/A),!, kbi:export(kbi:F/A), kbi:import(kbi:F/A).
import_ex(F/A):-kbi:export(kbi:F/A),system:import(kbi:F/A), kbi:import(kbi:F/A).

disp_ex(X):-fmt9(X).

lr:- notrace((listing(kbi:_),
  doall((current_key(K),recorded(K,P),
    locally(set_prolog_flag(write_attributes,portray),wdmsg(P)))))).

clr:-
  doall((current_key(K),recorded(K,_,Ref),erase(Ref))).

% for reloading
:- clr.


test_count(Goal,N):- 
   findall(Goal,(Goal,format('~N~p~n',[Goal])),List),
   length(List,LL),
   LL==N.

:- kbi:export(kbi:import_ex/1).
:- kbi:import(kbi:import_ex/1).
:- import_ex(make_type/1).
:- import_ex(assert_ex/1).
:- import_ex(disp_ex/1).
:- import_ex(is_recorded/1).
:- import_ex(lr/0).

%undo(Goal):- Redo = call(Goal), super_call_cleanup(true, (true; (Redo,setarg(1,Redo,true))), Redo).
undo(Goal):- true; (Goal,fail).

/*
% one list note on PNF  the Way i convert loves(joe,mary) to PNF...

loves(joe,mary)  <=> 
exists([R,X,Y,T], ((subRelation(R,loves), is_a(T,time), is_a(T,context),exists_durring(X,T),exists_durring(Y,T),
 ~different(joe,X),~different(mary,Y)) -> trueIn(T,holds(R,X,Y)))).

*/

tbl2:- P = exists([R,X,Y,T], 
  ((subRelation(R,loves), is_a(T,time), is_a(T,context),exists_durring(X,T),exists_durring(Y,T), 
              ~different(joe,X),~different(mary,Y)) => trueIn(T,holds(R,X,Y)))),
   must(test_boxlog(P)),
   must(assert_ex(P)).


tbl:- 
   P = (loves(joe,mary) <=> ((exists([R,X,Y,T], 
  ((subRelation(R,loves), is_a(T,time), is_a(T,context),exists_durring(X,T),exists_durring(Y,T), 
              ~different(joe,X),~different(mary,Y)) => trueIn(T,holds(R,X,Y))))))),
   must(test_boxlog(P)),
   must(assert_ex(P)).

f(0):- assert_ex(loves(joe,mary)).

:- fixup_exports.

% =================
% example
% =================

:- '$set_source_module'(kbi).
% rtArgsVerbatum(_):- dumpST,break.
:- module(kbi).
% :- ensure_abox(kbi).


:- make_type(female).
% :- make_type(god).
:- make_type(man).
:- make_identity(nameOf).  % Evil? come on, just needed something here
:- make_type(loves/2).

:- set_prolog_flag(logicmoo_modality,late).
:- set_prolog_flag(logicmoo_propagation, modal).


f(1):- assert_ex(man("John")).
f(1.1):- assert_ex(ex(X,(nameOf(X,"John"), man(X)))).   % same comment as as f8
f(1.2):- assert_ex(atleast(1,X,(man(X),nameOf(X,"John")))).   % constraining by identity relly meant only 1

f(2):- assert_ex(man("Joe")).   % man number 2
f(2.1):- assert_ex(ex(X,(nameOf(X,"Joe"), man(X)))).   % same comment as as f8
f(2.2):- assert_ex(atleast(1,X,(man(X),nameOf(X,"Joe")))).   % constraining by identity relly meant only 1

f(3):- assert_ex(room("TreeThirty")).

f(4):- assert_ex(room("OneTwenty")).

f(5):- assert_ex(ex(Child,(man(Child),child(Child)))).  % Look, its a man child!
f(5.1):- assert_ex(ex(Child,child(Child))). % would this create a second child?

f(6):- assert_ex(ex(P,((man(P);female(P)),nameOf(P,"Pat")))).  % Two *different* constraint paths for a single identity
f(6.1):- assert_ex(ex(P,(man(P);female(P)))).  % Two constraint paths




r(1):- (assert_ex(
  ex(Mary,
    ex(John,
   (   female(Mary),
       nameOf(Mary,"Mary"),
       man(John),
       nameOf(John,"John"),
       loves(John,Mary)))))).


r(2):- assert_ex((
 ex(God,
    ex(Mary,
   (   female(Mary),
       nameOf(Mary,"Mary"),
       god(God),
       nameOf(God,"AlFaqa"),
       loves(Mary,God)))))).

r(3):- assert_ex(
  all(Child,
    ex(Mother,
   (   child(Child),
       female(Mother),
       nameOf(Child,childOf(Mother)),       
       mother(Child,Mother))))).

r(4):- assert_ex(all(R,implies(room(R),exists(D,and(door(D),has(R,D)))))).


tstit(0) :- clr, f1, 
   test_count(man(_),1).

tstit(1) :- tstit(0), f2,
   test_count(man(_),1).

tstit(2) :- tstit(1), f3,
   test_count(man(_),1).

tstit(3) :- tstit(2), f4,
   test_count(man(_),2).

tstit(4) :- tstit(3), f5,
   test_count(man(_),2).
   

test_all:- forall(tstit(_),true).

:- set_prolog_flag(write_attributes,ignore).

:- lr.


/*

Examples:

?- 
   female(Whom).

?- female(Whom).

?- test_all.

assuming mltt stops short of aristotelian logic which requires intensional equivalence to prove ranking of subtyping (for example a married man is also a man)


:- install_retry_undefined(kbi,error).
:- install_retry_undefined(kbi,kbi_define).
:- install_retry_undefined(kbi,error).

*/

kbi_shared(MFA):- 
  get_mfa(MFA,M,F,A),
  dmsg(kbi_shared(M:F/A)),
  functor(P,F,A),
  M:ain(P:-call_tru(P)),
  kb_shared(M:F/A).

:- install_retry_undefined(kbi,kbi_shared).


:- kb_shared(baseKB:make_skolem/2).


:- ensure_abox(kbi).

:- meta_predicate proven_holds_t(*,?,?).
proven_holds_t(F, A, B):- nonvar(F),current_predicate(F/2),call(F,A,B).
:- meta_predicate proven_holds_t(*,?,?,?).
proven_holds_t(F, A, B, C):- nonvar(F),current_predicate(F/3),call(F,A,B,C).
/*
:- multifile(proven_not_neg/1).
:- dynamic(proven_not_neg/1).
*/
:- kb_shared(baseKB:proven_not_neg/1).
proven_not_neg(H):- compound(H), H=..[F,A,B], proven_tru(poss_t(F,A,B)),!.
proven_not_neg(H):- \+ proven_neg(H), \+ call_u(~ H).

:- kb_shared(baseKB:proven_not_poss/1).
proven_not_poss(H):- proven_not_tru(H).

:- kb_shared(baseKB:proven_tru/1).


attvar_or_const(C):- nonvar(C);attvar(C).
call_tru(X):- arg(1,X,E),call_tru(E,X).
call_tru(E,X):- \+ ground(E), (has_dom(E,(X))->rem_dom(E,(X)); true),
   nrlc((producer((X)))),has_dom(E,(X)),attvar_or_const(E).
call_tru(E,X):- (nonvar(X);not_has_dom(E,(X)),!, nrlc((proven_tru((X)))), \+ proven_neg((X))),attvar_or_const(E).
call_tru(_,X):- inherit_above(kbi, (X)).


loves(X,Y):-  (nonvar(X);nonvar(Y)),
              (has_dom(X,(loves(X,Y)))->rem_dom(X,(loves(X,Y))); true),
              (has_dom(Y,(loves(X,Y)))->rem_dom(Y,(loves(X,Y))); true),
              nrlc(producer(loves(X,Y))),
              (has_dom(X,(loves(X,Y)));has_dom(Y,(loves(X,Y)))),
              (attvar_or_const(X),attvar_or_const(Y)).
loves(X,Y):- (nonvar(X);not_has_dom(X,(loves(X,Y))),!, nrlc((proven_tru((loves(X,Y)))))),
             (nonvar(Y);not_has_dom(Y,(loves(X,Y))),!, nrlc((proven_tru((loves(X,Y)))))), 
             \+ proven_neg((loves(X,Y)))),attvar_or_const(X),attvar_or_const(Y).
loves(X,Y):- inherit_above(kbi, (loves(X,Y))).


nrlc(G):- no_repeats(loop_check(G)).

man(X):- \+ ground(X),
    (has_dom(X,man(X))->rem_dom(X,man(X)); true),
   nrlc((producer(man(X)))),has_dom(X,man(X)).
man(X):- (nonvar(X);not_has_dom(X,man(X)),!, nrlc((proven_tru(man(X)))), \+ proven_neg(man(X))).
man(X):- inherit_above(kbi, man(X)).


proven_tru(H):- loop_check(call_u(H)), \+ show_failure(proven_neg(H)).



%proven_tru(H):- \+ ground(H),nrlc((producer(H))).
%proven_tru(H):- cwc, (nonvar(H),loop_check(proven_neg(H)),!,fail) ; (fail,call_u(H)).

:- kb_shared(baseKB:proven_neg/1).


:- kb_shared(baseKB:proven_not_tru/1).
proven_not_tru(H):- \+ call_u( H).
% proven_not_tru(man(A)):- trace,dmsg(proven_not_tru(man(A))).
% :- '$set_source_module'(user).
% :- kbi:tbl.

%:- mpred_trace_exec.

(((producer(H):- _ )) ==> producing(H)).

producing(H)==>{predicate_property(H,defined)->true;show_call(must(kbi_shared(H)))}.

:- forall((clause(f(N),Body),iteger(N)),Body).
:- forall((clause(r(N),Body),iteger(N)),Body).

:- listing(producing/1).

end_of_file.


kbi:  ?- man(X).
add_dom(X, [man, made_skolem(X, skIsJohnNameOf_0FnSk), nameOf(X, "John")]) ;
add_dom(X, [man, made_skolem(X, skIsExistsNameOf_0FnSk), nameOf(X, "John")]) ;
add_dom(X, [man, made_skolem(X, skIsExistsNameOf_0FnSk), nameOf(X, "Joe")]) ;
add_dom(X, [man, made_skolem(X, skIsJoeNameOf_0FnSk), nameOf(X, "Joe")]) ;
add_dom(X, [man, child, made_skolem(X, skIsChildIsExists_0FnSk)]) ;
false.

kbi:  ?- female(X).
add_dom(X, [female, made_skolem(X, skIsFemaleIsExistsNameOf_0FnSk), nameOf(X, "Pat")]) ;
add_dom(X, [female, made_skolem(X, skIsFemaleIsExists_0FnSk)]) ;
add_dom(X, [female, made_skolem(X, skIsFemaleExistsNameOfLoves_0FnSk), nameOf(X, "Mary"), loves(OBJ478, X)]),
add_dom(OBJ478, [man, made_skolem(OBJ478, skIsJohnNameOf_0FnSk), nameOf(OBJ478, "John")]) ;
add_dom(X, [female, made_skolem(X, skIsFemaleExistsNameOfLoves_0FnSk), nameOf(X, "Mary"), loves(OBJ5760, X)]),
add_dom(OBJ5760, [man, made_skolem(OBJ5760, skIsExistsNameOf_0FnSk), nameOf(OBJ5760, "John")]) ;
add_dom(X, [female, made_skolem(X, skIsFemaleExistsNameOfLoves_0FnSk), nameOf(X, "Mary"), loves(OBJ9002, X)]),
add_dom(OBJ9002, [man, child, made_skolem(OBJ9002, skIsChildIsExists_0FnSk), nameOf(OBJ9002, "John")]) ;
add_dom(X, [female, made_skolem(X, skIsChildofIsFemaleExistsNameOfMother_0FnSk(OBJ12140)), nameOf(OBJ12140, childOf(X)), mother(OBJ12140, X)]) ;
false.

kbi:  ?- room(X).
add_dom(X, [room, made_skolem(X, skIsRoomTreeThirtyNameOf_0FnSk), nameOf(X, "TreeThirty")]) ;
add_dom(X, [room, made_skolem(X, skIsRoomOneTwentyNameOf_0FnSk), nameOf(X, "OneTwenty")]) ;
add_dom(X, [room, made_skolem(X, skIsOneTwentyNameOf_0FnSk), nameOf(X, "OneTwenty")]) ;
false.

kbi:  ?- door(X).
add_dom(X, [door, made_skolem(X, skIsDoorExistsHas_0FnSk(OBJ17852)), has(OBJ17852, X)]),
add_dom(OBJ17852, [room, made_skolem(OBJ17852, skIsRoomTreeThirtyNameOf_0FnSk), nameOf(OBJ17852, "TreeThirty")]) ;
add_dom(X, [door, made_skolem(X, skIsDoorExistsHas_0FnSk(OBJ18902)), has(OBJ18902, X)]),
add_dom(OBJ18902, [room, made_skolem(OBJ18902, skIsRoomOneTwentyNameOf_0FnSk), nameOf(OBJ18902, "OneTwenty")]) ;
add_dom(X, [door, made_skolem(X, skIsDoorExistsHas_0FnSk(OBJ21350)), has(OBJ21350, X)]),
add_dom(OBJ21350, [room, made_skolem(OBJ21350, skIsOneTwentyNameOf_0FnSk), nameOf(OBJ21350, "OneTwenty"), made_skolem(OBJ21350, skIsRoomTreeThirtyNameOf_0FnSk), nameOf(OBJ21350, "TreeThirty")]) ;
add_dom(X, [door, made_skolem(X, skIsDoorExistsHas_0FnSk(OBJ22760)), has(OBJ22760, X)]),
add_dom(OBJ22760, [room, made_skolem(OBJ22760, skIsOneTwentyNameOf_0FnSk), nameOf(OBJ22760, "OneTwenty"), made_skolem(OBJ22760, skIsRoomOneTwentyNameOf_0FnSk)]) ;
add_dom(X, [door, made_skolem(X, skIsDoorExistsHas_0FnSk(OBJ23672)), has(OBJ23672, X)]),
add_dom(OBJ23672, [room, made_skolem(OBJ23672, skIsOneTwentyNameOf_0FnSk), nameOf(OBJ23672, "OneTwenty")]) ;


:- dynamic producer/1.
:- multifile producer/1.
:- public producer/1.
:- module_transparent producer/1.

producer(A) :-
        inherit_above(kbi, producer(A)).
producer(man(A)) :-
        call_skolem(A, skIsJohnNameOf_0FnSk).
producer(nameOf(A, "John")) :-
        call_skolem(A, skIsJohnNameOf_0FnSk).
producer(man(A)) :-
        call_skolem(A, skIsExistsNameOf_0FnSk).
producer(nameOf(A, "John")) :-
        call_skolem(A, skIsExistsNameOf_0FnSk).
producer(man(A)) :-
        call_skolem(A, skIsJoeNameOf_0FnSk).
producer(nameOf(A, "Joe")) :-
        call_skolem(A, skIsJoeNameOf_0FnSk).
producer(nameOf(A, "Joe")) :-
        call_skolem(A, skIsExistsNameOf_0FnSk).
producer(room(A)) :-
        call_skolem(A, skIsRoomTreeThirtyNameOf_0FnSk).
producer(nameOf(A, "TreeThirty")) :-
        call_skolem(A, skIsRoomTreeThirtyNameOf_0FnSk).
producer(room(A)) :-
        call_skolem(A, skIsRoomOneTwentyNameOf_0FnSk).
producer(nameOf(A, "OneTwenty")) :-
        call_skolem(A, skIsRoomOneTwentyNameOf_0FnSk).
producer(child(A)) :-
        call_skolem(A, skIsChildIsExists_0FnSk).
producer(man(A)) :-
        call_skolem(A, skIsChildIsExists_0FnSk).
producer(child(A)) :-
        call_skolem(A, skIsChildExists_0FnSk).
producer(female(A)) :-
        call_skolem(A, skIsFemaleIsExistsNameOf_0FnSk),
        proven_not_tru(man(A)).
producer(man(A)) :-
        call_skolem(A, skIsFemaleIsExistsNameOf_0FnSk),
        proven_not_tru(female(A)).
producer(nameOf(A, "Pat")) :-
        call_skolem(A, skIsFemaleIsExistsNameOf_0FnSk).
producer(female(A)) :-
        call_skolem(A, skIsFemaleIsExists_0FnSk),
        proven_not_tru(man(A)).
producer(man(A)) :-
        call_skolem(A, skIsFemaleIsExists_0FnSk),
        proven_not_tru(female(A)).
producer(female(A)) :-
        call_skolem(A, skIsFemaleExistsNameOfLoves_0FnSk).
producer(man(A)) :-
        call_skolem(A, skIsExistsNameOfLoves_1FnSk(B)),
        skolem(B, skIsFemaleExistsNameOfLoves_0FnSk).
producer(loves(A, B)) :-
        call_skolem(A, skIsExistsNameOfLoves_1FnSk(B)),
        skolem(B, skIsFemaleExistsNameOfLoves_0FnSk).
producer(nameOf(A, "Mary")) :-
        call_skolem(A, skIsFemaleExistsNameOfLoves_0FnSk).
producer(nameOf(A, "John")) :-
        call_skolem(A, skIsExistsNameOfLoves_1FnSk(B)),
        skolem(B, skIsFemaleExistsNameOfLoves_0FnSk).
producer(female(A)) :-
        call_skolem(A, skIsGodIsFemaleExistsNameOfLoves_1FnSk(B)),
        skolem(B, skIsGodIsFemaleExistsNameOfLoves_0FnSk).
producer(god(A)) :-
        call_skolem(_, skIsGodIsFemaleExistsNameOfLoves_1FnSk(A)),
        skolem(A, skIsGodIsFemaleExistsNameOfLoves_0FnSk).
producer(loves(A, B)) :-
        call_skolem(A, skIsGodIsFemaleExistsNameOfLoves_1FnSk(B)),
        skolem(B, skIsGodIsFemaleExistsNameOfLoves_0FnSk).
producer(nameOf(A, "AlFaqa")) :-
        call_skolem(_, skIsGodIsFemaleExistsNameOfLoves_1FnSk(A)),
        skolem(A, skIsGodIsFemaleExistsNameOfLoves_0FnSk).
producer(nameOf(A, "Mary")) :-
        call_skolem(A, skIsGodIsFemaleExistsNameOfLoves_1FnSk(B)),
        skolem(B, skIsGodIsFemaleExistsNameOfLoves_0FnSk).
producer(female(A)) :-
        call_skolem(A,
                    skIsChildofIsFemaleExistsNameOfMother_0FnSk(_)).
producer(mother(B, A)) :-
        call_skolem(A,
                    skIsChildofIsFemaleExistsNameOfMother_0FnSk(B)).
producer(nameOf(B, childOf(A))) :-
        call_skolem(A,
                    skIsChildofIsFemaleExistsNameOfMother_0FnSk(B)).
producer(door(A)) :-
        call_skolem(A, skIsDoorExistsHas_0FnSk(B)),
        room(B).
producer(has(B, A)) :-
        call_skolem(A, skIsDoorExistsHas_0FnSk(B)),
        room(B).
producer(room(A)) :-
        call_skolem(A, skIsOneTwentyNameOf_0FnSk).
producer(nameOf(A, "OneTwenty")) :-
        call_skolem(A, skIsOneTwentyNameOf_0FnSk).


