
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
v:attr_unify_hook(Ex,V):- unify_two(v,Ex,V).
v:attr_unify_hook(Ex,V):- (var(V)->unify_two(v,Ex,V);(throw("!nameOf " : Ex=V))).


nameOf1(Ex,V):- atomic(Ex),!,text_to_string(Ex,V).
nameOf1(Ex,V):- nonvar(Ex),!,term_string(Ex,V).
nameOf1(Ex,V):- get_attr(Ex,v,V0),!,nameOf1(V0,V).
nameOf1(Ex,V):- add_dom(V,nameOf1(Ex,V)),!.

nameOf(Ex,V):- atomic(Ex),!,text_to_string(Ex,V).
nameOf(Ex,V):- nonvar(Ex),!,term_string(Ex,V).
nameOf(Ex,V):- get_attr(Ex,v,V0),!,nameOf(V0,V).
nameOf(Ex,V):- add_dom(V,nameOf(Ex,V)).
% nameOf(Ex,V):- nonvar(V),!,put_attr(Ex,v,V).
% nameOf(Ex,V):- freeze(V,nameOf(Ex,V)).

/*
nameOf(Ex,V):- get_attr(Ex,v,V0)->text_to_string(V0,V);put_attr(Ex,v,V).

nameOf(Ex,V):-get_index_type_of(Ex,TEx),get_index_type_of(V,TV),nameOf(TEx,TV,Ex,V).

nameOf(var,var,Ex,V).
nameOf(attvar,var,Ex,V).
nameOf(var,attvar,Ex,V).
nameOf(attvar,attvar,Ex,V).

get_index_type_of(V,K):-var(V),!,(attvar(V)->K=attvar;K==var).
get_index_type_of([],list(nil)):-!.
get_index_type_of([H|_],list(K)):-!,get_index_type_of(H,K).
get_index_type_of(C,compound(F,A)):-compound(C),!,functor(C,F,A).
get_index_type_of(A,string):- string(A),!.
get_index_type_of(A,number):- number(A),!.
get_index_type_of(A,atom):- atom(A),!.
get_index_type_of(_,unknown).

gindex_type(var).
gindex_type(attvar).
gindex_type(list(_)).
gindex_type(compound(_,_)).
gindex_type(string).
gindex_type(atom).
gindex_type(number).
gindex_type(unknown).

:- forall(gindex_type(L),forall(gindex_type(R),writeln(nameOf(L,R,'Ex','V')))).
*/


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


query_tru(Qry) :- no_repeats(loop_check(prove_tru(Qry))).

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
assert_ex3(P):- dmsg(P),ain(P).


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

tbl2:- test_boxlog((exists([R,X,Y,T], 
  ((subRelation(R,loves), is_a(T,time), is_a(T,context),exists_durring(X,T),exists_durring(Y,T), 
              ~different(joe,X),~different(mary,Y)) => trueIn(T,holds(R,X,Y)))))).


tbl:- test_boxlog(loves(joe,mary) <=> ((exists([R,X,Y,T], 
  ((subRelation(R,loves), is_a(T,time), is_a(T,context),exists_durring(X,T),exists_durring(Y,T), 
              ~different(joe,X),~different(mary,Y)) => trueIn(T,holds(R,X,Y))))))).



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


f1:- assert_ex(man("John")).

f2:- assert_ex(ex(X,(nameOf(X,"John"), man(X)))).   % same comment as as f8

f3:- assert_ex(man("Joe")).   % man number 2

f3a:- assert_ex(ex(X,(man(X),nameOf(X,"Joe")))).   % same comment as as f8

f4:- assert_ex(ex(Child,(man(Child),child(Child)))).  % Look, its a man child!

f5:- assert_ex(ex(Child,child(Child))). % would this create a second child?

f6:- assert_ex(ex(P,(man(P);female(P)))).  % Two constraint paths

f7:- assert_ex(ex(P,((man(P);female(P)),nameOf(P,"Pat")))).  % Two constraint paths for a single identity

f8:- assert_ex(atleast(1,X,(man(X),nameOf(X,"Joe")))).   % same comment as as f9
f9:- assert_ex(atleast(1,X,(man(X),nameOf(X,"John")))).   % constraining by identity relly meant only 1



r1:- (assert_ex(
  ex(Mary,
    ex(John,
   (   female(Mary),
       nameOf(Mary,"Mary"),
       man(John),
       nameOf(John,"John"),
       loves(John,Mary)))))).


r2:- assert_ex((
 ex(God,
    ex(Mary,
   (   female(Mary),
       nameOf(Mary,"Mary"),
       god(God),
       nameOf(God,"AlFaqa"),
       loves(Mary,God)))))).

r3:- assert_ex(
  all(Child,
    ex(Mother,
   (   child(Child),
       female(Mother),
       nameOf(Child,childOf(Mother)),       
       mother(Child,Mother))))).



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

   
*/
:- install_retry_undefined(kbi,error).
:- install_retry_undefined(kbi,kbi_define).
:- install_retry_undefined(kbi,error).
:- install_retry_undefined(kbi,kb_shared).


require_dom(Var,Closure):- add_dom(Var,Closure).

% skolem(X,Y):- no_repeats(loop_check(proven_tru(skolem(X,Y)))).
:- kb_shared(baseKB:skolem/2).


:- ensure_abox(kbi).

:- f1.
% :- '$set_source_module'(user).
% :- kbi:tbl.
