%:- if(( ( \+ ((current_prolog_flag(logicmoo_include,Call),Call))) )).
:- module(kbi,[existentialize/2,

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
/** <module> common_logic_kbi
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


:- module_transparent with_no_kif_var_coroutines/1.

with_no_kif_var_coroutines(Goal):- locally_each(t_l:no_kif_var_coroutines(true),Goal).

/* module Form Prolog sks (debugging)
*/

:- virtualize_source_file.


 :- meta_predicate query_ex(*).
 :- meta_predicate body_call(*).
 :- meta_predicate bless_ex(*,*).
 :- meta_predicate add_constraint_ex(*,*,*).
 :- meta_predicate reify(*).
 :- meta_predicate add_constraint_ex(*,*,*).
 :- meta_predicate test_count(0,*).
 :- meta_predicate undo(0).

:- use_module(library(must_trace)).
:- use_module(library(loop_check)).
:- use_module(library(logicmoo_typesystem)).

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

existentialize(P,NewP):- 
   existentialize_objs(P,MidP),
   existentialize_rels(MidP,NewP),!.

existentialize_objs(P,NewP):- 
 get_named_objs(P,Names),
 quantify_names(name_to_string,nameOf,Names,P,NewP),!.
  
existentialize_rels(P,NewP):-
 current_outer_modal_t(HOLDS_T),
 to_tlog(HOLDS_T,_KB,P,TLog),
 get_named_rels(TLog,Names),
 quantify_names(=,subRelationOf,Names,TLog,NewP),!.
  


already_existentialized(Term,Str):-  sub_term(NameOf,Term), compound(NameOf), NameOf=nameOf(_,StrW), name(Str,StrW).
already_existentialized(Term,Str):-  sub_term(NameOf,Term), compound(NameOf), NameOf=subRelationOf(_,Str).
already_existentialized(Term,Str):-  sub_term(NameOf,Term), compound(NameOf), NameOf=exists(X,_),Str==X.
already_existentialized(Term,Str):-  sub_term(NameOf,Term), compound(NameOf), NameOf=all(X,_),Str==X.

should_existentialize(Term,~ Sub,Str):-!,compound(Sub), should_existentialize(Term,Sub,Str).
should_existentialize(Term,Sub,Text) :- compound(Sub),functor(Sub,F,A),
  \+ dont_existentialize_args(Term,F,A),
  arg(N,Sub,Text),
  (string(Text);(existentialize_args(Sub,Term,F,A,N),atom(Text))).

string_better(Str,StrO):- string_lower(Str,StrL),StrL\==Str,!, StrO=Str.
string_better(Str,StrO):- toCamelcase(Str,StrL),text_to_string(StrL,StrO),!.

existentialize_args(_Sub,_Term,_F,1,1).
existentialize_args(Sub,Term,F,A,N):- 
  \+ dont_existentialize_args(Term,F,A),
  arg(_,Sub,Text),
  \+ string(Text),
  \+ compound(Text),
  (is_2nd_order_holds(F) -> N \==1 ; true),
  do_existentialize_f(F).

do_existentialize_f(loves).
do_existentialize_f(man).
do_existentialize_f(_).

dont_existentialize_args(_Term,F,_A):- dont_existentialize_f(F).

dont_existentialize_f(skolem).
dont_existentialize_f(nameOf).
dont_existentialize_f(equals).
dont_existentialize_f(different).
dont_existentialize_f(subRelationOf). 

get_named_objs(Term,Names):- 
   findall(Str,
    (sub_term(Sub,Term),
      should_existentialize(Term,Sub,Str),
      \+ already_existentialized(Term,Str)),
     NamesL),
   list_to_set(NamesL,Names).

should_existentialize_rel(_Term,Sub,Str):-compound(Sub),Sub=..[F,Str|_],is_2nd_order_holds(F).

get_named_rels(Term,Names):- 
   findall(Str,
    (sub_term(Sub,Term),
      should_existentialize_rel(_Term,Sub,Str),
      \+ already_existentialized(Term,Str)),
     NamesL),
   list_to_set(NamesL,Names).

quantify_names(_Conv,_Oper,[],P,P).
quantify_names(Conv,Oper,[Name|TODO],P,
 exists(X,(OperC & NewP))):- 
   OperC =.. [Oper,X,Str],
   call(Conv,Name,Str)->
   subst(P,Name,X,NextPM),
   add_var_to_env(Str,X),
   quantify_names(Conv,Oper,TODO,NextPM,NewP).
                                    
name_to_string(Name,Str):- text_to_string(Name,Text),string_better(Text,Str).


memberchk_eq(X, [Y|Ys]) :- (   X == Y ->  ! ;   memberchk_eq(X, Ys)).
subtract_eq([],_,[],[]).
subtract_eq([X|Xs],Ys,L,[X|Intersect]) :-   memberchk_eq(X,Ys),subtract_eq(Xs,Ys,L,Intersect).
subtract_eq([X|Xs],Ys,[X|T],Intersect) :-   subtract_eq(Xs,Ys,T,Intersect).

% :- abolish(user:portray/1).
:- dynamic(user:portray/1).
:- multifile(user:portray/1).

tru(P):- call_u(proven_tru(P)).

falsify(different(Puppy1, Puppy2)):- clause(proven_neg(different(Puppy1, Puppy2)),Body)*->once(Body);(!,fail).
falsify(P):- var(P),!,proven_neg(P).
falsify(~P):- !, call_u(proven_tru(poss(P))).
falsify(P):- call_u(proven_neg(P)).

make_identity(_):-!.
make_identity(I):- make_wrap(identityPred,I,2).

make_type(_):-!.
make_type(P):-make_wrap(call_tru,P,1).

make_wrap(T,MFA,D):- 
   get_mfa(MFA,M,F,AN),
   (AN==0->A=D;A=AN),
   functor(P,F,A), 
   asserta_if_new( ((P):- call(T,P))),
   asserta_if_new(baseKB:safe_wrap(M,F,A,T)),
   M:export(F/A),
   import(F/A).



kbi_define(MFA):- 
  get_mfa(MFA,M,F,A),
  kbi_define(M,F,A).

kbi_define(M,F,A):- clause_b(mpred_props(M,F,A,kbi_define)),!.
kbi_define(M,F,A):- ain(mpred_props(M,F,A,kbi_define)),
 functor(P,F,A),(predicate_property(M:P,static)->true;kbi_define_now(M,F,A,P)).

kbi_define_now(M,F,A,P):-  
  dmsg(kbi_define(M:F/A)),
  M:ain(P:-call_tru(P)),
  kb_shared(M:F/A).






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

assert_kbi(P):- must(assert_if_new(P)).

get_ex_quants_l(_,[],[],IO,IO).  
get_ex_quants_l(FreeVars,[X|ARGS],[Y|ARGSO],In,Rest):-
  visit_exs(X,Y,FreeVars,In,M),
  get_ex_quants_l(FreeVars,ARGS,ARGSO,M,Rest).

unify_two(AN,AttrX,V):- nonvar(V),!, (V='$VAR'(_)->true;throw(unify_two(AN,AttrX,V))).
unify_two(AN,AttrX,V):- get_attr(V,AN,OAttr),!,OAttr=@=AttrX,!. % ,show_call(OAttr=@=AttrX).
unify_two(AN,AttrX,V):- put_attr(V,AN,AttrX).

exists:attr_unify_hook(Ex,V):- unify_two(exists,Ex,V).


never_dom(Var,nesc(b_d(_,nesc,poss), ~ P )):- !, ensure_dom(Var,poss(P)).
never_dom(Var,nesc(~ P )):- !, ensure_dom(Var,poss(P)).
never_dom(Var,(~ P )):- !, ensure_dom(Var,poss(P)).
never_dom(NonVar,Closure):- nonvar(NonVar),!, \+ call_tru(NonVar,Closure).

%never_dom(Var,Closure):- attvar(Var),!,add_dom(Var,Closure).
%never_dom(Var,Closure):- add_dom(Var,Closure).

ensure_dom(NonVar,Closure):- nonvar(NonVar),!,call_tru(NonVar,Closure).
ensure_dom(Var,Closure):- attvar(Var),!,add_dom(Var,Closure).
ensure_dom(Var,Closure):- add_dom(Var,Closure).

not_nameOf(Ex,V):- \+ nameOf(Ex,V).

nameOf(Ex,V):- compound(V),!,proven_tru(nameOf(Ex,V)).
nameOf(Ex,V):- atomic(Ex),!,text_to_string(Ex,V).
nameOf(Ex,V):- nonvar(Ex),!,term_string(Ex,V).
nameOf(Ex,V):- nonvar(V),has_dom(Ex,nameOf(Ex,V0)),!,text_to_string(V0,V).
nameOf(Ex,V):- nonvar(V),!,add_dom(Ex,nameOf(Ex,V)),!,add_var_to_env(V,Ex).
nameOf(Ex,V):- var(V),has_dom(Ex,nameOf(Ex,V)),!,(nonvar(V)->add_var_to_env(V,Ex);true).

nameOf(Ex,V):- proven_tru(nameOf(Ex,V)).
% nameOf(Ex,V):- var(V),!,add_dom(Ex,nameOf(Ex,V)),!.



assign_ex(Ex,V):- nameOf(Ex,V).

reify((P,Q)):-!,reify(P),reify(Q).
reify(P):- query_ex(P).



% ex(P):- compound(P),P=..[_,I], (var(I)-> freeze(I,from_ex(P)) ; fail).

existential_var(Var,_):- nonvar(Var),!.
existential_var(Var,_):- attvar(Var),!.
existential_var(Var,P):- put_attr(Var,exists,P),!.


solve_ex(Var,_Vs,_Head,P,BodyList):- 
  existential_var(Var,P), 
  maplist(bless_with,BodyList), maplist(body_call,BodyList).

bless_with(P):- ground(P),!.
bless_with(P):- bless(P).

% body_call(P):- recorded(kbi,P).
body_call(P):- ground(P),!,loop_check(P).
body_call(P):- bless(P).


is_recorded(A):- context_module(M), recorded(M,A)*->nop(sanity(\+cyclic_term(A)));body_call(A).

% WORDED call_tru(P):- (clause(can_bless(P),Body)*->Body; ((fail,bless(P)))),is_recorded(P).


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


query_tru(Qry) :- nrlc((proven_tru_kbi(Qry))).

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


recorda_if_new(K,Lit1):- functor(Lit1,F,A),functor(Lit0,F,A),recorded(K,Lit0),Lit0=@=Lit1,!,wdmsg(skip_recorda(Lit0=@=Lit1)).
recorda_if_new(K,Lit1):- show_call(recorda(K,Lit1)).

recorda_if_new(Lit1):- context_module(M), recorda_if_new(M,Lit1). 

assert_ex2(P):- test_boxlog(P),!.

assert_ex2(P):- 
  kif_to_boxlog(P,BLU),
  sort(BLU,BL),
  must_maplist_det(assert_ex3,BL).

assert_ex3('$unused'(_):-_).

assert_ex3((H:-B)):- sort_body_better(H,B,BO),assert_ex4((H:-BO)).
assert_ex3(P):- assert_ex4(P).

assert_ex4(P):- assert_ex5(P).

assert_ex5(P):- assert_ex9(P).

assert_ex8(P):- nop(ain(P)),assert_ex9(P).
assert_ex9(P):- guess_varnames(P),portray_clause_w_vars(P).



new_sk_dict( _:{vs:_,sks:_,more:_}).
get_sk_props(X,Dict):- attvar(X),get_attr(X,skp,Dict).
ensure_sk_props(X,Dict):- sanity(var(X)),(get_sk_props(X,Dict)->true;((new_sk_dict(Dict),put_attr(X,skp,Dict)))).

:- kb_shared(baseKB:make_existential/3).

made_skolem(_,_).
skolem(X, count(_,_,SK),Which):- var(X), has_dom(X,made_skolem(SK,Which)), !.
skolem(X, Var,Which):- var(Var),!,call(call,clause(make_existential(_,Var,_),_)),skolem(X, Var,Which).
skolem(X, count(Start,End,SK),Which):- var(X),!, 
  \+ has_dom(X,made_skolem(SK,_)),
  functor(SK,SKF,_),
  !,
  between(1,Start,_),
  once((nb_get_next(SKF,Start,Which),
  add_dom(X,made_skolem(SK,Which)),
  make_existential(X,count(Start,End,SK),Which))).

skolem(X, SK,Which):- var(X),!, 
   \+ has_dom(X,made_skolem(SK,_)), !,
  add_dom(X,made_skolem(SK,Which)),
  make_existential(X,SK,Which).

skolem(E,SK,Which):- 
  nameOf(E,Named),!,(make_existential(X,SK,Which)*->nameOf(X,Named)).


% nb_get_first(SKF, Which):- (nb_current(SKF,Which) -> true ; (nb_setval(SKF,1),Which=1)).

nb_get_next(SKF, Max, Which):- flag(SKF,X,X+1), X == 0,!,Which=Max.
nb_get_next(SKF, Max, Which):- flag(SKF,X,X),!, (X == Max -> (Which=1,flag(SKF,_,0)) ; Which = X).

%iterate_numbs(_SK,Min,Max,Which):- Min==Max, !, between(1,Min,Which).
iterate_numbs(SKF,Min,Max,Which):- sanity(inf==Max),!, nb_get_next(SKF,Min,Which).
%iterate_numbs(_SK,Min,Max,Which):- !, (between(1,Min,Which);between(Min,Max,Which)).
  

assert_ex(P):-!,assert_ex2(P).


assert_ex(P):- 
  existentialize(P,PE)->P\==PE,!,
  assert_ex(PE).
  
assert_ex((P -> Q)):- !, assert_kbi(Q:-call_tru(P)).

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
                                    

disp_ex(X):-fmt9(X).

lr:- quietly((listing(producing/1),listing(proven_tru/1),listing(make_existential/3),
  doall((current_key(K),recorded(K,P),
    locally(set_prolog_flag(write_attributes,portray),wdmsg(P)))))).

clr:-
  doall((current_key(K),recorded(K,_,Ref),erase(Ref))).



test_count(Goal,N):- 
   findall(Goal,(Goal,format('~N~p~n',[Goal])),List),
   length(List,LL),
   LL==N.


%undo(Goal):- Redo = call(Goal), super_call_cleanup(true, (true; (Redo,setarg(1,Redo,true))), Redo).
undo(Goal):- true; (Goal,fail).

/*
% one list note on PNF  the Way i convert loves(joe,mary) to PNF...

loves(joe,mary)  <=> 
exists([R,X,Y,T], ((subRelation(R,loves), is_a(T,time), is_a(T,context),exists_durring(X,T),exists_durring(Y,T),
 ~different(joe,X),~different(mary,Y)) -> trueIn(T,holds(R,X,Y)))).

*/

attvar_or_const(C):- nonvar(C);attvar(C).

call_tru(X):- arg(1,X,E),call_tru(E,X).
call_tru(E,X):- \+ ground(E), (has_dom(E,(X))->rem_dom(E,(X)); true),
   nrlc((proven_tru((X)))),has_dom(E,(X)),attvar_or_const(E).
call_tru(E,X):- (nonvar(E);not_has_dom(E,(X)),!, nrlc((proven_tru_kbi((X)))), \+ proven_neg((X))),attvar_or_const(E).
call_tru(_,X):- context_module(M), inherit_above(M, (X)).

% call_tru(P):- is_recorded(P).
% call_tru(P):- bless(P),(clause(existing(P),Body)*->Body; true),ignore(is_recorded(P)).

:- kb_shared(baseKB:proven_neg/1).


loves(X,Y):-  (nonvar(X);nonvar(Y)),
              (has_dom(X,(loves(X,Y)))->rem_dom(X,(loves(X,Y))); true),
              (has_dom(Y,(loves(X,Y)))->rem_dom(Y,(loves(X,Y))); true),
              nrlc(proven_tru(loves(X,Y))),
              (has_dom(X,(loves(X,Y)));has_dom(Y,(loves(X,Y)))),
              (attvar_or_const(X),attvar_or_const(Y)).
loves(X,Y):- (nonvar(X);not_has_dom(X,(loves(X,Y))),!, nrlc((proven_tru_kbi((loves(X,Y)))))),
             (nonvar(Y);not_has_dom(Y,(loves(X,Y))),!, nrlc((proven_tru_kbi((loves(X,Y)))))), 
             \+ proven_neg(loves(X,Y)),
             attvar_or_const(X),attvar_or_const(Y).
loves(X,Y):- context_module(M), inherit_above(M, (loves(X,Y))).

proven_tru_kbi(G):- call(call,proven_tru(G)).

:- kb_shared(baseKB:proven_tru/1).

% proven_tru(G):- call(call,proven_tru(G)).

:- meta_predicate nrlc(0).
nrlc(G):- no_repeats(loop_check(G)).



man(X):- \+ ground(X),
    (has_dom(X,man(X))->rem_dom(X,man(X)); true),
   nrlc((proven_tru(man(X)))),has_dom(X,man(X)).
man(X):- (nonvar(X);not_has_dom(X,man(X)),!, nrlc((proven_tru_kbi(man(X)))), \+ proven_neg(man(X))).
man(X):- context_module(M), inherit_above(M, man(X)).



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
  kif_optionally_e(false,moveInwardQuants([],elim(all),KB),Mid1,Mid2),
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
expandQuants(KB,exists(X,NNF),FmlO):- expandQuants(KB,quant(atleast(1),X,NNF),FmlO).
expandQuants(KB,some(X,NNF),FmlO):- expandQuants(KB,quant(exactly(1),X,NNF),FmlO).
expandQuants(KB,quant(exactly(0),X,NNF),FmlO):- expandQuants(KB,~exists(X,NNF),FmlO).
expandQuants(KB,quant(atmost(0),X,NNF),FmlO):- expandQuants(KB,quant(exactly(0),X,NNF),FmlO).


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
un_quant3(KB,exists(X,NNF),exists(X,FmlO)):- !,un_quant3(KB,NNF,FmlO).
un_quant3(KB,quant(atleast(1),X,NNF),exists(X,FmlO)):- !,un_quant3(KB,NNF,FmlO).
un_quant3(KB,quant(isa(K),X,NNF),FmlO):- un_quant3(KB,NNF,NNFO),un_quant3(KB,isa(X,K) & NNFO,FmlO).
un_quant3(KB,quant(Quant,X,NNF),quant(Quant,X,FmlO)):- un_quant3(KB,NNF,FmlO).
% un_quant3(KB,quant(Quant,X,NNF),FmlO):- un_quant3(KB,NNF,NNFO),Quant=..[Q|AUNT],append([Q|AUNT],[X,NNFO],STERM),FmlO=..STERM.
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



subst_except_copy(Fml,X,Y,FmlY):- subst(Fml,X,Y,FmlY).
% subst_except_copy(Fml,X,Y,FmlY):- subst(Fml,X,Z,FmlZ),copy_term(Z=FmlZ,Y=FmlY).

% =================================
% Typed (Exactly/AtMost/AtLeast 2 ((?x Man)(?y Woman)(?z Child)) ...                     )
% =================================

nnf_ex(KB,quant(exactly(N),XL,NNF),FreeV,FmlO,Paths):- is_list(XL),
    (get_quantifier_isa(XL,X,Col) -> 
      nnf(KB,quant(exactly(N),X,isa(X,Col) & NNF),FreeV,FmlO,Paths);
      (XL=[X|MORE],!,
      (MORE==[] -> 
            nnf(KB,quant(exactly(N),X,NNF),FreeV,FmlO,Paths);
            nnf(KB,quant(exactly(N),X,quant(exactly(N),MORE,NNF)),FreeV,FmlO,Paths)))).

nnf_ex(KB,quant(atleast(N),XL,NNF),FreeV,FmlO,Paths):- is_list(XL),
    (get_quantifier_isa(XL,X,Col) -> 
      nnf(KB,quant(atleast(N),X,isa(X,Col) & NNF),FreeV,FmlO,Paths);
      (XL=[X|MORE],!,
      (MORE==[] -> 
            nnf(KB,quant(atleast(N),X,NNF),FreeV,FmlO,Paths);
            nnf(KB,quant(atleast(N),X,quant(atleast(N),MORE,NNF)),FreeV,FmlO,Paths)))).

nnf_ex(KB,quant(atmost(N),XL,NNF),FreeV,FmlO,Paths):- is_list(XL),
    (get_quantifier_isa(XL,X,Col) -> 
      nnf(KB,quant(atmost(N),X,isa(X,Col) & NNF),FreeV,FmlO,Paths);
      (XL=[X|MORE],!,
      (MORE==[] -> 
            nnf(KB,quant(atmost(N),X,NNF),FreeV,FmlO,Paths);
            nnf(KB,quant(atmost(N),X,quant(atmost(N),MORE,NNF)),FreeV,FmlO,Paths)))).

nnf_ex(KB,exists(XL,NNF),FreeV,FmlO,Paths):- is_list(XL),
    (get_quantifier_isa(XL,X,Col) -> 
      nnf(KB,exists(X,isa(X,Col) & NNF),FreeV,FmlO,Paths);
      (XL=[X|MORE],!,
      (MORE==[] -> 
            nnf(KB,exists(X,NNF),FreeV,FmlO,Paths);
            nnf(KB,exists(X,exists(MORE,NNF)),FreeV,FmlO,Paths)))).


% =================================
% Typed (Exists ((?x Man)(?y Woman)) ... )
% =================================

nnf_ex(KB,exists(TypedX,NNF),FreeV,FmlO,Paths):- get_quantifier_isa(TypedX,X,Col),!,
    nnf(KB,exists(X, NNF & isa(X,Col)),FreeV,FmlO,Paths).
nnf_ex(KB,exists(XL,NNF),FreeV,FmlO,Paths):- is_list(XL),XL=[X],!,
    nnf(KB,exists(X,NNF),FreeV,FmlO,Paths).
nnf_ex(KB,exists(XL,NNF),FreeV,FmlO,Paths):- is_list(XL),XL=[X|MORE],!,
    nnf(KB,exists(X,exists(MORE,NNF)),FreeV,FmlO,Paths).

% =================================
% Untyped (Exists (?x)  Fml)
% =================================


% nnf_ex(KB,exists(X,Fml),FreeV,NNF,Paths):-  \+ contains_var(X,Fml),!, trace_or_throw(bad_nnf(KB,exists(X,Fml),FreeV,NNF,Paths)).
% maybe this instead ? 
nnf_ex(KB,exists(X,Fml),FreeV,NNF,Paths):-  \+ contains_var(X,Fml),dmsg(( \+ contains_var(X,Fml))),!,nnf(KB,Fml,FreeV,NNF,Paths).


% =================================
% Untyped (Exists (?x)  Fml)
% =================================

% ATTVAR WAY
nnf_ex(KB,exists(X,Fml),FreeV,NNF1,Paths):- !,
 must_det_l((
    % add_dom(X,extensional(X)),
    term_slots(FreeV,Slots),
    skolem_f(KB, Fml, X, [KB|Slots], SkF),    
    nnf(KB, Fml <=> skolem(X,SkF,KB),FreeV,NNF1,Paths)
   )),!.


% =================================
% ==== AtLeast N ========
% ==== Cardinality (quantifier macros) ========
% =================================
% AtLeast 1:  We simply create the existence of 1
nnf_ex(KB,quant(atleast(N),X,Fml),FreeV,NNF,Paths):- N==1, !,
   nnf(KB,exists(X,Fml),FreeV,NNF,Paths).

nnf_ex(KB, ~ quant(atleast(N),X,Fml), FreeV,NNF,Paths):- NN is N - 1,
   nnf_ex(KB,quant(atmost(NN),X,Fml),FreeV,NNF,Paths).

nnf_ex(KB,quant(atleast(N),X,Fml),FreeV,NNF1,Paths):-  kif_option(true,skolem(nnf)), !,
 must_det_l((
    % add_dom(X,extensional(X)),
    term_slots(FreeV,Slots),
    skolem_f(KB, Fml, X, [KB|Slots], SkF),    
    nnf(KB, (Fml <=> skolem(X, count(N,inf,SkF),_Which)), FreeV, NNF1, Paths)
   )),!.

/*
nnf_ex(KB,quant(atleast(N),X,Fml),FreeV,NNF,Paths):- N == 2, !, 
   NEWFORM = ((skolem(X,skFn_only(Id,Set),KB) & idOf(X,Id,Set) & isSet(Set)) <=> Fml),
   add_var_to_env("Id",Id),add_var_to_env("Set",Set),
   nnf(KB,NEWFORM,FreeV,NNF,Paths),!.

% AtLeast 2: (This is just to confirm code .. thus, will comment out to use "AtLeast X:" rule)
nnf_ex(KB,quant(atleast(N),X,Fml),FreeV,NNF,Paths):-  N==2, !,          
  subst_except(Fml,X,Y,FmlY),
  %  Would this work?             
  % NEWFORM = ((exists(X,Fml) & exists(Y, FmlY & different(X,Y)))),
  %  or does it reify to be implication?
  NEWFORM =  ~  ( ~ different(X,Y) v exists(X,Fml)) v exists(Y,FmlY),
  %  exists 2 differnt?
  % NEWFORM =  (different(X,Y) <=> (exists(X,Fml) & exists(Y,FmlY))),
  nnf(KB,NEWFORM,FreeV,NNF,Paths).

nnf_ex(KB,quant(atleast(N),X,Fml),FreeV,NNF,Paths):- N > 1, kif_option(false,skolem(setOf)),!,  
   NEWFORM =  (all(X, exists(Set, (sizeOfLeast(Set,N) & elem(X,Set)))) <=> Fml), add_var_to_env("Set",Set),
   nnf(KB,NEWFORM,FreeV,NNF,Paths).
*/

% =================================
% ==== AtMost N ========
% ==== Cardinality (quantifier macros) ========
% =================================
nnf_ex(KB,~quant(atmost(0),X,Fml),FreeV,NNF,Paths):-  !,
  nnf_ex(KB, exists(X,Fml),FreeV,NNF,Paths).
                                               
nnf_ex(KB,quant(atmost(0),X,Fml),FreeV,NNF,Paths):-  !,
  nnf_ex(KB,all(X,~Fml),FreeV,NNF,Paths).

% AtMost 1: "If there exists 1 there does not exist 1 other"
nnf_ex(KB,quant(atmost(N),X,Fml),FreeV,NNF,Paths):- N == 1, !,
   subst_except_copy(Fml,X,Y,FmlY),
   NEWFORM =  ~( exists(X,Fml) & exists(Y,FmlY) & different(X,Y)),
   nnf(KB,NEWFORM,FreeV,NNF,Paths).

% AtMost N: "If there exists at least N there does not exist 1 other"
nnf_ex(KB,quant(atmost(N),X,Fml),FreeV,NNF,Paths):-   !,
   subst_except_copy(Fml,X,Y,FmlY),
   NEWFORM =  (quant(atleast(N),X,Fml) => ~(exists(Y, FmlY & different(X,Y)))),
   nnf(KB,NEWFORM,FreeV,NNF,Paths).

/*
% AtMost N: "If there exists 1 then there exists at most N-1"
nnf_ex(KB,quant(atmost(N),X,Fml),FreeV,NNF,Paths):- NewN is N - 1, !,
   subst_except(Fml,X,Y,FmlY),
   NEWFORM = (exists(Y, FmlY) => quant(atmost(NewN),X,Fml)),
  nnf(KB,~different(X,Y) v NEWFORM,FreeV,NNF,Paths).
*/

% =================================
% ==== Exactly N ========
% ==== Cardinality (quantifier macros) ========
% =================================
nnf_ex(KB,quant(exactly(0),X,Fml),FreeV,NNF,Paths):- !,
  nnf_ex(KB,all(X,~Fml),FreeV,NNF,Paths).

nnf_ex(KB,~ quant(exactly(0),X,Fml),FreeV,NNF,Paths):- !,
  nnf_ex(KB,exists(X,Fml),FreeV,NNF,Paths).

% Exactly 1: "If there exists 1 there does not exist 1 other"
nnf_ex(KB,quant(atmost(N),X,Fml),FreeV,NNF,Paths):- N == 1, !,
   subst_except_copy(Fml,X,Y,FmlY),
   NEWFORM =  ~( exists(X,Fml) & exists(Y,FmlY) & different(X,Y)),
   nnf(KB,NEWFORM,FreeV,NNF,Paths).

% Exactly N: states "There is AtMost N /\ AtLeast N"
nnf_ex(KB,quant(exactly(N),X,Fml),FreeV,NNF,Paths):- !,
   subst_except_copy(Fml,X,Y,FmlY),
   NEWFORM = (quant(atleast(N),X,Fml) & quant(atmost(N),Y,FmlY)),
   nnf(KB,NEWFORM,FreeV,NNF,Paths).

/*
nnf_ex(KB,~ quant(exactly(N),X,Fml),FreeV,NNF,Paths):- N > 0,!,
   Minus1 is N-1,Plus1 is N+1,
   NEWFORM =  (quant(atleast(Plus1),X,Fml) <=> ~quant(atmost(Minus1),X,Fml)),
   nnf(KB,NEWFORM,FreeV,NNF,Paths).


nnf_ex(KB,quant(exactly(N),X,Fml),FreeV,NNF,Paths):- !,
   subst_except_copy(Fml,X,Y,FmlY),
   NEWFORM = all(Y , ((quant(atleast(N),X,Fml) & different(X,Y))) => ~FmlY),
   nnf(KB,NEWFORM,FreeV,NNF,Paths).


nnf_ex(KB,quant(exactly(N),X,Fml),FreeV,NNF1,Paths):- fail,
 kif_option(true,skolem(nnf)), !,
 must_det_l((
    % add_dom(X,extensional(X)),
    term_slots(FreeV,Slots),
    skolem_f(KB, Fml, X, [KB|Slots], SkF),    
    nnf(KB, Fml <=> skolem(X,count(N,N,SkF),_Which),FreeV,NNF1,Paths)
   )),!.
*/

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
	SkV =..[vv|FreeVSet])),
       SkF = skF(Fun,SkV),
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

:- if(app_argv('--www') ; app_argv('--plweb'); app_argv('--irc')).
:- if(exists_source(pack(logicmoo_base/t/examples/fol/attvar_existentials))).
:- user:ensure_loaded((pack(logicmoo_base/t/examples/fol/attvar_existentials))).
:- endif.
:- endif.

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

x_skolem(Sk,skolem(Sk,Form,_)):-get_skolem(Sk,Form),del_attr(Sk,sk).

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
         nnf(KB, skolem(X,SKF,_Which) => NNFMid ,NewVars,NNF,Paths))).


:- fixup_exports.

