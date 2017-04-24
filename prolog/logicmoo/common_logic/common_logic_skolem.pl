%:- if(( ( \+ ((current_prolog_flag(logicmoo_include,Call),Call))) )).
:- module(common_logic_skolem,
	  [ form_sk/2,
	    sk_form/2,
            push_skolem/2,push_skolem/3,
            push_dom/2,annote/4,
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


member_eq(E, [H|T]) :-
    (   E == H
    ->  true
    ;   member_eq(E, T)
    ).

merge_forms(A,B,A):- A==B,!.
merge_forms(A,B,B):- member_eq(A,B),!.
merge_forms(A,B,A):- member_eq(B,A),!.
merge_forms(A,B,A):- A=B,!,wdmsg(seeeeeeeeeeeee_merge_forms(A,B)),!.
merge_forms(A,B,C):- flatten([A,B],AB),must(list_to_set(AB,C)),!.


:- fixup_exports.

