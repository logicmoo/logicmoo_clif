

:- mpred_unload_file.

:- file_begin(pfc).

:- set_fileAssertMt(baseKB).



prologSingleValued(C):-cwc,is_ftCompound(C),functor(C,F,_),!,prologSingleValued(F).

:-dynamic(baseKB:mpred_sv/2).
arity(mpred_sv,2).


% asserting mpred_sv(p,2) causes p/2 to be treated as a mpred_sv, i.e.
% if p(foo,1)) is a fact and we assert_db p(foo,2), then the forrmer assertion
% is retracted.
mpred_sv(Pred,Arity)==> prologSingleValued(Pred),arity(Pred,Arity),singleValuedInArg(Pred,Arity).

% prologSingleValued(Pred),arity(Pred,Arity) ==> hybrid_support(Pred,Arity).

% mdefault(((prologSingleValued(Pred),arity(Pred,Arity))==> singleValuedInArg(Pred,Arity))).
prologSingleValued(Pred),arity(Pred,Arity), \+ singleValuedInArg(Pred,_) ==> singleValuedInArg(Pred,Arity).


% singleValuedInArg(singleValuedInArg,2).

% TODO might we say this?
% Not really due to not every SingleValued pred have a cardinatity of 1 .. some might have no instances
% ((singleValuedInArg(Pred,N)/ ( \+ singleValuedInArgDefault(Pred,N,_))) ==> singleValuedInArgDefault(Pred,N,isMissing)).


prologHybrid(singleValuedInArgDefault, 3).
prologHybrid(singleValuedInArgDefault(prologSingleValued,ftInt,ftTerm)).

% This would been fun! singleValuedInArgDefault(singleValuedInArgDefault,3,isMissing).

((somtimesBuggyFwdChaining==> ((
  ((singleValuedInArgDefault(P, 2, V), arity(P,2), argIsa(P,1,Most)) ==> relationMostInstance(P,Most,V)))))).

(singleValuedInArgDefault(SingleValued,ArgN,S1)/ground(S1) ==> singleValuedInArg(SingleValued,ArgN)).

(somtimesBuggyFwdChaining==>
 ({FtInt=2},singleValuedInArgDefault(PrologSingleValued,FtInt,FtTerm),arity(PrologSingleValued,FtInt),
  argIsa(PrologSingleValued,1,Col)==>relationMostInstance(PrologSingleValued,Col,FtTerm))).

somtimesBuggyBackChaining ==> (((singleValuedInArgDefault(F, N, Q_SLOT)/is_ftNonvar(Q_SLOT), arity(F,A),
   {functor(P,F,A),replace_arg(P,N,Q_SLOT,Q),replace_arg(Q,N,R_SLOT,R)})
       ==> mdefault( Q <- ({ground(P)},~R/nonvar(R_SLOT))))).


((singleValuedInArg(Pred,_))==>(prologSingleValued(Pred))).

(((singleValuedInArg(F, N)/atom(F), arity(F,A), \+ singleValuedInArgDefault(F, N, Q_SLOT),
   {functor(P,F,A),arg(N,P,P_SLOT),replace_arg(P,N,Q_SLOT,Q)})
       ==> (( P ==> 
          {dif:dif(Q_SLOT,P_SLOT), call_u(Q), ground(Q)}, \+Q, P)))).

(((singleValuedInArg(F, N), arity(F,A), \+ singleValuedInArgDefault(F, N, Q_SLOT),
   {functor(P,F,A),arg(N,P,P_SLOT),replace_arg(P,N,Q_SLOT,Q)})
       ==> (( P ==> 
          {dif:dif(Q_SLOT,P_SLOT), call_u(Q), ground(Q)}, \+Q, P)))).

somtimesBuggy==>((singleValuedInArgDefault(P, 2, V), arity(P,2), argIsa(P,1,Most)) <==> relationMostInstance(P,Most,V)).


:- if(true;(baseKB:startup_option(datalog,sanity);baseKB:startup_option(clif,sanity);flag_call(runtime_debug == true) )).

:- dynamic(someSV_testeed/3).
arity(someSV_testeed,3).

singleValuedInArg(someSV_testeed,3).
someSV_testeed(a,b,1).
someSV_testeed(a,b,2).
someSV_testeed(a,c,3).

:- listing(someSV_testeed/3).
:- must( \+ someSV_testeed(a,b,1)).
:- must(someSV_testeed(a,b,2)).


% :- flag_call(runtime_debug=true).

:- dynamic(someSV_testing/3).
arity(someSV_testing,3).

someSV_testing(a,b,1).
someSV_testing(a,b,2).
someSV_testing(a,c,3).

:- mpred_trace_exec.
singleValuedInArg(someSV_testing,3).
someSV_testing(a,c,4).

:- listing(someSV_testing/3).
:- must(someSV_testing(a,c,4)).
:- must(someSV_testing(a,b,2)).
:- must( \+ someSV_testing(a,b,1)).
:- mpred_notrace_exec.
:- endif.



:- if((fail,flag_call(runtime_debug == true) ;baseKB:startup_option(datalog,sanity);baseKB:startup_option(clif,sanity))).

:- ensure_loaded(pack(logicmoo_base/t/examples/pfc/'sanity_sv.pfc')).

:- endif.



