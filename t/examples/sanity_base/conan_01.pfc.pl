#!/usr/bin/env swipl

:- module(sanity_ks_two,[]).

:- dynamic(prologHybrid/1).
:- ensure_loaded(library(pfc)).

/*

((prologHybrid(F),arity(F,A)/is_ftNameArity(F,A))<==>mpred_prop(F,A,prologHybrid)/is_ftNameArity(F,A)).

prologMultiValued(mudDescription(ftTerm,ftText), [predProxyAssert(add_description),predProxyRetract(remove_description),predProxyQuery(query_description)],prologHybrid).

prologHybrid(isEach(mudLastCommand/2,mudNamed/2, mudSpd/2,mudStr/2,typeGrid/3)).

((prologHybrid(F),arity(F,A)/is_ftNameArity(F,A))<==>mpred_prop(F,A,prologHybrid)/is_ftNameArity(F,A)).

*/

:- must((fully_expand( rtF(foo/2),O), O = (arity(foo, 2), rtF(foo), tPred(foo)))).



