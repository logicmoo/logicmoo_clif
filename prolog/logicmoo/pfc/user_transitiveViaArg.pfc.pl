

:- mpred_unload_file.

:- install_constant_renamer_until_eof.

:- file_begin(pfc).

:- set_fileAssertMt(baseKB).

argumentsConstrained(G):- cwc,ground(G),!.

% Example specialized
%((transitiveViaArg(P,PT,2)/ \+(P==PT)),arity(P,2)) ==> (t(P,I,Sub):- (cwc, dif(Sub,Super),t(PT,Sub,Super),t(P,I,Super))).
%((transitiveViaArgInverse(P,PT,2)/ \+(P==PT)),arity(P,2))==> (t(P,I,Sub):- (cwc, dif(Sub,Super),t(PT,Super,Sub),t(P,I,Super))).

functor_any(CONSQ,F,A):- cwc, length(IST,A),apply_term(F,IST,CONSQ),!.
fa_replace_arg(F,A,N,CONSQ,CSLOT,ASLOT,ANTE):-cwc, functor_any(CONSQ,F,A),arg(N,CONSQ,CSLOT),replace_arg(CONSQ,N,ASLOT,ANTE),!.

% Example generalized
(((transitiveViaArg(P,B,N) ),arity(P,A)/(fa_replace_arg(P,A,N,CONSQ,CSLOT,ASLOT,ANTE), P\=B)) ==>  
  (CONSQ:- (cwc,argumentsConstrained(CONSQ),dif(CSLOT,ASLOT),t(B,CSLOT,ASLOT),argumentsConstrained(ANTE),ANTE))).

transitiveViaArgInverse(P,B,N),arity(P,A)/(fa_replace_arg(P,A,N,CONSQ,CSLOT,ASLOT,ANTE), P\=B)==> 
  (CONSQ:- (cwc,argumentsConstrained(CONSQ),dif(CSLOT,ASLOT),t(B,ASLOT,CSLOT),argumentsConstrained(ANTE),ANTE)).


coExtensional(A,B)==> 
  (((genls(A,Supers)<==>genls(B,Supers)) , (genls(Subs,A)<==>genls(Subs,B)),  (isa(I,A)<==>isa(I,B))),
  coExtensional(B,A)).

%coExtensional(tPred,'Predicate').
%coExtensional(ttPredType,'PredicateType').

:- dynamic(anatomicallyCapableOf/3).

ttPredType('rtCapabilityPredicate').
isa(CAP_PRED,'rtCapabilityPredicate') ==> transitiveViaArg(CAP_PRED,genls,2).


'rtCapabilityPredicate'(anatomicallyCapableOf('mobEmbodiedAgent','ttFirstOrderCollection','rtBinaryRolePredicate')).

% disjointWith(A,B)==> (isa(I,A)==>~isa(I,B)).

%transitiveViaArg(isa,genls,2).
%transitiveViaArg(genls,genls,2).
%transitiveViaArgInverse(genls,genls,1).

/*       

~coExtensional(A, C) :- cwc,
        isa(B, A),
        ~isa(B, C).

~isa(B, A) :- cwc,
        coExtensional(A, C),
        ~isa(B, C).


isa(A, C) :- cwc,
        coExtensional(B, C),
        isa(A, B).

"
(implies
    (and 
      (isa ?INST ?TYPE1) 
      (isa ?INST ?TYPE2) 
      (collectionIntersection2 ?INTERSECTION ?TYPE1 ?TYPE2)) 
    (isa ?INST ?INTERSECTION))
".

*/
:- (compiling -> dmsg("IS COMPILING");dmsg("NOT COMPILING")).
:- set_prolog_flag(do_renames,restore).

