% File: /opt/PrologMUD/pack/logicmoo_base/prolog/logicmoo/common_logic/common_logic_compiler.pl
%:- if(( ( \+ ((current_prolog_flag(logicmoo_include,Call),Call))) )).
:- module(common_logic_compiler,         
          [ 
      nnf/3, 
           pnf/3, cf/5,
          % op(300,fx,'-'),
          /*op(1150,xfx,'=>'),
          op(1150,xfx,'<=>'),
          op(350,xfx,'xor'),
          op(400,yfx,'&'),  
          op(500,yfx,'v'),*/
            atom_compat/3,
            axiom_lhs_to_rhs/3,
            b_d_p/2,
            boxRule/3,
            cf_to_flattened_clauses/4,
            cf_to_flattened_clauses_0/4,
            cirRule/3,
            clausify/4,
            clean_repeats_d/2,
            cnf/3,
            cnf1/3,
            correct_boxlog/4,
            correct_boxlog_0/4,
            correct_cls/3,
            correct_cls0/3,
            corrected_modal/3,
            corrected_modal0/3,
            corrected_modal_recurse/3,
            corrected_modal_recurse0/3,
            ct_op/1,
            delete_sublits/3,
            to_modal1/3,
            is_skolem_setting/1,
            demodal_sents/3,
            diaRule/3,
            display_form/2,
            dnf/3,
            dnf1/3,
            expand_cl/3,
            flattenConjs/3,
            flatten_clauses/2,
            get_quantifier_isa/3,
            inclause/6,
            incorrect_cl/2,
            invert_modal/3,
            is_lit_atom/1,
            is_sent_op_modality/1,
            logical_neg/3,
            logical_pos/3,
            logically_matches/3,
            make_1_cl/4,
            make_clause_from_set/3,
            make_clause_set/3,
            make_clauses/3,
            make_each/3,
            mk_skolem/5,
            mk_skolem_name/5,
            modal2sent/2,
            mpred_quf/2,
            mpred_quf_0/2,
            neg_op/1,
            negate/3,
            negate0/3,
            negate_one/3,
            negate_one_maybe/3,
       nnf/3,
       nnf/5,
       nnf_label/5,
       nnf_shared/5,
            nonegate/3,
            nonvar_unify/2,
            notin/2,
            nowrap_one/3,
            pnf/3,
            pnf/4,
            putin/3,
            removeQ/3,
            removeQ/4,
            removeQ_LC/4,
            removes_literal/2,
            
            share_scopes/2,
            simplify_atom/2,
            simplify_cheap/2,
            simplify_cheap_must/2,
            skolem_bad/4,
            skolem_f/5,
            skolem_fn/6,
            skolem_fn_shared/6,
            % nnf_args/5,
       nnf_args/8,
            third_order/1,
            to_poss/3,
            to_regular_cl/4,
            unbuiltin_negate/3,
            unbuiltin_negate/4,
            until_op/1,
            variants_are_equal/3
          ]).

/** <module> common_logic_compiler

  Provides a prolog database replacement that uses an interpretation of KIF
 
   t/N
   hybridRule/2
   
 
  Logicmoo Project PrologMUD: A MUD server written in Prolog
  Maintainer: Douglas Miles
  Dec 13, 2035
 

  Compute normal forms for SHOIQ formulae.
  Skolemize SHOI<Q> formula.
 
  Copyright (C) 1999 Anthony A. Aaby <aabyan@wwc.edu>
  Copyright (C) 2006-2007 Stasinos Konstantopoulos <stasinos@users.sourceforge.net>
                1999-2015 Douglas R. Miles <logicmoo@gmail.com>
 
  This program is free software; you can redistribute it and/or modify
  it under the terms of the GNU General Public License as published by
  the Free Software Foundation; either version 2 of the License, or
  (at your option) any later version.
 
  This program is distributed in the hope that it will be useful,
  but WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
  GNU General Public License for more details.
 
  You should have received a copy of the GNU General Public License along
  with this program; if not, write to the Free Software Foundation, Inc.,
  51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA.


References
==========

[1] Planning with First-Order Temporally Extended Goals Using Heuristic
    Search, Baier, J. and McIlraith, S., 2006. Proceedings of the 21st
    National Conference on Artificial Intelligence (AAAI06), July, Boston, MA 

 
  FORMULA SYNTAX
 
   ~( A)
   &(F, F)
   v(F, F)
   '=>'(F, F)
   '<=>'(F, F)
   all(X,A)
   exists(X,A)
   atleast(X,N,A)
   atmost(X,N,A)


Expressions
-------------------

A BNF grammar for Expresions is the following:

BEXPR ::= <fluent-term> | ~FACT | FACT
BEXPR ::= or(BEXPR,BEXPR) | and(BEXPR,BEXPR) | not(BEXPR)

Temporal Boolean Expressions
----------------------------

BNF grammar:

TBE ::= BEXPR | final
TBE ::= always(TBE) | eventually(TBE) | until(TBE,TBE) | 
        release(CT,TBE,TBE) | cir(CT,TBE)


*/
%=%   mpred_clausify.P
%=%      SWI-Prolog version
%=%   Convert wffs to list of normal logic clauses
%=%
%=%   and       &  
%=%   or        v
%=%   not       ~
%=%   xor       xor
%=%   implies   =>   
%=%   iff       <=>  
%=%   all       all(X,0)
%=%   some      exists(Y,0)
%=%
%=%    all(X,p(X) => exists(Y, r(Y) & q(X,Y))) 
%=%  ===============
%=%    p(X) => r(sk1(X)) & q(X,sk1(X))
%=%  ===============
%=%    r(sk1(X)):- p(X).
%=%    q(X,sk1(X)):- p(X).


:- include(library('pfc2.0/mpred_header.pi')).
%:- user:ensure_loaded(library(pfc)).
%:- endif.
:- reexport(baseKB:library('logicmoo/common_logic/common_logic_skolem.pl')).

:- use_module(library(dictoo)).
:- virtualize_source_file.


:- include(common_logic_convert).

% % :- '$set_source_module'(common_logic_compiler).

% :- use_module(logicmoo(util/logicmoo_util_preddefs)).
:-
            op(1150,fx,(was_dynamic)),
            op(1150,fx,(was_multifile)),
            op(1150,fy,(was_module_transparent)),
            op(1150,fx,(was_export)).


:-ain(baseKB:predicateConventionMt(mud_test,baseKB)).

% :-reexport(library('logicmoo/common_logic/common_logic_snark')).


:- multifile((        
        baseKB:feature_test/0,
        baseKB:regression_test/0,
        baseKB:sanity_test/0)).
:- dynamic((        
        baseKB:feature_test/0,
        baseKB:regression_test/0,
        baseKB:sanity_test/0)).

% % :- '$set_source_module'(common_logic_compiler).


% :- use_module(logicmoo(snark/common_logic_sexpr)).

:- dynamic user:file_search_path/2.
:- multifile user:file_search_path/2.
:- prolog_load_context(source,File),file_directory_name(File,Dir),directory_file_path(_,Short,Dir),asserta_if_new(user:file_search_path(Short,Dir)).


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


% :- use_module(logicmoo(pttp/dbase_i_mpred_pttp_testing)). 
% :- use_module(logicmoo(pttp/dbase_i_mpred_pttp)). 

%  all(R, room(R) => exists(D, (door(D) & has(R,D))))
% for any arbitrary R, if R is a room then there exists some object D that is a door, and R has a D.
% door(sk6(_G180)):- room(_G180)
% has(_G180,sk6(_G180)):- room(_G180)
%  R is not a room if D is a door and R doesn't have D
% if there are no doors anywhere then there must not be rooms
% - room(R):- - has(R,_).


% SWI Prolog modules do not export operators by default
% so they must be explicitly placed in the user namespace

:- %(current_prolog_flag(argv,[pl|_]) -> )
     %op(400, fy, baseKB:(nesc) ),	% Necessity, Always
     %op(400, fy, baseKB:(poss) ),	% Possibly, Eventually
     op(400, fy, baseKB:(cir) ),	% Next time
     op(1075,xfx,user:'<-'),
  
  
     %op(400,fy,nesc),		% Necessity, Always
     %op(400,fy,poss),		% Possibly, Eventually
     op(400,fy,cir),		% Next time

     op(300,fx,'-'),
     op(300,fx,'~'),
     op(1075,xfx,'=>'),
     op(1075,xfx,'<-'),
     op(1075,xfx,'<=>'),
     op(350,xfx,'xor'),
     op(400,yfx,'&'),  
     op(500,yfx,'v')
     ,!.


:- thread_local(t_l:using_feature/1).
is_using_feature(Feature):- t_l:using_feature(Feature).

%= 	 	 

%% to_poss(KB, ?BDT, ?BDT) is det.
%
% Converted To Possibility.
%
to_poss(KB,X,poss(BDT,X)):- is_ftVar(X),share_scopes(KB,BDT),!.
to_poss(KB,poss(BDT,X),poss(BDT,X)):-nonvar(BDT),!,share_scopes(KB,BDT),!.
to_poss(KB,X,poss(BDT,X)):-share_scopes(KB,BDT),!.

to_nesc(KB,X,nesc(BDT,X)):- is_ftVar(X),share_scopes(KB,BDT),!.
to_nesc(KB,nesc(BDT,X),nesc(BDT,X)):-nonvar(BDT),!,share_scopes(KB,BDT),!.
to_nesc(KB,X,nesc(BDT,X)):-share_scopes(KB,BDT),!.


:- thread_local(t_l:current_form/1).

:- style_check(+singleton).


%% nnf(+KB,+Fml, ?NNF) is det.
%
% Negated Normal Form.
%
nnf(KB,FmlNV,NNF):-
  must(quietly(unnumbervars_with_names((KB,FmlNV),(KB0,FmlNV0)))),
   must( \+ contains_dvar(KB0:FmlNV0)),
   nnf0(KB0,FmlNV0,NNF).

%= 	 	 

%% nnf0( ?KB, ?Fml, ?NNF) is det.
%
% Negated Normal Form Primary Helper.
%
nnf0(KB,Fml,NNF):- 
 copy_term(Fml,Original),
 % ignore(KB='$VAR'('KB')),
   locally(t_l:current_form(Original),nnf(KB,Fml,[],NNF,_)),!.

:- thread_local(t_l:skolem_setting/1).

%= 	 	 

%% is_skolem_setting( ?S) is det.
%
% If Is A Skolem Setting.
%

% is_skolem_setting_default(push_skolem).
is_skolem_setting_default(in_nnf_implies).
is_skolem_setting(S):- t_l:skolem_setting(SS)->S=SS;is_skolem_setting_default(S).
%t_l:skolem_setting(push_skolem).
%t_l:skolem_setting(attvar).
%t_l:skolem_setting(in_nnf).
%t_l:skolem_setting(in_nnf_implies).
%t_l:skolem_setting(combine(=>)).
%t_l:skolem_setting(shared).
%t_l:skolem_setting(label).
%t_l:skolem_setting(removeQ).
%t_l:skolem_setting(eliminate).
%t_l:skolem_setting(ignore).


%= 	 	 

%% nnf_dnf( ?KB, ?Fml, ?DNF) is det.
%
% Negated Normal Form Disjunctive Normal Form.
%
nnf_dnf(KB,Fml,DNF):-
 locally(t_l:skolem_setting(ignore),
  (removeQ(KB,Fml,FmlUQ),
  nnf(KB,FmlUQ,NNF),
   dnf(KB,NNF,DNF))).



%= 	 	 

%% get_quantifier_isa( ?VALUE1, ?VALUE2, ?VALUE3) is det.
%
% get quantifier  (isa/2).
%

get_quantifier_isa([X,Col],X,Col):-var(X),nonvar(Col).



%% logically_matches( ?KB, ?A, ?B) is det.
%
% Logically Matches.
%
logically_matches(_KB,_A,_B):-!,fail.
logically_matches(KB,A,B):-nonvar(KB),!,logically_matches(_KB,A,B).
logically_matches(_,A,B):- (var(A);var(B)),!,A=B.
logically_matches(KB,all(_,A),B):-!,logically_matches(KB,A,B).
logically_matches(KB,B,all(_,A)):-!,logically_matches(KB,A,B).
logically_matches(KB,exists(V,A),exists(V,B)):-!,logically_matches(KB,A,B).
logically_matches(KB,[A],B):-!,logically_matches(KB,B,A).
logically_matches(KB,A,B):- once(corrected_modal_recurse(KB,A,AM)),A\=@=AM,!,logically_matches(KB,B,AM).
logically_matches(_,A,A).


is_leave_alone(P):- \+ compound(P),!.
is_leave_alone(P):- leave_as_is_logically(P),!.
is_leave_alone(P):- functor(P,F,A),is_leave_alone_pfa(P,F,A).

is_leave_alone_pfa(_,F,_):- arg(_,v((v),(&),(=>),(<=>),(all),(exists),(~)),F),!,fail.
is_leave_alone_pfa(_,assertTemplateReln,_).
is_leave_alone_pfa(_,mudEquals,2).

:- discontiguous(nnf1/5).
:- discontiguous(axiom_lhs_to_rhs/3).

discovered_var(_Fml,_Slots).
discovered_term_slots(_Fml,_Slots).

% =================================
% ====== drive negation inward ===
% =================================

%% nnf(KB,+Fml,+FreeV,-NNF,-Paths) is det.
%
% Fml,NNF:    See above.
% FreeV:      List of free variables in Fml.
% Paths:      Number of disjunctive paths in Fml.

% NonVar used in OUTPUT VAR
nnf(KB,Lit,FreeV,LitO,N):-nonvar(LitO),!,nnf1(KB,Lit,FreeV,LitM,N),!,LitM=LitO.
nnf(KB,Lit,FreeV,LitO,N):-var(FreeV),!,trace_or_throw(bad_nnf(KB,Lit,FreeV,LitO,N)).
nnf(KB,Lit,FreeV,LitO,N):- 
  (nb_current('$nnf_outer',Was);Was=[]),
  b_setval('$nnf_outer',[Lit|Was]),
  nnf1(KB,Lit,FreeV,LitO,N),!.

% for tracing
% nnf1(KB,Fin,FreeV,NNF,Paths):- dmsg(nnf1(KB,Fin,FreeV,NNF,Paths)),fail.

% Sentence was a Variable
nnf1(_KB, Lit,FreeV, Lit,1):- is_ftVar(Lit),!, %push_dom(Lit,ftSentence),
 discovered_var(Lit,FreeV).
nnf1(_KB,~Lit,FreeV,~Lit,1):- is_ftVar(Lit),!, %push_dom(Lit,ftSentence),
 discovered_var(Lit,FreeV).

% Skipped Args
nnf1(_KB,Lit,FreeV,Lit,1):- is_list(Lit),!,discovered_term_slots(Lit,FreeV).
nnf1(_KB,Lit,FreeV,Lit,1):- is_leave_alone(Lit),!,discovered_term_slots(Lit,FreeV).

% Catch and REwrite Temporal/Modals missed by preprocessor
nnf1(KB,Fin,FreeV,NNF,Paths):- corrected_modal(KB,Fin,F)-> Fin \=@= F,!,nnf(KB,F,FreeV,NNF,Paths).

/*
nnf1(KB,'tColOfCollectionSubsetFn'(Col,'tSetOfTheSetOfFn'(Var,Formulas)),FreeV,Var,2):- is_ftVar(Var), \+ is_ftVar(Col),
  nnf(KB,all(Var,isa(Var,Col)&Formulas),FreeV,SubForms,_),   
   asserta(added_constraints(KB,Var,SubForms)).
*/
    
% Simplification
nnf1(KB,~nesc(BDT,~F),FreeV,BOX,Paths):- nonvar(F),!,
   nnf1(KB,poss(BDT,F),FreeV,BOX,Paths).

nnf1(KB,~poss(BDT,~F),FreeV,BOX,Paths):- nonvar(F),!,
   nnf1(KB,nesc(BDT,F),FreeV,BOX,Paths).

nnf1(KB,~nesc(BDT,F),FreeV,BOX,Paths):- nonvar(F),!,
   nnf1(KB,poss(BDT,~F),FreeV,BOX,Paths).

nnf1(KB,~poss(BDT,F),FreeV,BOX,Paths):- nonvar(F),!,
   nnf1(KB,nesc(BDT,~F),FreeV,BOX,Paths).

% =================================
% Necessity, Always
% =================================

nnf1(KB,nesc(BDT,F),FreeV,BOX,Paths):- 
   nnf(KB,F,FreeV,NNF,Paths), cnf(KB,NNF,CNF), boxRule(KB,nesc(BDT,CNF), BOX).


% =================================
% Possibly
% =================================

% dmiles thinks this is ok
nnf1(KB,poss(BDT,PQ),FreeV,DIA,Paths):- fail, compound(PQ),PQ = (P=>Q), !,
   nnf1(KB,poss(BDT,P)=>Q,FreeV,DIA,Paths).

nnf1(KB,poss(BDT,F),FreeV,DIA,Paths):- 
   nnf(KB,F,FreeV,NNF,Paths), dnf(KB,NNF,DNF), diaRule(KB,poss(BDT,DNF), DIA).

% =================================
% Possibly, Eventually / Beliefs / Knows
% =================================

nnf1(KB, ~( Fml),FreeV,NNF,Paths):- nonvar(Fml),   
      (Fml = (beliefs(BDT,~F)) -> Fml1 = knows(BDT, ( F));
       Fml = (knows(BDT,~F)) -> Fml1 = beliefs(BDT, ( F))
	),!,
       nnf(KB,Fml1,FreeV,NNF,Paths).

%% axiom_lhs_to_rhs( ?KB, :LHS, :RHS) is det.
%
% Axiom Left-hand-side Converted To Right-hand-side.
%

axiom_lhs_to_rhs(_KB, poss(BDT,beliefs(A,~F1)),~nesc(BDT,knows(A,F1))).
axiom_lhs_to_rhs(_KB, all(Vs,poss(BDT,A & B)) ,  ~exists(Vs,nesc(BDT,A & B))).

% disabled
nnf1(KB,Fin,FreeV,DIA,Paths):-  fail,  copy_term(Fin,Fml),axiom_lhs_to_rhs(KB,F1,F2) , 
 \+ \+ (numbervars(Fin,0,_,[attvar(bind)]),logically_matches(KB,Fin,F1)),
  show_success(nnf,(nop(Fml),logically_matches(KB,Fin,F1))),show_call(why,nnf(KB,F2,FreeV,DIA,Paths)).

%   poss(beliefs(A,~F1)) ->  poss(~knows(A,F1)) ->  ~nesc(knows(A,F1))

nnf1(KB,cir(CT,F),FreeV,CIR,Paths):-
      nnf(KB,F,FreeV,NNF,Paths), 
      cirRule(KB,cir(CT,NNF), CIR),!.

% % axiom_lhs_to_rhs(KB,poss(- (- LIT)),poss(LIT)):-set_is_lit(LIT).
:- style_check(+singleton).

% =================================
% Typed (ForAll ((?x Man)(?y Woman)) ...                     )
% =================================

nnf1(KB,all(XL,NNF),FreeV,FmlO,Paths):- is_list(XL),
    (get_quantifier_isa(XL,X,Col) -> 
      nnf(KB,all(X,isa(X,Col)=>NNF),FreeV,FmlO,Paths);
      (XL=[X|MORE],!,
      (MORE==[] -> 
            nnf(KB,all(X,NNF),FreeV,FmlO,Paths);
            nnf(KB,all(X,all(MORE,NNF)),FreeV,FmlO,Paths)))).


% =================================
% Typed (Exactly 2 ((?x Man)(?y Woman)(?z Child)) ...                     )
% =================================

nnf1(KB,exactly(N,XL,NNF),FreeV,FmlO,Paths):- is_list(XL),
    (get_quantifier_isa(XL,X,Col) -> 
      nnf(KB,exactly(N,X,isa(X,Col)=>NNF),FreeV,FmlO,Paths);
      (XL=[X|MORE],!,
      (MORE==[] -> 
            nnf(KB,exactly(N,X,NNF),FreeV,FmlO,Paths);
            nnf(KB,exactly(N,X,exactly(N,MORE,NNF)),FreeV,FmlO,Paths)))).

% =================================
% Typed (Exists ((?x Man)(?y Woman)) ... )
% =================================

nnf1(KB,exists(TypedX,NNF),FreeV,FmlO,Paths):- nonvar(TypedX),get_quantifier_isa(TypedX,X,Col),!,
    nnf(KB,exists(X,isa(X,Col) & NNF),FreeV,FmlO,Paths).
nnf1(KB,exists(XL,NNF),FreeV,FmlO,Paths):- is_list(XL),XL=[X],!,
    nnf(KB,exists(X,NNF),FreeV,FmlO,Paths).
nnf1(KB,exists(XL,NNF),FreeV,FmlO,Paths):- is_list(XL),XL=[X|MORE],!,
    nnf(KB,exists(X,exists(MORE,NNF)),FreeV,FmlO,Paths).

% =================================
% Global Typed (ForAll ?x  ... )
% =================================
nnf1(KB,all(X,NNF),FreeV,all(X,NNF2),Paths):- is_using_feature(quants_removed_in_removeQ),!,
   nnf(KB,NNF,NewVars,NNF2,Paths),
   add_to_vars(X,FreeV,NewVars),!.

nnf1(KB,all(X,NNF),FreeV, NNF2, Paths):- is_using_feature(quants_removed_in_NNF),!,     
   nnf(KB,NNF,NewVars,NNF2,Paths),
   add_to_vars(X,FreeV,NewVars),!.


% =================================
% Existential Skolem Setting (only one of the next two clauses are used)  ========
% =================================
nnf1(KB,exists(X,Fml),FreeV,NNF,Paths):-  \+ contains_var(X,Fml),!, trace_or_throw(bad_nnf(KB,exists(X,Fml),FreeV,NNF,Paths)).
% maybe this instead ? nnf1(KB,exists(X,Fml),FreeV,NNF,Paths):-  \+ contains_var(X,Fml),!,nnf(KB,Fml,FreeV,NNF,Paths).

nnf1(KB,exists(X,Fml),FreeV,NNF,Paths):- is_skolem_setting(in_nnf_implies),!,
 must_det_l((
   nnf(KB,Fml,FreeV,NNF1,_Paths),
   term_slots(Fml+FreeV+NNF1,Slots),
    delete_eq(Slots,X,SlotsV1),
    delete_eq(SlotsV1,KB,SlotsV2),
    skolem_f(KB, Fml, X, SlotsV2, SkF),
    
%    nnf(KB,(skolem(X,SkF) => NNF1),[X|Slots],NNF,Paths), % push_skolem(X,SkF),
   subst(NNF1,X,SkF,SkFml),nnf(KB, SkFml ,[X|Slots],NNF,Paths),
          !)),!.

nnf1(KB,exists(X,Fml),FreeV,NNF,Paths):- is_skolem_setting(in_nnf_implies),!,
 must_det_l((
   add_to_vars(X,FreeV,NewVars),
    term_slots(NewVars,Slots),
    delete_eq(Slots,X,SlotsV1),
    delete_eq(SlotsV1,KB,SlotsV2),
    skolem_f(KB, Fml, X, SlotsV2, SkF),
    push_skolem(X,SkF),
    nnf(KB,(~skolem(X,SkF) v Fml),NewVars,NNF,Paths)
   )),!.

% disabled
nnf1(KB,exists(X,Fml),FreeV,exists(X,NNF),Paths):- (is_skolem_setting(removeQ);is_skolem_setting(attvar)),
   add_to_vars(X,FreeV,NewVars),
   nnf(KB,Fml,NewVars,NNF,Paths),!.

% disabled
nnf1(KB,exists(X,Fml),FreeV,NNF,Paths):- is_skolem_setting(in_nnf),!,
 must_det_l((
   add_to_vars(X,FreeV,NewVars),
    term_slots(NewVars,Slots),
    delete_eq(Slots,X,SlotsV1),
    delete_eq(SlotsV1,KB,SlotsV2),
    skolem_f(KB, Fml, X, SlotsV2, SkF),
    push_skolem(X,SkF),
   nnf(KB,Fml,NewVars,NNF,Paths))),!.

% disabled
nnf1(KB,exists(X,Fml),FreeV,NNF,Paths):- is_skolem_setting(push_skolem),!, wdmsg(nnf1(skolemizing(push_skolem,exists(X,Fml)))),
   push_skolem(X,true),
   nnf(KB,Fml,FreeV,NNF,Paths).

% disabled
nnf1(KB,exists(X,Fml),FreeV,NNF,Paths):- is_skolem_setting(old_mk_skolem),!, wdmsg(nnf1(skolemizing(exists(X,Fml),with(FreeV)))),
   must(mk_skolem(KB,Fml,X,FreeV,FmlSk)),
   nnf(KB,FmlSk,FreeV,NNF,Paths).

% exists(X,nesc(f(X)))  ->  exists(X, ~( poss( ~( f(X))))) ->   ~( poss( ~( f(X))))
% disabled
nnf1(KB,exists(_X,Fml),FreeV,NNF,Paths):- fail, nnf(KB, ~( poss(b_d(KB,nesc,poss), ~( Fml))),FreeV,NNF,Paths).

% disabled
nnf1(KB,exists(X,Fml),FreeV,NNF,Paths):- is_skolem_setting(label),
   nnf_label(KB,exists(X,Fml),FreeV,NNF,Paths),!.

% disabled
nnf1(KB,exists(X,Fml),FreeV,NNF,Paths):- is_skolem_setting(shared),
   nnf_shared(KB,exists(X,Fml),FreeV,NNF,Paths),!.

% disabled
nnf1(KB,exists(X,Fml),FreeV,NNF,Paths):- is_skolem_setting(ignore),
   add_to_vars(X,FreeV,NewVars),
   nnf(KB,Fml,NewVars,NNF,Paths).

% =================================
% ==== Cardinality (quantifier macros) ========
% =================================

% AtLeast 1:  We simply create the existence of 1
nnf1(KB,atleast(N,X,Fml),FreeV,NNF,Paths):- N==1, !,
   nnf(KB,exists(X,Fml),FreeV,NNF,Paths).

% AtLeast 2: (This is just to confirm code .. thus, will comment out to use "AtLeast X:" rule)
nnf1(KB,atleast(N,X,Fml),FreeV,NNF,Paths):-  N==2, !,  
  subst_except(Fml,X,Y,FmlY),
  %  Would this work?             
  %      NEWFORM = ((exists(X,Fml) & exists(Y,FmlY) & different(X,Y))),
  %  or does it need to be implication?
  NEWFORM = ((exists(X,Fml) & exists(Y,FmlY)) => different(X,Y)),
  nnf(KB,NEWFORM,FreeV,NNF,Paths).

% AtLeast 3: (This is just to confirm code .. thus, will comment out to use "AtLeast X:" rule)
nnf1(KB,atleast(N,X,Fml),FreeV,NNF,Paths):-  N==3, !,
  subst_except(Fml,X,Y,FmlY),subst_except(Fml,X,Z,FmlZ),
  NEWFORM = ((exists(X,Fml) & exists(Y,FmlY) & exists(Z,FmlZ)) => (different(X,Y) & different(X,Z) & different(Y,Z))),
  nnf(KB,NEWFORM,FreeV,NNF,Paths).

% AtLeast 4: (This is just to confirm code .. thus, will comment out to use "AtLeast X:" rule)
nnf1(KB,atleast(N,X,Fml),FreeV,NNF,Paths):-  N==4, is_using_feature(list_macros),!,
 exists([A,B,C,D],
 NEWFORM =  (different(A,B) & different(A,C) & different(A,D) & different(B,C) & different(B,D) & different(C,D) 
    & memberOf(X,[A,B,C,D]) => Fml)),
    nnf(KB,NEWFORM,FreeV,NNF,Paths).

% AtLeast N:  If AtLeast 4 above is correct than AtLeast N is correcT?
nnf1(KB,atleast(N,X,Fml),FreeV,NNF,Paths):- is_using_feature(list_macros),!,
   length(SET,N),
   NEWFORM = all(X, ((allDifferent(SET) & memberOf(X,SET)) => Fml)),
   nnf(KB,NEWFORM,FreeV,NNF,Paths).

% AtLeast N:  Non list macro PFCLog version (Might prefer this?)
nnf1(KB,atleast(N,X,Fml),FreeV,NNF,Paths):- % is_using_feature(inline_prolog),!,
    X= Skolem,
    NEWFORM =  
       ({between(1,N,Id)} => equals(Skolem, skolemIDAndFormFN(Id,Fml))),
    nnf(KB,NEWFORM,FreeV,NNF,Paths).

% AtLeast N:  This constructs N separate Skolems.. but did i name them the same?
nnf1(KB,atleast(N,X,Fml),FreeV,NNF,Paths):- NewN is N - 1, !,
    subst_except(Fml,X,Y,FmlY),        
    NEWFORM = ((exists(Y, FmlY) & atleast(NewN,X,Fml)) => different(X,Y)),
    nnf(KB,NEWFORM,FreeV,NNF,Paths),!.

% AtLeast N:  Non list macro version (Might prefer this?)
nnf1(KB,atleast(N,X,Fml),FreeV,NNF,Paths):- NewN is N - 1, !,
    subst_except(Fml,X,Y,FmlY),        
    NEWFORM = exists(Y, (FmlY & different(X,Y) & atleast(NewN,X,Fml))),
    nnf(KB,NEWFORM,FreeV,NNF,Paths),!.

% AtMost 1: "There may never be 2 (that is X, Y are different) and have Fml be true"
nnf1(KB,atmost(N,X,Fml),FreeV,NNF,Paths):- N==1, !, 
    subst_except(Fml,X,Y,FmlY),
   NEWFORM = ( ~ ( exists(X,Fml) & exists(Y,FmlY) & different(X,Y) ) ),
   nnf(KB,NEWFORM,FreeV,NNF,Paths).

% AtMost N: "If there are AtLeast N then  There Exists No More"
nnf1(KB,atmost(N,X,Fml),FreeV,NNF,Paths):- fail,  % wont work due to ~atleast = atmost (creating a loop (when in NNF))
   subst_except(Fml,X,Y,FmlY),
   NEWFORM = (atleast(N,X,Fml) => ~exists(Y, FmlY & different(X,Y))),
  nnf(KB,NEWFORM,FreeV,NNF,Paths).

% AtMost N: "If there exists 1 then there exists at most N-1"
nnf1(KB,atmost(N,X,Fml),FreeV,NNF,Paths):- NewN is N - 1, !,
   subst_except(Fml,X,Y,FmlY),
   NEWFORM = (exists(Y, FmlY) => atmost(NewN,X,Fml & different(X,Y))),
  nnf(KB,NEWFORM,FreeV,NNF,Paths).


% Exactly N: "There exists 1 more than the exact 1 smaller group"
nnf1(KB,exactly(N,X,Fml),FreeV,NNF,Paths):- number(X), N>1, NewN is N - 1, !,
    subst_except(Fml,X,Y,FmlY),      
    NEWFORM = exists(Y, (FmlY & (different(X,Y) =>  exactly(NewN,X,Fml)))),
    nnf(KB,NEWFORM,FreeV,NNF,Paths).

% Exactly N: states "There is AtMost N /\ AtLeast N"
nnf1(KB,exactly(N,X,Fml),FreeV,NNF,Paths):-            !,
   NEWFORM = (atleast(N,X,Fml) & atmost(N,X,Fml)),
   nnf(KB,NEWFORM,FreeV,NNF,Paths).

% Exactly 1: states "There is AtMost and AtLeast 1"
nnf1(KB,exactly(N,X,Fml),FreeV,NNF,Paths):- N==1, !,
     subst_except(Fml,X,Y,FmlY),
     NEWFORM = (exists(X,Fml) & exists(Y,FmlY))=>equals(X,Y),
    nnf(KB,NEWFORM,FreeV,NNF,Paths).



% =================================
% ==== basic macros ========
% =================================

% AllDifferent 4: "All 4 members are different"
nnf1(KB,allDifferent([A,B,C,D]),FreeV,NNF,Paths):- 
  NEWFORM =  (different(A,B) & different(A,C) & different(A,D) & different(B,C) & different(B,D) & different(C,D)),
  nnf(KB,NEWFORM,FreeV,NNF,Paths).

% AllDifferent Set: "All members are different"
nnf1(KB,allDifferent(SET),FreeV,NNF,Paths):- is_using_feature(list_macros),is_using_feature(inline_prolog),!,
  NEWFORM =  (
    {member(X,SET),member(Y,SET),X\==Y} 
       =>different(X,Y) ),
   nnf(KB,NEWFORM,FreeV,NNF,Paths).

% =================================
%  Temporal LTL/CTL/CTL* Logic
% =================================

% Release: \phi releases \psi if \psi is true until the first position in which 
%  \phi is true (or forever if such a position does not exist). 
nnf1(KB,release(CT,CurrentPsi,ReleaserPhi),FreeV,NNF,Paths):- 
   share_scopes(KB,CT),!,
   Fml1 = (ReleaserPhi => ~CurrentPsi),
  nnf(KB,Fml1,FreeV,NNF,Paths).

% Until: \psi holds at the current or a future position, and \phi has to hold until that position. At that position \phi does not have to hold any more
nnf1(KB,until(CurrentPsi,DisablerPhi),FreeV,NNF,Paths):- 
  Fml1 = (CurrentPsi v (DisablerPhi => ~CurrentPsi)),
  nnf(KB,Fml1,FreeV,NNF,Paths).

% ~until(Future,Current) -> ( always(~Current) v until(~Current,(~Future & ~Current)))
nnf1(KB,~until(CT,Future,Current),FreeV,NNF,Paths):- 

   nnf(KB, ~( Future),FreeV,NNFuture,_),
   nnf(KB, ~( Current),FreeV,NNCurrent,_),
   share_scopes(KB,CT),!,
   Fml1 = v(always(NNCurrent), until(CT,NNCurrent,&(NNFuture,NNCurrent))),
   nnf(KB,Fml1,FreeV,NNF,Paths).
   
% ~cir(CT,Future) -> cir(CT,~Future)
nnf1(KB,~cir(CT,Future),FreeV,NNF,Paths):- 
   nnf(KB,cir(CT,~Future),FreeV,NNF,Paths),!.

% A until B means it B starts after the ending of A
axiom_lhs_to_rhs(KB,startsAfterEndingOf(B,A),until(CT,A,B)):- share_scopes(KB,CT),!,set_is_lit(A),set_is_lit(B),!.

nnf1(KB,until(CT,A,B),FreeV,NNF,Paths):-  set_is_lit(A),set_is_lit(B),  share_scopes(KB,CT),!,
      nnf(KB,A,FreeV,NNF1,Paths1),
      nnf(KB,B,FreeV,NNF2,Paths2),
	Paths is Paths1 + Paths2,
        set_is_lit(NNF1),
        set_is_lit(NNF2),
	NNF = until(CT,NNF1, NNF2).

nnf1(KB,holdsIn(TIMESPAN,TRUTH),FreeV,NNF,Paths):-  
  nnf(KB,occuring(TIMESPAN) => TRUTH,FreeV,NNF,Paths).

nnf1(KB,holdsIn(TIMESPAN,TRUTH),FreeV,NNF,Paths):-  nnf(KB,temporallySubsumes(TIMESPAN,TRUTH),FreeV,NNF,Paths).

nnf1(KB,temporallySubsumes(TIMESPAN,TRUTH),FreeV,NNF,Paths):-  
 nnf(KB,(until(CT,TRUTH,~TIMESPAN)&until(CT,~TRUTH,TIMESPAN)),FreeV,NNF,Paths).

% =================================
% Equality
% =================================

nnf1(KB, ~( different(X , Y)),FreeV,NNF,Paths):- !, nnf(KB, ( equals(X , Y)),FreeV,NNF,Paths).
nnf1(KB, ~( equals(X , Y)),FreeV,NNF,Paths):- !, nnf(KB, ( different(X , Y)),FreeV,NNF,Paths).

nnf1(KB, ~( ~different(X , Y)),FreeV,NNF,Paths):- !, nnf(KB, ( ~equals(X , Y)),FreeV,NNF,Paths).
nnf1(KB, ~( ~equals(X , Y)),FreeV,NNF,Paths):- !, nnf(KB, ( ~different(X , Y)),FreeV,NNF,Paths).

%nnf1(KB,hasName(Entity,Name),FreeV,NNF,Paths):- nonvar(Entity),
%   nnf(KB,equals(Entity,Entity0) => hasName(Entity0,Name),FreeV,NNF,Paths).

% =================================
% Back to Normal NNF-ing 
% =================================

nnf1(KB, ~( xor(X , Y)),FreeV,NNF,Paths):-
   !,
  nnf(KB, ((X & Y) v ( ~( X) &  ~( Y))),FreeV,NNF,Paths).
   
nnf1(KB,xor(X , Y),FreeV,NNF,Paths):-
   !,
  nnf(KB,((X v Y) & ( ~( X) v  ~( Y))),FreeV,NNF,Paths).
   
nnf1(KB,(C => (A & B)),FreeV,NNFO,PathsO):- is_using_feature(two_implications),!,
      nnf(KB,A,FreeV,NNF1,Paths1),contains_no_negs(NNF1),
      nnf(KB,B,FreeV,NNF2,Paths2),contains_no_negs(NNF2),        
        to_poss(KB,NNF1,NNF1WFFChk),to_poss(KB,NNF2,NNF2WFFChk),
        FullNNF2 = ((NNF1WFFChk => (C => NNF2))),
        FullNNF1 = ((NNF2WFFChk => (C => NNF1))),
	PathsO is Paths1 * Paths2,
	(Paths1 > Paths2 -> NNF = (FullNNF2 & FullNNF1);
		            NNF = (FullNNF1 & FullNNF2)),
       did_use_hack(two_implications),
       nnf(KB,NNF,FreeV,NNFO,PathsO).

% not disabled
nnf1(KB,(A & B),FreeV,NNF,Paths):- fail, nb_current('$nnf_outer',[_,Was|_]), \+ has_modals(Was),!,
  % is_using_feature(co_mingling),!,
  to_poss(KB,A,PA),to_poss(KB,B,PB),
   NEWFORM = ((PB => A) & (PA => B)) ,
   nnf(KB,NEWFORM,FreeV,NNF,Paths).

nnf1(KB,(A & B),FreeV,NNF,Paths):- !,
      nnf(KB,A,FreeV,NNF1,Paths1),
      nnf(KB,B,FreeV,NNF2,Paths2),
	Paths is Paths1 * Paths2,
	(Paths1 > Paths2 -> NNF = (NNF2 & NNF1);
		            NNF = (NNF1 & NNF2)).

nnf1(KB,<=>(A,B),FreeV,NNFO,Paths):- !,
      nnf(KB,A=>B,FreeV,NNF1,Paths1),
      nnf(KB,B=>A,FreeV,NNF2,Paths2),
	Paths is Paths1 * Paths2,
	(Paths1 > Paths2 -> NNF = (NNF2 & NNF1);
		            NNF = (NNF1 & NNF2)),
       nnf(KB,NNF,FreeV,NNFO,Paths).

nnf1(KB,(A v B),FreeV,NNF,Paths):-
        nnf(KB,A,FreeV,NNF1,Paths1),
	nnf(KB,B,FreeV,NNF2,Paths2),
	Paths is Paths1 + Paths2,
	(Paths1 > Paths2 -> NNF = (NNF2 v NNF1);
		            NNF = (NNF1 v NNF2)).


nnf1(KB, ~( Fml),FreeV,NNF,Paths):- nonvar(Fml), Fml = ~( A) ,!, nnf(KB,A,FreeV,NNF,Paths).
nnf1(KB, ~( Fml),FreeV,NNF,Paths):- nonvar(Fml),   

        (Fml = ( ~( A)) -> must(double_neg(KB,A,Fml1));
         Fml = (nesc(BDT,F)) -> Fml1 = poss(BDT, ~( F));
	 Fml = (poss(BDT,F)) -> Fml1 = nesc(BDT, ~( F));

	 Fml = (cir(CT,F)) -> Fml1 = cir(CT, ~( F));
	 Fml = (until(CT,A,B)) -> 
            (nnf(KB, ~( A),FreeV,NNA,_), nnf(KB, ~( B),FreeV,NNB,_),Fml1 = v(always(CT,NNB), until(CT,NNB,&(NNA,NNB))));
             
         Fml = (exists(X,F)) -> Fml1 = all(X, ~( F));

	 Fml = (atleast(N,X,F)) -> Fml1 = atmost(N,X,F);
	 Fml = (atmost(N,X,F)) -> Fml1 = atleast(N,X,F);

	 Fml = ((A v B)) -> Fml1 = ( ~( A) &  ~( B) );
	 Fml = ((A & B)) -> Fml1 = ( ~( A) v  ~( B) );
	 Fml = ('=>'(A,B)) -> Fml1 = ( A  & ~( B) );
	 Fml = ('<=>'(A,B)) -> Fml1 = v(&(A,  ~( B)) , &( ~( A), B) )
	),!,
        must((share_scopes(KB,BDT),share_scopes(KB,CT))),!,
	nnf(KB,Fml1,FreeV,NNF,Paths).

nnf1(KB,Fml,FreeV,NNF,Paths):-  
	(Fml = '=>'(A,B) -> Fml1 = v( ~( A), B );         
	 Fml = '<=>'(A,B) -> Fml1 = v(&(A, B), &( ~( A),  ~( B)) );
         Fml = '<=>'(A,B) -> Fml1 = v('=>'(A, B), '=>'(B, A) )
	),!, nnf(KB,Fml1,FreeV,NNF,Paths).


/*

% =================================
% Higher Order
% =================================

nnf1(KB,Fml,FreeV,Out,Path):- Fml=..[F,A],third_order(F),  
  nnf(KB,A,FreeV,NNF1,Path1),!,
  Fml2=..[F,KB,NNF1],nnf(KB,Fml2,FreeV,Out,Path2),Path is Path1+Path2.
*/

/*

nnf1(KB,[F|ARGS],FreeV,[F2|ARGS2],N):- !,
   nnf(KB,F,FreeV,F2,N1),
   nnf(KB,ARGS,FreeV,ARGS2,N2),
   N is N1 + N2 - 1.

nnf1(KB,Fml,FreeV,Out,Paths):- 
   Fml=..[F|FmlA], 
   arg(_,v((v),(&),(=>),(<=>)),F),!,
   nnf_l(KB,FmlA,FreeV,NNF,Paths),
   Out =..[F|NNF],!.

*/

% =================================
% Forth Order Logic
% =================================
nnf1(KB,Fml,FreeV,FmlO,Paths):- no_poss(Fml),
  breakup_nnf(KB,Fml,FmlM),
  Fml\=@=FmlM,
  nnf(KB,FmlM,FreeV,FmlO,Paths).


% nnf(KB,Fml,_,Fml,1):- Fml=..[F,KB,_],third_order(F),!.


% =================================
% Logical Atoms
% =================================

nnf1(_KB,mudEquals(A,B),FreeV,mudEquals(A,B),1):- is_ftVar(A), !,no_freev(FreeV).

nnf1(KB, ~( Fml),FreeV,NNF,Paths):- nonvar(Fml), Fml = all(X,F), nnf(KB,exists(X, ~( F)),FreeV,NNF,Paths).

nnf1(KB,Fml,FreeV,FmlO,N):- 
  compound(Fml),
  \+ is_precond_like(Fml),
  arg(_,Fml,Function),
  compound(Function),
  notrace(is_function_expr('=>',Function)),
  % notrace(\+ has_function(Function)),
  function_to_predicate(Function,NewVar,PredifiedFunction),!,
  subst(Fml,Function,NewVar,FmlMid),!,
  nnf(KB,all(NewVar,(PredifiedFunction => FmlMid)),FreeV,FmlO,N).

nnf1(_KB,PreCond,FreeV,PreCond,1):- is_precond_like(PreCond), !,no_freev(FreeV).


% nnf(KB, IN,FreeV,OUT,Paths):- simplify_cheap(IN,MID),IN\=@=MID,nnf(KB, MID,FreeV,OUT,Paths).
% nnf(_KB , IN,[],OUT,1):- mnf(IN,OUT),IN\=OUT,!.

nnf1(KB,Fml,FreeV,FmlO,N):- must((nonegate(KB,Fml,FmlM),nnf_lit(KB,FmlM,FreeV,FmlO,N))).

nnf1(_KB,Fml,_,Fml,1):-!.


nnf_l(KB,[FmlA],FreeVA,[NNFA],PathsA):-!,
 nnf(KB,FmlA,FreeVA,NNFA,PathsA),!.
nnf_l(KB,[FmlA|FmlS],FreeV,[NNFA|NNFS],Paths):-
 nnf(KB,FmlA,FreeVA,NNFA,PathsA),
 nnf_l(KB,FmlS,FreeVS,NNFS,PathsS),
 append(FreeVS,FreeVA,FreeV),
 Paths is PathsA + PathsS.
nnf_l(_KB,[],[],[],0).


no_poss(Fml):- sub_term(Term,Fml),compound(Term),functor(Term,poss,_),!,fail.
no_poss(_Fml).

no_freev(FreeV):- ignore(FreeV=[]).
add_to_vars(X,FreeV,NewVars):- is_list(FreeV),!,list_to_set([X|FreeV],NewVars).
add_to_vars(X,FreeV,NewVars):- [X|FreeV]=NewVars.

nnf_lit(KB,all(X,Fml),FreeV,all(X,FmlO),N):- nonvar(Fml),!,nnf_lit(KB,Fml,FreeV,FmlO,N).
nnf_lit(KB, ~( Fml),FreeV, ~( FmlO),N):- nonvar(Fml),!,nnf_lit(KB,Fml,FreeV,FmlO,N).

nnf_lit(_KB,Fml,FreeV,Fml,1):- functor(Fml,_,N),N>2,!,no_freev(FreeV).
nnf_lit(KB,Fml,FreeV,FmlO,N3):- 
   Fml=..[F|ARGS],
   nnf_args(Fml,F,1,KB,ARGS,FreeV,FARGS,N1),
   Fml2=..[F|FARGS],
   (Fml2 \=@= Fml -> 
     ((nnf(KB,Fml2,FreeV,FmlO,N2),N3 is (N1 + N2 -1 )));
      must((FmlO=Fml2, N3 is N1))).
nnf_args(_Sent,_F,_N,_KB,[],_FreeV,[],0):- !.

nnf_args(Sent,F,N,KB,[A|RGS],FreeV,[FA|ARGS],N3):-  
 nop(closure_push(FA,admittedArgument(FA,N,F))),
 % push_dom(A,argIsaFn(F,N)),
 must((nnf_arg(KB,A,FreeV,FA,N1),sanity(number(N1)))),!,
 % push_dom(FA,argIsaFn(F,N)),
 % annote(lit,FA,Sent),
  NPlus1 is N + 1,
  nnf_args(Sent,F,NPlus1,KB,RGS,FreeV,ARGS,N2),!,
  must(N3 is (N1 + N2 -1)).


nnf_arg(_KB,A,FreeV,A,1):- notrace(is_arg_leave_alone(A)),!,no_freev(FreeV).
nnf_arg(KB,A,FreeV,FA,N1):-  nnf(KB,A,FreeV,FA,N1).

is_arg_leave_alone(A):- ground(A).
is_arg_leave_alone(A):- is_lit_atom(A).

%% is_lit_atom( ?IN) is det.
%
% If Is A Literal Atom.
%
is_lit_atom(IN):- leave_as_is_logically(IN),!.
is_lit_atom(IN):- \+ is_sent_with_f(IN).

is_sent_with_f(In):- is_a_sent_funct(F),subst(In,F,*,O),O \== In,!.

is_a_sent_funct((&)).
is_a_sent_funct((v)).
is_a_sent_funct((all)).
is_a_sent_funct((exists)).
is_a_sent_funct((=>)).
is_a_sent_funct((<=>)).
is_a_sent_funct((~)).

is_sent_like(XY):- \+ compound(XY),!,fail.
is_sent_like(_ & _).
is_sent_like(_ v _).
is_sent_like(_ => _).
is_sent_like(_ <=> _).
is_sent_like(all(_ , _)).
is_sent_like(exists(_ , _)).
% is_sent_like(~ _ ).
is_sent_like(~ XY ):- is_sent_like(XY).

must_distribute_maybe(KB,PAB,Was,OUT):-
  subst(PAB,Was,NewArg,NewPab),
  functor(PAB,F,_),
  must((arg(N,PAB,Arg),Arg==Was)),
  copy_term(NewPab:NewArg,CNewPab:CWas),
  CWas='$$val$$',
  must(distribute_on(F-N,KB,
      subst(CNewPab,CWas),Was,OUT)).

:- meta_predicate distribute_on(*,*,2,?,?).

distribute_on(_What,_KB,RE,XY,SAME):- \+ is_sent_like(XY),!, reconstuct(RE,XY,SAME).
distribute_on(_What,KB,RE,XY,SAME):- compound(KB),functor(XY,F,_), cant_distrubute_on(F,KB),!,reconstuct(RE,XY,SAME).
distribute_on(What,_KB,RE,XY,SAME):- functor(XY,F,_), cant_distrubute_on(F,What),!, reconstuct(RE,XY,SAME).
distribute_on(What,KB,RE,((X v Y)),(RECON1 v RECON2)) :- !, distribute_on(What,KB,RE,X,RECON1), distribute_on(What,KB,RE,Y,RECON2).
distribute_on(What,KB,RE,((X & Y)),(RECON1 & RECON2)) :- !, distribute_on(What,KB,RE,X,RECON1), distribute_on(What,KB,RE,Y,RECON2).
distribute_on(What,KB,RE,((X => Y)),(RECON1 => RECON2)) :- ! , distribute_on(What,KB,RE,X,RECON1), distribute_on(What,KB,RE,Y,RECON2).
distribute_on(What,KB,RE,((X <=> Y)),(RECON1 <=> RECON2)) :- ! , distribute_on(What,KB,RE,X,RECON1), distribute_on(What,KB,RE,Y,RECON2).
distribute_on(What,KB,RE,(all(V, X)),all(V , RECON1)) :- ! , distribute_on(What,KB,RE,X,RECON1).
distribute_on(What,KB,RE,(exists(V, X)),exists(V , RECON1)) :- ! , distribute_on(What,KB,RE,X,RECON1).
distribute_on(What,KB,RE, ~ X , RECON1) :- breakup_nnf(KB,~X,Xp), ( ~X ) \== Xp, ! , distribute_on(What,KB,RE,Xp,RECON1).
distribute_on(What,KB,RE, X , RECON1) :- breakup_nnf(KB, X,Xp), ( X ) \== Xp, ! , distribute_on(What,KB,RE,Xp,RECON1).
distribute_on(_What,_KB,RE,XY,SAME):- reconstuct(RE,XY,SAME),!.

:- meta_predicate reconstuct(2,?,?).

reconstuct(RE,Arg,OUT):- must(call(RE,Arg,OUT)).

can_distrubute_on(Sent,F-N):- !, can_distrubute_on(Sent,F,N).
can_distrubute_on(Sent,FN):-  can_distrubute_on(Sent,FN,0).

cant_distrubute_on(Sent,F-N):- !, cant_distrubute_on(Sent,F,N).
cant_distrubute_on(Sent,FN):- cant_distrubute_on(Sent,FN,0).


can_distrubute_on(Sent,F,N):- \+ cant_distrubute_on(Sent,F,N),!,fail.
can_distrubute_on(_Sent,_F,_A).

% % cant_distrubute_on(exists,F,A):- cant_distrubute_on(&,F,A).
% % cant_distrubute_on(all,F,A):- cant_distrubute_on(v,F,A).

cant_distrubute_on(v,release,3).
cant_distrubute_on(&,release,2).

cant_distrubute_on(v,until,2).
cant_distrubute_on(&,until,3).

% <Thanatological> Yeah ... it doesn''t appear that knowledge is distributive over disjuction.
cant_distrubute_on(v,knows,2).
cant_distrubute_on(&,beliefs,2).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% breakup_nnf(KB,+F1,?F2)
% uses LTL equivalencies to split up LTL formulae
% for example, always((f & g)) is converted
% into (always(f) & always(g))
% These transformations are useful to prevent
% blowup in the size of the automata
%
% ?- breakup_nnf(KB,sometimes((f & g)),X).
% X = (sometimes(f) & sometimes(g)).



%breakup_nnf(KB,eventually(F),X) :- !, breakup_nnf(KB,until(CT,true,F),X).
%breakup_nnf(KB,~(eventually(F)),X) :- !, breakup_nnf(KB,~(until(CT,true,F)),X).

breakup_nnf(_,Y,Y):- \+ compound(Y),!.
breakup_nnf(_,Y,Y):- is_ftVar(Y),!.
breakup_nnf(KB,cir(CT,(X & Y)),(cir(CT,Xp) & cir(CT,Yp))) :- ! , breakup_nnf(KB,X,Xp), breakup_nnf(KB,Y,Yp).
breakup_nnf(KB,cir(CT,X),cir(CT,Xp)) :- !,  breakup_nnf(KB,X,Xp).

breakup_nnf(KB,until(CT,(X & Y),Z),(U & V)) :- !, breakup_nnf(KB,until(CT,X,Z),U), breakup_nnf(KB,until(CT,Y,Z),V).
breakup_nnf(KB,until(CT,X,(Y v Z)),(U v V)) :- !, breakup_nnf(KB,until(CT,X,Y),U), breakup_nnf(KB,until(CT,X,Z),V).
breakup_nnf(KB,until(CT,X,Y),until(CT,Xp,Yp)) :- !, breakup_nnf(KB,X,Xp), breakup_nnf(KB,Y,Yp).                                        

breakup_nnf(KB,release(CT,(X v Y),Z),(U v V)) :- !, breakup_nnf(KB,release(CT,X,Z),U), breakup_nnf(KB,release(CT,Y,Z),V).
breakup_nnf(KB,release(CT,X,(Y & Z)),(U & V)) :- !, breakup_nnf(KB,release(CT,X,Y),U), breakup_nnf(KB,release(CT,X,Z),V).
breakup_nnf(KB,release(CT,X,Y),release(CT,Xp,Yp)) :- !, breakup_nnf(KB,X,Xp), breakup_nnf(KB,Y,Yp).


/*
breakup_nnf(KB,knows(Agt,(X v Y)), ~beliefs(Agt,(~X & ~Y))) :- !,
	breakup_nnf(KB,X,Xp),
	breakup_nnf(KB,Y,Yp).

breakup_nnf(KB,knows(AG,(~X v ~Y)), ~ beliefs(AG,(U & V))) :- !, 
   breakup_nnf(KB,X,U), breakup_nnf(KB,Y,V).

*/

breakup_nnf(KB,beliefs(Agt,(X & Y)),(beliefs(Agt,Xp) & beliefs(Agt,Yp))) :- ! ,  breakup_nnf(KB,X,Xp), breakup_nnf(KB,Y,Yp).
% wrong .. breakup_nnf(KB,knows(Agt,(X v Y)),(beliefs(Agt,Xp) v beliefs(Agt,Yp))) :- ! ,  breakup_nnf(KB,X,Xp),breakup_nnf(KB,Y,Yp).

breakup_nnf(KB,(X & Y),(Xp & Yp)) :- breakup_nnf(KB,X,Xp), breakup_nnf(KB,Y,Yp).
breakup_nnf(KB,(X v Y),(Xp v Yp)) :- breakup_nnf(KB,X,Xp), breakup_nnf(KB,Y,Yp).
breakup_nnf(KB,~(X),~(Xp)) :- breakup_nnf(KB,X,Xp).
breakup_nnf(KB,(X => Y),(Xp => Yp)) :- breakup_nnf(KB,X,Xp), breakup_nnf(KB,Y,Yp).
breakup_nnf(KB,(X <=> Y),(Xp <=> Yp)) :- breakup_nnf(KB,X,Xp), breakup_nnf(KB,Y,Yp).

breakup_nnf(KB,PAB,OUT):- \+ is_sent_like(PAB), arg(_,PAB,XY),is_sent_like(XY),!,must(must_distribute_maybe(KB,PAB,XY,OUT)).
breakup_nnf(KB,knows(E,P),knows(E,Q)) :- nnf(KB,P,[],Q,_), !.

breakup_nnf(_KB,X,X).



/*
mnf(Var,Var):-leave_as_is_logically(Var),!.
mnf(Fml,Out):-boxRule(_,Fml,M),Fml\=M,mnf(M,Out).
mnf(Fml,Out):-diaRule(_,Fml,M),Fml\=M,mnf(M,Out).
mnf(poss(DBT,A=>B),Out):- diaRule(_,poss(DBT,v( ~(-,B),A)),M),mnf(M,Out).
mnf(nesc(DBT,A=>B),Out):- mnf(v( ~(-,nesc(DBT, B)), nesc(DBT,A)),M),mnf(M,Out).
mnf([F|Fml],Out):- arg(_,v((v),(&),(=>),(<=>)),F),mnf(Fml,NNF),Out =..[F| NNF].
mnf(Var,Var):-!.
*/

% poss(P=>Q) ==>  poss( - Q v P )  ==>  - nesc( - ( - Q v P ) ) ==>  - nesc( Q & -P  )    .. how can i get the  nesc/poss very close to the P and Q ?

% poss(P=>Q)  ==>   ( -nesc(-P) =>  -nesc(-Q) )   ?

% poss(P=>Q)  ===>   poss( - Q v P ) ===>   poss(- Q) v poss(P)  ===>   - nesc(Q) v poss(P)   ===>      poss(P)=>nesc(Q)  

% poss(DBT,v( ~(-,B),A)) => -nesc(q & -p)


%= 	 	 

%% third_order( ?VALUE1) is det.
%
% Third Order.
%
third_order(asserted_t).


% boxRule(KB,A,B):- convertAndCall(as_dlog,boxRule(KB,A,B)).

%= 	 	 

%% boxRule( ?KB, ?BOX, ?BOX) is det.
%
% Datalog Rule.
%
boxRule(_KB,BOX, BOX):-leave_as_is_logically(BOX),!.
boxRule(KB,nesc(BDT,(A & B)), (BA & BB)):- nonvar(A),!, boxRule(KB,nesc(BDT,A),BA), boxRule(KB,nesc(BDT,B),BB).
% boxRule(KB,nesc(BDT, IN), BOX):- \+ is_lit_atom(IN), share_scopes(KB,BDT), nnf(KB, ~( nesc(BDT,  ~( IN))),BOX).
boxRule(_KB,BOX, BOX).
 

leave_as_is_logically(Box):- \+ compound(Box),!.
leave_as_is_logically('$VAR'(_)):-!.
leave_as_is_logically([]):-!.
leave_as_is_logically(NART):-functor(NART,nartR,_),!,ground(NART).
% leave_as_is_logically(~LIST):-!,leave_as_is_logically(LIST).
leave_as_is_logically(LIST):- is_list(LIST),!, maplist(leave_as_is_logically,LIST).

% leave_as_is_logically(~Box):- leave_as_is_logically(Box).

%= 	 	 

%% diaRule( ?KB, ?A, ?B) is det.
%
% Dia Rule.
%
diaRule(KB,A,B):- convertAndCall(as_dlog,diaRule(KB,A,B)).
diaRule(_KB,BOX, BOX):-leave_as_is_logically(BOX),!.
diaRule(KB,poss(BDT,(A v B)), v(DA,DB)):- !, diaRule(KB,poss(BDT,A),DA), diaRule(KB,poss(BDT,B),DB).
% dmiles thinks this is ok
% diaRule(KB,poss(BDT,(A & B)), &(DA,DB)):- !, diaRule(KB,poss(BDT,A),DA), diaRule(KB,poss(BDT,B),DB).
diaRule(_KB,DIA, DIA).


%= 	 	 

%% cirRule( ?KB, ?A, ?B) is det.
%
% Cir Rule.
%
cirRule(KB,A,B):- convertAndCall(as_dlog,cirRule(KB,A,B)).
cirRule(_KB,BOX, BOX):-leave_as_is_logically(BOX),!.
cirRule(KB,cir(CT,(A v B)), v(DA,DB)):- !, cirRule(KB,cir(CT,A),DA), cirRule(KB,cir(CT,B),DB).
cirRule(KB,cir(CT,(A & B)), &(DA,DB)):- !, cirRule(KB,cir(CT,A),DA), cirRule(KB,cir(CT,B),DB).
cirRule(_KB,CIR, CIR).



%= 	 	 

%% corrected_modal_recurse( ?VALUE1, ?Var, ?OUT) is det.
%
% Corrected Modal Recurse.
%
corrected_modal_recurse(_,Var,OUT):-leave_as_is_logically(Var),!,OUT=Var.
corrected_modal_recurse(KB, IN, OUT):- corrected_modal(KB,IN,OUTM),!,OUT=OUTM.
corrected_modal_recurse(KB, IN, OUTM):- corrected_modal_recurse0(KB, IN, M),!,
  (IN=@=M->OUT=M;corrected_modal_recurse(KB, M, OUT)),!,OUT=OUTM.


%= 	 	 

%% corrected_modal_recurse0( ?VALUE1, ?Var, ?OUT) is det.
%
% Corrected Modal Recurse Primary Helper.
%
corrected_modal_recurse0(_,Var,OUT):-leave_as_is_logically(Var),!,OUT=Var.
corrected_modal_recurse0(KB, IN,FOO):-  is_list(IN),!, must_maplist(corrected_modal_recurse(KB), IN,FOO ),!.
corrected_modal_recurse0(KB, H,FOO):-  compound(H),!,H=..[F|ARGS], must_maplist(corrected_modal_recurse(KB), ARGS,FOOL ),!,FOO=..[F|FOOL].
corrected_modal_recurse0(_, INOUT,  INOUT):- !.




%= 	 	 

%% corrected_modal( ?KB, ?IN, ?OUTM) is det.
%
% Corrected Modal.
%
corrected_modal(KB,IN,OUTM):-
  corrected_modal0(KB,IN,M),!,must(corrected_modal_recurse0(KB,M,OUT)),!,OUT=OUTM.



%= 	 	 

%% corrected_modal0( ?VALUE1, ?Var, :TermARG3) is det.
%
% Corrected Modal Primary Helper.
%
corrected_modal0(_,Var,_):-leave_as_is_logically(Var),!,fail.
corrected_modal0(_,nesc(BDT,F),nesc(BDT,F)):-!.
corrected_modal0(_,poss(BDT,F),poss(BDT,F)):-!.
corrected_modal0(_,until(CT,A,B),until(CT,A,B)):-!.
corrected_modal0(_,cir(CT,F),cir(CT,F)):-!.
corrected_modal0(KB,BF,nesc(b_d(KB,B,D),F)):- BF=..[B,F],b_d_p(B,D).
corrected_modal0(KB,BF,poss(b_d(KB,B,D),F)):- BF=..[D,F],b_d_p(B,D).
corrected_modal0(KB,CF,cir(ct(KB,CT),F)):- CF=..[CT,F],ct_op(CT).
corrected_modal0(KB,CF,until(ct(KB,CT),A,B)):- CF=..[CT,A,B],until_op(CT).
corrected_modal0(_,BF,nesc(b_d(KB,B,D),F)):- BF=..[B,KB,F],b_d_p(B,D).
corrected_modal0(_,BF,poss(b_d(KB,B,D),F)):- BF=..[D,KB,F],b_d_p(B,D).
corrected_modal0(_,CF,cir(ct(KB,CT),F)):- CF=..[CT,KB,F],ct_op(CT).
corrected_modal0(KB,CF,until(ct(KB,CT),A,B)):- CF=..[CT,KB,A,B],until_op(CT).


%= 	 	 

%% share_scopes( ?KB, ?BDT) is det.
%
% Share Scopes.
%
share_scopes(KB,BDT):-compound(BDT),ignore(arg(1,BDT,KB)),!.
share_scopes(KB,ENV):-ignore(KB=ENV),!.

/*
share_scopes(KB,Neg,CT,BDT):- ignore(Neg=ct(KB,SymNeg)),ignore(BDT=bt(KB,SymNesc,SymPoss)),ignore(CT=ct(KB,SymAllways)),
  ignore(KB=KB),ignore(KB=ct(KB,SymAllways)),ignore(KB=ct(KB,SymUntil)),
  ignore(SymNeg=(-)),
  ignore(SymUntil=(until)),
  ignore(SymNesc=(nesc)),
  ignore(SymPoss=(poss)),
  ignore(SymAllways=(allways)).
*/

%= 	 	 

%% until_op( ?VALUE1) is det.
%
% Until Oper..
%
until_op(until).


%= 	 	 

%% ct_op( ?VALUE1) is det.
%
% Ct Oper..
%
ct_op(cir).
ct_op(nextly).


%ct_op(ist).
%ct_op(asserted_t).


%= 	 	 

%% neg_op( ?VALUE1) is det.
%
% Negated Oper..
%
neg_op(not).
neg_op(~).
neg_op(~).
neg_op(-).
neg_op('\\+').


%= 	 	 

%% b_d_p( ?VALUE1, ?VALUE2) is det.
%
% Backtackable (debug) Pred.
%
b_d_p(nesc,poss).
b_d_p(box,dia).
%b_d_p(knows,beliefs).
b_d_p(always,eventually).
b_d_p_1(sometimes,always).

% b_d(KB,A,I):- genlPreds(I,A).

%=%
%=%  Conjunctive Normal Form (CNF) : assumes Fml in NNF
%=%
% Usage: cnf(KB, +NNF, ?CNF )

%= 	 	 

%% cnf( ?KB, ?A, ?B) is det.
%
% Confunctive Normal Form.
%
cnf(KB,A,B):- convertAndCall(as_dlog,cnf(KB,A,B)).
cnf(_KB,AS_IS,       AS_IS):-leave_as_is_logically(AS_IS),!.
cnf(KB,&(P,Q), &(P1,Q1)):- !, cnf(KB,P, P1), cnf(KB,Q, Q1).
cnf(KB,v(P,Q),     CNF):- !, cnf(KB,P, P1), cnf(KB,Q, Q1), cnf1(KB, v(P1,Q1), CNF ).
cnf(_KB,CNF,       CNF).


%= 	 	 

%% cnf1( ?KB, ?AS_IS, ?AS_IS) is det.
%
% Confunctive Normal Form Secondary Helper.
%
cnf1(_KB,AS_IS,       AS_IS):-leave_as_is_logically(AS_IS),!.
cnf1(KB, v(LEFT, R), &(P1,Q1) ):- nonvar_unify(LEFT , &(P,Q)), !, cnf1(KB, v(P,R), P1), cnf1(KB, v(Q,R), Q1).
cnf1(KB, v(P, RIGHT), &(P1,Q1) ):- nonvar_unify(RIGHT , &(Q,R)), !, cnf1(KB, v(P,Q), P1), cnf1(KB, v(P,R), Q1).
cnf1(_KB, CNF,                 CNF).


%= 	 	 

%% nonvar_unify( ?NONVAR, ?UNIFY) is det.
%
% Nonvar Unify.
%
nonvar_unify(NONVAR,UNIFY):- \+ leave_as_is_logically(NONVAR),  NONVAR=UNIFY.

%=%
%=% Disjunctive Normal Form (DNF) : assumes Fml in NNF
%=%
% Usage: dnf(KB, +NNF, ?DNF )

%= 	 	 

%% dnf( ?KB, ?A, ?B) is det.
%
% Disjunctive Normal Form.
%
dnf(KB,A,B):- convertAndCall(as_dlog,dnf(KB,A,B)).
dnf(_KB,AS_IS,       AS_IS):-leave_as_is_logically(AS_IS),!.
dnf(KB, v(P,Q),  v(P1,Q1) ):- !, dnf(KB,P, P1), dnf(KB,Q, Q1).
dnf(KB, &(P,Q), DNF):- !, dnf(KB,P, P1), dnf(KB,Q, Q1), dnf1(KB,&(P1,Q1), DNF).
dnf(_KB,DNF,       DNF).


%= 	 	 

%% dnf1( ?KB, ?DNF, ?DNF) is det.
%
% Disjunctive Normal Form Secondary Helper.
%
dnf1(KB,&(P, v(Q,R)),  v(P1,Q1) ):- !, dnf1(KB,&(P,Q), P1), dnf1(KB,&(P,R), Q1).
dnf1(KB,&(v(P,Q), R), v(P1,Q1) ):- !, dnf1(KB,&(P,R), P1), dnf1(KB,&(Q,R), Q1).
dnf1(_KB,DNF,                  DNF ).



%= 	 	 

%% simplify_cheap( :TermIN, ?IN) is det.
%
% Simplify Cheap.
%
simplify_cheap(IN,OUT):-nonvar(OUT),!,simplify_cheap(IN,M),!,OUT=M.
simplify_cheap(IN,IN):- leave_as_is_logically(IN),!.
% simplify_cheap(nesc(BDT,OUT),OUT):- !,nonvar(OUT),is_modal(OUT,BDT),!.
% simplify_cheap(poss(BDT, poss(BDT, F)),  poss(BDT, F)):-nonvar(F),!.

simplify_cheap( ~( poss(BDT,  ~(  F))), OUT):-nonvar(F),!, simplify_cheap_must(nesc(BDT,F),OUT).
simplify_cheap( ~( nesc(BDT,  ~(  F))), OUT):-nonvar(F),!, simplify_cheap_must(poss(BDT,F),OUT).
simplify_cheap( ~( poss(BDT,  (  F))), OUT):-nonvar(F),!, simplify_cheap_must(nesc(BDT,~F),OUT).
simplify_cheap( ~( nesc(BDT,  (  F))), OUT):-nonvar(F),!, simplify_cheap_must(poss(BDT,~F),OUT).
simplify_cheap(poss(BDT,nesc(BDT,IN)),OUT):- simplify_cheap_must(poss(BDT,IN),OUT).
simplify_cheap(poss(BDT,poss(BDT,IN)),OUT):- simplify_cheap_must(poss(BDT,IN),OUT).
simplify_cheap(nesc(BDT,poss(BDT,IN)),OUT):- simplify_cheap_must(poss(BDT,IN),OUT).
simplify_cheap(nesc(BDT,nesc(BDT,IN)),OUT):- simplify_cheap_must(nesc(BDT,IN),OUT).
%simplify_cheap( ~(  ~( IN)),OUT):- simplify_cheap_must(IN,OUT).
%simplify_cheap( ~(  poss(BDT, poss(BDT, F))),  ~( F)):-nonvar(F),!.
%simplify_cheap(poss(BDT, poss(BDT, F)),  poss(BDT, F)):-nonvar(F),!.
%simplify_cheap( ~( poss(_,  ~(  F))), F):-nonvar(F),!.
%simplify_cheap(IN,-OUT):- IN =  ~( poss(BDT,OUT)), is_modal(OUT,BDT),!.
%simplify_cheap(IN,-OUT):- IN =  ~( nesc(BDT,OUT)), \+is_modal(OUT,BDT),!.
simplify_cheap(INOUT,INOUT).
 
%= 	 	 

%% simplify_cheap_must( ?IN, ?IN) is det.
%
% Simplify Cheap Must Be Successfull.
%
simplify_cheap_must(IN,IN):- leave_as_is_logically(IN),!.
simplify_cheap_must(IN,OUT):- simplify_cheap(IN,OUT),!.
simplify_cheap_must(IN,IN).


%=
%=  Prenex Normal Form (PNF)
%=

% Usage: pnf(+KB, +Fml, ?PNF ) : assumes Fml in NNF



%= 	 	 

%% pnf( ?KB, ?F, ?PNF) is det.
%
% Pnf.
%
pnf(KB, F,PNF):- pnf(KB,F,[],PNF),!.

% pnf(+KB, +Fml, +Vars, ?PNF)


%= 	 	 

%% pnf( ?A, ?B, ?C, ?D) is det.
%
% Pnf.
%
pnf(A,B,C,D):- convertAndCall(as_dlog,pnf(A,B,C,D)),!.

pnf(_,Var,_ ,Var):- leave_as_is_logically(Var),!.

pnf(_, [],  _,           []):- !.

pnf(KB, IN,  _,              OUT):- is_list(IN),!, must_maplist(pnf(KB),IN,OUT).

%pnf(KB, IN, FreeV,              OUT):- once(mnf(IN,MID)),IN\=@=MID, pnf(KB,MID,FreeV,OUT).
%pnf(KB, IN, FreeV,              OUT):- simplify_cheap(IN,MID), pnf(KB,MID,FreeV,OUT).

pnf(KB,   all(X,F),Vs,   all(X,PNF)):- list_to_set([X|Vs],VVs), !, pnf(KB,F, VVs, PNF),!.

pnf(KB,   nesc(X,F),Vs,   nesc(X,PNF)):- !, pnf(KB,F,Vs, PNF),!.

pnf(KB,   poss(X,F),Vs,   poss(X,PNF)):- !, pnf(KB,F,Vs, PNF),!.

pnf(KB,  exists(X,F),Vs,exists(X,PNF)):- list_to_set([X|Vs],VVs), !, pnf(KB,F, VVs, PNF),!.

pnf(KB,  (&(exists(X,A) , B)),Vs,  exists(Y,PNF)):- !, copy_term((X,A,Vs),(Y,Ay,Vs)), pnf(KB,&(Ay,B),[Y|Vs], PNF),!.

pnf(KB,   ( v(exists(X,A)), B),Vs,  exists(Y,PNF)):- !, copy_term((X+A+Vs),(Y+Ay+Vs)), pnf(KB,(v(Ay,B)),[Y|Vs], PNF).!.

pnf(KB, &(all(X,A), B),Vs, all(Y,PNF)):- !, copy_term((X,A,Vs),(Y,Ay,Vs)), pnf(KB,&(Ay , B),[Y|Vs], PNF),!.

pnf(KB, v(all(X,A), B),Vs, all(Y,PNF)):- !, copy_term((X,A,Vs),(Y,Ay,Vs)), pnf(KB,v(Ay,B),[Y|Vs], PNF),!.

pnf(KB, &(A,exists(X,B)),Vs,  exists(Y,PNF)):- !, copy_term((X,B,Vs),(Y,By,Vs)),
                                        pnf(KB,&(A, By),[Y|Vs], PNF),!.
pnf(KB, v(A,exists(X,B)),Vs,  exists(Y,PNF)):- !, copy_term((X,B,Vs),(Y,By,Vs)),
                                        pnf(KB,v(A,By),[Y|Vs], PNF),!.
pnf(KB, &(A,all(X,B)),Vs, all(Y,PNF)):- !, copy_term((X,B,Vs),(Y,By,Vs)),
                                        pnf(KB,&(A,By),[Y|Vs], PNF),!.
pnf(KB, v(A,all(X,B)),Vs, all(Y,PNF)):- !, copy_term((X,B,Vs),(Y,By,Vs)),
                                        pnf(KB,v(A,By),[Y|Vs], PNF),!.

pnf(KB, &(A, B),Vs,       PNF ):- pnf(KB,A,Vs,Ap), pnf(KB,B,Vs,Bp), 
                                     (A\=Ap; B\=Bp), pnf(KB,&(Ap,Bp),Vs,PNF),!.

pnf(KB, v(A, B),Vs,       PNF ):- pnf(KB,A,Vs,Ap), pnf(KB,B,Vs,Bp), 
                                     (A\=Ap; B\=Bp), pnf(KB,v(Ap,Bp),Vs,PNF),!.


pnf(KB, [A|B], Vs,       PNF ):- !, pnf(KB,A,Vs,Ap), pnf(KB,B,Vs,Bp), 
                                     (A\=Ap; B\=Bp), pnf(KB,[Ap|Bp],Vs,PNF),!.


% disabled
pnf(KB, H,Vars,FOO ):- fail,  compound(H),H=..[F|ARGS], is_sentence_functor(F), !, pnf(KB, [F|ARGS],Vars,FOOL ),FOO=..FOOL.

pnf(_KB,          PNF, _,       PNF ).

%=%  Clausal Form (CF) : assumes Fml in PNF and
%                                 each quantified variable is unique

% cf(+Why,+KB,+Fml, -Cs)
% Cs is a list of the form: [cl(Head,Body), ...]
% Head and Body are lists.

% cf(Why,KB,A,B,C):- convertAndCall(as_dlog,cf(Why,KB,A,B,C)).


%% cf( ?Why, ?KB, ?Original, ?PNF, ?CLAUSESET) is det.
%
% Convert to Clausal Form
%

cf(Why,KB,_Original,PNF, FlattenedOUT):- 
 must_det_l((
  check_kif_varnames(PNF),
  removeQ(KB,PNF,[], UnQ),
  cnf(KB,UnQ,CNF0),!,
  nnf(KB,CNF0,[],CNF,_), 
  % wdmsg(cnf:-CNF),
 call(( conjuncts_to_list(CNF,Conj), make_clause_set([infer_by(Why)],Conj,EachClause),
  sanity(is_list(EachClause)),
  must_maplist(correct_cls(KB),EachClause,SOO),
  expand_cl(KB,SOO,SOOO))),
  sort(SOOO,SET),
  cf_to_flattened_clauses(KB,Why,SET,Flattened),
  list_to_set(Flattened,FlattenedM),!,
  correct_boxlog(FlattenedM,KB,Why,FlattenedOOO),
  demodal_clauses3(KB,FlattenedOOO,FlattenedO),  
  maplist(defunctionalize,FlattenedO,FlattenedOUT),
  nop((((pfc_for_print_left(FlattenedOOO,PrintPFC),wdmsg(boxlog:-PrintPFC),
  maybe_notrace(boxlog_to_pfc(FlattenedO,PFCPreview)),
  pfc_for_print_right(PFCPreview,PrintPFCPreview),wdmsg(preview:-PrintPFCPreview))),!,
  extract_conditions(PFCPreview,Conds), dmsg(conds= (Conds=>PFCPreview)))))).

check_kif_varnames(KIF):-check_varnames(KIF),fail.
check_kif_varnames(KIF):-ground(KIF),!.
%check_kif_varnames(KIF):-show_call(term_attvars(KIF,Vs)),Vs\==[].
check_kif_varnames(_KIF):-!.
      



%= 	 	 

%% clean_repeats_d( ?PTTP, ?PTTP) is det.
%
% Clean Repeats (debug).
%
clean_repeats_d((PTT,P0),PTTP):-!, conjuncts_to_list((PTT,P0),DLIST),list_to_set(DLIST,DSET),must_maplist(clean_repeats_d,DSET,CSET),list_to_conjuncts((,),CSET,PTTP),!.
clean_repeats_d((PTT;P0),PTTP):-!, disjuncts_to_list((PTT;P0),DLIST),list_to_set(DLIST,DSET),must_maplist(clean_repeats_d,DSET,CSET),list_to_conjuncts((;),CSET,PTTP),!.
clean_repeats_d(PTTP,PTTP).



%= 	 	 

%% invert_modal(+KB, +A, -B) is det.
%
% Invert Modal.
%

invert_modal(_KB,nesc(BD,A),poss(BD,A)):-set_is_lit(A),!.
invert_modal(_KB,poss(BD,A),nesc(BD,A)):-set_is_lit(A),!.
invert_modal(KB,A,OUT):- must(adjust_kif0(KB,poss(A),OUT)).

% invert_modal(KB,A,poss(b_d(KB,nesc,poss),A)):- is_using_feature(default_nesc),set_is_lit(A),!.
% invert_modal(KB,A,A):-!.



% double_neg(_KB,In,_):- is_ftVar(In),!,fail.
double_neg(KB,I,O):- invert_modal(KB,I,O)->I\=O,!.
double_neg(_,IO,IO):-!.
% double_neg(_KB,I,O):- weaken_to_poss(I,O).
% double_neg(KB,I, \+ ~(O)):-!.


%= 	 	 

%% removeQ( ?KB, ?F, ?HH) is det.
%
% Remove Q.
%
removeQ(KB, F,  HH):- removeQ(KB, F, _, RQ0),!,RQ0=HH.

% removes quantifiers (also pushes modal operators inside the negations) 


%= 	 	 

%% removeQ_LC( ?KB, ?MID, ?FreeV, ?OUT) is det.
%
% Remove Q Lc.
%
removeQ_LC(KB, MID,FreeV,OUT):-loop_check(removeQ(KB, MID,FreeV,OUT)).


%= 	 	 

%% removeQ( ?VALUE1, :TermVar, ?VALUE3, :TermVar) is det.
%
% Remove Q.
%
removeQ(_,Var,_ ,Var):- leave_as_is_logically(Var),!.

% removeQ(KB, H, Vars, HH ):- convertAndCall(as_dlog,removeQ(KB,H, Vars, HH )).
removeQ(KB, IN,FreeV,OUT):-  once(simplify_cheap(IN,MID)), IN\=@=MID, removeQ_LC(KB, MID,FreeV,OUT),!.

removeQ(KB,  ~( NN),Vars, XF):- nonvar(NN),NN= ~( F), invert_modal(KB,F,FI),!, removeQ(KB,  FI,Vars, XF) .
removeQ(KB, all(X,F),Vars, HH):- !,  removeQ(KB,F,[X|Vars], RQ0),RQ0=HH.

/*
removeQ(KB,  ~( nesc(BDT,  ~( F))),Vars, XF):- !,removeQ_LC(KB, poss(BDT, F),Vars, XF).
removeQ(KB,  ~( poss(BDT,  ~( F))),Vars, XF):- !,removeQ_LC(KB, nesc(BDT, F),Vars, XF).

removeQ(KB,  ~( nesc(BDT, (F))),Vars, XF):- !,removeQ(KB, poss(BDT,  ~( F)),Vars, XF).
removeQ(KB,  ~( poss(BDT, (F))),Vars, XF):- !,removeQ(KB, nesc(BDT,  ~( F)),Vars, XF).
*/

% removeQ(KB, nesc(BDT,  ~( F)),Vars, XF):- !,removeQ(KB,  ~( poss(BDT, F)),Vars, XF).
% removeQ(KB, poss(BDT,  ~( F)),Vars, XF):- !,removeQ(KB,  ~( nesc(BDT, F)),Vars, XF).

removeQ(KB,  exists(X,F),Vars, HH):- is_skolem_setting(removeQ),!,wdmsg(removeQ(skolemizing(exists(X,F)))),
	mk_skolem(KB,F,X,Vars,Fsk),
	removeQ(KB,Fsk,Vars, HH).

removeQ(KB, exists(X,F),Vars, HH):-   must(removeQ(KB,F,[X|Vars], RQ0)),RQ0=HH.

removeQ(KB, ':-'(H,B), Vars, ':-'(HH,BB ) ):- !, removeQ(KB,H, Vars, HH ),removeQ(KB,B, Vars, BB).
removeQ(KB, cl(H,B), _, O ):- !,correct_cls(KB,cl(H,B),O).
removeQ(KB,     [ H|B ],Vars, [ HH|BB ] ):- !,removeQ(KB,H, Vars, HH ),removeQ(KB,B, Vars, BB).

%removeQ(KB, H, Vars, HH ):- functor(H,F,1),adjust_kif(KB,H,MM),H\=@=MM,!, removeQ(KB, MM, Vars, HH ).

%removeQ(KB, H, Vars,HH ):- functor(H,F,1),kb_nlit(KB,F),once(nnf(KB,H,MM)),H\=@=MM,  removeQ_LC(KB, MM, Vars, HH ).
removeQ(KB, H,  Vars,HH ):- H =  ~(  _), once(nnf(KB,H,MM)),H\=@=MM,  removeQ_LC(KB, MM, Vars, HH ).

removeQ(KB, H, Vars, HH ):- convertAndCall(as_dlog,removeQ(KB,H, Vars, HH )).

removeQ(KB, H,Vars,HH ):- compound(H),H=..[F|ARGS],!,removeQ(KB, ARGS,Vars,ARGSO ),HH=..[F|ARGSO].

removeQ(KB, F,Vars,OUT ):- nnf(KB,F,Vars,F0,_),(F0 =@=F -> F0=OUT; removeQ(KB, F0,Vars,OUT )),!.





%= 	 	 

%% nowrap_one( ?Wrap, ?MORE, ?OUT) is det.
%
% Nowrap One.
%
nowrap_one(_,[One],One).
nowrap_one(Wrap,MORE,OUT):- OUT=..[Wrap,MORE].


%= 	 	 

%% display_form( ?KB, ?Form) is det.
%
% Display Form.
%
display_form(KB,Form):- demodal_sents(KB,Form,OutM),local_pterm_to_sterm(OutM,Out),portray_clause(current_output,Out,[max_depth(0),portrayed(true)]).


%= 	 	 

%% demodal_sents( ?KB, ?I, ?O) is det.
%
% Demodal Sentences.
%
demodal_sents(KB,I,O):- must(to_modal1(KB,I,M)),must(modal2sent(M,O)).


%= 	 	 

%% to_modal1( ?KB, :TermIn, ?Prolog) is det.
%
% Demodal.
%

% to_modal1(KB,In,Prolog):- call_last_is_var(to_modal1(KB,In,Prolog)),!.
to_modal1(_KB,Var, Var):- quietly(var_or_atomic(Var)),!.
to_modal1(KB,[H|T],[HH|TT]):- !, to_modal1(KB,H,HH),to_modal1(KB,T,TT).

to_modal1(KB, nesc(b_d(KB2,X,_),F), HH):- atom(X),KB\==KB2,XF =..[X,KB2,F],!,to_modal1(KB2,XF, HH).
to_modal1(KB, poss(b_d(KB2,_,X),F), HH):- atom(X),KB\==KB2,XF =..[X,KB2,F],!,to_modal1(KB2,XF, HH).

to_modal1(KB, nesc(b_d(KB,X,_),F),   HH):- atom(X), XF =..[X,F], !,to_modal1(KB,XF, HH).
to_modal1(KB, poss(b_d(KB,_,X),F),   HH):- atom(X), XF =..[X,F], !,to_modal1(KB,XF, HH).

to_modal1(KB, nesc(_,F),   HH):- XF =..[nesc,F], !,to_modal1(KB,XF, HH).
to_modal1(KB, poss(_,F),   HH):- XF =..[poss,F], !,to_modal1(KB,XF, HH).

to_modal1(KB,H,HH ):- H=..[F|ARGS],!,must_maplist(to_modal1(KB),ARGS,ARGSO),!,HH=..[F|ARGSO].


%= 	 	 

%% is_sent_op_modality( ?VALUE1) is det.
%
% If Is A Sentence Oper. Modality.
%
is_sent_op_modality(not).
is_sent_op_modality(poss).
is_sent_op_modality(nesc).

has_modals(P):- notrace((sub_term(A,P),compound(A),(functor(A,poss,_);functor(A,nesc,_)))),!.

%= 	 	 

%% atom_compat( ?F, ?HF, ?HHF) is det.
%
% Atom Compat.
%
 /* disabled */
atom_compat(F,HF,HHF):- fail,F\=HF, is_sent_op_modality(F),is_sent_op_modality(HF), format(atom(HHF),'~w_~w',[F,HF]).

remove_unused_clauses([],[]):- !.
remove_unused_clauses([Unused|FlattenedO4],FlattenedO):- 
   unused_clause(Unused) -> remove_unused_clauses(FlattenedO4,FlattenedO);
     (remove_unused_clauses(FlattenedO4,FlattenedM),FlattenedO=[Unused|FlattenedM]).

unusual_body :- call_u(feature_setting(use_unusual_body,true)),!,dmsg(used(unusual_body)).
unusual_body :- dmsg(skipped(unusual_body)),!,fail.

unused_clause(unused(C):-_):-nonvar(C),!.
unused_clause((C v _):-_):-nonvar(C),!.
% unused_clause(naf(C):- ~ _):-nonvar(C),!.

demodal_clauses3(KB,FlattenedO1,FlattenedOO):-
        demodal_clauses(KB,FlattenedO1,FlattenedO2),
        demodal_clauses(KB,FlattenedO2,FlattenedO3),
        demodal_clauses(KB,FlattenedO3,FlattenedO4),
        demodal_clauses(KB,FlattenedO4,FlattenedO5),
      remove_unused_clauses(FlattenedO5,FlattenedOO).

demodal_clauses(_KB,Var, Var):- var_or_atomic(Var),!.
demodal_clauses(KB,(Head:-Body),HeadOBodyO):- !, demodal_head_body(KB,Head,Body,HeadOBodyO),!.
demodal_clauses(KB,List,ListO):- is_list(List),!,must_maplist(demodal_clauses(KB),List,ListO),!.
demodal_clauses(KB,Head,HeadOBodyO):- demodal_head_body(KB,Head,true,HeadOBodyO),!.

% demodal_body(_KB,~ _Head,(skolem(_,B), \+ G), \+ G ):- nonvar(B),nonvar(G),!.
demodal_body(_KB,_Head,Var, Var):- var(Var),!.  
demodal_body(_KB, ~ _Head, (pos(A), ~B), ~B):- A==B,!.
demodal_body(_KB, ~ _Head, (~B, pos(A)), ~B):- A==B,!.
demodal_body(_KB, _Head, (pos(A), ~B), pos(B)):- A==B,!.
demodal_body(_KB, _Head, (~B, pos(A)), pos(B)):- A==B,!.
demodal_body(_KB,_Head, poss([infer_by(_)],G), poss(G)).
demodal_body(_KB,_Head, nesc([infer_by(_)],G), nsec(G)).
demodal_body(_KB,_Head, nesc(G), proven(G)):- nonvar(G),!.

demodal_body(_KB, _Head, ((A , B) , C), (A , B , C)):- nonvar(A),!.
demodal_body(_KB, _Head, (A , B , C), (A , B)):- A==C,!.
demodal_body(_KB, _Head, (A , B , C), (A , C)):- A==B,!.
demodal_body(_KB, _Head, (A , B), A):- A==B,!.

demodal_body(KB,Head,[H|T],[HH|TT]):- !, must(( demodal_body(KB,Head,H,HH),demodal_body(KB,Head,T,TT))),!.

% demodal_clauses(KB,G,O):- G=..[F,H], \+ leave_as_is(H), H=..[HF,HH], atom_compat(F,HF,HHF),!, GG=..[HHF,HH], demodal_clauses(KB,GG,O).

demodal_body(_KB,_Head,naf(~skolem(A,B)),skolem(A,B)):- nonvar(B),!.

demodal_body(_KB,Head, v(A, ~B), ~B):- A==Head,!.
demodal_body(_KB,Head, v(~B, A), ~B):- A==Head,!.
demodal_body(_KB,Head, v(A, B), B):- A==Head,!.
demodal_body(_KB,Head, v(B, A), B):- A==Head,!.

demodal_body(_KB, _Head, poss(A & B), (poss(A) , poss(B))):-nonvar(A),!.

%demodal_body(_KB, ~ _Head,(G1,G2), (G1 , \+ GG2)):- G2 \= (_,_), G2 = ~(GG2).
%demodal_body(_KB,_Head,(G1,G2), (G1, poss(GG2) )):- G2 \= (_,_), G2 = ~(GG2), nonvar(GG2).

demodal_body(KB,Head,(H & T),(HH,TT)):- !, must(( demodal_body(KB,Head,H,HH),demodal_body(KB,Head,T,TT))),!.
demodal_body(KB,Head,(H,T),(HH,TT)):- !, must(( demodal_body(KB,Head,H,HH),demodal_body(KB,Head,T,TT))),!.
demodal_body(KB,Head,(H v T),(HH v TT)):- !, must(( demodal_body(KB,Head,H,HH),demodal_body(KB,Head,T,TT))),!.


demodal_body(_KB, _Head, G, G):- !.

demodal_body(_KB,_Head, poss(poss( G)), poss(G)):- nonvar(G),!.
demodal_body(_KB, Head, G, true):- G==Head, unusual_body,!.
% demodal_body(_KB,_Head, poss(isa(I,C)), isa(I,C)):- !.

demodal_body(_KB,_Head, naf(~ G), poss(G)):- nonvar(G),!.
demodal_body(_KB,_Head, ~ (~ G), proven(G)):- nonvar(G), unusual_body,!.



demodal_body(KB,Head, v(~A, B), BB):- demodal_body(KB,Head,A,AA),AA==Head,!,demodal_body(KB,Head,B,BB).
%demodal_body(KB,Head, v(~B, A), BB):- demodal_body(KB,Head,A,AA),AA==Head,!,demodal_body(KB,Head,B,BB).
demodal_body(KB,Head, v(~A, B), (AA *-> BB)):- nonvar(A),!,demodal_body(KB,Head,A,AA),demodal_body(KB,Head,B,BB).
demodal_body(_KB,_Head, \+ (~ G), proven(G)):- nonvar(G),!.
demodal_body(_KB,_Head, \+ (~ G), poss(G)):- nonvar(G),!.

demodal_body(_KB, _Head, ( H, poss(G) ) , poss(G)):- H==G , unusual_body.
demodal_body(_KB, _Head, ( H, (G) ) , (G)):- H==G, unusual_body.
demodal_body(_KB, _Head, ( H, G ) , G):- H==true, unusual_body.
demodal_body(_KB, _Head, ( G, H ) , G):- H==true, unusual_body.
demodal_body(_KB, _Head, ( G *-> H ) , G):- H==true, unusual_body.
demodal_body(_KB, _Head, ( H *-> G ) , G):- H==true, unusual_body.

%demodal_body(_KB, Head, ( H, poss(G) ) , (H, G)):- pos_or_isa(H), pred_of(Head,GHead)-> G \= GHead,!.
%demodal_body(_KB, Head, ( poss(G) , H) , (G, H)):-  pos_or_isa(H), pred_of(Head,GHead)-> G \= GHead,!.
%demodal_body(_KB, Head, ( poss(G) ) , (G)):-  shared_vars(Head,G,SVG),SVG=[].
%demodal_body(_KB, Head, ( poss(G) ) , (G)):- Head \= ~ _,!.

demodal_body(KB,Head,H,HH ):- H=..[F|ARGS],!,must_maplist(demodal_body(KB,Head),ARGS,ARGSO),!,HH=..[F|ARGSO].

pos_or_isa(isa(_,_)).
pos_or_isa(poss(_)).

pred_of(Head, Head):- is_ftVar(Head),!.
pred_of(~ Head, Head).
pred_of(Head, Head).

demodal_head_body(KB,Head,Body,(Head:-BodyO)):- term_attvars(Head,AttVars),include(AttVars,is_skolem,HeadAttVars),
  term_attvars(Body,BodyAttVars),subtract_eq(HeadAttVars,BodyAttVars,SKList),
    transform_skolem_forms(SKList,HeadExtra),
    conjoin(HeadExtra,Body,NewBod),
    demodal_body(KB,Head,NewBod,BodyO),!.

demodal_head_body(KB,Head,Body,(HeadO:-BodyO)):-
   demodal_head(KB,Head,HeadO,HeadExtra),
   conjoin(HeadExtra,Body,NewBod),
   demodal_body(KB,Head,NewBod,BodyO),!.

demodal_head(_KB,~skolem(A,B),unused(~skolem(A,B)),true):- nonvar(B),!.
% demodal_head(_KB,~skolem(A,B),unused_skolem(A,B),true):- nonvar(B),!.
% demodal_head(_KB,different(A,B),not_equals(A,B),true):-!.
demodal_head(_KB,~different(A,B),equals(A,B),true):-!.
demodal_head(_KB,~equals(A,B), different(A,B),true):-!.
demodal_head(_KB,~mudEquals(A,B), different(A,B),true):-!.
demodal_head(_KB,~isa(A,B),not_isa(A,B),true):- nonvar(B),!.
demodal_head(_KB,naf(~Head),poss(Head),true):- !.
demodal_head(_KB,nesc(Head),Head,true):- !.
demodal_head(_KB,Head,Head,true):- !.
demodal_head(KB,Head,HeadO,true):-  demodal_clauses(KB,Head,HeadO).

%= 	 	 

%% modal2sent( :TermVar, :TermVar) is det.
%
% Modal2sent.
%
modal2sent(Var, Var):- !.
modal2sent(Var, Var):- var_or_atomic(Var),!.
% modal2sent(G,O):- G=..[F,H], \+ leave_as_is(H), H=..[HF,HH], atom_compat(F,HF,HHF),!, GG=..[HHF,HH], modal2sent(GG,O).
modal2sent([H|T],[HH|TT]):- !, must(( modal2sent(H,HH),modal2sent(T,TT))),!.
modal2sent(poss([infer_by(_)],G), \+ ~ G):- G \= ~ _.
modal2sent(nesc([infer_by(_)],G),G):- G \= ~ _.
%modal2sent(naf(~poss(~ G)), G):- nonvar(G),!.
%modal2sent(naf(~skolem(A,B)),skolem(A,B)):- nonvar(B),!.
modal2sent(H,HH ):- H=..[F|ARGS],!,must_maplist(modal2sent,ARGS,ARGSO),!,HH=..[F|ARGSO].


var_or_atomic(Var):- is_ftVar(Var),!.
var_or_atomic([]):-!.
var_or_atomic(Var):- atomic(Var),!.

%= 	 	 

%% clausify( ?KB, ?P, ?C, ?C) is det.
%
% Clausify.
%
clausify(KB, &(P,Q), C1, C2 ):- 
	!,
	clausify(KB, P, C1, C3 ),
	clausify(KB, Q, C3, C2 ).
clausify(KB, P, [cl(A,B)|Cs], Cs ):- 
	inclause(KB, P, A, [], B, [] ),
	!.
clausify(_KB, _, C, C ).


%= 	 	 

%% inclause( ?KB, ?P, ?A1, ?A, ?B, ?B) is det.
%
% Inclause.
%
inclause(KB, v(P,Q), A, A1, B, B1 ):- 
	!,
	inclause(KB, P, A2, A1, B2, B1 ),
	inclause(KB, Q, A,  A2, B,  B2 ).
inclause(KB,  ~(  PP) , A,  A, B1, B ):- 
        negate(KB,  ~(  PP),P),
	!,
	notin(P, A ),
	putin(P, B, B1 ).
inclause(_KB, P,  A1, A, B,  B ):- 
	!,
	notin(P, B ),
	putin(P, A, A1 ).


%= 	 	 

%% notin( ?X, ?Y) is det.
%
% Notin.
%
notin(X,[Y|_]):- X==Y, !, fail.
notin(X,[_|Y]):- !,notin(X,Y).
notin(_,[]).


%= 	 	 

%% putin( ?X, :TermARG2, :TermX) is det.
%
% Putin.
%
putin(X,[],   [X]   ):- !.
putin(X,[Y|L],[Y|L] ):- X == Y,!.
putin(X,[Y|L],[Y|L1]):- putin(X,L,L1).


%= 	 	 

%% simplify_atom( ?H, ?SH) is det.
%
% Simplify Atom.
%
simplify_atom(H,SH):-simplify_cheap(H,SH),!.
simplify_atom(H,H).


%= 	 	 

%% to_regular_cl( ?KB, ?H1, ?Has, ?H1) is det.
%
% Converted To Regular Clause.
%
to_regular_cl(KB,[(H1 & H2)],[Has],[cl([H1],H1P),cl([H2],H2P)]):- cnf(KB,Has,HasC),  append([HasC],[poss(H2)],H1P), append([HasC],[poss(H1)],H2P),!.
to_regular_cl(_KB,[(H1 & H2)],Has,[cl([H1],H1P),cl([H2],H2P)]):-  append(Has,[poss(H2)],H1P), append(Has,[poss(H1)],H2P),!.
to_regular_cl(_KB,[H],[],[cl([SH],[])]):-is_lit_atom(H),simplify_atom(H,SH).
to_regular_cl(_KB,HL,BL,[cl(HL,BL)]).



%= 	 	 

%% expand_cl( ?KB, :TermARG2, ?VALUE3) is det.
%
% Expand Clause.
%
expand_cl(_KB,[],[]):-!.
expand_cl(KB,[cl(H,B)|O],OOut):- 
      to_regular_cl(KB,H,B,More),!,
      expand_cl(KB,O,OO),
      append(More,OO,OOut).


%= 	 	 

%% make_clause_set( ?Extras, :TermARG2, ?VALUE3) is det.
%
% Make Clause Set.
%
make_clause_set(_Extras ,[],[]).
make_clause_set(Extras,[CJ|Conj],CLAUSES):-
   make_clauses(Extras,CJ,CLS),
   make_clause_set(Extras,Conj,CLAUS),
   append(CLS,CLAUS,CLAUSES).

% make_clauses(Extras,_,[CJ],cl([CJ],[])):-is_lit_atom(CJ),!.

%= 	 	 

%% make_clauses( ?Extras, ?CJ, ?OOut) is det.
%
% Make Clauses.
%
make_clauses(Extras,CJ,OOut):- disjuncts_to_list(CJ,Conj),make_clause_from_set(Extras,Conj,OOut).


%= 	 	 

%% negate_one_maybe( ?Extras, ?One, ?Neg) is det.
%
% Negate One Maybe.
%
negate_one_maybe(Extras,One,Neg):-negate_one(Extras,One,Neg).
   

%= 	 	 

%% make_clause_from_set( ?Extras, ?Conj, ?Out) is det.
%
% Make Clause Converted From Set.
%
make_clause_from_set(Extras,Conj,Out):- findall(E,make_each(Extras,Conj,E),Out).


%= 	 	 

%% make_each( ?Extras, ?Conj, ?E) is det.
%
% Make Each.
%
make_each(Extras,Conj,E):- member(One,Conj), make_1_cl(Extras,One,Conj,E).


%= 	 	 

%% make_1_cl( ?Extras, ?One, ?Conj, :TermOne) is det.
%
% make  Secondary Helper Clause.
%
make_1_cl(Extras,One,Conj,cl([One],NewBodyListO)):- 
  negate_one_maybe(Extras,One,NHead),!,
  One\={_}, NHead\={_},
  delete_eq(Conj,One,Rest0),delete_eq(Rest0,NHead,Rest),
  must_maplist(negate_one_maybe(Extras),Rest,NewBodyList),!,
  flattenConjs(Extras,NewBodyList,NewBodyListM),
  Pred= baseKB:as_prolog_hook, must_maplist(Pred,NewBodyListM,NewBodyListO).


%= 	 	 

%% flattenConjs( ?Extras, ?I, ?O) is det.
%
% Flatten Conjs.
%
flattenConjs(_Extras,I,O):- conjuncts_to_list(I,M),must_maplist(conjuncts_to_list,M,L),flatten(L,O).



:- was_export(logical_pos/3).
:- was_export(logical_neg/3).

%= 	 	 

%% logical_neg( ?KB, ?Wff, ?WffO) is det.
%
% Logical Negated.
%
logical_neg(KB,Wff,WffO):- 
  must(nonegate(KB,Wff,Wff1)),nnf(KB, ~( Wff1),Wff2),must(nonegate(KB,Wff2,WffO)),!.

%= 	 	 

%% logical_pos( ?KB, ?Wff, ?WffO) is det.
%
% Logical Pos.
%
logical_pos(KB,Wff,WffO):- 
  must(nonegate(KB,Wff,Wff1)),nnf(KB,Wff1,Wff2),must(nonegate(KB,Wff2,WffO)),!.



%= 	 	 

%% negate_one( ?KB, ?Wff, ?WffO) is det.
%
% Negate One.
%
negate_one(KB,Wff,WffO):- logical_neg(KB,Wff,WffO).



%= 	 	 

%% negate( ?KB, ?X, ?Z) is det.
%
% Negate.
%
negate(KB,X,Z):- must(defunctionalize(X,Y)), must_det(negate0(KB,Y,Z)).

%= 	 	 

%% negate0( ?VALUE1, ?X, ?X) is det.
%
% Negate Primary Helper.
%
negate0(_, ~( X),X).
negate0(_,X, ~( X)).




%= 	 	 

%% mpred_quf( ?In, ?Out) is det.
%
% Managed Predicate Quf.
%
mpred_quf(In,Out):- transitive(mpred_quf_0,In,Out).


%= 	 	 

%% mpred_quf_0( ?InOut, ?InOut) is det.
%
% Managed Predicate quf  Primary Helper.
%
mpred_quf_0(InOut,InOut):- not_ftCompound(InOut),!.
% mpred_quf_0(In,Out):- current_predicate(db_quf/4),db_quf(clause(assert,_Must),In,U,C),conjoin(U,C,Out).
mpred_quf_0(In,In).

:- was_export(nonegate/3).

%= 	 	 

%% nonegate( ?KB, ?IO, ?IO) is det.
%
% Nonegate.
%
nonegate(_KB,IO,IO):-!.
nonegate(KB,List,OutZ):- is_list(List),must_maplist(nonegate(KB),List,OutZ),!.
nonegate(KB,Fml,OutZ):- simplify_cheap(Fml,Fml2)-> Fml \=@= Fml2,nonegate(KB,Fml2,OutZ),!.
nonegate(KB,Fml,OutZ):- must((unbuiltin_negate(KB,Fml,Out),!,defunctionalize(Out,OutY),!,must(mpred_quf(OutY,OutZ)))),!.


%= 	 	 

%% unbuiltin_negate( ?Neg, ?VALUE2, ?Fml, ?Fml) is det.
%
% Unbuiltin Negate.
%
unbuiltin_negate(_Neg,_, Fml,Fml):- is_ftVar(Fml),!.
unbuiltin_negate(_Neg,_, Fml,Out):- get_functor(Fml,F,A),find_and_call(pttp_builtin(F,A)),!,must(Out=Fml).

%= 	 	 

%% unbuiltin_negate( ?KB, ?Fml, ?Out) is det.
%
% Unbuiltin Negate.
%
unbuiltin_negate(_KB,Fml,Out):- once(negate(KB,Fml,Neg)),negate(KB,Neg,Out),!.





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
         % MAYBE CLOSE nnf(KB,((mudEquals(X,SKF) => ~FmlSk)v Fml),NewVars,NNF,Paths).
         %nnf1(KB,  (((skolem(X,SKF))=>NNFMid) & FmlSk) ,NewVars,NNF,Paths))).
        % GOOD nnf(KB, isa(X,SKF) => (skolem(X,SKF)=>(NNFMid)) ,NewVars,NNF,Paths))).
         nnf(KB, skolem(X,SKF) => NNFMid ,NewVars,NNF,Paths))).


%= 	 	 

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
        mk_skolem_name(KB,X,LitsList,'',SK),
        atom_concat(SK,'_',SKU),
        % =(SKU,SKN), 
        gensym(SKU,SKN),        
        concat_atom(['sk',SKN,'Fn'],Fun),
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
        mk_skolem_name(KB,X,LitsList,'',SK),
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
/*


%=% Substitution

% Usage: subst_except(+Fml,+X,+Sk,?FmlSk)
subst_except(Fml,X,Sk,FmlSkO):- pred_subst(==,Fml,X,Sk,FmlSk),!,must(FmlSkO=FmlSk).


% Usage: pred_subst(+Pred,+Fml,+X,+Sk,?FmlSk)
pred_subst(Pred,   all(Y,P), X,Sk,   all(Y,P1) ):- !, pred_subst(Pred, P,X,Sk,P1 ).
pred_subst(Pred,exists(Y,P), X,Sk,exists(Y,P1) ):- !, pred_subst(Pred, P,X,Sk,P1 ).
pred_subst(Pred, &(P,Q), X,Sk,&(P1,Q1) ):- !, pred_subst(Pred, P,X,Sk,P1 ), pred_subst(Pred, Q,X,Sk,Q1 ).
pred_subst(Pred,  v(P,Q), X,Sk, v(P1,Q1) ):- !, pred_subst(Pred, P,X,Sk,P1 ), pred_subst(Pred, Q,X,Sk,Q1 ).

pred_subst(Pred,       P,    X,Sk,       P1    ):- call(Pred,P,X), Sk=P1,!.
pred_subst(_Pred,       P,    _,_,       P1    ):- is_ftVar(P), P1=P,!.
pred_subst(Pred,       P,    X,Sk,       P1    ):- compound(P),
                             P =..Args, 
                               pred_subst2(Pred, X, Sk, Args, ArgS ),!,
                             P1 =..ArgS.
pred_subst(_  ,        P,    _, _,       P     ).

pred_subst2(_   , _,  _, [], [] ).
pred_subst2(Pred, X, Sk, [A|As], [Sk|AS] ):- call(Pred, X, A), !, pred_subst2(Pred, X, Sk, As, AS).
pred_subst2(Pred, X, Sk, [A|As], [A|AS]  ):- is_ftVar(A), !, pred_subst2(Pred, X, Sk, As, AS).
pred_subst2(Pred, X, Sk, [A|As], [Ap|AS] ):- pred_subst(Pred, A,X,Sk,Ap ), pred_subst2(Pred, X, Sk, As, AS).
*/







%% mk_skolem_name( +KB, +Var, +TermFml, +SuggestionIn, -NameSuggestion) is det.
%
%  generate a skolem name..
%
mk_skolem_name(_O,Var,Fml,SIn,SOut):- is_ftVar(Fml), same_var(Var,Fml),!,atom_concat('Is',SIn,SOut).
mk_skolem_name(_O,_V,Fml,SIn,SIn):- is_ftVar(Fml),!.
mk_skolem_name(_O ,_V,[],SIn,SIn):- !.
mk_skolem_name(_O,_V, OP,SIn,SIn):- is_log_op(OP),!.
mk_skolem_name(_O,_V,Fml,SIn,SOut):- atomic(Fml),!,i_name(Fml,N),toPropercase(N,CU),!,(atom_contains(SIn,CU)->SOut=SIn;atom_concat(SIn,CU,SOut)).
mk_skolem_name(KB,Var,[H|T],SIn,SOut):- !,mk_skolem_name(KB,Var,H,SIn,M),mk_skolem_name(KB,Var,T,M,SOut).
mk_skolem_name(KB,Var,isa(VX,Lit),SIn,SOut):- same_var(Var,VX),is_ftNonvar(Lit),!,mk_skolem_name(KB,Var,['Is',Lit,'In'],'',F),atom_concat(F,SIn,SOut).
mk_skolem_name(KB,Var,Fml,SIn,SOut):- Fml=..[F,VX],same_var(Var,VX),!,mk_skolem_name(KB,Var,['Is',F,'In'],SIn,SOut).
mk_skolem_name(KB,Var,Fml,SIn,SOut):- Fml=..[F,Other,VX|_],same_var(Var,VX),!,(type_of_var(KB,Other,OtherType0),
   (OtherType0=='Unk'->OtherType='';OtherType=OtherType0)),
   mk_skolem_name(KB,Var,[OtherType,'Arg2Of',F],SIn,SOut).
mk_skolem_name(KB,Var,Fml,SIn,SOut):- Fml=..[F,VX|_],same_var(Var,VX),!,mk_skolem_name(KB,Var,['Arg1Of',F],SIn,SOut).
mk_skolem_name(KB,Var,Fml,SIn,SOut):- Fml=..[F,_,VX|_],same_var(Var,VX),!,mk_skolem_name(KB,Var,['Arg2Of',F],SIn,SOut).
mk_skolem_name(KB,Var,Fml,SIn,SOut):- Fml=..[F|_],!,mk_skolem_name(KB,Var,['ArgNOf',F],SIn,SOut).

% same_var(Var,Fml):-  ~(  ~( Var=Fml)),!.

%= 	 	 



%= 	 	 

%% removes_literal( :TermX, :TermX) is det.
%
% Removes Literal.
%
removes_literal(true_t(X),possible_t(X)).
removes_literal(true_t(X,Y),possible_t(X,Y)).
removes_literal(true_t(X,Y,Z),possible_t(X,Y,Z)).
removes_literal(true_t(X,Y,Z,A),possible_t(X,Y,Z,A)).

removes_literal(not_true_t(X),possible_t(X)).
removes_literal(not_true_t(X,Y),possible_t(X,Y)).
removes_literal(not_true_t(X,Y,Z),possible_t(X,Y,Z)).
removes_literal(not_true_t(X,Y,Z,A),possible_t(X,Y,Z,A)).




%= 	 	 

%% delete_sublits( ?H0, ?B, ?HH) is det.
%
% Delete Sublits.
%
delete_sublits(H0,B,HH):- delete_eq(H0,B,H1),delete_eq(H1,B,H2),delete_eq(H2,B,HH),!.

% cl([-nesc(p)], [-poss(p), nesc(q), -poss(q)]).



%= 	 	 

%% flatten_clauses( ?H, ?HHTT) is det.
%
% Flatten Clauses.
%
flatten_clauses([H|T],HHTT):-!,flatten_clauses(H,HH),flatten_clauses(T,TT),append(HH,TT,HHTT).
flatten_clauses(poss(~(~(H))),poss(HH)):- !,flatten_clauses(H,HH),!.
flatten_clauses(nesc(~(~(H))),HH):- !,flatten_clauses(H,HH),!.
flatten_clauses((H,T),HHTT):-!,flatten_clauses(H,HH),flatten_clauses(T,TT),append(HH,TT,HHTT).
flatten_clauses([H],[H]):-!.


%= 	 	 

%% correct_cls( ?KB, ?H, ?HH) is det.
%
% Correct Clauses.
%
correct_cls(KB,H,HH):-loop_check(correct_cls0(KB,H,HH),H=HH),!.


%= 	 	 

%% correct_cls0( ?KB, :TermCL0, ?CL1) is det.
%
% Correct Clauses Primary Helper.
%
correct_cls0(_KB,CL0,CL0):- is_ftVar(CL0),!.
correct_cls0(KB,CL0,CL1):- is_list(CL0),!,must_maplist(correct_cls(KB),CL0,CL1).
correct_cls0(KB,(H,T),HHTT):-!,correct_cls(KB,H,HH),correct_cls(KB,T,TT),append(HH,TT,HHTT).
correct_cls0(KB,(H:-B),O):-!,conjuncts_to_list(H,HH),conjuncts_to_list(B,BB),correct_cls0(KB,cl(HH,BB),O).

correct_cls0(KB,CL,O):- demodal_sents(KB,CL,CLM),CL\=@=CLM,!,correct_cls(KB,CLM,O).
correct_cls0(KB,cl(H,B),O):-flatten_clauses(B,BB),B\=@=BB,correct_cls0(KB,cl(H,BB),O).
correct_cls0(KB,cl(H,B),O):-removeQ(KB,H,HH),removeQ(KB,B,BB),(H\=@=HH ; B\=@=BB),!, correct_cls(KB,cl(HH,BB),O).

correct_cls0(KB,cl(H,B),O):- member(E,B),removes_literal(E,R),delete_sublits(B,R,BB),BB\=@=B,!,correct_cls(KB,cl(H,BB),O).



correct_cls0(KB,cl(H,B),O):- list_to_set(H,HH),HH\=@=H,!,correct_cls(KB,cl(HH,B),O).
correct_cls0(KB,cl(H,B),O):- list_to_set(B,BB),BB\=@=B,!,correct_cls(KB,cl(H,BB),O).

/*
correct_cls0(_,cl([ ~( poss(H))],B),cl([z_unused(~pos(H:-B))],[])):-member( ~( H),B),!.
correct_cls0(KB,cl([ ~( poss(H))],B),O):- correct_cls0(KB,cl([ ~( (H))],B),O).
correct_cls0(KB,cl([ ~( H)],B),O):- delete_sublits(B,poss(H),BB),BB\=@=B,!,correct_cls(KB,cl([ ~( H)],BB),O).
correct_cls0(KB,cl([ ~( H)],B),O):- delete_sublits(B,(H),BB),BB\=@=B,!,correct_cls(KB,cl([ ~( H)],BB),O).
correct_cls0(KB,cl([H],B),O):- delete_sublits(B,H,BB),BB\=@=B,!,correct_cls(KB,cl([H],BB),O).
correct_cls0(KB,cl([H],B),O):- delete_sublits(B, ~( H),BB),BB\=@=B,!,correct_cls(KB,cl([H],BB),O).

correct_cls0(KB,cl(H,B),O):- member(E,B),E=poss( ~( _)),delete_sublits(B,E,BB),BB\=@=B,!,correct_cls(KB,cl(H,BB),O).
correct_cls0(KB,cl(H,B),O):- member(E,B),E=nesc( ~( P)),delete_sublits(B,E,BB),BB\=@=B,!,correct_cls(KB,cl(H,[ ~( P)|BB]),O).
correct_cls0(KB,cl(H,B),O):- member(E,B),delete_sublits(B,poss(E),BB),BB\=@=B,!,correct_cls(KB,cl(H,BB),O).
correct_cls0(KB,cl(H,B),O):- member( ~( E),B),delete_sublits(B,poss(E),BB),BB\=@=B,!,correct_cls(KB,cl(H,BB),O).
correct_cls0(KB,cl(H,B),O):- member( ~( E),B),delete_sublits(B,E,BB),BB\=@=B,!,correct_cls(KB,cl(H,BB),O).
correct_cls0(KB,cl(H,B),O):- member(nesc( ~( E)),B),delete_sublits(B,poss(E),BB),BB\=@=B,!,correct_cls(KB,cl(H,BB),O).

% correct_cls0(KB,cl([(poss(H))],B),O):- correct_cls0(KB,cl([((H))],B),O).

correct_cls0(_,cl(H,B),O):- member(E,B),member( ~( E),B),!,incorrect_cl(cl(H,B),O).

correct_cls0(_,cl([nesc((H))],B),cl([z_unused(nesc(H:-B))],[])):-member((H),B),!.
correct_cls0(KB,cl([nesc((H))],B),O):- delete_sublits(B, ~( H),BB),BB\=@=B,!,correct_cls(KB,cl([(H)],BB),O).
correct_cls0(KB,cl([ ~( (H))],B),O):- correct_cls(KB,cl([ ~( poss(H))],B),O).
*/

correct_cls0(_KB,cl(H,B),O):- !,O=cl(H,B).
correct_cls0(KB,H,O):-correct_cls0(KB,(H:-true),O).


%= 	 	 

%% incorrect_cl( :TermH, ?H) is det.
%
% Incorrect Clause.
%
incorrect_cl(cl(H,B),cl([z_unused(H:-B)],[])).



:- was_export(correct_boxlog/4).

%= 	 	 

%% correct_boxlog( ?CLAUSES, ?KB, ?Why, ?FlattenedO) is det.
%
% Correct Datalog.
%
correct_boxlog((CLAU,SES),KB,Why,FlattenedO):- nonvar(SES),conjuncts_to_list((CLAU,SES),CLAUSES),!,correct_boxlog_0(CLAUSES,KB,Why,FlattenedO),!.
correct_boxlog(CLAUSES,KB,Why,FlattenedO):- (\+ is_list(CLAUSES)),!,correct_boxlog_0([CLAUSES],KB,Why,FlattenedO),!.
correct_boxlog(BOXLOG,KB,Why,FlattenedS):-correct_boxlog_0(BOXLOG,KB,Why,FlattenedS),!.


%= 	 	 

%% correct_boxlog_0( ?BOXLOG, ?KB, ?Why, ?FlattenedS) is det.
%
% correct Datalog  Primary Helper.
%
correct_boxlog_0(BOXLOG,KB,Why,FlattenedS):-
  must_det_l((  
   must_maplist(adjust_kif(KB),BOXLOG,MODAL),
   %wdmsgl(modal(MODAL)),   
   must_maplist(to_modal1(KB),MODAL,CLAUSES),
   must_maplist(correct_cls(KB),CLAUSES,NCFs),
   must_maplist(clauses_to_boxlog(KB,Why),NCFs,ListOfLists),
   flatten([ListOfLists],Flattened),
   must_maplist(removeQ(KB),Flattened,FlattenedM),
   must_maplist(to_modal1(KB),FlattenedM,FlattenedO),
   predsort(variants_are_equal,FlattenedO,FlattenedS),
   nop(wdmsgl(horn(FlattenedS))))),!.


%= 	 	 

%% variants_are_equal( ?Order, ?A, ?B) is det.
%
% Variants Are Equal.
%
variants_are_equal( =, A,B):- unnumbervars(A+B,AA+BB),AA=@=BB,!.
variants_are_equal( Order, A,B):- compare(Order,A,B).


%= 	 	 

%% cf_to_flattened_clauses( ?KB, ?Why, ?NCFsI, ?FlattenedO) is det.
%
% Cf Converted To Flattened Clauses.
%
cf_to_flattened_clauses(KB,Why,NCFsI,FlattenedO):-
  loop_check(cf_to_flattened_clauses_0(KB,Why,NCFsI,FlattenedO),NCFsI=FlattenedO),!.


%= 	 	 

%% cf_to_flattened_clauses_0( ?KB, ?Why, ?NCFsI, ?FlattenedO) is det.
%
% cf Converted To flattened clauses  Primary Helper.
%
cf_to_flattened_clauses_0(KB,Why,NCFsI,FlattenedO):- 
 must_det_l((
   must_maplist(correct_cls(KB),NCFsI,NCFs),
   % wdmsgl(cf(NCFs)),
   must_maplist(clauses_to_boxlog(KB,Why),NCFs,ListOfLists),
   flatten([ListOfLists],Flattened),
   baseKB:as_prolog_hook(Flattened,FlattenedL),
   list_to_set(FlattenedL,FlattenedS),
   must_maplist(demodal_sents(KB),FlattenedS,FlattenedO))),!.
  
% :- autoload([verbose(false)]).

:- fixup_exports.

