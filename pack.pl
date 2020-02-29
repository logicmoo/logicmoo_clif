name(logicmoo_base).
version('1.4.111').
author('Douglas R. Miles','logicmoo@gmail.com').
title('LogicMOO - Extends Prolog Programming to support Dynamic Epistemic Logic (DEL) with Constraints').
keywords([pfc,extension,clif,datalog,del,fol,snark,logicmoo,memoization]).
home('https://github.com/TeamSPoon/logicmoo_base/').
download('https://github.com/TeamSPoon/logicmoo_base.git/release/*.tgz').
requires(pfc).
requires(multimodal_dcg).
%requires(s_expression).
requires(instant_prolog_docs).
requires(eggdrop).
requires(logicmoo_utils).
requires(wam_common_lisp).
autoload(false).


