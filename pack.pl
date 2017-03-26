name(logicmoo_base).
version('1.1.117').
author('Douglas R. Miles','logicmoo@gmail.com').
title('LogicMOO - Extends Prolog Programming to support Dynamic Epistemic Logic (DEL) with Constraints').
keywords([pfc,extension,clif,datalog,del,fol,snark,logicmoo,memoization]).
home('https://github.com/TeamSPoon/logicmoo_base/').
download('https://github.com/TeamSPoon/logicmoo_base.git/release/*.tgz').
requires(pfc).
requires(must_trace).
requires(loop_check).
requires(subclause_expansion).
requires(clause_attvars).
requires(file_scope).
requires(each_call_cleanup).
requires(multimodal_dcg).
requires(prologmud).
requires(with_thread_local).
requires(s_expression).
requires(xlisting_web).
requires(xlisting).
requires(instant_prolog_docs).
requires(eggdrop).
requires(logicmoo_utils).
autoload(false).


