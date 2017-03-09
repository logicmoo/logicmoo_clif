
:- ensure_loaded(library('logicmoo/plarkc/logicmoo_i_cyc_rewriting')).

:- mpred_unload_file.

:- set_prolog_flag_until_eof(do_renames,term_expansion).

:- file_begin(pfc).

ttBarrierStr(A)/(atomic_list_concat([A,"Type"],AType0),
  atomic_list_concat([A,''],Type0),
  if_defined(do_renames(Type0,Type),true),
  if_defined(do_renames(AType0,TypeType),true)) ==> barrierSpindle(TypeType,Type).



barrierSpindle(TypeType,Type)==> 
   generatesAsFirstOrder(Type), isa(TypeType,ttBarrierType),isa(Type,ttBarrier),typeGenls(TypeType,Type).

ttBarrier(C)==>tSet(C).
(ttBarrierType(C)==>(tSet(C),ttTypeType(C))).

/*

@ TODO RE-ENABLE WHEN NEEDED
ttBarrier(C)==>(isa(I,C)==>mainClass(I,C)).

ttBarrier(A)/dif(A,B),ttBarrier(B)==> disjointWith(A,B).
% ttBarrierType(A)/dif(A,B),ttBarrierType(B)==> disjointWith(A,B).

*/

ttBarrierStr("Action").
ttBarrierStr("Agent").
ttBarrierStr("Artifact").
barrierSpindle('ttSpecifiedPartTypeCollection','tPartTypePhysicalPartOfObject').
ttBarrierStr("Capability").
ttBarrierStr("Event").
ttBarrierStr("FormulaTemplate").
ttBarrierStr("Goal").
ttBarrierStr("Group").
ttBarrierStr("LinguisticObject").
ttBarrierStr("Microtheory").
ttBarrierStr("PersonTypeByActivity").
ttBarrierStr("Place").
ttBarrierStr("Quantity").
ttBarrierStr("Relation").
ttBarrierStr("ScalarInterval").
ttBarrierStr("Situation").
ttBarrierStr("ExpressionType").
ttBarrierStr("TimeParameter").
ttBarrierStr("Topic").
% ttBarrierStr("Collection").

