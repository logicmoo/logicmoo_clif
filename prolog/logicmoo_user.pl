:- if(('$current_source_module'(SM),'context_module'(M),'$current_typein_module'(CM),asserta(baseKB:'wusing_pfc'(M,CM,SM,logicmoo_mod)))).
:- module(logicmoo_mod,[use_logicmoo_mod/0,
 op(1150,xfx,'=>'),
 op(1140,xfx,'<='),
 op(1130,xfx,'<=>'),
 op(600,yfx,'&'),
 op(600,yfx,'v'),
 op(350,xfx,'xor'),
 op(300,fx,'-')]).
/*   
  LogicMOO Base FOL/PFC Setup
% Dec 13, 2035
% Douglas Miles

*/

:- abolish(use_logicmoo_mod/0).
:- prolog_load_context(file,File),unload_file(File).
:- asserta(use_logicmoo_mod).
:- endif.

:- retract(baseKB:'wusing_pfc'(M,CM,SM,logicmoo_mod)),
   assert(baseKB:'using_pfc'(M,CM,SM,logicmoo_mod)),
   assert(baseKB:'using_pfc'(M,CM,SM,pfc_mod)),
   M:reexport(logicmoo_lib),
   M:reexport(library(pfc_lib)),
   (M==SM -> 
     (ensure_abox(SM),ain(genlMt(SM,baseKB)));     
  (module_property(SM,class(user))->ain(genlMt(SM,baseKB));
          wdmsg(baseKB:'lusing_pfc'(M,CM,SM,logicmoo_mod)))),!.



