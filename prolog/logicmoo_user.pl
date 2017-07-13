:- if(('$current_source_module'(SM),'$current_typein_module'(CM),asserta(baseKB:'using_pfc'(CM,SM,logicmoo_mod)))).
:- module(logicmoo_mod,[use_logicmoo_mod/0,op(1199,fx,('==>')),
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

:- reexport(logicmoo_lib).     

:- baseKB:'using_pfc'(_,SM,logicmoo_mod),!, 
  /* op(1199,fx,SM:('==>')),
   op(1190,xfx,SM:('::::')),
   op(1180,xfx,SM:('==>')),
   op(1170,xfx,SM:'<==>'),
   op(1160,xfx,SM:('<-')),
   op(1150,xfx,SM:'=>'),
   op(1140,xfx,SM:'<='),
   op(1130,xfx,SM:'<=>'),
   op(600,yfx,SM:'&'),
   op(600,yfx,SM:'v'),
   op(350,xfx,SM:'xor'),
   op(300,fx,SM:'~'),
   op(300,fx,SM:'-'), */
   (module_property(SM,class(user))->ain(genlMt(SM,baseKB));true).

 % , ensure_abox(SM),!.



