cat $0
swipl -g "use_module(library(logicmoo_user)),xlisting(xlisting),qsave_program(test_fol,[class(development),goal(prolog)]),halt"

echo "alias run_test='swipl -x test_fol -l '"
echo "use: run_test make_wff_01.pl"
