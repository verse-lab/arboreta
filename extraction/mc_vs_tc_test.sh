# the work flow is: 
# 1. generate random histories (for now, in Python)
# 2. run matrix clocks on histories (for now, in Python) and dump the results into text files
# 3. run treeclocks on histories (for now, in OCaml; so need to dump the histories into text files) 
#    and dump the results into text files

# now repeat the three steps above for several times and ...

num_tests="${1:-1000}"

tmpdirname=mc_vs_tc_tmp
mkdir -p ${tmpdirname}

for i in $(seq 1 "${num_tests}")
do
    testname=test_${i}
    historyname=${tmpdirname}/history_${testname}.out

    # step 1 & 2
    python3 mc_vs_tc_main.py ${historyname} ${tmpdirname}/mc_${testname}_ 0

    # step 3
    dune exec ./main.exe simulate 0 ${tmpdirname}/tc_${testname}_ < ${historyname}
done

python3 mc_vs_tc_checker.py 1 ${num_tests} mc_vs_tc_tmp/history_test_%d.out mc_vs_tc_tmp/mc_test_%d_%d.out mc_vs_tc_tmp/tc_test_%d_%d.tr
