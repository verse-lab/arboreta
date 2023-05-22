# for now, only compare within the histories with the same number of processes 

import os, sys

def get_num_process_and_history(history_filename):
    num_process = -1
    history = ""
    with open(history_filename) as f:
        num_process = int(f.readline())
        history = f.read()
    return num_process, history

if __name__ == "__main__":
    assert(len(sys.argv) == 6)
    gen_lb = int(sys.argv[1])
    gen_rb = int(sys.argv[2])
    history_filename_template = sys.argv[3]
    mc_filename_template = sys.argv[4]
    tc_filename_template = sys.argv[5]

    res = dict()
    history_set = set()
    
    for i in range(gen_lb, gen_rb + 1):
        history_filename = history_filename_template % i
        n, history = get_num_process_and_history(history_filename)
        # avoid checking identical histories
        if history in history_set:
            continue
        history_set.add(history)

        if n not in res:
            res[n] = dict()
        
        content = []
        for j in range(n):
            mc_filename = mc_filename_template % (i, j)
            tc_filename = tc_filename_template % (i, j)
            text_mc, text_tc = "", ""
            with open(mc_filename) as f:
                text_mc = f.read()
            with open(tc_filename) as f:
                text_tc = f.read()
            
            content.append({ "mc": text_mc, "tc": text_tc })
        
        res[n][i] = content
        
    # now start to check
    for n, group in res.items():
        for j in range(n):
            print("with %d processes and on the process #%d: " % (n, j))

            st_mc = dict()
            st_tc = dict()
            for testid, content in group.items():
                this_st = st_mc.get(content[j]["mc"], set())
                this_st.add(testid)
                st_mc[content[j]["mc"]] = this_st

                this_st = st_tc.get(content[j]["tc"], set())
                this_st.add(testid)
                st_tc[content[j]["tc"]] = this_st

            print("mc_same_but_tc_not_same: ")
            for k, this_st in st_mc.items():
                for testid in this_st:
                    this_st2 = st_tc[group[testid][j]["tc"]]
                    
                    mc_same_but_tc_not_same = this_st.difference(this_st2)
                    # avoid symmetric output; the same for below
                    mc_same_but_tc_not_same = { x for x in mc_same_but_tc_not_same if x > testid }
                    if mc_same_but_tc_not_same:
                        print("for history #%d, the mc_same_but_tc_not_same set is " % testid, end="")
                        print(mc_same_but_tc_not_same)
            
            print("tc_same_but_mc_not_same: ")
            for k, this_st in st_tc.items():
                for testid in this_st:
                    this_st2 = st_mc[group[testid][j]["mc"]]
                    
                    tc_same_but_mc_not_same = this_st.difference(this_st2)
                    tc_same_but_mc_not_same = { x for x in tc_same_but_mc_not_same if x > testid }
                    if tc_same_but_mc_not_same:
                        print("for history #%d, the tc_same_but_mc_not_same set is " % testid, end="")
                        print(tc_same_but_mc_not_same)

            print()