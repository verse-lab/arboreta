import sys, cyaron, os
from respect_treegen import SIZE_LB, SIZE_RB
from tree_clock import imono_check, dmono_check, treeprint, read_tree_from_file
from treegen import goodtreegen

def sanity_check(root_ret, edges_ret, info_ret, info_prime):
    if root_ret not in info_prime:
        return True
    return info_ret[root_ret]["clk"] > info_prime[root_ret]["clk"]

if __name__ == "__main__":
    assert (len(sys.argv) == 5)
    inputfile = sys.argv[1]
    outputfile = sys.argv[2]

    if not os.path.exists(outputfile):
        exit(0)

    (root1, edges1, info1), (root2, edges2, info2) = read_tree_from_file(inputfile, 2)
    root_ret, edges_ret, info_ret = read_tree_from_file(outputfile, 1)[0]

    round = int(sys.argv[3])

    for i in range(round):
        while True:
            n = cyaron.randint(SIZE_LB, SIZE_RB)

            # generate a tree that both T1 and T2 respect
        
            root_prime, edges_prime, info_prime = goodtreegen(n)

            if not dmono_check(root1, edges1, info1, info_prime)[0] or \
                not imono_check(root1, edges1, info1, info_prime)[0] or \
                not dmono_check(root2, edges2, info2, info_prime)[0] or \
                not imono_check(root2, edges2, info2, info_prime)[0] or \
                not sanity_check(root_ret, edges_ret, info_ret, info_prime):
                continue
            
            # now check the operation result also respects it
            dmono_check_res = dmono_check(root_ret, edges_ret, info_ret, info_prime)
            if not dmono_check_res[0]:
                print("Failed dmono check inside subtree #%d at node #%d" % (dmono_check_res[1], dmono_check_res[2]))
                with open(sys.argv[4], "w") as sys.stdout:
                    treeprint(root_prime, edges_prime, info_prime)
                exit(1)

            imono_check_res = imono_check(root_ret, edges_ret, info_ret, info_prime)
            if not imono_check_res[0]:
                print("Failed imono check inside subtree #%d at node #%d" % (imono_check_res[1], imono_check_res[2]))
                with open(sys.argv[4], "w") as sys.stdout:
                    treeprint(root_prime, edges_prime, info_prime)
                exit(1)

            break
        
        # if (i + 1) % 10 == 0:
        #     print("Passed %d tests. " % (i + 1))
