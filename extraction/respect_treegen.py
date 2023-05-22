import cyaron
from treegen import goodtreegen
from tree_clock import dmono_check, imono_check, treeprint

SIZE_LB = 9
SIZE_RB = 12

if __name__ == "__main__":
    while True:
        n, m = cyaron.randint(SIZE_LB, SIZE_RB), cyaron.randint(SIZE_LB, SIZE_RB)
        
        # see 2.test
        # if n > m:
        #     n, m = m, n

        root1, edges1, info1 = goodtreegen(n)
        root2, edges2, info2 = goodtreegen(m)

        if not dmono_check(root1, edges1, info1, info2)[0] or not imono_check(root1, edges1, info1, info2)[0]:
            continue
        
        # output 2 first
        treeprint(root2, edges2, info2)
        treeprint(root1, edges1, info1)
        break
