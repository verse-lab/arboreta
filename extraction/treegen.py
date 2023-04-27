from cyaron import Graph, Vector
import cyaron

def treeprint(root, edges, info):
    def dfs(n : int, par : int):
        # print the tree according to pre-order traverse
        nonlocal info, edges
        print(n, info[n]["clk"], info[n]["aclk"], info[n]["chn_sz"], sep="\n")

        for e in edges[n]:
            if e == par:
                continue
            dfs(e, n)
    
    dfs(root, -1)

def le_check(n1, par1, edges1, info1, info2 : dict) -> tuple[bool, int]:
    def dfs(n : int, par : int) -> tuple[bool, int]:
        nonlocal info1, info2, edges1
        corr = info2[n]["clk"] if n in info2 else 0
        if info1[n]["clk"] > corr:
            return False, n
        
        for e in edges1[n]:
            if e == par:
                continue
            subres = dfs(e, n)
            if not subres[0]:
                return subres
        return True, -1

    return dfs(n1, par1)

def dmono_check(root1, edges1, info1, info2 : dict) -> tuple[bool, int, int]:
    def dfs(n : int, par : int) -> tuple[bool, int, int]:
        nonlocal info1, info2, edges1
        corr = info2[n]["clk"] if n in info2 else 0
        if info1[n]["clk"] <= corr:
            subres = le_check(n, par, edges1, info1, info2)
            if not subres[0]:
                return False, n, subres[1]
            
        for e in edges1[n]:
            if e == par:
                continue
            subres = dfs(e, n)
            if not subres[0]:
                return subres
        return True, -1, -1
    
    return dfs(root1, -1)

def imono_check(root1, edges1, info1, info2 : dict) -> tuple[bool, int, int]:
    def dfs(n : int, par : int) -> tuple[bool, int, int]:
        nonlocal info1, info2, edges1
        corr = info2[n]["clk"] if n in info2 else 0
            
        for e in edges1[n]:
            if e == par:
                continue
            if info1[e]["aclk"] <= corr:
                subres = le_check(e, n, edges1, info1, info2)
                if not subres[0]:
                    return False, e, subres[1]
            subres = dfs(e, n)
            if not subres[0]:
                return subres
        return True, -1, -1
    
    return dfs(root1, -1)

def goodtreegen(treesize : int):
    tr = Graph.tree(treesize)
    edges = [[] for _ in range(treesize)]
    for edge in tr.iterate_edges():
        s, e = edge.start, edge.end
        s -= 1
        e -= 1
        edges[s].append(e)
        edges[e].append(s)
    
    info = dict()
    
    def dfs(n : int, par : int):
        nonlocal info, edges
        chn = []
        for e in edges[n]:
            if e == par:
                continue
            dfs(e, n)
            chn.append(e)

        # generate aclks for each child
        chn_sz = len(chn)
        aclk_seq = [x[0] for x in Vector.random(chn_sz, [(1, 30)], 1)]
        aclk_seq.sort(key=lambda x: -x)
        # also see 2.test
        clk = max(1, (aclk_seq[0] if chn_sz > 0 else 0) + cyaron.randint(0, 10))
        
        for i, e in enumerate(chn):
            info[e]["aclk"] = aclk_seq[i]
        info[n] = dict()
        info[n]["clk"] = clk
        info[n]["chn_sz"] = chn_sz

    root = cyaron.randint(0, treesize - 1)

    dfs(root, -1)
    info[root]["aclk"] = 0

    return root, edges, info

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
