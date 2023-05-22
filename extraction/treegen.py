from cyaron import Graph, Vector
import cyaron

def goodtreegen(treesize : int):
    # tree size: the number of nodes in the tree
    tr = Graph.tree(treesize)
    edges = [[] for _ in range(treesize)]
    for edge in tr.iterate_edges():
        s, e = edge.start, edge.end
        s -= 1
        e -= 1
        # edges are bidirectional
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
