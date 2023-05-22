def treeprint(root, edges, info):
    # a tree is characterized by three components: root node, edges and information carried by each node
    def dfs(n : int, par : int):
        # print the tree according to pre-order traverse
        nonlocal info, edges
        print(n, info[n]["clk"], info[n]["aclk"], info[n]["chn_sz"], sep="\n")

        for e in edges[n]:
            if e == par:
                continue
            dfs(e, n)
    
    dfs(root, -1)

def read_tree_from_file(filename, treenum):
    number_lis = []
    with open(filename) as f:
        text = "".join(f.readlines())
        number_lis = text.strip().split()
    
    cur = 0
    res = []

    def get_num():
        nonlocal number_lis, cur
        n = int(number_lis[cur])
        cur += 1
        return n

    def dfs(info : dict, edges : list) -> int :
        nonlocal get_num
        tid = get_num()
        clk = get_num()
        aclk = get_num()
        chn_sz = get_num()

        while tid >= len(edges):
            edges.append([])
        
        info[tid] = dict()
        info[tid]["clk"] = clk
        info[tid]["aclk"] = aclk
        info[tid]["chn_sz"] = chn_sz
        for _ in range(chn_sz):
            ch = dfs(info, edges)
            edges[tid].append(ch)
            edges[ch].append(tid)
        
        return tid

    for _ in range(treenum):
        info = dict()
        edges = []
        rt = dfs(info, edges)
        res.append((rt, edges, info))

    return res

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

