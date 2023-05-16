def mc_init(n):
    return [[0 for _ in range(n)] for _ in range(n)]

def mc_incr(mc, t):
    mc[t][t] += 1
    return mc

def mc_join(n, mc1, mc2, snd, rcv):
    res = [[max(mc1[i][j], mc2[i][j]) for j in range(n)] for i in range(n)]
    # an update like vector clock
    res[rcv] = [max(mc2[rcv][j], mc1[snd][j]) for j in range(n)]
    return res

def mc_print(mc):
    for vc in mc:
        print(vc)

def mc_to_string(mc):
    return "\n".join([str(vc) for vc in mc])
