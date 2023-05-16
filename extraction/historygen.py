import cyaron

EXAMPLE_HISTORY_1 = [
    (1, 1, 3, 1), 
    (2, 1, 1, 2), 
    (3, 2, 2, 2), 
    (1, 3, 2, 3), 
    (2, 4, 3, 3), 
    (3, 4, 1, 4)
]

EXAMPLE_HISTORY_2 = [
    (3, 1, 1, 1), 
    (2, 1, 3, 2), 
    (1, 2, 2, 2), 
    (1, 3, 2, 3), 
    (2, 4, 3, 3), 
    (3, 4, 1, 4)
]

def random_history_gen(num_process, num_message):
    edges = []
    local_clocks = [0 for _ in range(num_process)]
    
    for _ in range(num_message):
        snd = cyaron.randint(0, num_process - 1)
        rcv = cyaron.randint(0, num_process - 2)
        if rcv >= snd:
            rcv += 1
        local_clocks[snd] += 1
        local_clocks[rcv] += 1
        edges.append((snd + 1, local_clocks[snd], rcv + 1, local_clocks[rcv]))
    
    return edges

def history_dump(num_process, edges, filepath):
    with open(filepath, "w") as f:
        f.write("%d\n%d\n" % (num_process, len(edges)))
        for e in edges:
            f.write("\n".join([str(x) for x in e]))
            f.write("\n")
