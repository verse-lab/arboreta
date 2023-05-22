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
        # the lines above simply generate a random pair
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

def read_history(filepath):
    edges = []
    num_process = 0
    with open(filepath) as f:
        num_process = int(f.readline())
        num_message = int(f.readline())
        for _ in range(num_message):
            ev = []
            for _ in range(4):
                ev.append(int(f.readline()))
            edges.append(tuple(ev))
    return num_process, edges

def string_of_event(ev):
    return "process #%d (local time: %d) --> process #%d (local time: %d)" % ev

if __name__ == "__main__":
    # history_dump(3, EXAMPLE_HISTORY_1, "examples/tc_same_mc_different/history_1")
    # history_dump(3, EXAMPLE_HISTORY_2, "examples/tc_same_mc_different/history_2")
    pass
