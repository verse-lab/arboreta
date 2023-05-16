from historygen import *
from clock_simulator import *
import sys

NUM_PROCESS_LB = 3
NUM_PROCESS_RB = 6

NUM_MESSAGE_LB = 4
NUM_MESSAGE_RB = 12

if __name__ == "__main__":
    assert(len(sys.argv) == 3)
    history_filename = sys.argv[1]
    mc_filename_prefix = sys.argv[2]

    n, m = cyaron.randint(NUM_PROCESS_LB, NUM_PROCESS_RB), cyaron.randint(NUM_MESSAGE_LB, NUM_MESSAGE_RB)
    edges = random_history_gen(n, m)
    history_dump(n, edges, history_filename)

    mcs = mc_simulate(n, edges)
    # print the clocks into different files
    for i, mc in enumerate(mcs):
        with open(mc_filename_prefix + str(i) + ".out", "w") as f:
            f.write(mc_to_string(mc) + "\n")
