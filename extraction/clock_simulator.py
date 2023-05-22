from matrix_clock import *
from historygen import string_of_event, read_history
import sys

def clock_simulate(num_process, edges, clock_init, clock_incr, clock_join, printer=None):
    local_clocks = [clock_init() for _ in range(num_process)]
    
    for ev in edges:
        snd, _, rcv, _ = ev
        snd -= 1
        rcv -= 1
        local_clocks[snd] = clock_incr(local_clocks[snd], snd)
        local_clocks[rcv] = clock_incr(local_clocks[rcv], rcv)
        local_clocks[rcv] = clock_join(local_clocks[snd], local_clocks[rcv], snd, rcv)
        if printer:
            printer(ev, local_clocks[rcv])

    return local_clocks

def mc_simulate(num_process, edges, verbosity):
    def aux1():
        return mc_init(num_process)
    def aux2(mc1, mc2, snd, rcv):
        return mc_join(num_process, mc1, mc2, snd, rcv)
    def mc_printer(ev, mc):
        print(string_of_event(ev))
        print("resulting matrix clock: ")
        print(mc_to_string(mc))
        print()
    
    return clock_simulate(num_process, edges, aux1, mc_incr, aux2, mc_printer if verbosity > 0 else None)

if __name__ == "__main__":
    assert(len(sys.argv) == 2)
    history_filename = sys.argv[1]

    n, edges = read_history(history_filename)
    mc_simulate(n, edges, 1)
