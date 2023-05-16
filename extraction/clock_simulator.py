from matrix_clock import *

def clock_simulate(num_process, edges, clock_init, clock_incr, clock_join):
    local_clocks = [clock_init() for _ in range(num_process)]
    
    for snd, _, rcv, _ in edges:
        snd -= 1
        rcv -= 1
        local_clocks[snd] = clock_incr(local_clocks[snd], snd)
        local_clocks[rcv] = clock_incr(local_clocks[rcv], rcv)
        local_clocks[rcv] = clock_join(local_clocks[snd], local_clocks[rcv], snd, rcv)

    return local_clocks

def mc_simulate(num_process, edges):
    def aux1():
        return mc_init(num_process)
    def aux2(mc1, mc2, snd, rcv):
        return mc_join(num_process, mc1, mc2, snd, rcv)
    return clock_simulate(num_process, edges, aux1, mc_incr, aux2)
