from ctypes import *
import re
import sys, getopt
import time

types = {
    "r": 0,
    "w": 1,
    "acq": 2,
    "rel": 3,
    "fork": 4,
    "join": 5,
    "other": 6
}

class Event(Structure):
    _fields_ = [
        ("type", c_int),
        ("thread", c_int),
        ("var", c_int),
        ("lock", c_int),
        ("thr2", c_int)
    ]

class Engine:

    def __init__(self, path, engine):
        self.engine = engine
        self.path = path
        self.event = Event()
        self.is_race = False
        self.thr_map = {}
        self.thr_cnt = 0
        self.var_map = {}
        self.var_cnt = 0
        self.lock_map = {}
        self.lock_cnt = 0
        self.event_cnt = 0
        
        with open(self.path, "r") as f:
            for line in f.readlines():
                self.preparse(line)
                self.event_cnt += 1

        print('number of events: %d' % (self.event_cnt))
        print('number of threads: %d' % (self.thr_cnt))
        print('number of variables: %d' % (self.var_cnt))
        print('number of locks: %d' % (self.lock_cnt))

    def init(self, clock):
        self.is_race = False
        self.cdll = cdll.LoadLibrary('./libEngine_' + self.engine + '_' + clock + '.so')
        init_detector = self.cdll.init_detector
        init_detector.argtypes = [c_int, c_int, c_int]
        init_detector(self.thr_cnt, self.var_cnt, self.lock_cnt)
    
    def free(self):
        free_detector = self.cdll.free_detector
        free_detector()

    def preparse(self, line):
        res = re.search(r"\s*(\w+)\s*\|(\w+)\((.+)\)\|.*", line)
        if(res):
            thrd = res.group(1)
            if self.thr_map.get(thrd) == None:
                self.thr_map[thrd] = self.thr_cnt
                self.thr_cnt += 1
            tpe = types[res.group(2)]
            info = res.group(3)
            if tpe == 0 or tpe == 1:
                if self.var_map.get(info) == None:
                    self.var_map[info] = self.var_cnt
                    self.var_cnt += 1
            elif tpe == 2 or tpe == 3:
                if self.lock_map.get(info) == None:
                    self.lock_map[info] = self.lock_cnt
                    self.lock_cnt += 1
            elif tpe == 4 or tpe == 5:
                if self.thr_map.get(info) == None:
                    self.thr_map[info] = self.thr_cnt
                    self.thr_cnt += 1
        else:
            print(line)
        
    def parse(self, line):
        res = re.search(r"\s*(\w+)\s*\|(\w+)\((.+)\)\|.*", line)
        if(res):
            self.event.thread = self.thr_map.get(res.group(1))
            self.event.type = types[res.group(2)]
            info = res.group(3)
            if self.event.type == 0 or self.event.type == 1:
                self.event.var = self.var_map.get(info)
            elif self.event.type == 2 or self.event.type == 3:
                self.event.lock = self.lock_map.get(info)
            elif self.event.type == 4 or self.event.type == 5:
                self.event.thr2 = self.thr_map.get(info)
            return 1
        else:
            return None

    def detect(self):
        count = 0
        t = 0
        with open(self.path, "r") as f:
            for line in f.readlines():
                if(self.parse(line)):
                    count += 1
                    detect = self.cdll.detect
                    detect.restype = c_int
                    detect.argtypes = [POINTER(Event)]
                    t1 = time.process_time()
                    res = detect(byref(self.event))
                    t2 = time.process_time()
                    t += (t2 - t1) * 100000000
                    if(res == 1):
                        self.is_race = True
                        break 
        if(self.is_race):
            print("RACE FOUND after " + str(count) + " events.")
        else:
            print("No race found after " + str(count) + " events.")
        return t / 100000.0

if __name__ == "__main__":
    opts, args = getopt.getopt(sys.argv[1:], "t:a:")
    path, algo = "", ""
    for opt, arg in opts:
        if opt == '-t':
            path = arg
        elif opt == '-a':
            algo = arg
    
    engine = Engine(path, algo)
    
    # sum = 0
    # for i in range(3):
    #     engine.init("vc")
    #     sum += engine.detect()
    #     engine.free()
    # print('vc time: %.3f ms' % (1.0 * sum / 3))

    sum = 0
    for i in range(3):
        engine.init("tc")
        sum += engine.detect()
        engine.free()
    print('tc time: %.3f ms' % (1.0 * sum / 3))

    # sum = 0 
    # for i in range(3):
    #     engine.init("ptc")
    #     sum += engine.detect()
    #     engine.free()
    # print('ptc time: %.3f ms' % (1.0 * sum / 3))
