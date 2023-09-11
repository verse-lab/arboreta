from ctypes import *
from random import random
import re

types = {
    "Rd": 0,
    "Wr": 1,
    "Acquire": 2,
    "Release": 3,
    "Fork": 4,
    "Join": 5,
    "Other": 6
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
        self.count = 0
        self.is_race = False
        self.var_map = {}
        self.var_cnt = 0
        self.lock_map = {}
        self.lock_cnt = 0

        self.cdll = cdll.LoadLibrary('./Engine_' + engine + '.so')
        init_detector = self.cdll.init_detector
        init_detector()
    
    def parse(self, line):
        res = re.search(r"\s*@\s*(\w+)\((\d+),\s*(\S+)\)\s*", line)
        if(res):
            self.event.type = types[res.group(1)]
            self.event.thread = int(res.group(2))
            info = res.group(3)
            if self.event.type == 0 or self.event.type == 1:
                if self.var_map.get(info) == None:
                    self.var_map[info] = self.var_cnt
                    self.var_cnt += 1
                self.event.var = self.var_map.get(info)
            elif self.event.type == 2 or self.event.type == 3:
                if self.lock_map.get(info) == None:
                    self.lock_map[info] = self.lock_cnt
                    self.lock_cnt += 1
                self.event.lock = self.lock_map.get(info)
            elif self.event.type == 4 or self.event.type == 5:
                self.event.thr2 = int(info)
            return 1
        else:
            return None

    def detect(self):
        with open(self.path, "r") as f:
            for line in f.readlines():
                if(self.parse(line)):
                    self.count += 1
                    detect = self.cdll.detect
                    detect.restype = c_int
                    detect.argtypes = [POINTER(Event)]
                    if(detect(byref(self.event)) == 1):
                        self.is_race = True
                        break 
        if(self.is_race):
            print("RACE FOUND after " + str(self.count) + " events.")
        else:
            print("No race found after " + str(self.count) + " events.")

engine = Engine("traces/trace", "ft")
engine.detect()

