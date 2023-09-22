import sys, getopt
import os

pathfile = "paths"

def generatePath():
    w = os.walk("benchmarks")
    with open(pathfile, "w") as f:
        for (dirpath, dirnames, filenames) in w:
            for filename in filenames:
                if "std" in filename:
                    f.write(dirpath + "/" + filename[:-4] + '\n')

def unzip():
    with open(pathfile, "r") as f:
        for filename in f.readlines():
            dir = "/".join(filename[:-1].split("/")[:-1])
            print(dir)
            os.system("unzip " + filename[:-1] + ".zip -d " + dir)
            os.system("rm " + filename[:-1] + ".zip")

def generatePBS():
    if not os.path.exists("pbsf"):
        os.mkdir("pbsf")
    if not os.path.exists("resultsf"):
        os.mkdir("resultsf")
    with open(pathfile, "r") as f:
        for filename in f.readlines():
            name = filename[:-1].replace("/", "-")
            with open("pbsf/" + name + ".pbs", "w") as pbsFile:
                pbsFile.write("#!/bin/bash\n\n")
                pbsFile.write("#PBS -q largemem\n")
                pbsFile.write("#PBS -P Personal\n")
                pbsFile.write("#PBS -l select=1:ncpus=1:mem=400gb\n")
                pbsFile.write("#PBS -l walltime=10:00:00\n")
                pbsFile.write("#PBS -j oe\n")
                pbsFile.write("#PBS -o resultsf/" + name + "\n\n")

                pbsFile.write("module load python\n")
                pbsFile.write("cd $PBS_O_WORKDIR\n")
                pbsFile.write("python engine.py -t ~/scratch/TreeClock/" + filename[:-1] + ".std -a hb\n")


def submit(index):
    if index == 1:
        start, end = 0, 80
    else:
        start, end = 81, 156

    cnt = 0
    for filename in os.listdir("pbsf"):
        if start <= cnt <= end:
            os.system("qsub pbsf/" + filename)
        cnt += 1


if __name__ == "__main__":
    opts, args = getopt.getopt(sys.argv[1:], "m:")
    for opt, arg in opts:
        if opt == '-m':
            if arg == "generatePath":
                generatePath()
            elif arg == "unzip":
                unzip()
            elif arg == "generatePBS":
                generatePBS()
            elif arg == "submit1":
                submit(1)
            elif arg == "submit2":
                submit(2)
            
