#!/opt/local/bin/python

# assumes that Z3_DIR is set to root directory of the Z3 codebase

import os, sys
from glob import glob
import subprocess
from subprocess import STDOUT, CalledProcessError, check_output, TimeoutExpired
import time

# TO_DEF: default timeout
TO_DEF = 5

# check command-line args:
num_args = len(sys.argv)
if not (2 <= num_args and num_args <= 4):
    print >> sys.stderr, 'expects benchmark dir and optional timout'
    sys.exit(1)

# benches: all smt2 files in the given directory:
bench_dir = sys.argv[1]
benches = [ ]
for path, dirs, files in os.walk(bench_dir):
    for fn in files:
        if fn.endswith(".smt2"):
            benches.append(os.path.join(path, fn))

# get filename of z3
z3_dir = os.environ['Z3_DIR']
z3 = z3_dir + "/build/z3"
writeFileName = sys.argv[3]
writeFile = open ("%s" %writeFileName,'w+')
# set timeout:
timeout = TO_DEF
if num_args == 3:
    timeout = sys.argv[2]

# for each benchmark:
for bench in benches:
    # run z3 on benchmark
	writeFile.write("running z3")
	writeFile.flush()
	try:
		start = time.time()
		run_out = check_output([ z3, bench ], stderr=STDOUT, timeout=timeout)
		run_txt = run_out.decode(sys.stdout.encoding)
		has_sat = "sat" in run_txt
		has_unsat = "unsat" in run_txt
		if has_sat:
			if has_unsat:
				res = "UNSAT"
			else:
				res = "SAT"
		else:
			res = "UNK"
		writeFile.write("unk output:%s" % run_txt)
		writeFile.write("\n")
		writeFile.flush()
		bench_time = "{:.3f}".format(time.time() - start)
	except CalledProcessError:
		res = "ERR"
		bench_time = "NA"
	except TimeoutExpired:
		# case: timed out:
		res = "NA"
		bench_time = "TO"
	 # print line of the CSV:
	writeFile.write(",%s-%s-%sS" %(os.path.basename(bench),res,bench_time))
	writeFile.write("\n")
	writeFile.flush()

