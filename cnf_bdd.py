#!/usr/bin/python3
from pyeda.inter import *
import sys
sys.setrecursionlimit(10000)

class cnf_encoder:
    def __init__(self, infile, outfile):
        self.infile = infile
        self.outfile = outfile
        self.puzzle = []
        self._read_file()
    def _call_c(self):
        from subprocess import run
        run(['./a.out', self.infile])
    def _read_file(self):
        f = open(self.infile, 'r')
        for line in f:
            words = line.strip().split()
            row = []
            for word in words:
                row.append(int(word))
            self.puzzle.append(row)
        f.close()
    def print_puzzle(self):
        for row in self.puzzle:
            print(row)
    def gen_bddexp(self):
        self._call_c()
        f = open('sat_in')
        _ = f.readline()
        exp = ''
        for line in f:
            line = line.strip().split()
            exp += '('
            for var in line:
                if var == '0':
                    exp = exp[:-1] + ')'
                else:
                    if int(var) > 0:
                        exp += 'v' + var + '|' 
                    else:
                        exp += '~v' + str(-int(var)) + '|'
            exp += '&'
        exp = exp[:-1]
        self.bddexp = expr(exp)
    def write_count(self):
        f = open(self.outfile, 'w')
        f.write(str(self.bddexp.satisfy_count()))
        f.close()

def main(argv):
    enc = cnf_encoder(argv[0], argv[1])
    enc.gen_bddexp()
    enc.write_count()

if __name__ == '__main__':
    main(sys.argv[1:])
