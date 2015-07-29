#! /usr/bin/env python

# --------------------------------------------------------------------
import sys, os, subprocess as sp, resource

# --------------------------------------------------------------------
ROOT  = os.path.join(os.path.dirname(__file__), '..')
ARLC  = os.path.realpath(os.path.join(ROOT, 'arlc'))
EXPL  = os.path.realpath(os.path.join(ROOT, 'examples/popl'))
FILES = [
  'histogram',
  'dummysum',
  'noisysum',
  'two-level-a',
  'two-level-b',
  'binary',
  'idc',
  'dualquery',
  'competitive-b',
  'competitive',
  'fixedprice',
  'summarization',
]

# --------------------------------------------------------------------
def countlines(filename):
    with open(filename) as stream:
        contents = [x.strip() for x in stream.readlines()]
        contents = [x for x in contents if x]
    return len(contents)

# --------------------------------------------------------------------
def _main():
    benchs  = []
    rusage0 = resource.getrusage(resource.RUSAGE_CHILDREN)

    for name in FILES:
        print 'Benchmarking %s' % name
        filename = os.path.join(EXPL, name + '.rlc')
        status   = sp.call([ARLC, '-L examples/popl', filename], cwd=ROOT)
        count    = countlines(filename)
        rusage   = resource.getrusage(resource.RUSAGE_CHILDREN)
        time     =   (rusage.ru_stime - rusage0.ru_stime) \
                   + (rusage.ru_utime - rusage0.ru_utime)
        rusage0  = rusage

        benchs.append((name, status == 0, count, time))

    width = max([len(x[0]) for x in benchs if x[1]])
    for name, ok, count, time in benchs:
        if not ok: continue
        print '{\\tt %-*s} & %3d & %4.2f s.\\\\' % (width, name, count, time)

# --------------------------------------------------------------------
if __name__ == '__main__':
    _main()
