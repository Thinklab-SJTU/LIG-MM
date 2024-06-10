import sys
from partialstmt import *

if __name__ == '__main__':
    if len(sys.argv) != 2:
        print('Usage: split.py <file>')
        sys.exit(1)
    filename = sys.argv[1]
    pslist = []
    with open(filename, 'r') as f:
        src = f.read()
        base = 0
        while base < len(src):
            base, psl = segment_process_ps(src, base)
            pslist += psl
            base += 1
    for (i, ps) in enumerate(pslist):
        if len(ps) > 0:
            print(ps)
            if i < len(pslist) - 1:
                print("\n$\n")