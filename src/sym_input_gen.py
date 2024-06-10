import os

def concatenate_symbolic_files(path):
    file_list = ['spec_def.txt', 'call_func.txt','variable_use.txt', 'local_variable.txt', 'assertion.txt', 'post_assertion.txt', 'loop_body.txt']
    # dir_path = os.path.dirname(os.path.realpath(__file__))
    dir_path = path = path
    with open(os.path.join(dir_path, 'sym_input.txt'), 'w') as outfile:
        for fname in file_list:
            with open(os.path.join(dir_path, fname)) as infile:
              if fname == 'variable_use.txt':
                parts = infile.read().split(';')
                parts[1:] = [', '.join([s.strip() for s in parts[1:]])]
                if parts[1][-2] == ',':
                    parts[1] = parts[1][:-2]
                outfile.write(parts[0] + 'Invgen(' + parts[1] + ')')
              elif fname == 'local_variable.txt':
                if os.stat(os.path.join(dir_path, fname)).st_size == 0:
                  outfile.write('/*@')
                else: 
                  outfile.write('/*@ With ' + infile.read())
              elif fname == 'assertion.txt':
                 outfile.write('\t\tRequire ' + infile.read()) 
              elif fname == 'post_assertion.txt':
                 outfile.write('\t\tEnsure ' + infile.read() + '\n*/\n{')
              elif fname == 'loop_body.txt':
                 outfile.write(infile.read())
              else:
                outfile.write(infile.read())
              outfile.write('\n')
        outfile.write('\n}\n')
    print('Symbolic file generate successfully!')

if __name__ == '__main__':
  concatenate_symbolic_files()
