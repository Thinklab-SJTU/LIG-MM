import os

def concatenate_solver_files(path):
    file_list = ['spec_def.txt','variable_use.txt', 'local_variable.txt', 'assertions.txt']
    # dir_path = os.path.dirname(os.path.realpath(__file__))
    dir_path = path
    with open(os.path.join(dir_path, 'sol_input.txt'), 'w') as outfile:
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
                outfile.write('\n Require emp \n Ensure emp \n */ \n{\n')
              else:
                outfile.write(infile.read())
                outfile.write('\n')
            outfile.write('\n')
        outfile.write('}\n')
    print('Solver input file generate successfully!')

if __name__ == '__main__':
  concatenate_solver_files(".")
