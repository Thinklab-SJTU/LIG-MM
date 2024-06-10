import os
import queue
import re
import sys
import time
import argparse
import logging
from datetime import datetime
from transformers import AutoTokenizer, AutoModelForCausalLM
from z3 import Solver, Bool, Implies, And, Or, sat
import torch

from sol_input_gen import concatenate_solver_files
from sym_input_gen import concatenate_symbolic_files

# sys.path.append('./llm')
from run_llm import use_llm, add_segment_for_solver, find_variable
from utils import remove_space, refine_output, refine_case, finetune_instance, undo_rename_special_variables


def inv_choose(nodes, edge, name):
    s = Solver()
    node_vars = {node: Bool(node) for node in nodes}
    for edge in edges:
        if edge[1] == 'AND':
            t = True
            for i in edge[2]:
                t = And(t, node_vars[i])
            s.add(Implies(node_vars[edge[0]], t))
        elif edge[1] == 'OR':
            t = False
            for i in edge[2]:
                t = Or(t, node_vars[i])
            s.add(Implies(node_vars[edge[0]], t))
        else:
            t = node_vars[edge[0]]
            for i in edge[2]:
                t = And(t, node_vars[i])
            s.add(t)

    result = s.check()
    if result == sat:
        count = 0
        model = s.model()
        inv = ''
        for node in name:
            if model[node_vars['p' + name[node]]] == True:
                if count == 0:
                    inv += node + '\n'
                else:
                    inv += '||' + node + '\n'
                count = count + 1
    else:
        inv = 'Nothing'
    return inv


def extract_variable_names(c_code):
    pattern = r'\b((int|char|float|double|struct\s+\w+)\s+[*]?\s*(\w+))'
    matches = re.findall(pattern, c_code)
    variable_names = [match[2] for match in matches]
    return variable_names


def program_variable_output(path):
    with open(path + 'variable_use.txt') as infile:
        parts = infile.read().split(';')
    parts[1:] = extract_variable_names('; '.join(parts[1:]))
    parts[1:] = [';'.join(parts[1:])]
    return 'Code ' + parts[1] + ';\n'


def bfs_call_f(f, start, max_step, path):
    q = queue.Queue()
    q.put((start, 0))
    son = {}
    id = {}
    name = {}
    id[start] = [0]
    while not q.empty():
        current, step = q.get()
        if step > max_step:
            son[current] = []
            continue
        neighbors, flag = f(current, path)
        if flag == 2:  # fail in execution
            with open(path + 'Igen.txt', 'w') as outfile:
                outfile.write("fail in execution\n")
            return ({}, {})
        son[current] = neighbors
        if flag == 1:
            continue
        if flag == 3:
            continue
        count = 0
        for neighbor in neighbors:
            id[neighbor] = id[current].copy()
            id[neighbor][0] = id[neighbor][0] + 1
            if len(neighbors) > 1:
                count = count + 1
                id[neighbor].append(count)
            if neighbor not in son:
                q.put((neighbor, step + 1))
    for key in id:
        name[key] = 'I'
        for i in id[key]:
            name[key] = name[key] + '_' + str(i)
    with open(path + 'Igen.txt', 'w') as outfile:
        outfile.write(program_variable_output(path))
        for key in son:
            key_ = remove_space(key)
            print(name[key], key_)
            outfile.write(name[key] + ': ' + key_ + ';\n')
    return (name, son)


def parse_sym_output(results):
    now = ''
    answer = []
    if results == '':
        return ([], 1)
    if results.find("fail in Inv entail") != -1:
        stop_flag = 0
        results = results.splitlines()
        for i in results[1:]:
            if i == 'try entail':
                answer.append(now)
                now = ''
            elif i == "-------------------------":
                now = ''
            elif i == "End":
                now = ''
            else:
                now = now + i
    elif results.find('Invariant PASS:') != -1:
        stop_flag = 1
        results = results.splitlines()
        for i in results[1:]:
            if i == 'try entail':
                answer.append(now)
                now = ''
            elif i == "End":
                now = ''
            elif i == "-------------------------":
                now =''
            else:
                now = now + i
    elif results.find('Dead') != -1:
        stop_flag = 3
    else:
        stop_flag = 2
        sys.exit("Execution failed")
    return (answer, stop_flag)

def parse_sol_output(results):
    pre = ''
    post = ''
    res = ''
    succ = []
    fail = []
    flag = -1
    mark = -1
    results = results.replace('End solver\n', '')
    results = results.replace('execution finished ', '')
    results = results.replace('==========================', '')
    results = results.splitlines()
    for message in results:
      if message == '':
        continue 
      if message == 'Success entail':
        flag = 1
        mark = 0
        pre = ''
        post = ''
        res = ''
        continue
      if message == 'Fail to entail':
        flag = 0
        mark = 0
        pre = ''
        post = ''
        res = ''
        continue 
      if message == '-------------------------':
        if flag == 1:
          succ.append((pre,post,res))
        elif flag == 0:
          fail.append((pre,post,res))
        continue
      if message == 'try entail':
        mark = 1
        continue 
      if message == 'Res':
        mark = 2
        continue 
      if mark == 0:
        pre = pre + message
      elif mark == 1:
        post = post + message
      elif mark == 2:
        res = res + message
    return (succ, fail)

def rename_exists(input_string):
    # 使用正则表达式匹配变量，并替换为对应的 v__i 形式
    def repl(m):
        nonlocal count
        count += 1
        return f"v__{count}"

    # 找到 exists 后的变量部分
    exists_match = re.search(r'exists\s+([^,]+)', input_string)
    if exists_match:
        variables_chunk = exists_match.group(1)
        variables = variables_chunk.split()

        # 替换变量为 v__i 形式
        count = 0
        replacement_map = {}  # 用于存储变量和对应的替换形式
        for var in variables:
            count += 1
            replacement_map[var] = f"v__{count}"

        # 替换字符串中的变量
        for var, repl_str in replacement_map.items():
            input_string = re.sub(rf"\b{var}\b", repl_str, input_string)

    return input_string

def symbolic(x, path):
    with open(path + 'assertion.txt', 'w') as outfile:
        outfile.write(rename_exists(x))
    concatenate_symbolic_files(path)
    os.system("python3 ../symbolic/split.py {}sym_input.txt > ../symbolic/sym_input.txt".format(path))
    os.system("./../symbolic/asymexe ../symbolic/sym_input.txt > {}sym_output.txt".format(path))
    with open(path + "sym_output.txt") as infile:
        results = infile.read()
    return parse_sym_output(results)

def check_entail(nodes, path):
    entail_rel = {}
    for node in nodes:
        entail_rel[node] = []
    for node in nodes:
        with open(path + 'assertions.txt', 'w') as outfile:
            outfile.write('/*@ ' + node + '*/\n')
            outfile.write(' '.join(['/*@ ' + node0 + '*/\n' for node0 in nodes]))
        concatenate_solver_files(path)
        os.system("python3 ../symbolic/split.py {}sol_input.txt > ../solver/sol_input.txt".format(path))
        os.system("./../solver/full_solver ../solver/sol_input.txt > {}sol_output.txt".format(path))
        with open(path + 'sol_output.txt') as infile:
            results = infile.read().split('==========================')
        for i in range(len(results)):
            if results[i].count('emp') == 1:
                entail_rel[nodes[i]].append(node)
    return entail_rel

def entailment_solver(pre, inv, inv_post):
    with open(path + 'assertions.txt', 'w') as outfile:
        outfile.write('/*@ ' + inv + '*/\n')
        outfile.write('/*@ ' + pre + '*/\n')
        outfile.write('/*@ ' + inv_post[0] + '*/\n')
    concatenate_solver_files(path)
    os.system("python3 ../symbolic/split.py {}sol_input.txt > ../solver/sol_input.txt".format(path))
    os.system("./../solver/full_solver ../solver/sol_input.txt > {}sol_output.txt".format(path))
    with open(path + 'sol_output.txt') as infile:
        results = infile.read().split('==========================')
    return results

def get_code(assertions):
    out = code_head
    i = 0
    for assertion in assertions:
        out = out + "I_{}: ".format(i) + assertion + ";\n"
        i = i+1
    return out

def use_solver(input, segment, model_output, v_list=None):
    # input: the collection of invariants
    # segment: the segment to be eliminated
    # model_output: the segments that have been eliminated, not include the output. Set it for [] if not needed.
    
    input = input[input.find("\n") + 1:]
    input_data = ""
    if v_list is None:
        code_head = program_variable_output(path)
        v_list = code_head[code_head.find(" ") + 1:-2].split(';')
    for v in v_list:
        input_data += "*{}".format(v)
        if not v == v_list[-1]:
            input_data += ','
        else:
            input_data += ';\n'
    
    input_data = '/*@ {} */\n'.format(segment)
    if input_data.find("OUTPUT") != -1:
      input_data = ''
    invs = input.split('\n')
    for inv in invs[:-1]:
        if inv == "":
            continue
        inv_ = inv[inv.find(":") + 1:].replace(';', '')
        inv_ = add_segment_for_solver(inv_, model_output)
        if inv_.find("OUTPUT") != -1:
          continue
        input_data += '\n/*@' + inv_ + '*/\n'
    with open(path + 'assertions.txt', 'w') as outfile:
        outfile.write(input_data)

    concatenate_solver_files(path)
    os.system("python3 ../symbolic/split.py {}sol_input.txt > ../solver/sol_input.txt".format(path))
    os.system("./../solver/key_solver ../solver/sol_input.txt > {}sol_output.txt".format(path))
    with open(path + 'sol_output.txt') as infile:
        output = infile.read()
    # check the status after the solver. 0 for fail, 1 for success, 2 for end
    # if the Fail to entail is less than 2, it is success. Otherwise, it is fail.
    # if the number of emp is larger than len(invs) - 2, it is end.
    succ, fail = parse_sol_output(output)
    print(succ, fail)

    def get_sep(str):
        ret = str[str.rfind("&&")+2:]
        while ret[0] == ' ':
            ret = ret[1:]
        ret = ret.replace(" ","")
        return ret

    new_succ = []
    for pre, post, res in succ:
        segs = res.split("*")
        vis = {}
        flag = True
        for seg in segs:
            sseg = get_sep(seg)
            if sseg in vis:
                flag = False
                break
            else:
                vis[sseg] = True
        if flag == True:
            new_succ.append((pre, post, res))
        else:
            fail.append((pre, post, pre))

    succ = new_succ
    logger.info("-----------After elimation:-----------")
    logger.info("succ:")
    for asser in succ:
        logger.info("(" + asser[0] + ") , (" + asser[1] + ") , (" + asser[2] + ")")
    logger.info("fail:")
    for asser in fail:
        logger.info("(" + asser[0] + ") , (" + asser[1] + ") , (" + asser[2] + ")")
    logger.info("--------------------------------------\n")
    out_1 = code_head
    i = 0
    seps = {}
    now_sep = ""
    total = 0
    for pre, post, res in succ:
        out_1 = out_1 + "I_{}: ".format(i) + res + ";\n"
        now_sep = get_sep(res)
        if now_sep == "emp":
            continue
        now_sep = now_sep.replace(" ","")
        if now_sep in seps:
            seps[now_sep].append(i)
        else:
            total = total + 1
            seps[now_sep] = [i]
        i = i+1
    out_sep = []
    for key, val in seps.items():
        if len(val) == 1:
            out_sep.append(val[0])
    flag = False
    sep = []
    if total <= 4:
        flag = True
        for key, val in seps.items():
            if len(val) == 1:
                continue
            sep.append(key)

    out_2 = code_head
    i = 0
    for pre, post, res in fail:
        out_2 = out_2 + "I_{}: ".format(i) + pre + ";\n"
        i = i+1
    # succ：消成功的断言pre post res；fail：消去失败的

    status = 1 # 可以消去部分但还没消完
    if (succ == []) and (fail != []):
        status = 0 #没有能消成功的
    elif total == 0:
        status = 2 #消完了
    
    return status, out_1, out_2, flag, sep, out_sep

def check1(input_code, seg):
    input_code = input_code.split("\n")
    input_code = input_code[1:]
    while input_code[-1].find('I') == -1:
        input_code = input_code[:-1]
    for assertion in input_code:
        if assertion.find(seg) == -1:
            return False
    return True

def check2(input_code, seg, seg2):
    input_code = input_code.split("\n")
    input_code = input_code[1:]
    while input_code[-1].find('I') == -1:
        input_code = input_code[:-1]
    for assertion in input_code:
        if assertion.find(seg) == -1 and assertion.find(seg2) == -1:
            return False
    return True

def check(input_code, segs, f): # f==True: 表示是!=0这种的等式
    input_code = input_code.split("\n")
    input_code = input_code[1:]
    while input_code[-1].find('I') == -1:
        input_code = input_code[:-1]
    total = len(input_code)
    cnt = 0
    for assertion in input_code:
        flag = False
        for seg in segs:
            if assertion.find(seg) != -1:
                flag = True
                break
        if flag == True: #含有该等式
            cnt += 1
        elif f == False:
            return False
    if f == True: # !=0这种，大于1就行
        if cnt >= 2:
            return True
        else:
            return False
    return True

others = []

def add_repeating_segs(guess, repeat):
    var_list = find_variable(guess)
    
    new_var_list = []
    for var in var_list:
        if var.find("u_") == -1:
            new_var_list.append(var)
    var_list = new_var_list
    repeat = repeat + "&&"
    while repeat.find("&&") != -1:
        now_seg = repeat[:repeat.find("&&")]
        repeat = repeat[repeat.find("&&")+2:]
        now_var = now_seg
        if now_var.find('(') != -1:
            now_var = now_var[now_var.find('('):]
        flag = False
        for var in var_list:
            if now_var.find(var) != -1:
                flag = True
                break
        if flag == True:
            if now_seg.find("==") != -1 or now_seg.find("!=") != -1:
                guess = now_seg + "&&" + guess
            else:
                guess = guess + "*" + now_seg
    return guess

def add_repeating_segs_2(guess, input_code, var_list):
    repeat = input_code.split("\n")
    repeat = repeat[1]
    repeat = repeat[repeat.find(':')+2:]
    while repeat.find("&&") != -1:
        now_seg = repeat[:repeat.find("&&")]
        if now_seg.find('exists') != -1:
            now_seg = now_seg[now_seg.find(',')+1:]
        repeat = repeat[repeat.find("&&")+2:]
        if now_seg.find(',') != -1:
            now_seg = now_seg[now_seg.find(',')+1:]
        if now_seg.find('*') != -1: #
            now_seg = now_seg[:now_seg.find('*')] #
        print("!!! now_seg: ", now_seg)
        if now_seg.find(var_list[0]) != -1 or now_seg.find(var_list[1]) != -1:
            segs = []
            f = False
            pattern = re.compile('[a-zA-Z]==[a-zA-Z]')
            if (re.match(pattern, now_seg)): # a==b
                a = now_seg[:now_seg.find("==")]
                b = now_seg[now_seg.find("==")+2:]
                segs = [now_seg, b+"=="+a]
            pattern = re.compile('[a-zA-Z]!=[a-zA-Z]')
            if (re.match(pattern, now_seg)): # a!=b
                a = now_seg[:now_seg.find("!=")]
                b = now_seg[now_seg.find("!=")+2:]
                segs = [now_seg, b+"!="+a]
            pattern = re.compile('[a-zA-Z]==0')
            if (re.match(pattern, now_seg)): # a==0
                a = now_seg[:now_seg.find("==")]
                segs = [now_seg]
            pattern = re.compile('[a-zA-Z]!=0')
            if (re.match(pattern, now_seg)): # a!=0
                a = now_seg[:now_seg.find("!=")]
                segs = [now_seg]
                f = True
            
            if check(input_code, segs, f):
                guess = now_seg + "&&" + guess
    return guess


def new_guess_inv(assertions_set):
    llm_time = 0
    solver_time = 0
    if assertions_set.find("I") == -1: #没有断言
        return '', llm_time, solver_time

    input_code = assertions_set
    for i in range(10):
        new_input_code, v_map = refine_case(assertions_set, pointer_mode=1)
        while new_input_code[-1] == '\n':
            new_input_code = new_input_code[:-1]
        new_input_code += "\n"

        logger.info("------------begin using llm:-----------")
        t0 = time.time()
        seg = use_llm(model, tokenizer, model_path=None, input=new_input_code)
        seg = undo_rename_special_variables(seg, v_map)
        if seg[-1] == '\n':
            seg = seg[:-1]
        t1 = time.time()
        logger.info("seg: {}".format(seg))
        seg = refine_output(seg)
        logger.info("seg_2: {}".format(seg))
        guessing_seg = seg[seg.find('<|OUTPUT1|>')+11:seg.find('<|OUTPUT2|>')]
        repeating_seg = seg[seg.find('<|OUTPUT2|>')+11:]
        if guessing_seg.find("lseg")!=-1:
            pos = guessing_seg.find("lseg")
            if pos==0 or guessing_seg[pos-1]!='d': # lseg且不是dlseg
                a = guessing_seg[pos + 5 : guessing_seg[5:].find(',')]
                b = guessing_seg[guessing_seg[5:].find(',')+1 : guessing_seg[5:].find(')')]
                r2 = add_repeating_segs_2(guessing_seg, new_input_code, [a, b])
                guessing_seg = undo_rename_special_variables(r2, v_map)
                if guessing_seg[-1] == '\n':
                    guessing_seg = guessing_seg[:-1]

        if guessing_seg.find('u_2')!=-1:
            guessing_seg = "exists u_1 u_2, " + guessing_seg
        elif guessing_seg.find('u_1')!=-1:
            guessing_seg = "exists u_1, " + guessing_seg
        r1 = add_repeating_segs(guessing_seg, repeating_seg)
        guessing_seg = undo_rename_special_variables(r1, v_map)
        if guessing_seg[-1] == '\n':
            guessing_seg = guessing_seg[:-1]
        logger.info("--->llm's guessing_seg: "+guessing_seg)
        logger.info("---------------------------------------")
        test = use_solver(input_code, guessing_seg, model_output=[])
        t2 = time.time()

        llm_time += t1 - t0
        solver_time += t2 - t1
        if test[5] != []:
            global others
            others.extend(test[5])
        if test[0] == 0: #一个都消不掉，没成功，继续找
            continue
        if test[0] == 2: #全部消完，不用递归找了
            return guessing_seg, llm_time, solver_time
        if test[3] == True: #剩最后一个，消完
            print("*** test[4]: ", test[4])
            if test[4] != []:
                result = ""
                for x in test[4]:
                    result = result + guessing_seg + "*" + x + "||"
                result = result[:-2]
                return result, llm_time, solver_time
            else:
                return guessing_seg, llm_time, solver_time
        # 可以消去部分
        inv_1, t00, t01 = new_guess_inv(test[1]) #succ部分，消去之后继续找下一个inv
        inv_2, t10, t11 = new_guess_inv(test[2]) #fail部分，无法消去，也继续找下一个inv
        llm_time += t00 + t10
        solver_time += t01 + t11
        out = ""
        if inv_1 != "":
            out = inv_1 + "*" + guessing_seg, llm_time, solver_time
        else:
            out = guessing_seg, llm_time, solver_time
        if inv_2 != "":
            out = out + " || (" + inv_2 + ")"
        return out, llm_time, solver_time
    return '', llm_time, solver_time

def add_exists(input_string):
    pattern = re.compile(r'__[0-9]\d*')
    f = re.findall(pattern, input_string)
    f = list(dict.fromkeys(f))
    if f == []:
        return input_string
    add_var = ' '.join(f)
    out_string = "exists "
    if input_string.find('exists') != -1:
        out_string += add_var + input_string[6:]
    else:
        out_string += add_var + ',' + input_string
    return out_string

def guess_inv():
    logger.info("----------start guessing invariant:----------")
    with open(path + 'Igen.txt') as infile:
        input = infile.read()
    
    assertions = input.split('\n')
    assertions = assertions[1:]
    ori = [] #ori: 原来的断言
    logger.info("original assertions:")
    for x in assertions:
        x = x[x.find(":")+2:-1]
        ori.append(x)
        logger.info(x)
    
    global others
    others = []
    new_assertion, llm_time, solver_time = new_guess_inv(input)

    other_str = ""
    for x in others:
        other_str = other_str + ori[x] + "||"
    new_assertion = other_str + new_assertion
    if new_assertion != "" and new_assertion[-1] == '|':
        new_assertion = new_assertion[:-2]
    
    
    segs = new_assertion.split('||')
    pro_assertion = ""
    for seg in segs:
        pro_assertion += add_exists(seg) + '||'
    
    pro_assertion = pro_assertion[:-2]

    return pro_assertion, llm_time, solver_time



if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument("--path", default = 'SLING/changed_codes/sll/find', type=str, help = "the path of the example")
    parser.add_argument("--epochs", default=8, type=int, help="the number of training epochs")
    parser.add_argument("--size", default=250000, type=int, help="data size")
    parser.add_argument("--op", default = "listrep1-lseg5-dlistrep1-dlseg10-listbox_seg5-ptree_rep0-llistrep0-llseg0-output1-pointer1-noise1", type = str, help = "the name of model")
    parser.add_argument('--log_method', default = 'default', help = 'method of logging')

    args = parser.parse_args()

    path = '../dataset/' + args.path + '/'
    op = args.op
    num_train_epochs = args.epochs
    data_size = args.size
    model_path = '../model/try-codegen-{}-{}-{}'.format(op, num_train_epochs, data_size)
    device = torch.device("cuda" if torch.cuda.is_available() else "cpu")
    model = AutoModelForCausalLM.from_pretrained(model_path).to(device)
    tokenizer = AutoTokenizer.from_pretrained(model_path)

    TEST_CASE = 'test_' + args.path + '_' + 'try-codegen-{}-{}-{}'.format(op, num_train_epochs, data_size)
    log_dir = "../log/" + args.path + "/"
    if not os.path.exists(log_dir):
        os.makedirs(log_dir)
    logger = logging.getLogger('invgen')
    logger.setLevel(logging.DEBUG)
    if args.log_method == 'time':
        log_path = os.path.join(log_dir, datetime.now().strftime('%Y%m%d-%H%M%S'))
    else:
        log_path = os.path.join(log_dir, 'log')
        with open(log_path + '.log', 'w') as file:
            file.truncate()
    fh = logging.FileHandler(log_path + ".log")
    fh.setLevel(logging.DEBUG)
    sh = logging.StreamHandler()
    sh.setLevel(logging.INFO)
    logger.addHandler(fh)
    logger.addHandler(sh)

    logger.info(TEST_CASE)

    with open(path + 'I0.txt') as infile:
        start = infile.read()
    t0 = time.time()
    logger.info(t0)
    name, son = bfs_call_f(symbolic, start, 2, path)

    nodes = [key for key in son]
    t1 = time.time()
    logger.info(t1)
    new_assertion, llm_time, solver_time = guess_inv()
    t2 = time.time()
    logger.info(t2)
    logger.info("pre_time: {}".format(t1 - t0))
    logger.info("running_time: {}".format(t2 - t1))
    logger.info("llm_time: {}".format(llm_time))
    logger.info("solver_time: {}".format(solver_time))
    other_str = ""    

    logger.info("----------guessing invariant:----------")
    if new_assertion == "":
        logger.info('\n')
    else:
        logger.info(new_assertion)
    logger.info("---------------------------------------")
    name[new_assertion] = 'I_new'
    nodes.append(new_assertion)

#-----------------------------------------

    entail_rel = check_entail(nodes, path)

    edges = [('c' + name[nodes[0]], "SINGLE", ['c' + name[s] for s in nodes[1:]]),
             ('cI_new', 'OR', ['p' + name[s] for s in entail_rel[new_assertion]]), ('pI_new', 'AND', ['cI_new'])]
    nodes = ['c' + name[key] for key in nodes] + ['p' + name[key] for key in nodes]
    for key in son:
        edges.append(('c' + name[key], 'OR', ['p' + name[s] for s in entail_rel[key]]))
        if son[key] == []:
            continue
        edges.append(('p' + name[key], 'AND', ['c' + name[s] for s in son[key]]))

    inv = new_assertion
    if inv == 'Nothing':
        logger.info("Guess Fail!!!!!!")
    else:
        Success_Guess = True
        inv_1 = inv + '||'
        while inv_1.find('||') != -1:
            pos = inv_1.find('||')
            inv_now = inv_1[:pos]
            inv_post, flag = symbolic(inv_now, path)
            results = entailment_solver(start, inv_now, inv_post)
            flag = False
            for i in results:
                if i.find("Success entail") != -1:
                    flag = True
            if flag == False:
                Success_Guess = False
                break
            inv_1 = inv_1[pos+2:]
        logger.info("-------------Guess result:-------------")
        if Success_Guess:
            logger.info("SUCCESS GUESS!!!")
        logger.info("---------------------------------------")