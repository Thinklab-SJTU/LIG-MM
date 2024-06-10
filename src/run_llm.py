import os

import numpy as np
from transformers import AutoTokenizer, AutoModelForCausalLM
import torch
from utils import remove_space, get_test_cases, refine_case, get_test_cases_from_file, undo_rename_special_variables, refine_output

program = '../../solver/asolver'
data_header_dlseg = 'struct list {\nint head;\nstruct list *tail;\nstruct list *next;\nstruct list *prev;\n};\n$\n/*@ Let listrep(l) = l == 0 && emp ||\nexists t, data_at(field_addr(l, tail), t) * listrep(t)\n*/\n$\n/*@ Let lseg(x, y) = x == y && emp ||\nexists z, data_at(field_addr(x, tail), z) * lseg(z, y)\n*/\n$\n/*@ Let dlseg(x, xp, yp, y) = x == y && xp == yp && emp || exists z, data_at(field_addr(x, next), z) * data_at(field_addr(x, prev), xp) * dlseg(z, x, yp, y)\n*/\n$\n/*@ Let dlistrep(l, p) = l == 0 && emp ||exists t, data_at(field_addr(l, next), t) *data_at(field_addr(l, prev), p) *dlistrep(t, l)\n*/\n'
data_header_lseg = 'struct list {\nint head;\nstruct list *tail;\n};\n$\n/*@ Let listrep(l) = l == 0 && emp ||\nexists t, data_at(field_addr(l, tail), t) * listrep(t)\n*/\n$\n/*@ Let lseg(x, y) = x == y && emp ||\nexists z, data_at(field_addr(x, tail), z) * lseg(z, y)\n*/\n'


# def finetune(line):
#     if 'exists' in line:
#         temp_list = line[0:line.find(',')].split(' ')
#         for temp in temp_list:
#             if "__" in temp:
#                 x = chr(ord('a') + np.random.randint(0, 26))
#                 temp_new = temp.replace('__', '{}_'.format(x))
#                 while temp_new in line:
#                     x = chr(ord('a') + np.random.randint(0, 26))
#                     temp_new = temp.replace('__', '{}_'.format(x))
#                 line = line.replace(temp, temp_new)
#     line = remove_space(line)
#     return line


def find_variable(inv):
    inv = remove_space(inv)
    if inv == "":
        return []
    inv = inv[inv.rfind("(") + 1:inv.rfind(")")]
    vars = inv.split(',')
    remove_list = []
    for var in vars:
        if var == '0' or ")" in var or "&&" in var or "==" in var:
            remove_list.append(var)
    vars_new = []
    for var in vars:
        if var not in remove_list and var not in vars_new:
            vars_new.append(var)
    return vars_new


def add_segment_for_solver(inv, segments, v_list=None):
    data_header = "exists"
    mark = 1
    var_list = find_variable(inv)
    e_v_list = []
    if "exists" in inv:
        e_v_list = inv[inv.find("exists") + 7:inv.find(",")].split(' ')
    if "data_at" in inv or "listrep" in inv or 'lseg' in inv:
        mark = 0
    for r_seg in np.random.permutation(len(segments)):
        seg = segments[r_seg]
        var_list += find_variable(seg)
        if mark == 1:
            inv += ' && ' + seg
            mark = 0
        else:
            inv += ' * ' + seg
    if v_list is not None:
        add_list = []
        for v in var_list:
            if v not in v_list and v not in add_list:
                add_list.append(v)
        for v in e_v_list:
            if v not in v_list and v not in add_list:
                add_list.append(v)
        for v in add_list:
            data_header += ' ' + v
        if data_header != "exists":
            if "exists" not in inv:
                inv = data_header + ',' + inv
            else:
                inv = data_header + inv[inv.find(','):]
    return remove_space(inv)


def use_solver(input, segment, model_output, v_list=None, op='lseg', thread_num=0):
    # input: the collection of assertions (I0I1I2I3)
    # segment: the segment to be eliminated
    # model_output: the segments that have been eliminated, not include the output. Set it for [] if not needed.
    torch.nn.Softmax()
    origin_input = input
    if op == "lseg":
        data_header = data_header_lseg
    elif op == "dlseg":
        data_header = data_header_dlseg
    else:
        raise NotImplementedError
    input_data = data_header + "$\nstruct list "
    # remove header "Code: ***"
    code_head = input[0:input.find("\n") + 1]
    if v_list is None:
        v_list = code_head[code_head.find(":") + 2:-2].split(';')
    input = input[input.find("\n") + 1:]
    # add variable statement
    for v in v_list:
        input_data += "*{}".format(v)
        if not v == v_list[-1]:
            input_data += ','
        else:
            input_data += ';\n'
    # add segment to be eliminated, including the segments in model_output
    # input_data += '#\n/*@ {} */\n'.format(add_segment_for_solver(segment, model_output))
    input_data += '$\n/*@ {} */\n'.format(add_segment_for_solver(segment, model_output, v_list))
    # add invariants, including the segments in model_output for each one
    invs = input.split('\n')
    for inv in invs[:-1]:
        inv_ = inv[inv.find(":") + 1:].replace(';', '')
        # inv_ = add_segment_for_solver(inv_, model_output, v_list)
        input_data += '$\n/*@' + inv_ + '*/\n'
    # use the solver. The input and output are stored in the sample_input folder with random file name.
    r = np.random.randint(0, 10)
    with open("../../solver/sample_input/input_{}_{}.txt".format(thread_num, r), "w") as f:
        f.write(input_data)
    os.system("rm ../../solver/sample_input/output_{}_{}.txt".format(thread_num, r))
    os.system(
        "./{} ../../solver/sample_input/input_{}_{}.txt > ../../solver/sample_input/output_{}_{}.txt".format(program,
                                                                                                             thread_num,
                                                                                                             r,
                                                                                                             thread_num,
                                                                                                             r))
    with open("../../solver/sample_input/output_{}_{}.txt".format(thread_num, r), "r") as f:
        output = f.read()
    print(input_data)
    print(output)
    print(r)
    # check the status after the solver. 0 for fail, 1 for success, 2 for end
    # if the Fail to entail is less than 2, it is success. Otherwise, it is fail.
    # if the number of emp is larger than len(invs) - 2, it is end.
    status = 0
    if output == '':
        return '', status, -100, ''
    count = output.count('emp')
    if output.count('Fail to entail') <= 2:
        if count >= len(invs) - 3:
            status = 2
        else:
            status = 1
    else:
        status = 0
    # reform the output to be used as the input invariants for the next iteration
    output = output.replace('Fail to entail\n', '')
    output = output.replace('execution finished ', '')
    output_data = output.split('==========================')
    out = code_head
    for j in range(len(output_data)):
        if output_data[j] == '\n':
            continue
        # output_data[j] = finetune(output_data[j])
        out_ = remove_space(output_data[j].replace('\n', ''))
        for seg in model_output:
            out_ = out_.replace("&&" + seg + "*", '&&')
            out_ = out_.replace("&&" + seg, '')
            out_ = out_.replace("*" + seg, '')
            out_ = out_.replace(seg, '')
        out_ = out_.replace("&&emp", "")
        out += 'I_{}: '.format(j) + out_ + '\n'
    # print(out)
    # return the new invariants after solver, the status and the number of emp
    return out, status, count, origin_input


def use_llm(model=None, tokenizer=None, model_path=None, input="", file=None, need_refine=False):
    # model: the large language model used for generating invariants
    # tokenizer: the tokenizer of the llm
    # model_path: if the model and tokenizer is not provided, the model_path is used to load the model and tokenizer
    # input: the input invariants for the model
    # output: the generated invariants
    if model is None or tokenizer is None:
        if model_path is not None:
            model = AutoModelForCausalLM.from_pretrained(model_path)
            tokenizer = AutoTokenizer.from_pretrained(model_path)
        else:
            raise NotImplementedError
    if "data_at" in input or "->" in input:
        need_refine = True
    if need_refine:
        input, v_map = refine_case(input, pointer_mode=1)
    else:
        v_map = {}
    if file is not None:
        print(len(input), file=file)
        print(input,file=file)
        print(v_map,file=file)
    else:
        print(len(input))
        print(input)
        print(v_map)
    max_new_tokens = 200
    text = '<|INPUT|>' + input[0:2048] + '<|OUTPUT1|>'
    input_ids = tokenizer(text, return_tensors="pt").input_ids
    device = torch.device("cuda" if torch.cuda.is_available() else "cpu")
    input_ids = input_ids.to(device)
    generated_ids = model.generate(input_ids, max_new_tokens=max_new_tokens, do_sample=False)
    output = tokenizer.decode(generated_ids[0], truncate_before_pattern=[r"\n\n^#", "^'''", "\n\n\n"])
    if v_map != {}:
        output = undo_rename_special_variables(output, v_map)
    if output[-1] == '\n':
        output = output[:-1]
    return output


if __name__ == '__main__':
    # op = "listrep1-lseg5-dlistrep1-dlseg10-listbox_seg5-ptree_rep0-llistrep0-llseg0-output1-pointer1-noise1"
    op = "listrep0-lseg0-dlistrep0-dlseg0-listbox_seg0-ptree_rep0-tree_rep1-llistrep0-llseg0-output1-pointer1-noise1"
    num_train_epochs = 5
    data_size = 20000
    test_mode = 2
    if test_mode == 1:
        test_cases, test_answers = get_test_cases(op)
        test_names = []
    elif test_mode == 2:
        test_cases, test_answers, test_names = get_test_cases_from_file()
    else:
        raise NotImplementedError
    # test_cases = [test_cases[2]]
    # with open('Igen.txt','r') as f:
    #     test_case = ""
    #     lines = f.readlines()
    #     for line in lines:
    #         test_case += line
    #     test_cases = [test_case]
    # model_path = '../../model/try-codegen2-{}-{}'.format(op, num_train_epochs)
    model_path = '../../model/try-codegen-{}-{}-{}'.format(op, num_train_epochs, data_size)
    model = AutoModelForCausalLM.from_pretrained(model_path)
    tokenizer = AutoTokenizer.from_pretrained(model_path)
    device = torch.device("cuda" if torch.cuda.is_available() else "cpu")
    model = model.to(device)
    file = open('../../examples/llm_log/{}-{}-{}-output{}.log'.format(op, num_train_epochs, data_size, test_mode), 'w')
    for test_case in test_cases:
        if len(test_names) > 0:
            print(test_names[test_cases.index(test_case)], file=file)
        input = test_case
        origin_input = input
        model_output = []
        for i in range(1):
            # print(input)
            output = use_llm(model, tokenizer, model_path=None, input=input, file=file)
            # output = segments[i]
            print(output,file=file)
            # print(refine_output(output),file=file)
            output = output[output.rfind('<|OUTPUT1|>'):]
            if '\n' in output:
                output = output[:output.find('\n')]
            # test = use_solver(origin_input, output, model_output, op=op)
            test = ["", 2, 0, ""]
            model_output.append(output)
            input = test[0]
            print(test[1],file=file)
            if test[1] != 1:
                break
        print(test_cases.index(test_case) + 1, test[1], model_output,file=file)
        print(test_answers[test_cases.index(test_case)],file=file)
        print('-' * 100,file=file)
        # break
