import random
import re
import glob
import numpy as np


def remove_space(line):
    if 'exists' not in line:
        line = line[0:line.find(':') + 2] + line[line.find(':') + 2:].replace(' ', '')
    else:
        line = line[0:line.find(',') + 1] + line[line.find(',') + 1:].replace(' ', '')
    line = line.replace(" ,", ",")
    line = line.replace('\n', '')
    return line


def random_choose_variable(v_list=None, is_zero_rate=0.0, is_temp_rate=0.0):
    # choose variable randomly, avoid the same variable from v_list
    is_temp = np.random.rand() < is_temp_rate
    if is_temp:
        # generate a temp variable __*
        x = '__' + str(np.random.randint(0, 100))
        while x in v_list:
            x = '__' + str(np.random.randint(0, 100))
        return x

    is_zero = np.random.rand() < is_zero_rate
    if is_zero:
        # generate a zero variable 0
        x = '0'
        return x

    x = chr(ord('a') + np.random.randint(0, 26))
    if v_list is None:
        return x
    while x in v_list:
        x = chr(ord('a') + np.random.randint(0, 26))
    return x


def finetune_instance(line):
    # finetune the line from the splitter
    # the core idea is the find the invs end with [1 1], which will give us many equations.
    # make variables replacement guide by the equations
    if 'exist ' in line:
        line = line.replace('exist ', 'exists ')
    line = remove_space(line)

    line_head = ""
    if 'exists' in line:
        line_head = line[0:line.find(',') + 1]
        line = line[line.find(',') + 1:]
    addition_term = ""
    match_results = re.findall(r"\b(?<!->)[a-zA-Z_]\w*\b\s*==\s*\b[a-zA-Z_]\w*\b", line)
    # extract the equations ({}=={} && {}=={} ...) in the line, but ignore equations like {}->tail=={}
    if match_results:
        line_to_replace = '&&'.join(match_results)
        assert line_to_replace in line
        line = re.sub(r"\b{}\b(\*|\&\&)?".format(line_to_replace), '', line)
        # remove the equations from the line, and the * or && behind it
        replace_lists = match_results
        replace_variables = []
        for replace_list in replace_lists:
            variables = replace_list.split('==')
            assert len(variables) == 2
            if "__" not in variables[0] and not re.match(r"v\d", variables[0]) \
                    and "__" not in variables[1] and not re.match(r"v\d", variables[1]):
                # special case where the equation needs to be maintained
                addition_term += variables[0] + '==' + variables[1] + "&&"
            elif "__" not in variables[1] and not re.match(r"v\d", variables[1]):
                replace_variables.append(variables)

        def replace(match):
            value = match.group()
            for replace_variable in replace_variables:
                if value == replace_variable[0]:
                    value = replace_variable[1]
            return value

        # replace variables in the line, find variable via the gap between (, or ,) or ,, .
        # line = re.sub(r"(?<=[(,])[^(),]+(?=[,)])", replace, line)

        # replace variables in the line, find variable by the word boundary
        pattern = r"\b(?<!->)(?<!\.)[a-zA-Z_]\w*\b(?!\(|\bprev\b|\bnext\b|\btail\b)"
        line = re.sub(pattern, replace, line)

    line = line_head + addition_term + line

    # fix the tail of the line
    line.replace('&&&&', '&&')
    line.replace('&&*', '&&')
    while line[-1:] == '&':
        line = line[:-1]
    return line


def generate_header(v_list):
    # generate the header of the file Code: x;y;z;...
    header = "Code: "
    rand_range = np.random.permutation(len(v_list))
    for i in rand_range:
        v = v_list[i]
        if '_' not in v and '0' not in v:
            header += " {} ;".format(v)
    header = remove_space(header)
    header += '\n'
    return header


def line_rename_temp(line, v_list):
    # rename the temp variables (v1, v2, ...) from the splitter to __*
    if "exists" not in line:
        temp_variables = []
    else:
        line_re = line[:line.find(',')]
        temp_variables = line_re.split(' ')[1:]
    for v in v_list:
        if re.match(r"v\d", v) or "__" in v:
            temp_variables.append(v)
    temp_list = re.findall(r'__\d+', line)
    for v in temp_list:
        if v not in temp_variables:
            temp_variables.append(v)
    for temp in temp_variables:
        # temp variables may exist in v_list, such as dlseg(x, 0, __0, p), the third arguments may be a temp variable
        # here we rename all the temp variables, v* from the splitter and __* from the arguments
        if re.match(r"v\d", temp) or "__" in temp:
            new_temp = random_choose_variable(v_list, is_zero_rate=0.0, is_temp_rate=1.0)
            line = re.sub(r'(?<!\d){}(?!\d)'.format(temp), new_temp, line)
            v_list.append(new_temp)
    return line, v_list


def line_reorder(line, rand=True):
    # inside reorder, split by &&, suppose we have already changed * to &&
    if '&&' not in line:
        return line
    # assert "*" not in line
    line_parts = line.split('&&')
    line_parts_equality = []
    line_parts_data_at = []
    line_parts_other = []
    for part in line_parts:
        if "exists" in part:
            part = part[part.find(',') + 1:]
        # if ("==" in part or "!=" in part) and "->" not in part and ")." not in part and "(*" not in part:
        if ("==" in part or "!=" in part or ("==" not in part and ">" in part) or (
                "==" not in part and ">" in part)):
            if rand:
                operator = "==" if "==" in part else "!="
                var_s = part.split(operator)
                var_s = np.random.permutation(var_s)
                while var_s[0] == '0':  # avoid 0==x, 0 is better placed in the end
                    var_s = np.random.permutation(var_s)
                part = operator.join(var_s.tolist())
            if "*" in part:  # judge if it is a data_at operation
                line_parts_data_at.append(part)
            else:
                # if "!" not in part:  # TODO: temporal operation
                line_parts_equality.append(part)
        else:
            line_parts_other.append(part)
    if rand:
        line_parts_equality = np.random.permutation(line_parts_equality).tolist()
        line_parts_data_at = np.random.permutation(line_parts_data_at).tolist()
        line_parts_other = np.random.permutation(line_parts_other).tolist()
    line_parts = line_parts_equality + line_parts_data_at + line_parts_other
    line_body = '&&'.join(line_parts)
    line, _ = line_check(line_body, [])
    return line


# def line_reorder(line):
#     # inside reorder, split by *
#     if '*' not in line:
#         return line
#     line_re = line[:line.find('*')]
#     line_parts = line.split('*')
#     if "&&" in line_re:
#         line_parts[0] = line_re[line_re.rfind('&&') + 2:]
#         line_re = line_re[:line_re.rfind('&&') + 2]
#     elif "exists" in line_re:
#         line_parts[0] = line_re[line_re.find(',') + 1:]
#         line_re = line_re[:line_re.find(',') + 1]
#     else:
#         line_parts[0] = line_re
#         line_re = ""
#     line_parts = np.random.permutation(line_parts)
#     for part in line_parts:
#         line_re += '*' + part
#     line = line_re.replace("&&*", "&&")
#     line = line.replace(",*", ",")
#     if line[0] == '*':
#         line = line[1:]
#     return line


def line_check(line, v_list=None):
    # check if all temp variables are defined in the beginning of the line
    # may be used when you put a temp variable as an argument. e.g. dlseg(x, 0, __0, p)
    # line_re = line[0:line.find(',')] if "exists" in line else ""
    line = line[line.find(',') + 1:] if "exists" in line else line
    defined_vars = []
    temp_list = re.findall(r'__\d+', line)
    for v in temp_list:
        if "__" in v and v not in defined_vars and v in line:
            defined_vars.append(v)
    if len(defined_vars) > 0:
        line = "exists " + " ".join(defined_vars) + "," + line
    new_v_list = [v for v in v_list if not (("__" in v) and (v not in defined_vars))]
    return line, new_v_list


def line_simplify(line, pointer_mode=0):
    if pointer_mode == 0:
        raise NotImplementedError
    pattern = r"field_addr\((\w+),(\w+)\)"  # match field_addr(x , y)
    line = re.sub(pattern, r"&*\1.\2", line)  # change to x->y
    # pattern = r"data_at\(field_addr\((\w+),(\w+)\),(\w+)\)"  # match data_at(field_addr(x , y), z)
    # line = re.sub(pattern, r"\1->\2==\3", line)  # change to x->y == z
    # line = line.replace("*", "&&")
    # p = r"(?<!\()"
    # line = re.sub(p + r"\*", "&&", line)
    line = re.sub(r"\!\((\w+)\s*==\s*(\w+)\)", r"\1!=\2", line)  # change !(x==y) to x!=y
    line = re.sub(r"data_at\(([^,()]+),([^,()]+)\)", r"*\1==\2", line)  # change to *x == y
    while "*&" in line:
        line = line.replace("*&", "")
    # NOTE we know fix the pointer_mode to 1
    if pointer_mode:  # change A->C == B to *A.C == B
        pattern = r"([_a-zA-Z0-9][_a-zA-Z0-9]*)->([_a-zA-Z0-9][_a-zA-Z0-9]*)==([_a-zA-Z0-9][_a-zA-Z0-9]*)"
        replacement = r"*\1.\2==\3"
        line = re.sub(pattern, replacement, line)
    # change &*A.C == B to *A.C == *B, but make sure xxx&&*A.C == B is not changed.
    pattern = r"(?<!&)&([_a-zA-Z0-9/*][_a-zA-Z0-9]*)\.([_a-zA-Z0-9][_a-zA-Z0-9]*)==([_a-zA-Z0-9][_a-zA-Z0-9]*)"
    replacement = r"\1.\2==*\3"
    line = re.sub(pattern, replacement, line)
    pattern = r"([_a-zA-Z0-9][_a-zA-Z0-9]*)==&([_a-zA-Z0-9/*][_a-zA-Z0-9]*)\.([_a-zA-Z0-9][_a-zA-Z0-9]*)"
    replacement = r"*\1==\2.\3"
    line = re.sub(pattern, replacement, line)
    # check: *A.C --> (*A).C
    pattern = r"\*([_a-zA-Z0-9][_a-zA-Z0-9]*)\.([_a-zA-Z0-9][_a-zA-Z0-9]*)"  # match *A.C
    line = re.sub(pattern, r"(*\1).\2", line)  # change to (*A).C
    return line

def check_wxw(line):
    pattern = r'(?<![\w*])(\b[a-zA-Z]\b)==(__\d+)(?!\w)|(?!\w)(__\d+)==(\b[a-zA-Z]\b)(?!\w)(?!\.)'
    match_results = re.findall(pattern, line)
    for match_result in match_results:
        if '*' in match_result:
            continue
        v1 = ""
        v2 = ""
        for v in match_result:
            if v != "":
                if "__" in v:
                    v1 = v
                else:
                    v2 = v
        line = re.sub(r'\b' + v1 + r'\b', v2, line)
    return line

def refine_case(case, pointer_mode=0):
    lines = case.split('\n')
    new_case = ""
    ind = 0
    v_map = {}
    line_index = {}
    for line in lines:
        if "Code:" not in line and ":" in line:
            assert ";" in line
            line = line.replace(".link1", ".prev")
            line = line.replace(".link2", ".next")
            line = line.replace(".link", ".tail")
            line = re.sub(rf"\b.data\b", '.head', line)

            prev_index = line[0:line.find(':')]
            line = line[line.find(':') + 2:line.find(";")]  # NOTE: we regard * and && as the same for now
            line = line[0] + re.sub("(?<!&)\*", "&&", line[1:])
            line = remove_space(line)
            line, _ = line_rename_temp(line, [])
            line, _ = line_check(line, [])
            line = line_simplify(line, pointer_mode=pointer_mode)
            line = line_reorder(line, rand=False)
            # handle the case that variable named as "head" "tail" "x_prev" "x_next" "head_node" "tail_node"
            line, v_map = line_rename_special_variables(line, v_map)
            line = line_remove_useless_temp_variables(line)
            line = check_wxw(line)
            if prev_index.count("_") > 1:
                header = prev_index[0:3]
                if header not in line_index:
                    line_index[header] = 0
                else:
                    continue
                    line_index[header] += 1
                line = header + "_{}".format(line_index[header]) + ": " + line + ';'
            else:
                line = "I_{}_0: ".format(ind) + line + ';'
            ind += 1
        new_case += line + '\n'
    if v_map != {}:
        new_case_first_line = new_case.split('\n')[0]
        new_case_first_line = new_case_first_line.replace("Code: ", "Code: " + ";".join(v_map.values()) + ";")
        new_case = new_case.replace(new_case.split('\n')[0], new_case_first_line)
    return new_case, v_map


def line_remove_useless_temp_variables(line):
    pattern = r"\b(?<!->)(?<!\.)[a-zA-Z_]\w*\b(?!\(|\btail\b)"
    v_map = re.findall(pattern, line)
    line_parts = line.split("&&")
    for v1 in v_map:
        if "__" in v1:
            for v2 in v_map:
                if "__" not in v2:
                    for i in range(len(line_parts)):
                        if line_parts[i] == "{}=={}".format(v1, v2) or line_parts[i] == "{}=={}".format(v2, v1):
                            line = re.sub(r"\b{}\b".format(v1), v2, line)
                            line = re.sub(r"\b&&{}=={}\b".format(v2, v2), "", line)
    line, _ = line_check(line, [])
    return line


def refine_output(output):
    assert '<|OUTPUT1|>' in output
    assert '<|OUTPUT2|>' in output
    output1 = output[output.find('<|OUTPUT1|>') + 11:output.find('<|OUTPUT2|>')]
    output2 = output[output.find('<|OUTPUT2|>') + 11:].split('&&')
    variables = re.findall(r"\b(?<!->)(?<!\.)[a-zA-Z_]\w*\b(?!\(|\btail\b)", output1)
    input = output[output.find("Code ") + 5:output.find(";\n")]
    input_variables = input.split(';')
    variables += input_variables
    final_output = '<|OUTPUT1|>' + output1 + '<|OUTPUT2|>'
    for o in output2:
        variables_new = re.findall(r"\b(?<!->)(?<!\.)[a-zA-Z_]\w*\b(?!\(|\btail\b)", o)
        check = 0
        for v in variables_new:
            if v not in variables:
                check = 1
                break
        if check == 0:
            final_output += o + "&&"
    if final_output[-2:] == "&&":
        final_output = final_output[0:-2]
    return final_output


def line_rename_special_variables(line, v_map):
    pattern = r"\b(?<!->)(?<!\.)[a-zA-Z_]\w*\b(?!\(|\btail\b)"
    variables = re.findall(pattern, line)
    v_list = variables
    # check_1 = 0
    # check_2 = 0
    for v in variables:
        if len(v) >= 2 and v[0] != "_" and v != "exists":
            new_v = random_choose_variable(v_list=v_list) if v not in v_map else v_map[v]
            line = re.sub(r"(?<!\.)\b{}\b".format(v), new_v, line)
            v_list.append(new_v)
            v_map[v] = new_v
        # if ("_prev" in v or "_next" in v) and check_1 == 0:
        #     new_v = random_choose_variable(v_list=v_list) if v not in v_map else v_map[v]
        #     line = re.sub(r"\b{}\b".format(v), new_v, line)
        #     v_list.append(new_v)
        #     v_map[v] = new_v
        #     # check_1 = 1
        # if ("_node" in v or "head" in v) and check_2 == 0:
        #     new_v = random_choose_variable(v_list=v_list) if "head_node" not in v_map else v_map["head_node"]
        #     line = re.sub(r"\b{}\b".format("head_node"), new_v, line)
        #     v_list.append(new_v)
        #     v_map["head_node"] = new_v
        #     new_v = random_choose_variable(v_list=v_list) if "head" not in v_map else v_map["head"]
        #     line = re.sub(r"\b{}\b".format("head"), new_v, line)
        #     v_list.append(new_v)
        #     v_map["head"] = new_v
        #     new_v = random_choose_variable(v_list=v_list) if "tail_node" not in v_map else v_map["tail_node"]
        #     line = re.sub(r"\b{}\b".format("tail_node"), new_v, line)
        #     v_list.append(new_v)
        #     v_map["tail_node"] = new_v
        #     new_v = random_choose_variable(v_list=v_list) if "tail" not in v_map else v_map["tail"]
        #     line = re.sub(r"\b(?<!\.)(?<=\b)tail\b", new_v, line) # avoid replacing "tail" in "(*A).tail"
        #     v_list.append(new_v)
        #     v_map["tail"] = new_v
        #     check_2 = 1
    return line, v_map


def undo_rename_special_variables(case, v_map):
    lines = case.split('\n')
    new_case = ""
    r_vmap = dict(zip(v_map.values(), v_map.keys()))
    for line in lines:
        if "Code:" not in line:
            pattern = r"\b(?<!->)(?<!\.)[a-zA-Z_]\w*\b(?!\(|\btail\b)"
            variables = re.findall(pattern, line)
            for v in variables:
                if v in r_vmap:
                    line = re.sub(r"\b{}\b".format(v), r_vmap[v], line)
        else:
            variables = line[line.find(":") + 2:].split(';')
            for v in variables:
                if v in r_vmap:
                    line = re.sub(r"\b{};\b".format(v), "", line)
        new_case += line + '\n'
    return new_case


def line_replace(line, v_list):
    variables = re.findall(r"\b(?<!->)(?<!\.)[a-zA-Z_]\w*\b(?!\()", line)
    var_list = []
    for var in variables:
        if var not in var_list and var != "lambda" and var != "emp" and var != "exists":
            var_list.append(var)
    v = random.choice(var_list)
    count = 0
    while "__" in v and count < 10:
        v = random.choice(var_list)
        count += 1
    if count == 10:
        return line, v_list
    new_v = random_choose_variable(v_list=v_list, is_zero_rate=0.0, is_temp_rate=0.0)
    line = re.sub(r"(?<!\.)\b{}\b".format(v), new_v, line)
    line_start = 0 if "exists" not in line else line.find(',') + 1
    line = line[0:line_start] + "{}=={}&&".format(*np.random.permutation([v, new_v]).tolist()) + line[line_start:]
    v_list.append(new_v)
    return line, v_list


def get_test_cases_from_file():
    file_list = glob.glob('../../examples/invs/*.txt')
    test_names = []
    test_cases = []
    test_answers = []
    for file in file_list:
        text = ""
        if "input" in file:
            # if "insert_input" in file:
            with open(file, 'r') as f:
                lines = f.readlines()
                for line in lines:
                    text += line
            test_names.append(file)
            test_cases.append(text)
            text = ""
            outputfile = file.replace("input", "output")
            with open(outputfile, 'r') as f:
                lines = f.readlines()
                for line in lines:
                    text += line
            test_answers.append(text)
    return test_cases, test_answers, test_names


def process_to_new_framework(definition, instance_input, instance_output, core_seg):
    definition = definition[:definition.find("UNFOLD") - 1]
    predicates_exists = []
    predicates_new = []
    definition_exists = ""
    definition_new = ""
    for input_definition in definition.split('\n'):
        # 提取变量名和字段名
        matches = re.search(r'\b[A-Za-z_][A-Za-z0-9_]*\b(?=\()', input_definition)
        if matches:
            predicate_name = matches.group(0)
            if predicate_name in instance_input:
                predicates_exists.append(predicate_name)
                definition_exists += input_definition + '\n'
            elif predicate_name in instance_output:
                predicates_new.append(predicate_name)
                definition_new += input_definition + '\n'
        else:
            definition_exists += input_definition + '\n'
    for name in predicates_exists:
        new_name = 'predicate_{}'.format(np.random.randint(0, 100))
        definition_exists = definition_exists.replace(name, new_name)
        core_seg = core_seg.replace(name, new_name)
        instance_input = instance_input.replace(name, new_name)
        instance_output = instance_output.replace(name, new_name)
    count = 0
    for name in predicates_new:
        new_name = 'predicate_new_{}'.format(count)
        count += 1
        definition_new = definition_new.replace(name, new_name)
        core_seg = core_seg.replace(name, new_name)
        instance_input = instance_input.replace(name, new_name)
        instance_output = instance_output.replace(name, new_name)
    return  definition_exists, instance_input, instance_output, core_seg, definition_new


def get_test_cases(op):
    text_lseg_1 = "Code: w;v;p;t;\nI_0: w==0&&v==p&&listrep(p);\nI_1: p!=0&&w==p&&v==t&&data_at(field_addr(w,tail),0)*listrep(v);\nI_2: p!=0&&w!=0&&v==t&&data_at(field_addr(p,tail),0)*data_at(field_addr(w,tail),p)*listrep(v);\nI_3: exists v1 ,p!=0&&v1!=0&&w!=0&&v==t&&data_at(field_addr(p,tail),0)*data_at(field_addr(v1,tail),p)*data_at(field_addr(w,tail),v1)*listrep(v);\n"
    # text_lseg_1 = "Code: w;v;p;t;\nI_0: w==0&&v==p&&listrep(p);\nI_1: p!=0&&w==p&&v==t&&data_at(field_addr(w,tail),0)*listrep(v);\nI_2: p!=0&&w!=0&&v==t&&data_at(field_addr(p,tail),0)*data_at(field_addr(w,tail),p)*listrep(v);\nI_3: exists v1 ,p!=0&&v1!=0&&w!=0&&v==t&&data_at(field_addr(p,tail),0)*data_at(field_addr(w,tail),v1)*data_at(field_addr(v1,tail),p)*listrep(v);\nI_4: exists v1 v2 ,p!=0&&v1!=0&&v2!=0&&w!=0&&v==t&&data_at(field_addr(p,tail),0)*data_at(field_addr(w,tail),v1)*data_at(field_addr(v1,tail),v2)*data_at(field_addr(v2,tail),p)*listrep(v);\n"
    # append
    text_lseg_2 = "Code: x;t;u;\nI_0: x!=0&&x==t&&data_at(field_addr(t,tail),u)*listrep(u);\nI_1: x!=0&&t!=0&&data_at(field_addr(x,tail),t)*data_at(field_addr(t,tail),u)*listrep(u);\nI_2: exists v1 ,x!=0&&t!=0&&v1!=0&&data_at(field_addr(x,tail),v1)*data_at(field_addr(v1,tail),t)*data_at(field_addr(t,tail),u)*listrep(u);\nI_3: exists v1 v2 ,x!=0&&t!=0&&v1!=0&&v2!=0&&data_at(field_addr(x,tail),v1)*data_at(field_addr(v1,tail),v2)*data_at(field_addr(v2,tail),t)*data_at(field_addr(t,tail),u)*listrep(u);\n"

    # iter
    text_lseg_3 = "Code: l;p;\nI_0: l==p&&listrep(p);\nI_1: l!=0&&data_at(field_addr(l,tail),p)*listrep(p);\nI_1: exists v1,l!=0&&v1!=0&&data_at(field_addr(l,tail),v1)*data_at(field_addr(v1,tail),p)*listrep(p);\nI_3: exists v1 v2 ,l!=0&&v1!=0&&data_at(field_addr(l,tail),v1)*data_at(field_addr(v1,tail),v2)*data_at(field_addr(v2,tail),p)*listrep(p);\n"

    # merge
    text_lseg_4 = "Code: x;y;t;p;\nI_0: t==p&&data_at(field_addr(t,tail),0)*listrep(x)*listrep(y);\nI_1: data_at(field_addr(p,tail),t)*data_at(field_addr(t,tail),0)*listrep(x)*listrep(y);\nI_2: exists v1 ,data_at(field_addr(p,tail),v1)*data_at(field_addr(v1,tail),t)*data_at(field_addr(t,tail),0)*listrep(x)*listrep(y);\nI_3: exists v1 v2 ,data_at(field_addr(p,tail),v1)*data_at(field_addr(v1,tail),v2)*data_at(field_addr(v2,tail),t)*data_at(field_addr(t,tail),0)*listrep(x)*listrep(y);\n"

    # iter_twice
    text_lseg_5 = "Code: l;p;\nI_0: l==p&&listrep(p);\nI_1: exists v1,l!=0&&v1!=0&&data_at(field_addr(l,tail),v1)*data_at(field_addr(v1,tail),p)*listrep(p);\nI_2: exists v1 v2 v3,l!=0&&v1!=0&&data_at(field_addr(l,tail),v1)*data_at(field_addr(v1,tail),v2)*data_at(field_addr(v2,tail),v3)*data_at(field_addr(v3,tail),p)*listrep(p);\nI_3: exists v1 v2 v3 v4 v5,l!=0&&v1!=0&&data_at(field_addr(l,tail),v1)*data_at(field_addr(v1,tail),v2)*data_at(field_addr(v2,tail),v3)*data_at(field_addr(v3,tail),v4)*data_at(field_addr(v4,tail),v5)*data_at(field_addr(v5,tail),p)*listrep(p);\n"

    # rev_append
    text_lseg_6 = "Code: x;t;u;y;\nI_0: x==t&&u==y&&listrep(x)*listrep(y);\nI_1: t==y&&data_at(field_addr(y,tail),u)*listrep(x)*listrep(u);\nI_2: exists v1 ,t==y&&data_at(field_addr(y,tail),v1)*data_at(field_addr(v1,tail),u)*listrep(x)*listrep(u);\nI_3: exists v1 v2 ,t==y&&data_at(field_addr(y,tail),v1)*data_at(field_addr(v1,tail),v2)*data_at(field_addr(v2,tail),u)*listrep(x)*listrep(u);\n"

    # rev_append_twice
    text_lseg_7 = "Code: x;t;u;y;\nI_0: x==t&&u==y&&listrep(x)*listrep(y);\nI_1: exists v1 ,t==y&&data_at(field_addr(y,tail),v1)*data_at(field_addr(v1,tail),u)*listrep(x)*listrep(u);\nI_2: exists v1 v2 v3,t==y&&data_at(field_addr(y,tail),v1)*data_at(field_addr(v1,tail),v2)*data_at(field_addr(v2,tail),v3)*data_at(field_addr(v3,tail),u)*listrep(x)*listrep(u);\nI_3: exists v1 v2 v3 v4 v5,t==y&&data_at(field_addr(y,tail),v1)*data_at(field_addr(v1,tail),v2)*data_at(field_addr(v2,tail),v3)*data_at(field_addr(v3,tail),v4)*data_at(field_addr(v4,tail),v5)*data_at(field_addr(v5,tail),u)*listrep(x)*listrep(u);\n"

    # multi_merge
    text_lseg_8 = "Code: x;y;t;p;u;v;w;q;\nI_0: t==p&&w==q&&data_at(field_addr(w,tail),0)*listrep(u)*listrep(v)*data_at(field_addr(t,tail),0)*listrep(x)*listrep(y);\nI_1: data_at(field_addr(q,tail),w)*data_at(field_addr(w,tail),0)*listrep(u)*listrep(v)*data_at(field_addr(p,tail),t)*data_at(field_addr(t,tail),0)*listrep(x)*listrep(y);\nI_2: exists v1 v6,data_at(field_addr(q,tail),v6)*data_at(field_addr(v6,tail),w)*data_at(field_addr(w,tail),0)*listrep(u)*listrep(v)*data_at(field_addr(p,tail),v1)*data_at(field_addr(v1,tail),t)*data_at(field_addr(t,tail),0)*listrep(x)*listrep(y);\nI_3: exists v1 v2 v6 v8,data_at(field_addr(q,tail),v6)*data_at(field_addr(v6,tail),v8)*data_at(field_addr(v8,tail),w)*data_at(field_addr(w,tail),0)*listrep(u)*listrep(v)*data_at(field_addr(p,tail),v1)*data_at(field_addr(v1,tail),v2)*data_at(field_addr(v2,tail),t)*data_at(field_addr(t,tail),0)*listrep(x)*listrep(y);\n"

    # multi_rev
    text_lseg_9 = "Code: w;v;p;t;x;y;\nI_0: y==t&&x==p&&listrep(x)*listrep(y);\nI_1: w==p&&v==t&&data_at(field_addr(w,tail),0)*data_at(field_addr(v,tail),0)*listrep(x)*listrep(y);\nI_2: data_at(field_addr(p,tail),0)*data_at(field_addr(w,tail),p)*listrep(y)*data_at(field_addr(t,tail),0)*data_at(field_addr(v,tail),t)*listrep(x);\nI_3: exists v1 v10,data_at(field_addr(p,tail),0)*data_at(field_addr(w,tail),v1)*data_at(field_addr(v1,tail),p)*listrep(y)*data_at(field_addr(t,tail),0)*data_at(field_addr(v,tail),v10)*data_at(field_addr(v10,tail),t)*listrep(x);\n"

    # multi_append
    text_lseg_10 = "Code: x;y;z;t;\nI_0: t==z&&listrep(x)*listrep(y)*listrep(z);\nI_1: exists v9 v7, data_at(field_addr(t,tail),v9)*data_at(field_addr(v9,tail),v7)*data_at(field_addr(v7,tail),z)*listrep(z)*listrep(x)*listrep(y);\nI_2: exists v9 v7 v1 v6, data_at(field_addr(t,tail),v1)*data_at(field_addr(v1,tail),v6)*data_at(field_addr(v6,tail),v9)*data_at(field_addr(v9,tail),v7)*data_at(field_addr(v7,tail),z)*listrep(z)*listrep(x)*listrep(y);\nI_3: exists v9 v7 v1 v6 v2 v8, data_at(field_addr(t,tail),v2)*data_at(field_addr(v2,tail),v8)*data_at(field_addr(v8,tail),v1)*data_at(field_addr(v1,tail),v6)*data_at(field_addr(v6,tail),v9)*data_at(field_addr(v9,tail),v7)*data_at(field_addr(v7,tail),z)*listrep(z)*listrep(x)*listrep(y);\n"

    # reverse
    text_dlseg_1 = "Code: w;v;p;t;\nI_0: w==0&&v==p&&dlistrep(p,0);\nI_1: p!=0&&w==p&&v==t&&data_at(field_addr(p,next),0)*data_at(field_addr(p,prev),v)*dlistrep(v,p);\nI_2: p!=0&&v==t&&data_at(field_addr(p,next),0)*data_at(field_addr(p,prev),w)*data_at(field_addr(w,next),p)*data_at(field_addr(w,prev),v)*dlistrep(v,w);\nI_3: exists v0 ,p!=0&&v==t&&data_at(field_addr(p,next),0)*data_at(field_addr(p,prev),v0)*data_at(field_addr(v0,next),p)*data_at(field_addr(v0,prev),w)*data_at(field_addr(w,next),v0)*data_at(field_addr(w,prev),v)*dlistrep(v,w);\n"

    # iter_front
    text_dlseg_2 = "Code: p;x;\nI_0: x!=0&&p==x&&dlistrep(x,0);\nI_1: x!=0&&data_at(field_addr(x,prev),0)*data_at(field_addr(x,next),p)*dlistrep(p,x);\nI_2: exists v11,x!=0&&data_at(field_addr(x,prev),0)*data_at(field_addr(x,next),v11)*data_at(field_addr(v11,prev),x)*data_at(field_addr(v11,next),p)*dlistrep(p,v11);\nI_3: exists v11 v12,x!=0&&data_at(field_addr(x,prev),0)*data_at(field_addr(x,next),v11)*data_at(field_addr(v11,prev),x)*data_at(field_addr(v11,next),v12)*data_at(field_addr(v12,prev),v11)*data_at(field_addr(v12,next),p)*dlistrep(p,v12);\n"

    # iter_back
    text_dlseg_3 = "Code: p;head;tail;head_node;tail_node;\nI_0_0: p==tail_node&&data_at(head,head_node)*data_at(tail,tail_node)*dlseg(head_node,0,tail_node,0);\nI_1_0: p==tail_node&&head_node==tail_node&&data_at(head,head_node)*data_at(tail,tail_node);\nI_1_1: data_at(head,head_node)*data_at(tail,tail_node)*dlseg(head_node,0,p,tail_node)*data_at(field_addr(tail_node,prev),p)*data_at(field_addr(tail_node,next),0);\nI_2_0: p==tail_node&&head_node==tail_node&&data_at(head,head_node)*data_at(tail,tail_node);\nI_2_1: exists v0 ,data_at(head,head_node)*data_at(tail,tail_node)*dlseg(head_node,0,p,v0)*data_at(field_addr(v0,prev),p)*data_at(field_addr(v0,next),tail_node)*data_at(field_addr(tail_node,prev),v0)*data_at(field_addr(tail_node,next),0);\nI_3_0: p==tail_node&&head_node==tail_node&&data_at(head,head_node)*data_at(tail,tail_node);\nI_3_1: exists v0 v1 ,data_at(head,head_node)*data_at(tail,tail_node)*dlseg(head_node,0,p,v1)*data_at(field_addr(v1,prev),p)*data_at(field_addr(v1,next),v0)*data_at(field_addr(v0,prev),v1)*data_at(field_addr(v0,next),tail_node)*data_at(field_addr(tail_node,prev),v0)*data_at(field_addr(tail_node,next),0);\n"

    # list_box
    text_listbox_1 = "Code: p;x;q;\nI_0: data_at(p,x) * data_at(q,x) * listrep(x);\nI_1: x!=0&&data_at(p,x)*data_at(q,field_addr(x,tail))*listrep(x);\nI_2: exists v1, v1!=0&&data_at(p,x)*data_at(field_addr(x,tail),v1)*data_at(q,field_addr(v1,tail))*listrep(v1);\nI_3: exists v1 v2, v2!=0&&data_at(p, x)*data_at(field_addr(x,tail),v1)*data_at(field_addr(v1,tail),v2)*data_at(q,field_addr(v2,tail))*listrep(v2);\n"

    text_listbox_2 = "Code: p;q;\nI_0: exists v0, data_at(p,v0) * data_at(q,v0) * listrep(v0);\nI_1: exists v0, v0!=0&&data_at(p,v0)*data_at(q,field_addr(v0,tail))*listrep(v0);\nI_2: exists v0 v1, v1!=0&&data_at(p,v0)*data_at(field_addr(v0,tail),v1)*data_at(q,field_addr(v1,tail))*listrep(v1);\nI_3: exists v0 v1 v2, v2!=0&&data_at(p, v0)*data_at(field_addr(v0,tail),v1)*data_at(field_addr(v1,tail),v2)*data_at(q,field_addr(v2,tail))*listrep(v2);\n"

    # ptree_insert
    text_ptree_1 = "Code: x;y;t;v;x_par;\nI_0: y == x && t == x_par && tree_rep(x , x_par);\nI_1_0: exists v15 v16 , v15 < v && t == x && data_at(field_addr(t, left), v16) * data_at(field_addr(t, right), y) * data_at(field_addr(t, parent), x_par) * data_at(field_addr(t, data), v15) * tree_rep(v16, t) * tree_rep(y, t);\nI_1_1: exists v15 v16 , v15 > v && t == x && data_at(field_addr(t, left), y) * data_at(field_addr(t, right), v16) * data_at(field_addr(t, parent), x_par) * data_at(field_addr(t, data), v15) * tree_rep(y, t) * tree_rep(v16, t);\nI_2_0: exists v11 v12 v13 v14 , v11 < v && v12 < v && data_at(field_addr(x, left), v13) * data_at(field_addr(x, right), t) * data_at(field_addr(x, parent), x_par) * data_at(field_addr(x, data), v11) * tree_rep(v13, x) * data_at(field_addr(t, left), v14) * data_at(field_addr(t, right), y) * data_at(field_addr(t, parent), x) * data_at(field_addr(t, data), v12) * tree_rep(v14, t) * tree_rep(y, t);\nI_2_1: exists v11 v12 v13 v18 , v11 < v && v12 > v && data_at(field_addr(x, left), v13) * data_at(field_addr(x, right), t) * data_at(field_addr(x, parent), x_par) * data_at(field_addr(x, data), v11) * tree_rep(v13, x) * data_at(field_addr(t, left), y) * data_at(field_addr(t, right), v18) * data_at(field_addr(t, parent), x) * data_at(field_addr(t, data), v12) * tree_rep(y, t) * tree_rep(v18, t);\nI_2_2: exists v11 v12 v17 v14 , v11 > v && v12 < v && data_at(field_addr(x, left), t) * data_at(field_addr(x, right), v17) * data_at(field_addr(x, parent), x_par) * data_at(field_addr(x, data), v11) * tree_rep(v17, x) * data_at(field_addr(t, left), v14) * data_at(field_addr(t, right), y) * data_at(field_addr(t, parent), x) * data_at(field_addr(t, data), v12) * tree_rep(v14, t) * tree_rep(y, t);\nI_2_3: exists v11 v12 v17 v18 , v11 > v && v12 > v && data_at(field_addr(x, left), t) * data_at(field_addr(x, right), v17) * data_at(field_addr(x, parent), x_par) * data_at(field_addr(x, data), v11) * tree_rep(v17, x) * data_at(field_addr(t, left), y) * data_at(field_addr(t, right), v18) * data_at(field_addr(t, parent), x) * data_at(field_addr(t, data), v12) * tree_rep(y, t) *tree_rep(v18, t);\n"

    # ans
    answers = {
        text_lseg_1: "lseg(w,p)*data_at(field_addr(p,tail),0)*listrep(v)",
        text_lseg_2: "lseg(x,t)*data_at(field_addr(t,tail),u)*listrep(u)",
        text_lseg_3: "lseg(l,p)*listrep(p)",
        text_lseg_4: "lseg(p,t)*data_at(field_addr(t,tail),0)*listrep(x)*listrep(y)",
        text_lseg_5: "lseg(l,p)*listrep(p)",
        text_lseg_6: "lseg(y,u)*listrep(x)*listrep(u)",
        text_lseg_7: "lseg(y,u)*listrep(x)*listrep(u)",
        text_lseg_8: "lseg(p,t)*data_at(field_addr(t,tail),0)*listrep(x)*lseg(q,w)*data_at(field_addr(w,tail),0)*listrep(y)",
        text_lseg_9: "lseg(w,p)*data_at(field_addr(p,tail),0)*listrep(y)*lseg(v,t)*data_at(field_addr(t,tail),0)*listrep(x)",
        text_lseg_10: "lseg(t,z)*listrep(z)*listrep(x)*listrep(y)",
        text_dlseg_1: "dlseg(w,v,p,0) * dlistrep (v, w)",
        text_dlseg_2: "dlseg(x,0,u_1,p) * dlistrep(p, u_1)",
        text_dlseg_3: "p == tail_node && head_node == tail_node && data_at(head , head_node) * data_at(tail , tail_node) || exists p_next, data_at(head , head_node) * data_at(tail , tail_node) *dlseg(head_node , 0 , p , p_next) * dlseg(p_next , p , tail_node , 0)",
        text_listbox_1: "listbox_seg(p,q)",
        text_listbox_2: "listbox_seg(p,q)",
        text_ptree_1: "ptree_rep(t, u_1, x, x_par)"
    }
    test_cases = []
    if "lseg" in op and "lseg0" not in op:
        test_cases += [text_lseg_1, text_lseg_2, text_lseg_3, text_lseg_4, text_lseg_5, text_lseg_6, text_lseg_7,
                       text_lseg_8, text_lseg_9, text_lseg_10]
    if "dlseg" in op and "dlseg0" not in op:
        test_cases += [text_dlseg_1, text_dlseg_2, text_dlseg_3]
    if "listbox_seg" in op and "listbox_seg0" not in op:
        test_cases += [text_listbox_1, text_listbox_2]
    if "ptree_rep" in op and "ptree_rep0" not in op:
        test_cases += [text_ptree_1]
    test_answers = []
    for case in test_cases:
        test_answers.append(answers[case])
    # for i in range(len(test_cases)):
    #     test_cases[i] = refine_case(test_cases[i])
    return test_cases, test_answers


if __name__ == '__main__':
    test_cases, test_answers = get_test_cases("lseg+dlseg")
    for i in range(len(test_cases)):
        print("Test case %d:" % i)
        print(test_cases[i])
        print("Answer:")
        print(test_answers[i])
        print("========================================")
        print()
