# -*- coding: utf-8 -*-

import re

WS0 = r"(\s)*"
IdentPat = re.compile(r"[a-zA-Z_][a-zA-Z0-9_]*")
TokPat = re.compile(r"\s*([a-zA-Z_][a-zA-Z0-9_]*|[*])")
CompositeStartPat = re.compile(r"\s*(struct|union|enum)\s+[a-zA-Z_][a-zA-Z0-9_]*\s*[{]")

def parse_param(s: str):
    s = s.strip()
    toks = []
    while len(s) > 0:
        mtok = re.match(TokPat, s)
        if mtok:
            toks.append(mtok.group().strip())
            s = s[mtok.end():]
        else:
            return None
    if len(toks) >= 2 and re.fullmatch(IdentPat, toks[-1]):
        return " ".join(toks[:-1]), toks[-1]
    else:
        return None
    
# int foo(int a, int b) -> int foo(int, int); int a; int b; int __return;
# void bar(int a, int b) -> void bar(int, int); int a; int b;
def process_funhead(s: str):
    lp_idx = s.find('(')
    rp_idx = s.find(')')
    if lp_idx == -1 or rp_idx == -1:
        return None
    fun_str = s[:lp_idx].strip()
    param_str = s[lp_idx + 1 : rp_idx].strip()
    mf = parse_param(fun_str)
    if mf:
        if mf[0] == 'void':
            ret_decl = []
        else:
            ret_decl = [mf[0] + ' ' + "__return;"]
        fun_decl = mf[0] + ' ' + mf[1] + "("
        if param_str == 'void':
            fun_decl += 'void);'
            param_decls = []
        else:
            params = param_str.split(',')
            param_decls = []
            if len(params) >= 1:
                mp = parse_param(params[0])
                if mp:
                    fun_decl += mp[0]
                    param_decls.append(mp[0] + ' ' + mp[1] + ';')
                else:
                    return None
                for p in params[1:]:
                    mp = parse_param(p)
                    if mp:
                        fun_decl += ','
                        fun_decl += mp[0]
                        param_decls.append(mp[0] + ' ' + mp[1] + ';')
                    else:
                        return None
                fun_decl += ');'
            else:
                return None
        return [fun_decl] + param_decls + ret_decl, rp_idx
    else:
        return None

# find the index of the ')' matching the first '(' in s[base:]
def match_paren(s: str, base: int):
    cnt = 0
    for i in range(base, len(s)):
        if s[i] == '(':
            cnt += 1
        elif s[i] == ')':
            assert(cnt > 0)
            if cnt == 1:
                return i
            else:
                cnt -= 1
    raise Exception("() not match!")

# find the index of the '}' matching the first '{' in s[base:]
def match_brace(s: str, base: int):
    cnt = 0
    for i in range(base, len(s)):
        if s[i] == '{':
            cnt += 1
        elif s[i] == '}':
            assert(cnt > 0)
            if cnt == 1:
                return i
            else:
                cnt -= 1
    raise Exception("{} not match!")

def have_prefix(s: str, prefix: str):
    l = len(prefix)
    return len(s) >= l and s[0:l] == prefix

# return the index of end of the next ps in s
# and list of partial statement to be executed
# ignore [0 : base]
def segment_process_ps(s: str, base: int, funhead2decl=True) -> tuple:
    length = len(s)
    while base < length and s[base].isspace():
        base += 1
    if base == length:
        return (length - 1, [""])
    
    prefix_tmp = s[base:]

    composite_match = re.match(CompositeStartPat, prefix_tmp)

    if composite_match:
        _, end = composite_match.span()
        lbrace_offset = end - 1
        rbrace_offset = match_brace(prefix_tmp, lbrace_offset)
        semic_idx = s.find(';', base + rbrace_offset + 1)
        return (semic_idx, [s[base : semic_idx + 1]])
    elif have_prefix(prefix_tmp, '{') or have_prefix(prefix_tmp, '}'):
        return (base, [s[base]])
    elif have_prefix(prefix_tmp, 'else'):
        return (base + 3, [s[base : base + 4]])
    elif have_prefix(prefix_tmp, 'while'):
        p_idx = match_paren(s, base)
        return (p_idx, [s[base : p_idx + 1]])
    elif have_prefix(prefix_tmp, 'for'):
        p_idx = match_paren(s, base)
        return (p_idx, [s[base : p_idx + 1]])
    elif have_prefix(prefix_tmp, 'if'):
        p_idx = match_paren(s, base)
        return (p_idx, [s[base : p_idx + 1]])
    elif have_prefix(prefix_tmp, '//@'):
        newline_idx = s.find('\n', base)
        if newline_idx == -1: # line comment terminated by EOF
            return (length - 1, s[base:])
        else:
            return (newline_idx - 1, [s[base : newline_idx + 1]])
    elif have_prefix(prefix_tmp, '/*@'):
        end_idx = s.find('*/', base)
        if end_idx == -1:
            raise Exception("comment not finished!")
        else:
            ass_str = s[base + 3 : end_idx]
            return (end_idx + 1, [s[base : end_idx + 2]])
    elif have_prefix(prefix_tmp, '//'):
        newline_idx = s.find('\n', base)
        if newline_idx == -1: # line comment terminated by EOF
            return (length - 1, "")
        else: # skip plain comment
            next_start_index = newline_idx + 1
            return segment_process_ps(s, next_start_index)
    elif have_prefix(prefix_tmp, '/*'):
        end_idx = s.find('*/', base)
        if end_idx == -1:
            raise Exception("comment not finished!")
        else: # skip plain comment
            next_start_index = end_idx + 2
            return segment_process_ps(s, next_start_index)
    else:
        funhead_match = process_funhead(prefix_tmp)
        if funhead_match:
            (decls, end) = funhead_match
            if funhead2decl:
                return (base + end, decls)
            else:
                return (base + end, [s[base : base + end + 1]])
        semi_idx = s.find(';', base)
        lbrace_idx = s.find('{', base)
        if semi_idx == -1:
            if lbrace_idx == -1:
                raise Exception("invalid statement")
            else:
                end_idx = lbrace_idx - 1
        else:
            if lbrace_idx == -1:
                end_idx = semi_idx
            else:
                if semi_idx < lbrace_idx:
                    end_idx = semi_idx
                else:
                    end_idx = lbrace_idx - 1
        return (end_idx, [s[base : end_idx + 1]])
