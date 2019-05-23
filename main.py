#-*- coding:utf-8 -*-
# Author: Xiang
# Date: 2019/5/20

import random
import string

# 语法类，描述某语法，并进行语法分析
class Grammar:
    # 内部成员变量
    grammar = {}    # 文法的基本定义
    begin_ch = ''   # 文法的开始符号
    vt = [] # 终结符集合
    vn = [] #非终结符集合
    first = {}  # 各非终结符的FIRST集
    follow = {} # 各终结符的FOLLOW集
    parsing_table = {}  # 文法的LL(1)分析表

    # 构造函数，传入自定义的文法grammar与开始符号begin_ch以初始化
    def __init__(self, grammar, begin_ch):
        self.grammar = grammar
        self.begin_ch = begin_ch
        for rule in grammar:
            temp = grammar[rule].split('|')
            self.grammar[rule] = temp
        print('*****初始文法*****')
        self.print_grammar()
    # End def __init__

    # 间接左递归路径更新
    def trace_lr(self, vn, rule_1, rule_2, lr_list):
        # lr_list用于记录rule_1左递归经过的规则
        for item in self.grammar[rule_2]:
            # 若当前规则不为空，则继续判断
            if len(item) == 0:
                continue
            # 若当前规则最左符号为非终结符，则检查其是否与rule_1相同
            if item[0] in vn:
                # 若为直接左递归，则跳过此条规则
                if item[0] == rule_2:
                    continue
                # 若不同且非直接左递归，则进入下一层
                elif not item[0] == rule_1:
                    # 若沿着该路径可得rule_1，则加入当前规则至lr_list，返回True
                    if self.trace_lr(vn, rule_1, item[0], lr_list):
                        lr_list.append(rule_2)
                        return True
                # 若相同，则加入当前规则至lr_list，返回True
                elif item[0] == rule_1:
                    lr_list.append(rule_2)
                    return True
        # 若经过上述推导无法得到rule_1，返回false
        return False

    # 消除间接左递归
    def indirect_left_recursion(self):
        vn = [rule for rule in self.grammar]
        lr_list = []  # 暂存间接左递归的路径
        delete_list = []  # 记录被替换掉的多余规则
        for rule in vn:
            # 若当前规则被判定为多余规则即将被删掉，则跳过操作
            if rule in delete_list:
                continue
            for item in self.grammar[rule]:
                # 若该规则最左侧是不为rule的非终结符，检查其是否存在间接左递归
                if item[0] == rule:
                    continue
                if item[0] in vn and self.trace_lr(vn, rule, item[0], lr_list):
                    n = len(lr_list)
                    for i in range(n):  # 获取替换的目标规则next_r
                        if i < n - 1:
                            next_r = lr_list[i+1]
                        else:
                            next_r = rule
                        # 用lr_list[i]内的规则替换掉next_r的最左符号
                        for r in self.grammar[next_r]:
                            if len(self.grammar[next_r]) > 0 and r[0] == lr_list[i]:
                                r_temp = [a + r[1:] for a in self.grammar[lr_list[i]]]
                                self.grammar[next_r].remove(r)
                                self.grammar[next_r] += r_temp
                                delete_list.append(lr_list[i])  # 将被替换的规则加入delete_list
                    lr_list = []
        if len(delete_list) > 0:
            # 消除间接左递归后
            print('*****消除间接左递归*****')
            self.print_grammar()
            print('*****删除多余符号*****')
            for rule in delete_list:
                self.grammar.pop(rule)
            self.print_grammar()
        else:
            print('*****不存在间接左递归*****')

    # 消除直接左递归
    def immediate_left_recursion(self):
        # 新建一个字典，用于存储消除直接左递归后的文法
        grammar_new = {}
        is_exist_lr = False
        for rule_1 in self.grammar:
            temp = self.grammar[rule_1]
            flag = False    # 是否存在直接左递归的标记，默认不存在
            alpha = []  # 紧跟在直接左递归后的规则
            beta = []   # 不存在左递归的规则
            for (index, item) in enumerate(temp):
                if item[0] == rule_1:
                    flag = True
                    is_exist_lr = True
                    temp[index] = item[1:]
                    alpha.append(temp[index])
                else:
                    beta.append(temp[index])
            # 根据公式，将alpha与beta内的规则还原
            if flag:
                # 随机生成一个不重复的字母，作为派生规则的非终结符
                while True:
                    rule_2 = random.choice(string.ascii_uppercase)
                    if rule_2 not in self.grammar \
                        and rule_2 not in grammar_new:
                        break
                grammar_new[rule_1] = [b+rule_2 for b in beta]
                grammar_new[rule_2] = [a+rule_2 for a in alpha]
                grammar_new[rule_2].append('')
            else:
                grammar_new[rule_1] = temp
        if is_exist_lr:
            print('*****消除直接左递归*****')
            self.grammar = grammar_new
        else:
            print('*****不存在直接左递归*****')
    # End def is_left_recursion

    # 递归求first集
    def first_deep(self, first, key):
        for item in self.grammar[key]:
            # 若该规则为空符号串且空符号串不在first中，直接加入first
            if item == '' and '' not in first:
                first.append('')
            # 若该规则首符号为终结符且不在first中，直接加入first
            elif item[0] in self.vt and item[0] not in first:
                first.append(item[0])
            # 若规则非空且首符号为非终结符，再次递归
            else:
                self.first_deep(first, item[0])
    # End def first_deep

    # 列表去重，去除空符号串
    def simplify(self, mylist):
        for item in mylist:
            mylist[item] = list(set(mylist[item]))
            if '' in mylist[item]:
                mylist[item].remove('')
    # End def simplify

    # 判断某非终结符能否广义推导到空符号串
    def is_generalized_to_empty(self, rule):
        # 若可直接推导为空
        if '' in self.grammar[rule]:
            return True
        # 若不可直接推导为空
        for item in self.grammar[rule]:
            for i in item:
                # 若规则中包含非终结符的定义
                if i in self.vn:
                    return False
                # 检查广义推导
                if self.is_generalized_to_empty(i):
                    return True
                else:
                    return False
    # End def is_generalized_to_empty

    # 构造first和follow集，同时求vn和vt
    def first_and_follow(self):
        # 创建终结符vt和非终结符vn数组
        self.vn = [a for a in self.grammar]
        for rule in self.grammar:
            for item in self.grammar[rule]:
                for i in item:
                    if i not in self.vt and i not in self.vn:
                        self.vt.append(i)
        # 求first集合follow集
        # 先求first集
        for rule in self.grammar:
            self.first[rule] = []
            for item in self.grammar[rule]:
                if item == '' and '' not in self.first[rule]:
                    self.first[rule].append('')
                elif item[0] in self.vt and item[0] not in self.first[rule]:
                    self.first[rule].append(item[0])
                else:
                    self.first_deep(self.first[rule], item[0])  # 递归
        # 再求follow集
        for rule in self.grammar:
            self.follow[rule] = []   # 初始化follow集
        self.follow[self.begin_ch].append('#')    # 根据步骤1，加入‘#’号
        for rule in self.grammar:
            for item in self.grammar[rule]:
                for i in range(len(item)):  # 根据步骤2加入符号
                    if item[i] in self.vn and i < len(item)-1:
                        if item[i+1] in self.vt:
                            self.follow[item[i]].append(item[i+1])
                        else:
                            self.follow[item[i]].extend(self.first[item[i+1]])
        self.simplify(self.follow)  # 去重，去掉空符号串
        for rule in self.grammar:
            for item in self.grammar[rule]:
                n = len(item)
                for i in range(n):  # 根据步骤3加入符号
                    if item[i] in self.vn and i == n-1:
                        self.follow[item[i]].extend(self.follow[rule])
                    elif item[i] in self.vn and i < n-1 \
                            and item[i+1] in self.vn:
                        # 若其后的非终结符定义的规则能广义推导到空符号串
                        if self.is_generalized_to_empty(item[i+1]):
                            self.follow[item[i]].extend(self.follow[rule])
        self.simplify(self.follow)  # 去重，去掉空符号串
        # return self.vn, self.vt, self.first, self.follow
    # End def first_and_follow

    # 构造文法分析表
    def construct_parsing_table(self):
        # 初始化分析表为空（后续加入空符号串时，用‘#’代替）
        for i in self.vn:
            self.parsing_table[i] = {}
            for j in self.vt:
                self.parsing_table[i][j] = ''
            self.parsing_table[i]['#'] = ''
        # 遍历文法，同时利用first集和follow集，开始构造分析表
        for rule in self.grammar:
            for item in self.grammar[rule]:
                if item == '':  # 当规则为空符号串时，找follow集
                    for i in self.follow[rule]:
                        # 此处用‘#’代替空符号串
                        self.parsing_table[rule][i] = '#'
                elif item[0] in self.vt: # 当规则为终结符时，直接加入分析表
                    self.parsing_table[rule][item[0]] = item
                elif item[0] in self.vn: # 当规则为非终结符时
                    for i in self.first[item[0]]:    # 找非终结符的first集
                        if not i == '': # first不为空时，直接加入分析表
                            self.parsing_table[rule][i] = item
                        else:   # first为空时，找follow集
                            for i in self.follow[rule]:
                                self.parsing_table[rule][i] = '#'
        # return self.parsing_table
    # End def parsing_table

    # LL(1)分析器总控程序
    def analysis(self, s):
        # 输入待分析串并初始化分析栈和预留输入串栈
        analysis_stack = ['#', self.begin_ch]
        remain_str_stack = list(reversed(s + '#'))
        flag = True
        print('*****开始分析目标串：\'', s, '\'*****')
        print('******************************************************')
        print('分析栈：', analysis_stack)
        print('余留串：', remain_str_stack)  
        while flag:
            print('******************************************************')
            # 分别获取两个栈的栈顶元素
            a_top = analysis_stack[len(analysis_stack)-1]
            r_top = remain_str_stack[len(remain_str_stack)-1]
            # 将自定义符号串归结为‘i’
            if r_top not in self.vt and not r_top == '#':
                while r_top not in self.vt and not r_top == '#':
                    remain_str_stack.pop()
                    r_top = remain_str_stack[len(remain_str_stack)-1]
                remain_str_stack.append('i')
                r_top = 'i'
                print('将自定义符号串归结为\'i\'')
                print('分析栈：', analysis_stack)
                print('余留串：', remain_str_stack)
            # 当两个栈顶元素相同时，分别pop
            if a_top == r_top and not a_top == '#':
                analysis_stack.pop()
                remain_str_stack.pop()
                print('分析栈：', analysis_stack)
                print('余留串：', remain_str_stack)
                continue
            # 当两个栈顶都为‘#’时，文法分析成功
            elif a_top == '#' and r_top == '#':
                flag = False
                print('分析成功，该句子符合本文法。')
                continue
            # 当两个栈顶元素不同时，寻找是否存在产生式用以归结
            else:
                # 若分析栈栈顶元素是非终结符，则寻找规则
                if a_top in self.vn:
                    rule_temp = self.parsing_table[a_top][r_top]
                    print('所用产生式：', rule_temp)
                    rule_temp = list(reversed(rule_temp))
                    if rule_temp == ['#']:
                        analysis_stack.pop()
                    elif not rule_temp == ['#'] and len(rule_temp):
                        analysis_stack.pop()
                        n = len(rule_temp)
                        for i in range(n):
                            analysis_stack.append(rule_temp[i])
                    else:
                        flag = False
                        print('无对应产生式，分析失败，该句子不符合本文法。')
                        continue
                # 若分析栈栈顶不是非终结符，则匹配失败
                else:
                    flag = False
                    print('无对应分析表项，分析失败，该句子不符合本文法。')
                    continue
            print('分析栈：', analysis_stack)
            print('余留串：', remain_str_stack)       
    # End def analysis

    # 格式化输出grammar
    def print_grammar(self):
        for rule in self.grammar:
            print(rule + ' -> ', end = '')
            for (index, item) in enumerate(self.grammar[rule]):
                if item == '':
                    temp = '\'\''
                else:
                    temp = item
                if not index == len(self.grammar[rule]) - 1:
                    print(temp + ' | ', end = '')
                else:
                    print(temp)

    # 输出文法定义、vn、vt、first集、follow集和文法分析表
    def print_all(self):
        self.print_grammar()
        print('*****非终结符集vn和终结符集vt*****')
        print('VN：', self.vn)
        print('VT：', self.vt)
        print('*****FIRST集*****')
        for rule in self.first:
            print('FIRST(' + rule + ') = {', end = '')
            for (index, item) in enumerate(self.first[rule]):
                if not index == len(self.first[rule]) - 1:
                    print('\'' + item + '\', ', end = '')
                else:
                    print('\'' + item + '\'}')
        print('*****FOLLOW集*****')
        for rule in self.follow:
            print('FOLLOW(' + rule + ') = {', end = '')
            for (index, item) in enumerate(self.follow[rule]):
                if not index == len(self.follow[rule]) - 1:
                    print('\'' + item + '\', ', end = '')
                else:
                    print('\'' + item + '\'}')
        print('*****文法分析表*****')
        for i in range(len(self.vt) + 2):
            print('--------', end = '')
        print('-\n|\t', end = '')
        for i in self.vt:
            print(i, '\t', end = '')
        print('#\t|\n|', end = '')
        for i in range(len(self.vt) + 2):
            print('--------', end = '')
        print('')
        for i in self.vn:
            print('|', i, '\t', end = '')
            for j in self.vt:
                print(self.parsing_table[i][j], '\t', end = '')
            print(self.parsing_table[i]['#'], end ='')
            print('\t|')
        for i in range(len(self.vt) + 2):
            print('--------', end = '')
        print('-')
    # End def output
# End class Grammar

if __name__ == '__main__':
    # 文法G[E]
    grammar_E = {
        'E':'E+T|T',
        'T':'T*F|F',
        'F':'(E)|i'
    }
    begin_ch = 'E'
    # 文法G[S]
    # grammar_E = {
    #     'S':'Qc|c',
    #     'Q':'Rb|b',
    #     'R':'Sa|a'
    # }
    # begin_ch = 'S'
    # 自定义文法输入
    # grammar_E = {}
    # n = int(input('请输入文法的表达式数目：'))
    # begin_ch = input('请输入文法的开始符号：')
    # print('请按S->A|B的格式，输入上述', n, '条规则，自定义标识符用‘i’表示：')
    # grammar_temp = []
    # for i in range(n):
    #     s = input().split('->')
    #     grammar_E[s[0]] = s[1]
    my_grammar = Grammar(grammar_E, begin_ch)  # 创建Grammar实例
    my_grammar.indirect_left_recursion()  # 消除间接左递归
    my_grammar.immediate_left_recursion()  # 消除直接左递归同时更新vn和vt
    my_grammar.first_and_follow()  # 求FIRST和FOLLOW集
    my_grammar.construct_parsing_table()  # 构造LL(1)文法分析表
    my_grammar.print_all()  # 输出以上结果
    s = 'abc+age+80'    # 文法G[E]判断通过样例
    # s = '(abc-80(*s5)'  # 文法G[E]判断失败样例
    # s = 'cabcabc'    # 文法G[S]判断通过样例
    # s = 'abcbcabccc'  # 文法G[S]判断失败样例
    # s = input('请输入待分析的符号串：')
    my_grammar.analysis(s)
    