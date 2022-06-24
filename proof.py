"""
    姓名:金汉磊
"""
import re


class Simplify:
    def __init__(self, formula):
        self.simple_formula = None
        # 删空格
        formula = re.sub(r'\s+', '', formula)
        self.formula = formula

    def convert(self):
        """
        转化成只有蕴含和非的形式
        """
        stack_op = []  # 符号
        stack_expression = []  # 表达式
        ind = 0
        while ind < len(self.formula):
            res = re.match('[¬]*[A-Z|a-z]+[\w]*', self.formula[ind:])
            if res:
                stack_expression.append(res.group())
                ind += res.span()[1]
            elif self.formula[ind] in ['∨', '∧', '↔', '→', '¬', '(']:
                stack_op.append(self.formula[ind])
                ind += 1
            elif self.formula[ind] == ')':
                while stack_op and stack_op[-1] != '(':
                    tmp_op = stack_op.pop()
                    self.change(tmp_op, stack_expression)
                stack_op.pop()
                ind += 1
                while stack_op and stack_op[-1] == '¬':
                    tmp_op = stack_op.pop()
                    self.change(tmp_op, stack_expression)
            else:
                raise Exception("expression error")
        while stack_op:
            tmp_op = stack_op.pop()
            self.change(tmp_op, stack_expression)
        self.simple_formula = stack_expression[0]
        return self.simple_formula

    @staticmethod
    def change(op, stack_expression):
        def add_brackets(ex):
            """
            加括号
            """
            res = re.match('[¬]*[A-Z|a-z]+[A-Z|a-z|\d]*', ex)
            flg1 = res and res.span()[-1] == len(ex)
            flg2 = re.match('[¬]*\(', ex) and ex[-1] == ')'
            if not (flg1 or flg2):
                ex = '(' + ex + ')'
            return ex

        if op == '¬':
            expression = '¬' + add_brackets(stack_expression.pop())
        elif op == '∨':
            exp2 = add_brackets(stack_expression.pop())
            exp1 = add_brackets(stack_expression.pop())
            expression = '(¬' + exp1 + '→' + exp2 + ')'
        elif op == '∧':
            exp2 = add_brackets(stack_expression.pop())
            exp1 = add_brackets(stack_expression.pop())
            expression = '¬(' + exp1 + '→¬' + exp2 + ')'
        elif op == '↔':
            exp2 = add_brackets(stack_expression.pop())
            exp1 = add_brackets(stack_expression.pop())
            expression = '¬((' + exp1 + '→' + exp2 + ')→¬(' + exp2 + '→' + exp1 + '))'
        elif op == '→':
            exp2 = add_brackets(stack_expression.pop())
            exp1 = add_brackets(stack_expression.pop())
            expression = '(' + exp1 + '→' + exp2 + ')'
        else:
            raise Exception("change error " + op)
        stack_expression.append(expression)

    def proof(self, table):
        return Proof(self.simple_formula, table)


class Proof:
    def __init__(self, formula, table) -> None:
        self.formula = formula
        self.table = table
        self.prove_steps = []
        self.reasons = ['none', 'none',
                        '∀α ├α→¬¬α',
                        '∀α,β ├¬α→(α→β)',
                        'if ∑├α, then ∀β holds ∑├β→α',
                        'if ∑├α, ∑├¬β then ∑├¬(α→β)']

    def valueof(self, var):
        """
        判断命题符号的真假
        """
        if var in [True, False]:
            return var
        elif not self.table.get(var) is None:
            return self.table.get(var)
        else:
            raise Exception("key error " + str(var))

    def calculate(self, op, stack_expression):
        if op == '¬':
            val = not self.valueof(stack_expression.pop())
        elif op == '→':
            val2 = self.valueof(stack_expression.pop())
            val1 = self.valueof(stack_expression.pop())
            if val1 is True and val2 is False:
                val = False
            else:
                val = True
        else:
            raise Exception("operation error " + op)
        stack_expression.append(val)

    def calculate_value(self, part_formula=None):
        if part_formula is None:
            part_formula = self.formula
        stack_op = []
        stack_expression = []
        regex1 = '[A-Z|a-z]+[A-Z|a-z|0-9]*'
        reobj1 = re.compile(regex1)
        ind = 0
        while ind < len(part_formula):
            res = reobj1.match(part_formula[ind:])
            if res:
                stack_expression.append(self.valueof(res.group()))
                ind += res.span()[1]
            elif part_formula[ind] in ['→', '(']:
                stack_op.append(part_formula[ind])
                ind += 1
            elif part_formula[ind] == '¬':
                res_next = reobj1.match(part_formula[ind + 1:])
                if res_next:
                    stack_expression.append(not self.valueof(res_next.group()))
                    ind += res_next.span()[1] + 1
                else:
                    stack_op.append(part_formula[ind])
                    ind += 1
            elif part_formula[ind] == ')':
                while stack_op and stack_op[-1] != '(':
                    tmp_op = stack_op.pop()
                    self.calculate(tmp_op, stack_expression)
                stack_op.pop()
                ind += 1
                while stack_op and stack_op[-1] == '¬':
                    tmp_op = stack_op.pop()
                    self.calculate(tmp_op, stack_expression)
            else:
                raise Exception("expression error")
        while stack_op:
            tmp_op = stack_op.pop()
            self.calculate(tmp_op, stack_expression)

        return stack_expression[0]

    def pattern_match(self, part_formula):
        """
        得出表达式满足定理2.8.10的哪一种情形
        """
        stack_op = []
        regex1 = '[A-Z|a-z]+[A-Z|a-z|0-9]*'
        reobj1 = re.compile(regex1)
        ind = 0
        # first_left_bracket = -1
        while ind < len(part_formula) - 1:
            res = reobj1.match(part_formula[ind:])
            if res:
                ind += res.span()[1]
            elif part_formula[ind] == '(':
                stack_op.append((part_formula[ind], ind))
                ind += 1
            elif part_formula[ind] in ['¬', '→']:
                stack_op.append((part_formula[ind], ind))
                ind += 1
            elif part_formula[ind] == ')':
                while stack_op and stack_op[-1][0] != '(':
                    stack_op.pop()
                stack_op.pop()
                ind += 1
                while stack_op and stack_op[-1][0] == '¬':
                    stack_op.pop()
            else:
                raise Exception("expression error")
        if part_formula[-1] == ')':
            stack_op.append((part_formula[-1], len(part_formula) - 1))

        im_index = self.find_index(stack_op, '→')
        left_index = self.find_index(stack_op, '(')
        if len(stack_op) == 0 and self.calculate_value(part_formula):
            return 0, part_formula  # 额外添加的情形0，即表达式为命题符号本身
        elif len(stack_op) > 1 and stack_op[0][0] == '¬' and stack_op[1][0] == '¬' \
                and self.calculate_value(part_formula[2:]):
            return 2, part_formula[2:]
        elif stack_op[0][0] == '¬' and im_index != -1 \
                and self.calculate_value(part_formula[left_index + 1:im_index]) \
                and not self.calculate_value(part_formula[im_index + 1:len(part_formula) - 1]):
            return 5, part_formula[left_index + 1:im_index], part_formula[im_index + 1:len(part_formula) - 1]
        elif stack_op[0][0] == '(' and im_index != -1:
            if not self.calculate_value(part_formula[left_index + 1:im_index]):
                return 3, part_formula[left_index + 1:im_index], part_formula[im_index + 1:len(part_formula) - 1]
            elif self.calculate_value(part_formula[im_index + 1:len(part_formula) - 1]):
                return 4, part_formula[left_index + 1:im_index], part_formula[im_index + 1:len(part_formula) - 1]
            else:
                raise Exception("expression match false" + part_formula)
        elif stack_op[0][0] == '¬' and not self.calculate_value(part_formula[1:]):
            return 1, part_formula[1:]
        else:
            # print(left_index,im_index)
            raise Exception("expression match false" + part_formula)

    def find_index(self, stack_op, character):
        """
        得出某个符号在符号栈中的索引
        """
        for indx in range(len(stack_op) - 1, -1, -1):
            if stack_op[indx][0] == character:
                return stack_op[indx][1]
        return -1

    def process_formula(self, simple_formula, num=0):
        """
        递归得调用pattern_match，并将证明过程添加进prove_steps栈，num为递归树的深度
        """
        pattern = self.pattern_match(simple_formula)
        if pattern[0] == 0:
            self.prove_steps.append(('∑├' + simple_formula, self.reasons[0], num))
            return
        elif pattern[0] == 1:
            self.prove_steps.append(('∑├' + simple_formula, self.reasons[1], num))
            return
        elif pattern[0] == 2:
            self.prove_steps.append(('∑├' + simple_formula, self.reasons[2], num))
            self.process_formula(pattern[1], num + 1)
        elif pattern[0] == 3:
            self.prove_steps.append(('∑├' + simple_formula, self.reasons[3], num))
            self.process_formula('¬' + pattern[1], num + 1)
        elif pattern[0] == 4:
            self.prove_steps.append(('∑├' + simple_formula, self.reasons[4], num))
            self.process_formula(pattern[2], num + 1)
        elif pattern[0] == 5:
            self.prove_steps.append(('∑├' + simple_formula, self.reasons[5], num))
            self.process_formula(pattern[1], num + 1)
            self.process_formula('¬' + pattern[2], num + 1)
        else:
            raise Exception("process_formula error\n" + str(pattern))

    def disp(self):
        """
        显示prove_steps栈中的证明过程，其中定理2.8.10情形5中use step使用的必是递归树同层的前两个证明步骤
        """
        if not self.calculate_value():
            print('非重言式.')
            return
        self.process_formula(self.formula)
        longest = len(self.prove_steps[0][0])
        prove_steps = list(reversed(self.prove_steps))
        indx = 0
        while indx < len(prove_steps):
            step, reason, num = prove_steps[indx]
            if reason == self.reasons[5]:
                pre = []
                for p_ind in range(indx):
                    if prove_steps[p_ind][2] == num + 1:
                        pre.append(p_ind)
                reason = reason + ',use step {},{}'.format(pre[-2], pre[-1])
            print('{0}\t{1:<{width}}{2}'.format(indx, step, reason, width=longest + 2))
            indx += 1


if __name__ == '__main__':
    formulas = '(P∨(Q∧R))↔((P∨Q)∧(P∨R))'
    table = {'P': True, 'Q': False, 'R': False}

    simplify = Simplify(formulas)
    print('简化前的公式如下：')
    print(simplify.formula, end='\n\n')
    print('简化后的公式如下：')
    print(simplify.convert(), end='\n\n')
    print('公式的证明过程如下：')
    simplify.proof(table).disp()
