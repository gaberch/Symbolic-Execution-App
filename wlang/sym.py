# The MIT License (MIT)
# Copyright (c) 2016 Arie Gurfinkel

# Permission is hereby granted, free of charge, to any person obtaining
# a copy of this software and associated documentation files (the
# "Software"), to deal in the Software without restriction, including
# without limitation the rights to use, copy, modify, merge, publish,
# distribute, sublicense, and/or sell copies of the Software, and to
# permit persons to whom the Software is furnished to do so, subject to
# the following conditions:

# The above copyright notice and this permission notice shall be
# included in all copies or substantial portions of the Software.

# THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
# EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
# MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
# NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
# LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION
# OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
# WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.

from __future__ import print_function

import wlang.ast
import cStringIO
import sys
import wlang.undef_visitor

import z3

class SymState(object):
    def __init__(self, solver = None):
        # environment mapping variables to symbolic constants
        self.env = dict()
        # path condition
        self.path = list ()
        self._solver = solver
        if self._solver is None:
            self._solver = z3.Solver ()

        # true if this is an error state
        self._is_error = False

    def add_pc (self, *exp):
        """Add constraints to the path condition"""
        self.path.extend (exp)
        self._solver.append (exp)
        
    def is_error (self):
        return self._is_error
    def mk_error (self):
        self._is_error = True
        
    def is_empty (self):
        """Check whether the current symbolic state has any concrete states"""
        res = self._solver.check ()
        return res == z3.unsat

    def pick_concrete (self):
        """Pick a concrete state consistent with the symbolic state.
           Return None if no such state exists"""
        res = self._solver.check ()
        if res <> z3.sat:
            return None
        model = self._solver.model ()
        import wlang.int
        st = wlang.int.State ()
        for (k, v) in self.env.items():
            st.env [k] = model.eval (v)
        return st
        
    def fork(self):
        """Fork the current state into two identical states that can evolve separately"""
        child = SymState ()
        child.env = dict(self.env)
        child.add_pc (*self.path)
        
        return (self, child)
    
    def __repr__ (self):
        return str(self)
        
    def to_smt2 (self):
        """Returns the current state as an SMT-LIB2 benchmark"""
        return self._solver.to_smt2 ()
    
        
    def __str__ (self):
        buf = cStringIO.StringIO ()
        for k, v in self.env.iteritems():
            buf.write (str (k))
            buf.write (': ')
            buf.write (str (v))
            buf.write ('\n')
        buf.write ('pc: ')
        buf.write (str (self.path))
        buf.write ('\n')
            
        return buf.getvalue ()
                   
class SymExec (wlang.ast.AstVisitor):
    def __init__(self):
        pass

    def run (self, ast, state):
        ## set things up and 
        ## call self.visit (ast, state=state)
        return self.visit(ast, state=state)


    def visit_IntVar (self, node, *args, **kwargs):
        return kwargs['state'].env[node.name]
    
    def visit_BoolConst(self, node, *args, **kwargs):
        return z3.BoolVal (node.val)

    def visit_IntConst (self, node, *args, **kwargs):
        return z3.IntVal (node.val)
    
    def visit_RelExp (self, node, *args, **kwargs):
        lhs = self.visit (node.arg (0), *args, **kwargs)
        rhs = self.visit (node.arg (1), *args, **kwargs)
        if node.op == '<=': return lhs <= rhs
        if node.op == '<': return lhs < rhs
        if node.op == '=': return lhs == rhs
        if node.op == '>=': return lhs >= rhs
        if node.op == '>': return lhs > rhs
        
        assert False

    def visit_BExp (self, node, *args, **kwargs):
        kids = [self.visit (a, *args, **kwargs) for a in node.args]

        if node.op == 'not':
            assert node.is_unary ()
            assert len (kids) == 1
            return z3.Not (kids[0])

        if node.op == 'or':
            return z3.Or(*kids)
        elif node.op == 'and':
            return z3.And(*kids)

        assert False
        
    def visit_AExp (self, node, *args, **kwargs):
        kids = [self.visit (a, *args, **kwargs) for a in node.args]

        fn = None
        base = None

        if node.op == '+':
            fn = lambda x, y: x + y
            
        elif node.op == '-':
            fn = lambda x, y: x - y

        elif node.op == '*':
            fn = lambda x, y: x * y

        elif node.op == '/':
            fn = lambda x, y : x / y
            
        assert fn is not None
        return reduce (fn, kids)
        
    def visit_SkipStmt (self, node, *args, **kwargs):
        return [kwargs['state']]    
    
    def visit_PrintStateStmt (self, node, *args, **kwargs):    
        print(kwargs['state'])
        return [kwargs['state']]

    def visit_AsgnStmt (self, node, *args, **kwargs):
        st = kwargs['state']
        x = self.visit(node.rhs, *args, **kwargs)
        st.env[node.lhs.name] = z3.FreshInt(node.lhs.name)
        st.add_pc(st.env[node.lhs.name] == x) 
        return [st]

    def visit_IfStmt (self, node, *args, **kwargs):
        cond = self.visit (node.cond, *args, **kwargs)

        then_case,else_case = kwargs['state'].fork()
        then_case.add_pc(cond)
        else_case.add_pc(z3.Not(cond))

        res = []
        
        if not then_case.is_empty():
            kwargs['state'] = self.visit(node.then_stmt, state = then_case)
            res.extend(kwargs['state'])

        if not else_case.is_empty():
            if not node.has_else():
                res.append(then_case)
            else:
                kwargs['state'] = self.visit(node.else_stmt, state = else_case)
                res.extend(kwargs['state'])

        return res
            
    def visit_WhileStmt (self, node, *args, **kwargs):
        if node.inv is not None:
            pre_inv = z3.simplify (self.visit(node.inv,*args,**kwargs))
            pre_state, loop_state = kwargs['state'].fork()

            pre_state.add_pc(z3.Not(pre_inv))
            if not pre_state.is_empty():
                print ("Invariant does not hold before initial loop entry")
                print(node.inv)
                print(pre_state)
                pre_state.mk_error()

            get_def = wlang.undef_visitor.UndefVisitor()
            get_def.check(node.body)

            for var in get_def.get_defs():
                loop_state.env[var.name] = z3.FreshInt(var.name)

            inv_pre = z3.simplify(self.visit(node.inv,*args,state=loop_state))
            loop_state.add_pc(inv_pre)

            cond = self.visit(node.cond, *args, state = loop_state)
            enter_st,exit_st = loop_state.fork()

            if not enter_st.is_empty():
                res = self.visit(node.body, state = enter_st)

                for i in res:
                    inv_post = z3.simplify(self.visit(node.inv, *args, state = i))
                    i.add_pc(z3.Not(inv_post))

                    if not i.is_empty():
                        print("Invariant does not hold within the loop")
                        print("inv: ", node.inv)
                        print("inv_post: ", inv_post)
                        print("i: ", i)
                        print("pc", z3.And (i.path).sexpr())
                        i.mk_error()

            if not exit_st.is_empty():
                return [exit_st]                


        out = []
        count = 1
        execution = [kwargs['state']]

        while count <= 10:
            res = []
            for x in execution:

                
                cond = self.visit (node.cond, state = x)
                true_case, false_case = x.fork()
                true_case.add_pc(cond)
                false_case.add_pc(z3.Not(cond))

                if not false_case.is_empty():
                    out.append(false_case)
                
                if not true_case.is_empty():
                    kwargs['state'] = self.visit (node.body, state = true_case)
                    res.extend(kwargs['state'])

            execution = res
            count += 1
        
        return out

                

    def visit_AssertStmt (self, node, *args, **kwargs):
        ## Don't forget to print an error message if an assertion might be violated
        
        cond = self.visit (node.cond, *args, **kwargs)

        true_case,false_case = kwargs['state'].fork()
        true_case.add_pc(cond)
        false_case.add_pc(z3.Not(cond))

        if not false_case.is_empty():
            print ("Assertion may be violated for: ", cond)
            false_case.mk_error()

        if not true_case.is_empty():
            return [true_case]
        else:
            return []

        
    
    def visit_AssumeStmt (self, node, *args, **kwargs):
        st = kwargs['state']
        cond = self.visit(node.cond,*args, **kwargs)
        st.add_pc (cond)
        if not st.is_empty():
            return [st]
        else:
            return []

    
    def visit_StmtList (self, node, *args, **kwargs):
          

        res = []
        nkwargs = dict(kwargs)
        st = [kwargs['state']] 

        for s in node.stmts:
            temp_res = []
            for i in st:
                nkwargs ['state'] = i
                kwargs['state'] = self.visit(s,state = nkwargs ['state'])
                temp_res.extend(kwargs['state'])
            res = temp_res
        
        return res

    def visit_HavocStmt (self, node, *args, **kwargs):
        st = kwargs['state']
        for var in node.vars:
            st.env[var.name] = z3.FreshInt (var.name)
        return [st]




        
def _parse_args ():
    import argparse
    ap = argparse.ArgumentParser (prog='sym',
                                  description='WLang Interpreter')
    ap.add_argument ('in_file', metavar='FILE', help='WLang program to interpret')
    args = ap.parse_args ()
    return args
    
def main ():
    args = _parse_args ()
    ast = wlang.ast.parse_file (args.in_file)
    st = SymState ()
    sym = SymExec ()

    states = sym.run (ast, st)
    if states is None:
        print ('[symexec]: no output states')
    else:
        count = 0
        for out in states:
            count = count + 1
            print ('[symexec]: symbolic state reached')
            print (out)
        print ('[symexec]: found', count, 'symbolic states')
    return 0

if __name__ == '__main__':
    sys.exit (main ())
                    
