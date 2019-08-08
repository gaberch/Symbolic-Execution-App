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

import unittest
import wlang.ast as ast
import wlang.sym
import z3
import sys
import os

class TestSym (unittest.TestCase):
    def test_one (self):
        prg1 = "havoc x; assume x > 10; assert x > 15"
        ast1 = ast.parse_string (prg1)
        sym = wlang.sym.SymExec ()
        st = wlang.sym.SymState ()
        out = [s for s in sym.run (ast1, st)]
        self.assertEquals (len(out), 1)
    def test_arithmetic (self):
        prg1 = "x :=  10; y := 15; if x < y then {x := x + y * 5/5 - 2}"
        ast1 = ast.parse_string (prg1)
        sym = wlang.sym.SymExec ()
        st = wlang.sym.SymState ()
        out = [s for s in sym.run (ast1, st)]
        self.assertEquals (len(out), 1)
    def test_bool_const (self):
        prg1 = "x :=  10; if true then {x := x + 1}"
        ast1 = ast.parse_string (prg1)
        sym = wlang.sym.SymExec ()
        st = wlang.sym.SymState ()
        out = [s for s in sym.run (ast1, st)]
        self.assertEquals (len(out), 1)
    def test_bool_exp (self):
        prg1 = "x :=  1; y := 2; if x < y or x >= 0 and not x <= 15 then skip"
        ast1 = ast.parse_string (prg1)
        sym = wlang.sym.SymExec ()
        st = wlang.sym.SymState ()
        out = [s for s in sym.run (ast1, st)]
        self.assertEquals (len(out), 1)
    def test_rel_exp (self):
        prg1 = "x :=  1; y := 2; if x > y or x = 1  then skip; print_state"
        ast1 = ast.parse_string (prg1)
        sym = wlang.sym.SymExec ()
        st = wlang.sym.SymState ()
        out = [s for s in sym.run (ast1, st)]
        self.assertEquals (len(out), 1)
    def test_pick_concrete (self):
        prg1 = "x :=  1; while x < 5 do {x := x + 1}"
        ast1 = ast.parse_string (prg1)
        sym = wlang.sym.SymExec ()
        st = wlang.sym.SymState (z3.Solver())
        self.assertIsNotNone(st.pick_concrete())
    def test_pick_concrete2 (self):
        # prg1 = "if 1 > 2 then x := 1"
        # ast1 = ast.parse_string (prg1)
        sym = wlang.sym.SymExec ()
        st = wlang.sym.SymState (z3.Solver())
        st.add_pc(z3.BoolVal(False))
        self.assertIsNone(st.pick_concrete())
    def test_to_smt2 (self):
        prg1 = "x := 1"
        ast1 = ast.parse_string (prg1)
        sym = wlang.sym.SymExec ()
        st = wlang.sym.SymState ()
        st.to_smt2()
        self.assertIsNotNone(st.to_smt2())
    def test_if_else(self):
        prg1 = "x := 1; if x > 5 then skip else false "
        ast1 = ast.parse_string (prg1)
        sym = wlang.sym.SymExec ()
        st = wlang.sym.SymState ()
        out = [s for s in sym.run (ast1, st)]
        self.assertEquals (len(out), 1)
    def test_if_else2(self):
        prg1 = "x := 1; if x > 5 then skip else y := 2"
        ast1 = ast.parse_string (prg1)
        sym = wlang.sym.SymExec ()
        st = wlang.sym.SymState ()
        out = [s for s in sym.run (ast1, st)]
        self.assertEquals (len(out), 1)
    def test_while(self):
        prg1 = "x := 1; while x < 5 do x := x+1"
        ast1 = ast.parse_string (prg1)
        sym = wlang.sym.SymExec ()
        st = wlang.sym.SymState ()
        out = [s for s in sym.run (ast1, st)]
        self.assertEquals (len(out), 1)
    def test_assert(self):
        prg1 = "x := 1; assert x > 5"
        ast1 = ast.parse_string (prg1)
        sym = wlang.sym.SymExec ()
        st = wlang.sym.SymState ()
        out = [s for s in sym.run (ast1, st)]
        self.assertEquals (len(out), 0)
    def test_assert2(self):
        prg1 = "x := 1; assert x < 5"
        ast1 = ast.parse_string (prg1)
        sym = wlang.sym.SymExec ()
        st = wlang.sym.SymState ()
        out = [s for s in sym.run (ast1, st)]
        self.assertEquals (len(out), 1)
    def test_assume(self):
        prg1 = "y := 2; assume y > 5"
        ast1 = ast.parse_string (prg1)
        sym = wlang.sym.SymExec ()
        st = wlang.sym.SymState ()
        out = [s for s in sym.run (ast1, st)]
        self.assertEquals (len(out), 0)
    def test_main_parse (self):
        filePathForTest = os.path.join(os.getcwd(), 'wlang', 'test1.prg')
        sys.argv.append(filePathForTest)
        file_path = wlang.sym._parse_args()
        output = wlang.sym.main()
        self.assertEqual(file_path.in_file, filePathForTest )
        self.assertEqual(output, 0)
    def test_while_inv (self):
        prg1 = "havoc x,y; assume y >= 0; c := 0; r := x; while c < y inv r = x + c and c <= y do { r:= r+1; c := c+1}; assert r = x+y"
        ast1 = ast.parse_string (prg1)
        sym = wlang.sym.SymExec ()
        st = wlang.sym.SymState ()
        out = [s for s in sym.run (ast1, st)]
        self.assertEquals (len(out), 0)
    def test_while_wrong_inv (self):
        prg1 = "havoc x,y; assume y >= 0; c := 0; r := x; while c < y inv c > y do { r:= r+1; c := c+1}; assert r = x+y"
        ast1 = ast.parse_string (prg1)
        sym = wlang.sym.SymExec ()
        st = wlang.sym.SymState ()
        out = [s for s in sym.run (ast1, st)]
        self.assertEquals (len(out), 1)