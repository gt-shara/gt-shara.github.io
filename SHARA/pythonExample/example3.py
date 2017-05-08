# Copyright (c) Microsoft Corporation 2015

from z3 import *
fp = Fixedpoint()

goal= Bool("goal1")
fp.register_relation(goal.decl())
R1 = Function('R1',IntSort(),BoolSort())
fp.register_relation(R1)
x1 = Int("x1")
x2 = Int("x2")
fp.declare_var(x1,x2)
a1 = x1 == 1
fp.rule(R1(x1),a1)
a2 = x2 == (x1 + 2)
fp.rule(R1(x2),And(R1(x1),a2))
a3 = x1 == 41
fp.rule(goal,And(R1(x1),a3))
fp.set(engine='duality')

print "current set of rules\n", fp
print fp.query(goal)
