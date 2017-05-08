# Copyright (c) Microsoft Corporation 2015

from z3 import *
fp = Fixedpoint()

goal= Bool("goal1")
fp.register_relation(goal.decl())
R1 = Function('R1',IntSort(),BoolSort())
R2 = Function('R2',IntSort(),BoolSort())
R3 = Function('R3',IntSort(),BoolSort())
R4 = Function('R4',IntSort(),BoolSort())
fp.register_relation(R1)
fp.register_relation(R2)
fp.register_relation(R3)
fp.register_relation(R4)
x1 = Int("x1")
fp.declare_var(x1)
a1 = x1 >= 0
a2 = x1 == 0
fp.rule(R1(x1),a1)
fp.rule(R2(x1),a2)
fp.rule(R3(x1),And(R1(x1),R2(x1)))
a2 = x1 != 0
fp.rule(goal,And(R3(x1),a2))
fp.set(engine='duality')

print "current set of rules\n", fp
print fp.query(goal)
