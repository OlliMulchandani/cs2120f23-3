from z3 import *
#s = Solver()
x = Int('x')
print(simplify(5*(2+x)+3*(5*x+4)-(x**2)**2))


x = Int('x')
y = Int('y')
n = x + y >= 3
print ("num args: ", n.num_args())
print ("children: ", n.children())
print ("1st child:", n.arg(0))
print ("2nd child:", n.arg(1))
print ("operator: ", n.decl())
print ("op name:  ", n.decl().name())

x = Real('x')
y = Real('y')
solve(x**2 + y**2 > 3, x**3 + y < 5)

set_option(precision=30)
print ("Solving, and displaying result with 30 decimal places")
solve(x**2 + y**2 == 3, x**3 == 2)


print (1/3)
print (RealVal(1)/3)
print (Q(1,3))

x = Real('x')
print (x + 1/3)
print (x + Q(1,3))
print (x + "1/3")
print (x + 0.25)

p = Bool('p')
q = Bool('q')
r = Bool('r')
solve(Implies(p, q), r == Not(q), Or(Not(p), r))

p = Bool('p')
q = Bool('q')
print (And(p, q, True))
print (simplify(And(p, q, True)))
print (simplify(And(p, False)))