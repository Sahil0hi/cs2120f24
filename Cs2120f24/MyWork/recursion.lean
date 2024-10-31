def baseSum := 0

def stepSum: Nat → Nat → Nat
| n', sumn' => sumn' + (n' + 1)


#eval baseSum
#eval stepSum 0 0 --1,1

#eval stepSum 1 1 --2,3
#eval stepSum 2 3 --3,6
#eval stepSum 3 6 --4,10
#eval stepSum 4 10 --5,15



-- FACTORIAL (PRODUCT)

def facBase :=1

def stepFac(n' facn' : Nat): Nat := (n' + 1) * facn'

#eval facBase
#eval stepFac 0 1 --1,1
#eval stepFac 1 1 --2,2
#eval stepFac 2 2 --3,6
#eval stepFac 3 6 --4,24
#eval stepFac 4 24 --5,120


def fac : Nat → Nat := Nat.rec facBase stepFac
#eval fac 5



def sum : Nat → Nat := Nat.rec baseSum stepSum
#eval sum 5

def sum_up : Nat → Nat
| Nat.zero => 0
| Nat.succ n' => Nat.succ n' + sum_up n'

def sum_up' : Nat → Nat
| 0 => 0
| n'+1 => (n'+1) + sum_up' n'

#eval sum_up' 5
