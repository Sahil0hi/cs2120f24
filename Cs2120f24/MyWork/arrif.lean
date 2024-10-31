
structure ArithVar : Type :=
   mk :: (index : Nat)
   deriving Repr

   inductive ArithUnOp : Type
   | neg_elim

   inductive ArithBinOp : Type
   | add
   | sub
   | mul

   inductive ArithExpr : Type
   | lit_expr (from_ : Nat) : ArithExpr
   | var_expr (from_var : ArithVar)
   | un_op_expr (op: ArithUnOp) (e : ArithExpr)
   | bin_op_expr (op: ArithBinOp) ( e1 e2 : ArithExpr)


   def v₀ := ArithVar.mk 0
   def v₁ := ArithVar.mk 1
   def v₂ := ArithVar.mk 2

   def X := ArithExpr.var_expr v₀
   def Y := ArithExpr.var_expr v₁
   def Z := ArithExpr.var_expr v₂


   #check ArithExpr.bin_op_expr ArithBinOp.add X Y

   -- concrete syntax
   notation " { "v" }" => ArithExpr.var_expr v
--notation:max "++" n => ArithExpr.un_op_expr ArithUnOp.neg_elim n
--notation:max "--" n => ArithExpr.un_op_expr ArithUnOp.neg_elim n
notation e1 "+" e2 => ArithExpr.bin_op_expr ArithBinOp.add e1 e2
notation e1 "-" e2 => ArithExpr.bin_op_expr ArithBinOp.sub e1 e2
notation e1 "*" e2 => ArithExpr.bin_op_expr ArithBinOp.mul e1 e2

def N := {⟨3⟩ }
def M := {⟨4⟩ }
def P := {⟨5⟩ }

#check X+Y
#check (X+Y) * Z - (ArithExpr.lit_expr 1)
#check (X+Y) * Z - (ArithExpr.lit_expr 1)

def arithEval : ArithExpr → (ArithVar → Nat) → Nat
lit_expr(fromNat :Nat), i => fromNat
var_expr(v), i => i v
un_op_expr(from_var: ArithVar), i => i from_var
un_op_expr(op: ArithUnOp)(e: ArithExpr) => match op with
