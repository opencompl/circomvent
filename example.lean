-- 1. What language you're defining semantics for.

-- TOP | v1, v2 ... vn
inductive Op 
| Add
| Mul
| Push (n : Nat) 
deriving DecidableEq, Repr

abbrev Program := List Op



def Op.eval (stack : List Nat) (op : Op) : List Nat :=
  match op, stack with
  | Op.Push n, _ =>
    (n :: stack)
  | Op.Add, v1 :: v2 :: rest =>
    ((v1 + v2) :: rest)
  | Op.Mul, v1 :: v2 :: rest =>
    ((v1 * v2) :: rest)
  | _, xs => xs

def Program.eval (prog : Program)
     (stack : List Nat := []) : List Nat :=
  prog.foldl Op.eval stack

def prog1 : Program := [Op.Push 3, Op.Push 4, Op.Add]

example : prog1.eval [] = [7] := by rfl

def prog_add (x y : Nat) : Program := 
    [Op.Push x, Op.Push y, Op.Add]

theorem eval_prog_add_eq_add : ∀ (x y : Nat),
    ((prog_add x y).eval [])[0]! = (x + y) := by
  intros i j 
  simp [prog_add, Program.eval, Op.eval]
  grind

theorem length_eval_prog_add_eq_1 : ∀ (x y : Nat),
    ((prog_add x y).eval []).length = 1 := by
  intros i j 
  simp [prog_add, Program.eval, Op.eval]

