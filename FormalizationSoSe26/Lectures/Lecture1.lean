import Mathlib.Tactic
-- This is a Lean file.

-- Fundamentally Lean is a functional programming language.
-- That means it can be used for completely standard programming.

-- But everything in Lean has a `type`.
-- We can check the type with `check`

#check 3
#check "test"

-- As `functional` suggests, `functions` are key in Lean.
-- We define functions using `def`.

-- Here is a function called `linear_combo`.
def linear_combo (x y : ℕ) : ℕ := 3*x + 4*y

-- We can leave the types implicit:
def implicit_linear_combo (x y : ℕ) := 3*x + 4*y

-- `eval` evaluates functions.
#eval linear_combo 2 3
#eval implicit_linear_combo 2 3

-- We can define functions in Lean via pattern matching.
-- This allows changing the output based on the input.
def made_up_function : ℕ → ℕ
| 0     => 1
| 1     => 5
| _     => 7

#eval made_up_function 9

-- In fact we can use pattern matching to define function recursively.
def fib : ℕ → ℕ
  | 0     => 1
  | 1     => 1
  | n + 2 => fib n + fib (n + 1)

#eval fib 13

-- We can use recursion to do some cool things.

#check Bool
#check true
#check false

def even : ℕ → Bool
  | 0     => true
  | n + 1 => not (even n)

def odd : ℕ  → Bool
  | 0     => false
  | n + 1 => not (odd n)

#eval even 6
#eval even 9

#eval odd 13
#eval odd 8

#check and

def mystery : ℕ → Bool := fun n => and (even n) (odd n)

#eval mystery 7
#eval mystery 8

-- We can also define lists in Lean.

#check List -- Notice lists need to have a type!
#check List Nat -- Now we have a list of natural numbers.

-- We can define lists of natural numbers:
def random_list : List Nat := [3, 22, 38, 25, 7]
#eval random_list

def range_list : List Nat := List.range 10
#eval range_list

-- We can extract elements from lists
#eval range_list[7]
#eval random_list[2]

-- We can also apply functions to lists.
#eval (random_list.map odd)

-- Here is a simple iterated sum:
#eval Id.run do
  let mut sum := 0
  for i in List.range 101 do
    sum := sum + i
  return sum

-- This is the end of the standard programming part.

-- Let's start with some mathematics.

-- Lean has some crucial additional types built in.
-- This includes the type of all types, called `Type`.
#check Type
-- It is analogous to the set of all sets.

-- (here for the first time we are seeing some annoying universe level stuff)

-- For example we can pick out the type of natural numbers.
def some_type : Type := ℕ

-- There is also the type of all propositions, called `Prop`.
#check Prop

-- The type `Prop` records all "possible truth values" and concretely `True` and `False`.
#check True
#check False

-- Even more interestingly, there is the type of all equalities, called `Eq`.
#check Eq
#check Eq 3 4

-- A more common way to write it is with `=`.
#check 3 = 4

-- These are indeed equal.
#eval (Eq 3 4) = (3 = 4)
-- Equality types tell us if two things are equal.

-- In general we only know that everything is equal to itself.
#check rfl
#check (@rfl _ 3)
#check (@rfl _ Bool)
#check (@rfl _ List)
#check (@rfl _ Type)

-- If we have a type `X`, a `formula` on `X` is a function `X → Prop`.

-- We already saw natural numbers.
#check ℕ

-- In particular, a `formula` on the natural numbers is just a function
#check ℕ → Prop

-- For example, we have the following formula:
def is_nonzero : ℕ → Prop := fun n => n ≠ 0

-- We will see more complicated examples later.

-- Let us see some examples of formulas on natural numbers.
#check Nat.add_comm
#check Nat.add_assoc
#check Nat.mul_comm
-- In all of these cases the input are some natural numbers `n`, `m`, (`k`).
-- The output is an equality, which is a proposition!

#check Nat.add_comm _ 4

-- How do we prove new things? We construct new functions and equalities!
-- One standard way is to compose two functions or equalities.
def maybe_too_complicated : 2 + (3 + 4) = 4 + (2 + 3) :=
  Nat.add_comm 4 (2 + 3) ▸ Eq.symm (Nat.add_assoc 2 3 4)

def wasnt_too_complicated : 2 + (3 + 4) = 4 + (2 + 3) :=
  Eq.refl (2 + (3 + 4))  ▸ Eq.symm (Nat.add_assoc 2 3 4)

variable (a b c : ℕ)

theorem exercise : a + b = b + a := Nat.add_comm a b

def too_complicated : a + (b + c) = c + (a + b) :=
  Nat.add_comm c (a + b) ▸ Eq.symm (Nat.add_assoc a b c)

-- This is getting complicated! We want:
--  Tactics!
--  Interactivity!

def still_easy : 2 + (3 + 4) = 4 + (2 + 3) := by
  rfl

-- One standard tactic is `rw` (rewrite).
-- It takes an equality and replaces one side with the other.
def now_easy : a + (b + c) = c + (a + b) := by
  rw [Nat.add_comm c (a+b)]
  rw [Nat.add_assoc a b c]

def even_easier : a + (b + c) = c + (a + b) := by
  rw [Nat.add_comm c (a+b)]
  rw [Nat.add_assoc]

def further_easier : a + (b + c) = c + (a + b) := by
  rw [Nat.add_comm c (a+b), Nat.add_assoc]

-- A very advanced tactic is `ring` which can solve any equality that holds in a commutative ring.
def easiest : a + (b + c) = c + (a + b) := by
  ring

-- We will discuss tactics in more detail in the coming lectures.

-- Tactics are great! But they can't solve everything!
def FermatLastTheorem := ∀ x y z n : ℕ, n > 2 ∧ x * y * z ≠ 0 → x ^ n + y ^ n ≠ z ^ n

theorem FermatLastTheoremHolds : FermatLastTheorem := by sorry
