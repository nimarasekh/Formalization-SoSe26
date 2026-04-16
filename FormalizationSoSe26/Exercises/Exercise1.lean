-- Here are couple basic exercises to get you started with Lean.


-- ###NON-TACTICS EXERCISES###
--  Recall that Nat are the natural numbers in Lean.
#check Nat

-- The function Nat.mul_assoc gives us the associativity of multiplication.
#check Nat.mul_assoc

variable (a b c : Nat)

-- Use the function Nat.add_assoc to complete this exercise.
-- (Do not use any tactics!)
example : (a * b) * c = a * (b * c) := sorry

-- Of course, if a = b, then we must also have b = a
-- In fact there is a function for that:
#check Eq.symm

-- Compose your solution to the first question and Eq.symm to solve the following:
-- (Do not use any tactics!)
example :  a * (b * c) = (a * b) * c := sorry

-- We have seen addition and multiplication of natural numbers.
-- Of course they are also distributive.
-- Both left and right:
#check Nat.left_distrib
#check Nat.right_distrib

-- We already know that multiplication is commutative!
#check Nat.mul_comm
-- So we should be able to prove right distributivity directly.
-- That's hard! Let's try some first step towards it:
example : (b + c) * a  = a * b + a * c:= sorry

-- How about actual right distributivity?
-- That's hard with direct methods and we will see how to tackle it with tactics!

-- ###TACTICS EXERCISES###
/-
Let's solve questions 1-3 with tactics.
We will use the `rw` tactic to rewrite the left-hand side of the equation
to the right-hand side.
-/

-- Let's try this out with the first exercise:
example : (a * b) * c = a * (b * c) := by sorry
  -- use the tactic `rw` to rewrite the left-hand side

  -- If you are confused, Solution for exercise1tactics:
  -- rw [Nat.mul_assoc a b c]

-- Now use `rw` simililarly to solve the other two exercises:
example :  a * (b * c) = (a * b) * c := by sorry

example : (b + c) * a  = a * b + a * c:= by sorry

-- Now, we can use the `rw` tactic to solve the exercise 4:
example : (b + c) * a  = b * a + c * a:= by sorry
