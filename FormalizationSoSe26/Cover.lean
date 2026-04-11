-- This is a Lean file

-- Try open it with VS Code after you have set things up.

-- Here is a sample import from Mathlib.
-- If there are any errors, then Mathlib has not been set up correctly.
import Mathlib.CategoryTheory.Category.Basic


#check 3 -- "CLICK HERE"
-- If everything went according to plan you should see a "3 : Nat" or "3 : ℕ" on the right hand side.
def hello := "world"

#check hello -- "CLICK HERE"
-- Here you should see a "hello : String" on the right hand side.

#eval 3 + 4 -- "CLICK HERE"
-- Similarly now you should see "7"

--  Here you should see "Prop : Type" and "Type : Type 1"
#check Prop -- "CLICK HERE"
#check Type -- "CLICK HERE"

-- Here is some advanced mathematics, just to check things work alright.

variable {C} [catC : CategoryTheory.Category C] {X Y Z : C} (f : X ⟶ Y) (h : Y ⟶ Z)

-- Here you should see something of type X ⟶ Z
#check (catC.comp f h) -- "CLICK HERE"

def composition' (g : Y ⟶ Z) : X ⟶ Z := by {
 -- "CLICK HERE" Here you should see a proof state with goal X ⟶ Z
 exact catC.comp f g
} --"CLICK HERE" If you click here you should see "No goals"

-- If any of the steps above did not work:
-- Stop right here and check the steps or ask for help!
