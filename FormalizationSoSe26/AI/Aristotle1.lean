import Mathlib.Tactic

set_option maxHeartbeats 8000000

/-- All groups of order 2 are isomorphic. -/
theorem groups_of_order_two_isomorphic
    (G G' : Type*) [Group G] [Group G']
    (hG : Nat.card G = 2) (hG' : Nat.card G' = 2) :
    Nonempty (G ≃* G') :=
  ⟨mulEquivOfPrimeCardEq (p := 2) hG hG'⟩
