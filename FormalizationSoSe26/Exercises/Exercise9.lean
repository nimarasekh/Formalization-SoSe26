import Mathlib.Tactic

/-
Here are a set of exercises about algebra and linear algebra.
They vary in difficulty and cover a variety of topics.
Feel free to skip and pick whatever exericise you like.
-/

section subgroups

/-
Here are some exercises about subgroups of a group.

The first exercises in this section are somewhat easier
than the other ones about groups.
-/

variable {G H : Type*} [Group G] [Group H]

open Subgroup

example (f : G →* H) (S T : Subgroup H) (hST : S ≤ T) : comap f S ≤ comap f T := by
  sorry

example (f : G →* H) (S T : Subgroup G) (hST : S ≤ T) : map f S ≤ map f T := by
  sorry

variable {K : Type*} [Group K]

-- Remember you can use the `ext` tactic to prove an equality of subgroups.
example (φ : G →* H) (ψ : H →* K) (U : Subgroup K) :
    comap (ψ.comp φ) U = comap φ (comap ψ U) := by
    sorry

-- Pushing a subgroup along one homomorphism and then another is equal to
-- pushing it forward along the composite of the homomorphisms.
example (φ : G →* H) (ψ : H →* K) (S : Subgroup G) :
    map (ψ.comp φ) S = map ψ (S.map φ) := by
    sorry

-- For this exercise recall that subgroups have the identity element.
#check Subgroup.one_mem

lemma eq_bot_iff_card {K : Subgroup G} :
    K = ⊥ ↔ Nat.card K = 1 := by
  suffices (∀ x ∈ K, x = 1) ↔ ∃ x ∈ K, ∀ a ∈ K, a = x by
    simpa [eq_bot_iff_forall, Nat.card_eq_one_iff_exists]
  sorry


/-
For this last exercise we need the following fact about divisibility and the previous lemma.
-/
#check card_dvd_of_le

lemma inf_bot_of_coprime (K L : Subgroup G)
    (h : (Nat.card K).Coprime (Nat.card L)) : K ⊓ L = ⊥ := by
  sorry

end subgroups

section groups_conjugate
/-
In this exercise we look at the conjugation action of subgroups.
-/
variable {G H : Type*} [Group G] [Group H]

/-
First for a subgroup we define the conjugate subgroup.
We already need the following facts about subgroups:
-/
#check Subgroup.one_mem
#check Subgroup.inv_mem
#check Subgroup.mul_mem

def conjugate (x : G) (G₁ : Subgroup G) : Subgroup G where
  carrier := {a : G | ∃ h, h ∈ G₁ ∧ a = x * h * x⁻¹}
  one_mem' := by sorry
  inv_mem' := by sorry
  mul_mem' := by sorry

lemma conjugate_one (K : Subgroup G) : conjugate 1 K = K := by
  sorry

instance : MulAction G (Subgroup G) where
  smul := conjugate
  one_smul := by sorry
  mul_smul := by sorry

end groups_conjugate

noncomputable section groups_index
/-
We now look at some exercises about the index of a subgroup and the cardinality.
-/
variable {G : Type*} [Group G] {K L : Subgroup G}

open MonoidHom

#check Nat.card_pos -- The nonempty argument will be automatically inferred for subgroups
#check Subgroup.index_eq_card
#check Subgroup.index_mul_card
#check Nat.eq_of_mul_eq_mul_right

lemma aux_card_eq [Finite G] (h' : Nat.card G = Nat.card K * Nat.card L) :
    Nat.card (G ⧸ K) = Nat.card L := by
    sorry

variable [K.Normal] [L.Normal] [Fintype G] (h : Disjoint K L)
         (h' : Nat.card G = Nat.card K * Nat.card L)

#check Nat.bijective_iff_injective_and_card
#check ker_eq_bot_iff
#check restrict
#check ker_restrict
#check ker_prod
#check QuotientGroup.mk'
#check MulEquiv.ofBijective

def iso₁ : L ≃* G ⧸ K := by
  sorry
/-
This one is harder.
For this one you want to use the same results reviewed before `iso₁`,
along with the following:
-/
#check Nat.card_prod

def iso₂ : G ≃* (G ⧸ K) × (G ⧸ L) := by
  apply MulEquiv.ofBijective <| (QuotientGroup.mk' K).prod (QuotientGroup.mk' L)
  rw [Nat.bijective_iff_injective_and_card]
  sorry

#check MulEquiv.symm
#check MulEquiv.trans
#check MulEquiv.prodCongr

def finalIso : G ≃* K × L := by
  sorry

end groups_index

section rings_ideals
/-
In this section we look at basic exercises about rings and ideals.
They should be reasonably straightforward.
-/

/-
If `R` is a ring, then the zero ideal is an ideal of `R`.
-/
def zeroIdeal (R : Type*) [Ring R] : Ideal R where
  carrier := {0}
  zero_mem' := by sorry
  add_mem' := by sorry
  smul_mem' := by sorry

/-
If `R` and `S` are rings, and `f : R →+* S` is a ring homomorphism,
then the preimage of an ideal `I` of `S` under `f` is an ideal of `R`.
-/
def preimageIdeal {R S : Type*} [Ring R] [Ring S] (f : R →+* S) (I : Ideal S) : Ideal R where
  carrier := f ⁻¹' I
  zero_mem' := by sorry
  add_mem' := by sorry
  smul_mem' := by sorry

end rings_ideals

section chinese_remainder
/-
Let's look at rings and ideals and use that to prove the Chinese Remainder Theorem.
This section is significantly harder.
-/

-- Recall that for a ring and an idea, we have a quotient map.
example {R : Type*} [CommRing R] (I : Ideal R) : R →+* R ⧸ I :=
  Ideal.Quotient.mk I

#check Ideal.Quotient.eq_zero_iff_mem
#check Ideal.Quotient.lift

variable {ι R : Type*} [CommRing R]
open Ideal Quotient Function

/-
Let us start by constructing the homomorphism from ``R ⧸ ⨅ i, I i`` to ``Π i, R ⧸ I i``
featured in the Chinese Remainder Theorem. We only need the following:
-/
#check RingHom.mem_ker
#check ker_Pi_Quotient_mk

def chineseMap (I : ι → Ideal R) : (R ⧸ ⨅ i, I i) →+* Π i, R ⧸ I i :=
  Ideal.Quotient.lift (⨅ i, I i) (Pi.ringHom fun i : ι ↦ Ideal.Quotient.mk (I i))
    (by sorry)

/-
The next two are sanity checks and should follow by definition with `rfl`.
-/
lemma chineseMap_mk (I : ι → Ideal R) (x : R) :
    chineseMap I (Quotient.mk _ x) = fun i : ι ↦ Ideal.Quotient.mk (I i) x :=
  sorry

lemma chineseMap_mk' (I : ι → Ideal R) (x : R) (i : ι) :
    chineseMap I (mk _ x) i = mk (I i) x :=
  sorry

/-
We now want to show `chineseMap` is injective.

Here we also want the following:
-/
#check injective_lift_iff
#check ker_Pi_Quotient_mk

lemma chineseMap_inj (I : ι → Ideal R) : Injective (chineseMap I) := by
  sorry

theorem isCoprime_Inf {I : Ideal R} {J : ι → Ideal R} {s : Finset ι}
    (hf : ∀ j ∈ s, IsCoprime I (J j)) : IsCoprime I (⨅ j ∈ s, J j) := by
  classical
  simp_rw [isCoprime_iff_add] at *
  induction s using Finset.induction with
  | empty =>
      simp only [Finset.notMem_empty, not_false_eq_true, iInf_neg, iInf_top, Submodule.add_eq_sup,
        le_top, sup_of_le_right, one_eq_top]
  | @insert i s _ hs =>
      rw [Finset.iInf_insert, inf_comm, one_eq_top, eq_top_iff, ← one_eq_top]
      set K := ⨅ j ∈ s, J j
      calc
        1 = I + K                  :=  by {
        -- For this first step we need `Finset.mem_insert_of_mem`
          sorry
        }
        _ = I + K * (I + J i)      := by {
          -- For this next step we need `Finset.mem_insert_self`, but also `mul_one`
          sorry
        }
        _ = (1 + K) * I + K * J i  := by ring
        _ ≤ I + K ⊓ J i            := by {
          -- For this last step you can start with the `gcongr` tactic
          -- and also benefit from `mul_le_left` and `mul_le_inf`
          sorry
        }

/-
We now want to show `chineseMap` is surjective.
This one is quite involved.
-/

set_option linter.unusedFintypeInType false in
lemma chineseMap_surj [Fintype ι] {I : ι → Ideal R}
    (hI : ∀ i j, i ≠ j → IsCoprime (I i) (I j)) : Surjective (chineseMap I) := by
  classical
  intro g
  choose f hf using fun i ↦ Ideal.Quotient.mk_surjective (g i)
  have key : ∀ i, ∃ e : R, mk (I i) e = 1 ∧ ∀ j, j ≠ i → mk (I j) e = 0 := by
    intro i
    have hI' : ∀ j ∈ ({i} : Finset ι)ᶜ, IsCoprime (I i) (I j) := by {
      sorry
    }
    rcases isCoprime_iff_exists.mp (isCoprime_Inf hI') with ⟨u, hu, e, he, hue⟩
    replace he : ∀ j, j ≠ i → e ∈ I j := by simpa using he
    refine ⟨e, ?_, ?_⟩
    · simp only [eq_sub_of_add_eq' hue, map_sub, map_one, eq_zero_iff_mem.mpr hu, sub_zero]
    · exact fun j hj ↦ eq_zero_iff_mem.mpr (he j hj)
  choose e he using key
  use mk _ (∑ i, f i * e i)
  sorry

/-
Finally, we combine all these things in the Chinese Remainder Theorem Isomorphism.
-/
noncomputable def chineseIso [Fintype ι] (f : ι → Ideal R)
    (hf : ∀ i j, i ≠ j → IsCoprime (f i) (f j)) : (R ⧸ ⨅ i, f i) ≃+* Π i, R ⧸ f i :=
  { Equiv.ofBijective _ ⟨chineseMap_inj f, chineseMap_surj hf⟩,
    chineseMap f with }

end chinese_remainder

section vectorspaces
/-
Let's prove that the preimage of a subspace under a linear map is a subspace.
This one should not be too complicated.

Recall the notation for preimage of a function `f` is `f ⁻¹'`.
Also recall we learned one useful trick about preimages:
-/
#check Set.mem_preimage

/-
Of course, we also need some basic facts about linear maps:
-/
#check LinearMap.map_zero
#check LinearMap.map_add
#check LinearMap.map_smul

variable {K V W : Type} [Field K] [AddCommGroup V] [AddCommGroup W] [Module K V] [Module K W]

def preimage (f : V →ₗ[K] W) (H : Submodule K W) :
    Submodule K V where
  carrier := f ⁻¹' H
  zero_mem' := by sorry
  add_mem' := by sorry
  smul_mem' := by sorry

end vectorspaces

section dimension
/-
Let's prove that if a linear map between two vector spaces is bijective,
then their dimensions are equal.

The following should be useful:
-/

#check LinearMap.rank_le_of_injective
#check LinearMap.rank_le_of_surjective

variable {K V W : Type} [Field K] [AddCommGroup V] [AddCommGroup W] [Module K V] [Module K W]
         [FiniteDimensional K V] [FiniteDimensional K W]

example (f : V →ₗ[K] W) (hf : Function.Bijective f) : Module.rank K V = Module.rank K W := by
  sorry

end dimension

section matrix

open Matrix
/-
Let's try to see that the product of two invertible matrices is also invertible.
Concretely, we check the determinant of the product of two matrices is non-zero.

This can help:
-/
#check det_mul

variable {K : Type} {n : ℕ} [Field K] (A B : Matrix (Fin n) (Fin n) K)

example (eqA : A.det ≠ 0) (eqB : B.det ≠ 0) : (A * B).det ≠ 0 := by
  sorry

end matrix
