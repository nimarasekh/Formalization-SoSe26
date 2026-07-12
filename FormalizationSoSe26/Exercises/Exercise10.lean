import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Convolution

section classical_integration

open intervalIntegral Interval Convolution

/-
Specialize the computation of the integral of `x` to the interval `0..b`.
Note, `integral_id` might be useful.
-/
example (b : ℝ) :
    (∫ x in (0 : ℝ)..b, x) = b ^ 2 / 2 := by
  sorry

/-
Specialize the computation of the integral of `1 / x` to the interval `1..b`.
`integral_one_div` might be useful.
-/
example {b : ℝ} (hb : (0 : ℝ) ∉ [[(1 : ℝ), b]]) :
    (∫ x in (1 : ℝ)..b, 1 / x) = Real.log b := by
  sorry

/-
Use the first fundamental theorem of calculus for the identity function.
-/
example (a b : ℝ) :
    deriv (fun u ↦ ∫ x in a..u, x) b = b := by
  have hf : Continuous (fun x : ℝ ↦ x) := sorry
  sorry

/-
Use the second fundamental theorem of calculus, but call the derivative `g`
rather than `f'`.
Hint: Can you use `integral_eq_sub_of_hasDerivAt`?
-/
example {F g : ℝ → ℝ} {a b : ℝ}
    (hF : ∀ x ∈ [[a, b]], HasDerivAt F (g x) x)
    (hg : IntervalIntegrable g MeasureTheory.volume a b) :
    (∫ y in a..b, g y) + F a = F b := by
  sorry

/-
Unfold the convolution of two real-valued functions at a point.
-/
example (f g : ℝ → ℝ) (x : ℝ) :
    (f ⋆ g) x = ∫ t, f t * g (x - t) := by
  sorry

/-
Assume the convolution `f ⋆ g` is continuous and has an antiderivative `F`
on the interval `[[a, b]]`.

Combine FTC-1, FTC-2, and the definition of convolution.
-/
example (f g F : ℝ → ℝ) (a b : ℝ)
    (hfg : Continuous (f ⋆ g))
    (hF : ∀ x ∈ [[a, b]], HasDerivAt F ((f ⋆ g) x) x) :
    deriv (fun u ↦ ∫ x in a..u, (f ⋆ g) x) b
      + (∫ x in a..b, (f ⋆ g) x)
      =
    (∫ t, f t * g (b - t)) + (F b - F a) := by
  sorry

end classical_integration

section measure_theory

open Set Function MeasureTheory

variable {α : Type*} [MeasurableSpace α]

/-
This checks that the complement operation can be applied to a known measurable set.
-/
example : MeasurableSet ((∅ : Set α)ᶜ) := by
  sorry

variable {ι : Type*} [Encodable ι]

/-
This asks for a countable union of complements of measurable sets to be measurable.
-/
example {f : ι → Set α} (h : ∀ i, MeasurableSet (f i)) :
    MeasurableSet (⋃ i, (f i)ᶜ) := by
  sorry

/-
This asks for a countable intersection of complements of measurable sets to be measurable.
-/
example {f : ι → Set α} (h : ∀ i, MeasurableSet (f i)) :
    MeasurableSet (⋂ i, (f i)ᶜ) := by
  sorry

variable {μ : Measure α}

/-
This applies the infimum formula for the measure of a set to the complement of a set.
-/
example (s : Set α) :
    μ (sᶜ) = ⨅ (t : Set α) (_ : sᶜ ⊆ t) (_ : MeasurableSet t), μ t := by
  sorry

/-
This rewrites the almost everywhere notation back into the underlying filter statement.
-/
example {P : α → Prop} :
    (∀ᶠ x in ae μ, P x) ↔ ∀ᵐ x ∂μ, P x := by
  sorry

/-
This combines countable closure of measurable sets with subadditivity and additivity for
pairwise disjoint countable unions.
-/
example {f : ℕ → Set α} (hmeas : ∀ i, MeasurableSet (f i))
    (hdis : Pairwise (Disjoint on f)) :
    MeasurableSet ((⋃ i, f i)ᶜ) ∧
      μ (⋃ i, f i) ≤ ∑' i, μ (f i) ∧
      μ (⋃ i, f i) = ∑' i, μ (f i) := by
  sorry

end measure_theory

section integral_measure_theory

open MeasureTheory

variable {α : Type*} [MeasurableSpace α]
variable {μ : Measure α}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-
This checks that the notation for integrating with respect to `μ` is just
the term `integral μ f`.
-/
example {f : α → E} :
    ∫ a, f a ∂μ = integral μ f := by
  sorry

/-
This checks that the pointwise sum of two integrable functions is integrable.
-/
example {f g : α → E} (hf : Integrable f μ) (hg : Integrable g μ) :
    Integrable (fun a => f a + g a) μ := by
  sorry

/-
This asks you to apply additivity of the integral to a pointwise sum.
-/
example {f g : α → E} (hf : Integrable f μ) (hg : Integrable g μ) :
    ∫ a, f a + g a ∂μ = ∫ a, f a ∂μ + ∫ a, g a ∂μ := by
  sorry

/-
This asks you to apply compatibility of the integral with scalar multiplication.
-/
example (c : ℝ) {f : α → E} :
    ∫ a, c • f a ∂μ = c • ∫ a, f a ∂μ := by
  sorry

/-
This asks you to compute the integral of a constant function over a set.
-/
example {s : Set α} (c : E) :
    ∫ _ in s, c ∂μ = (μ s).toReal • c := by
  sorry

/-
This combines integrability of sums with two applications of additivity of the integral.
-/
example {f g h : α → E} (hf : Integrable f μ) (hg : Integrable g μ)
    (hh : Integrable h μ) :
    ∫ a, (f a + g a) + h a ∂μ =
      (∫ a, f a ∂μ + ∫ a, g a ∂μ) + ∫ a, h a ∂μ := by
  sorry

end integral_measure_theory
