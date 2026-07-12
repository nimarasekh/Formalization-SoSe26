import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Convolution

/-
Last week we discussed abstract algebra, and in particular group theory and ring theory.

Today we will discuss some analysis, and in particular integration theory and measure theory.
-/

section classical_integration

open intervalIntegral Interval Convolution
/-
Let us do a review of classical integration.

Notice here we opened `Interval` to introduce the notation `[[a, b]]`
for the segment from `min a b` to `max a b`
-/

/-
Lean already knows about integration and can compute some integrals.

The following computations require
`Mathlib.Analysis.SpecialFunctions.Integrals.Basic`
we imported above.
-/
example (a b : ℝ) : (∫ x in a..b, x) = (b ^ 2 - a ^ 2) / 2 :=
  integral_id

example {a b : ℝ} (h : (0 : ℝ) ∉ [[a, b]]) :
  (∫ x in a..b, 1 / x) = Real.log (b / a) :=
    integral_one_div h

/-
More generally, we have the two fundamental theorems of calculus.
-/
example (f : ℝ → ℝ) (hf : Continuous f) (a b : ℝ) :
  deriv (fun u ↦ ∫ x in a..u, f x) b = f b :=
    (integral_hasStrictDerivAt_right (hf.intervalIntegrable _ _) (hf.stronglyMeasurableAtFilter _ _)
        hf.continuousAt).hasDerivAt.deriv

example {f : ℝ → ℝ} {a b : ℝ} {f' : ℝ → ℝ} (h : ∀ x ∈ [[a, b]], HasDerivAt f (f' x) x)
    (h' : IntervalIntegrable f' MeasureTheory.volume a b) : (∫ y in a..b, f' y) = f b - f a :=
  integral_eq_sub_of_hasDerivAt h h'
/-
Notice in the second one we chose the notation `f'` for the derivative of `f`.
However, we could have chosen any other name for the derivative, e.g. `g` or `h`.
-/

/-
On a more advanced level, we can also define `convolutions` of functions.
-/
example (f : ℝ → ℝ) (g : ℝ → ℝ) : f ⋆ g = fun x ↦ ∫ t, f t * g (x - t) :=
  rfl

end classical_integration

section measure_theory

open Set Function
/-
Let us now discuss a more abstract topic and move on to measure theory.
-/

/-
We have a typeclass `MeasurableSpace` which gives us a notion of measurable sets
i.e., a σ-algebra.
-/
#check MeasurableSpace
#print MeasurableSpace

variable {α : Type*} [MeasurableSpace α]

/-
`MeasurableSet` determines whether a set is measurable or not.
This will of course depend on the σ-algebra we have chosen.
-/

-- The empty set is measurable
example : MeasurableSet (∅ : Set α) :=
  MeasurableSet.empty

-- The whole space is measurable
example : MeasurableSet (univ : Set α) :=
  MeasurableSet.univ

-- The complement of a measurable set is measurable
example {s : Set α} (hs : MeasurableSet s) : MeasurableSet (sᶜ) :=
  hs.compl

/-
Unsurprisingly, Lean already knows that `ℕ` and `ℝ` are measureable.
i.e., we can enumerate their elements.
-/
example : MeasurableSpace ℕ := by infer_instance
example : MeasurableSpace ℝ := by infer_instance

#check Encodable
#print Encodable
/-
Of course, σ-algebras are closed under countable unions and intersections.
Here we use `Encodable` to enumerate the index set.

Note `ℕ` and `Fin n` are already known to be encodable.
-/
example : Encodable ℕ := by infer_instance
example (n : ℕ) : Encodable (Fin n) := by infer_instance

variable {ι : Type*} [Encodable ι]

-- Measurable sets are closed under countable unions
example {f : ι → Set α} (h : ∀ b, MeasurableSet (f b)) : MeasurableSet (⋃ b, f b) :=
  MeasurableSet.iUnion h

-- Measurable sets are closed under countable intersections
example {f : ι → Set α} (h : ∀ b, MeasurableSet (f b)) : MeasurableSet (⋂ b, f b) :=
  MeasurableSet.iInter h

/-
We can now define a measure on a measurable space.
-/
#check MeasureTheory.Measure
#print MeasureTheory.Measure

/-
Via the `MeasureTheory` namespace, we can simplify the notation.
-/
open MeasureTheory

#check Measure
#print Measure

variable {μ : Measure α}

/-
We can see that the measure of a set is equal
to the infimum of the measures of all measurable sets containing it.
-/
example (s : Set α) : μ s = ⨅ (t : Set α) (_ : s ⊆ t) (_ : MeasurableSet t), μ t :=
  measure_eq_iInf s

/-
The measure of a countable union of measurable sets is
less than or equal to the sum of their measures.
-/
example (s : ι → Set α) : μ (⋃ i, s i) ≤ ∑' i, μ (s i) :=
  measure_iUnion_le s

/-
If the sets are pairwise disjoint, then we have equality.
-/
example {f : ℕ → Set α} (hmeas : ∀ i, MeasurableSet (f i)) (hdis : Pairwise (Disjoint on f)) :
    μ (⋃ i, f i) = ∑' i, μ (f i) :=
  μ.m_iUnion hmeas hdis

/-
Finally, we can use measure theory to define `almost everywhere` properties.
-/
#check ae
#print ae

/-
Using `ae`, we can define the notion of a property holding almost everywhere.
This involves the notation `∀ᵐ`.
-/
example {P : α → Prop} : (∀ᵐ x ∂μ, P x) ↔ ∀ᶠ x in ae μ, P x :=
  Iff.rfl

end measure_theory

section integral_measure_theory

open MeasureTheory
/-
With measure at hand, we can now define the integral of a function with respect to a measure.
-/
variable {α : Type*} [MeasurableSpace α]
variable {μ : Measure α}

/-
Notice the integral in Lean allows an arbitrary target, as long as it sufficient structure.
-/
#check integral
#print integral

#check Integrable
#print Integrable

/-
So, we will assume that the target is a complete normed vector space over the reals.
-/
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {f : α → E}

/-
Now with `E` at hand, we can see the integral of a function `f`
with respect to a measure `μ` is defined as follows:
-/

#check ∫ a, f a ∂μ
#print integral

-- Of course, `∫` is just notation for `integral`.
example : ∫ a, f a ∂μ = integral μ f := by rfl

/-
With these notation at hand, we can now prove some basic properties of the integral.
For example, the integral is linear.
-/
example {f g : α → E} (hf : Integrable f μ) (hg : Integrable g μ) :
    ∫ a, f a + g a ∂μ = ∫ a, f a ∂μ + ∫ a, g a ∂μ :=
  integral_add hf hg

/-
The integral of a constant function is just the measure of the set times the constant.

Note, this computation even works when `s` is not measurable,
as both sides will be equal to `0` in that case.
-/
example {s : Set α} (c : E) : ∫ _ in s, c ∂μ = (μ s).toReal • c :=
  setIntegral_const c

end integral_measure_theory

section major_results

open MeasureTheory Topology Filter

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {E : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {f : α → E}
/-
Let us end with some advanced results in measure theory.
-/

-- First we have the dominated convergence theorem.
example {F : ℕ → α → E} {f : α → E} (bound : α → ℝ) (hmeas : ∀ n, AEStronglyMeasurable (F n) μ)
    (hint : Integrable bound μ) (hbound : ∀ n, ∀ᵐ a ∂μ, ‖F n a‖ ≤ bound a)
    (hlim : ∀ᵐ a ∂μ, Tendsto (fun n : ℕ ↦ F n a) atTop (𝓝 (f a))) :
    Tendsto (fun n ↦ ∫ a, F n a ∂μ) atTop (𝓝 (∫ a, f a ∂μ)) :=
  tendsto_integral_of_dominated_convergence bound hmeas hint hbound hlim

-- We also have Fubini's theorem.
example {α : Type*} [MeasurableSpace α] {μ : Measure α} [SigmaFinite μ] {β : Type*}
    [MeasurableSpace β] {ν : Measure β} [SigmaFinite ν] (f : α × β → E)
    (hf : Integrable f (μ.prod ν)) : ∫ z, f z ∂ μ.prod ν = ∫ x, ∫ y, f (x, y) ∂ν ∂μ :=
  integral_prod f hf

end major_results
