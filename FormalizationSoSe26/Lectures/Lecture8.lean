import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

section review


/-
The last couple of lectures we discussed:
- `structures`: to define new mathematical definitions on types
- `classes`: to define structures which allow instances
- `instances`: examples of classes that Lean can synthesize automatically
- `hierarchies`: To relate and extend classes
- `morphisms`: To define structure-preserving maps between structures
- `subobjects`: To define subsets of structures that inherit the structure

This officially ends the `computer science` part of the course.
For the rest of the course, we will return to the `mathematics` part.
-/

end review

/-
Today we will do some analysis in *Lean*.

Concretely, we will look at the following topics:
* `filters`: a generalization of sequences and neighborhoods
* `limits`: a limits via filters
* `derivatives`: derivatives via limits
-/

section why_filters

/-
In topology, one of basic concepts is that of a limit.
Say `f : ℝ → ℝ`. There are many variants of limits.
* the limit of `f(x)` as `x` tends to `x₀`
* the limit of `f(x)` as `x` tends to `x₀`, with the additional assumption that `x ≠ x₀`
* the limit of `f(x)` as `x` tends to `∞`
* the limit of `f(x)` as `x` tends to `-∞`
* the limit of `f(x)` as `x` tends to `x₀⁻`
* the limit of `f(x)` as `x` tends to `x₀⁻`, with the additional assumption that `x ≠ x₀`
* the limit of `f(x)` as `x` tends to `x₀⁺`
* the limit of `f(x)` as `x` tends to `x₀⁺`, with the additional assumption that `x ≠ x₀`.

This gives 8 different notions of behavior of `x`.

Similarly, the value `f(x)` can have the same behavior:
* `f(x)` tends to `x₀`
* `f(x)` tends to `x₀`, with the additional assumption that `f(x) ≠ x₀`
* `f(x)` tends to `∞`
* `f(x)` tends to `-∞`
* `f(x)` tends to `x₀⁻`
* `f(x)` tends to `x₀⁻`, with the additional assumption that `f(x) ≠ x₀`
* `f(x)` tends to `x₀⁺`
* `f(x)` tends to `x₀⁺`, with the additional assumption that `f(x) ≠ x₀`.

This gives 8 different notions of behavior of `f(x)`.

In total this gives `64` notions of limits.

This means whenever we have statement that involves two limits, for example:

Lemma. If `f x` tends to `y₀` when `x` tends to `x₀` and `g y` tends to `z₀` when `y` tends to `y₀`,
then `(g ∘ f) x` tends to `z₀` when `x` tends to `x₀`.

Then such a lemma will have `512 = 8 × 8 × 8` different versions.

*Problem:* We do not want to prove a lemma **512** times.
*Solution:* Use `filters` as one unified framework.
-/

end why_filters

section filters

open Filter Topology

/-
# Definition of Filters

We now define `filters`

If `X` is a type, a filter `F : Filter X` is a
collection of sets `F.sets : Set (Set X)` satisfying the following:
* the filter contains the whole set `X`
* A filter is closed under finite intersections.
* A filter is closed under taking supersets.
-/

variable {X Y : Type*} (F : Filter X)

#check (F.sets : Set (Set X))
-- A filter contains the whole set.
#check (F.univ_sets : Set.univ ∈ F.sets)
-- A filter is closed under taking supersets.
#check (F.sets_of_superset : ∀ {U V},
  U ∈ F.sets → U ⊆ V → V ∈ F.sets)
-- A filter is closed under finite intersections.
#check (F.inter_sets : ∀ {U V}, U ∈ F.sets → V ∈ F.sets → U ∩ V ∈ F.sets)

/-
# Examples of Filters
Let us see some examples of filter in Lean.

In all these examples we can think of ``being in a filter`` as ``being very large``.
-/

/-
For the first example we consider the set `ℕ` of natural numbers.
The filter `(atTop : Filter ℕ)` is made of sets of `ℕ` containing
`{n | n ≥ N}` for some `N`

In this example our `large subsets` are the ones unbounded above.
-/
#check (atTop : Filter ℕ)

-- Notice we can describe this filter very explicitly.
example {s : Set ℕ} : s ∈ atTop ↔   ∃ N, ∀ n ≥ N, n ∈ s := mem_atTop_sets

-- This first example is not actually specific to `ℕ`.
-- It works for any type `X` with a partial order.
#check (atTop : Filter ℝ)

example {s : Set ℝ} : s ∈ atTop ↔   ∃ N, ∀ n ≥ N, n ∈ s := mem_atTop_sets

/-
For the second example we consider the set `ℝ` of real numbers.
The filter `𝓝 x` is made of sets of `ℝ` made of neighborhoods of `x` in `ℝ`

In this example our `large subsets` are the ones containing a neighborhood of `x`.
-/
#check (𝓝 3 : Filter ℝ)

-- Again we can describe this filter very explicitly.
example {U : Set ℝ} (openU : IsOpen U) : U ∈ 𝓝 3 ↔ 3 ∈ U := IsOpen.mem_nhds_iff openU

/-
Next we hav ean example of a filter on `ℝ × ℝ × ℝ` motivated by measure theory.
`μ.ae` is made of sets whose complement has zero measure with respect to a given measure `μ`.
-/
#check (MeasureTheory.ae MeasureTheory.volume : Filter (ℝ × ℝ × ℝ))

-- Again we can explicitly see this is the case
example {s : Set (ℝ × ℝ × ℝ)} :
  s ∈ MeasureTheory.ae MeasureTheory.volume ↔ MeasureTheory.volume (sᶜ) = 0 :=
    MeasureTheory.mem_ae_iff

/-
Finally, for every type `X` and term `s : Set X`,
we have the principal filter `𝓟 s` made of sets containing `s`.

Here our `large subsets` are the ones containing `s`.
-/
example (X : Type*) (s : Set X) : Filter X := 𝓟 s

-- Again we can explicitly see this is the case
example {X : Type*} {s t : Set X} : t ∈ 𝓟 s ↔ s ⊆ t := by exact mem_principal

/-
# Operations on Filters

We can modify filters via the `pushforward` and `pullback` operations.
-/

/-
The *pushforward* of filters generalizes images of sets.
For a given map `f : X → Y`, the pushforward of a filter `F : Filter X` is the filter
is a filter on `Y` made of sets whose preimage is in `F`.
-/
example {X Y : Type*} (f : X → Y) : Filter X → Filter Y :=
  Filter.map f

example {X Y : Type*} (f : X → Y) (F : Filter X) (V : Set Y) :
    V ∈ Filter.map f F ↔ f ⁻¹' V ∈ F := refl _

-- Let's check this really agrees with images of sets for principal filters.
example {X Y : Type*} (f : X → Y) {s : Set X} : (𝓟 s).map f = 𝓟 (f '' s) := map_principal

-- Mapping filters is monotone: if l ≤ l', then l.map f ≤ l'.map f
#check Filter.map_mono

-- Mapping filters composes
#check Filter.map_map

/-
The *pullback* of filters generalizes preimages
For a given map `f : X → Y`, the pullback of a filter `G : Filter Y`
is a filter on `X` made of sets whose image is in `G`.
-/
example {X Y : Type*} (f : X → Y) : Filter Y → Filter X :=
  Filter.comap f

example {X Y : Type*} (f : X → Y) (G : Filter Y) (U : Set X) :
    U ∈ Filter.comap f G ↔ ∃ V ∈ G, f ⁻¹' V ⊆ U := refl _

-- -- This is again monotone and composes, but the composition is contravariant.
#check Filter.comap_mono
#check Filter.comap_comap

-- Let's check this really agrees with preimages of sets for principal filters.
example {X Y : Type*} (f : X → Y) {s : Set Y} : (𝓟 s).comap f = 𝓟 (f ⁻¹' s) := comap_principal

end filters

section limits

open Filter Topology

/-
Now we our notion of filters at hand, we can define limits in a very general way.
We will define the limit of a function `f : X → Y` as `x`tends to `x₀` in `X`
and `f(x)` tends to `y₀` in `Y` as follows:
-/

/- Using these operations, we can define the limit. -/
def MyTendsto {X Y : Type*} (f : X → Y)
    (F : Filter X) (G : Filter Y) :=
  map f F ≤ G

/-
Would the definition be different if we used the comap instead?
No, `map` and `comap` interact well.
-/

example {X Y : Type*} (f : X → Y) (F : Filter X) (G : Filter Y) :
    map f F ≤ G ↔ F ≤ comap f G := by
      exact map_le_iff_le_comap

#check Tendsto

lemma Tendsto_iff {X Y : Type*} (f : X → Y)
    (F : Filter X) (G : Filter Y) :
    Tendsto f F G ↔ ∀ S : Set Y, S ∈ G → f ⁻¹' S ∈ F := by
  rw [Tendsto]
  simp only [(· ≤ ·)]
  simp_rw [mem_map] -- or: simp only [mem_map]
  -- note that `rw` does not work because it cannot rewrite inside a ∀ quantifier

-- The point of the proof helped us understand, but we could have just used `refl`:
lemma Tendsto_iff' {X Y : Type*} (f : X → Y)
    (F : Filter X) (G : Filter Y) :
    Tendsto f F G ↔ ∀ S : Set Y, S ∈ G → f ⁻¹' S ∈ F := refl _

/- A sequence `u` converges to `x` -/
example (u : ℕ → ℝ) (x : ℝ) : Prop :=
  Tendsto u atTop (𝓝 x)

/- `\lim_{x → x₀} f(x) = y₀` -/
example (f : ℝ → ℝ) (x₀ y₀ : ℝ) : Prop :=
  Tendsto f (𝓝 x₀) (𝓝 y₀)

/- `\lim_{x → x₀⁻, x ≠ x₀} f(x) = y₀⁺` -/
example (f : ℝ → ℝ) (x₀ y₀ : ℝ) : Prop :=
  Tendsto f (𝓝[<] x₀) (𝓝[≥] y₀)

/- `\lim_{x → ∞} f x = y` -/
example (f : ℝ → ℝ) (y : ℝ) : Prop :=
  Tendsto f atTop (𝓝 y)

/- `\lim_{x → ∞} f x = ∞` -/
example (f : ℝ → ℝ) : Prop :=
  Tendsto f atTop atTop

/- `\lim_{x → -∞} f x = ∞` -/
example (f : ℝ → ℝ) : Prop :=
  Tendsto f atBot atTop

/-
Now the following states all possible composition lemmas all at once!
This one case will cover all `512` possible cases.
-/
example {X Y Z : Type*} {F : Filter X} {G : Filter Y} {H : Filter Z}
    {f : X → Y} {g : Y → Z}
    (hf : Tendsto f F G) (hg : Tendsto g G H) :
    Tendsto (g ∘ f) F H := by
  rw [Tendsto] at hf hg ⊢
  calc
    map (g ∘ f) F = map g (map f F) := by rw [map_map]
    _             ≤ map g G := by gcongr -- or: apply map_mono; exact hf
    _             ≤ H := hg

end limits

section limitsLogic

open Filter Topology

/-
Filters also allow us to reason about things that are "eventually true".
If `F : Filter X` and `P : X → Prop` then `∀ᶠ n in F, P n`
means that `P n` is eventually true for `n` in `F`.
It is defined to be `{ x | P x } ∈ F`.

The following example shows that if `P n` and `Q n` hold for sufficiently large `n`,
then so does `P n ∧ Q n`.
-/

example (P Q : ℕ → Prop) (hP : ∀ᶠ n in atTop, P n) (hQ : ∀ᶠ n in atTop, Q n) :
    ∀ᶠ n in atTop, P n ∧ Q n :=
  hP.and hQ

/-
This example is quite simple: in more complicated examples, it's useful to separate the
bookkeeping from the mathematical content: this is what the `filter_upwards` tactic is good for.
-/
example (P Q : ℕ → Prop)
    (hP : ∀ᶠ n in atTop, P n)
    (hQ : ∀ᶠ n in atTop, Q n) :
    ∀ᶠ n in atTop, P n ∧ Q n := by
  -- `filter_upwards [hP, hQ]` converts your goal to `∀ n, P n → Q n → (P n ∧ Q n)`
  filter_upwards [hP, hQ]
  -- Now, we are out of "filter land" and only need to prove some basic logic.
  intro n hpn hqn
  tauto -- solves elementary logic problems
  -- or: `constructor <;> assumption`



/-
If `P n` implies `Q n` and `P n` holds for sufficiently large `n`, then so does `Q n`:
this is another instance of `Filter.Eventually.mono`
-/
example (P Q : ℕ → Prop) (hP : ∀ᶠ n in atTop, P n) (hPQ : ∀ n, P n → Q n) :
    ∀ᶠ n in atTop, Q n := by
      apply hP.mono
      apply hPQ

-- Let's use `filter_upwards` now
example (P Q : ℕ → Prop) (hP : ∀ᶠ n in atTop, P n) (hPQ : ∀ n, P n → Q n) :
    ∀ᶠ n in atTop, Q n := by
  filter_upwards [hP] using hPQ

/-
Let's make that a bit more complicated:
Assume if `P n` implies `Q n` for n sufficiently large
and `P n` holds for sufficiently large `n`, then so does `Q n`.
-/
example (P Q : ℕ → Prop) (hP : ∀ᶠ n in atTop, P n) (hPQ : ∀ᶠ n in atTop, P n → Q n) :
    ∀ᶠ n in atTop, Q n := by
  filter_upwards [hP, hPQ]
  intro n hp hpq
  exact hpq hp

-- Here is a shorter proof of the same result:
example (P Q : ℕ → Prop) (hP : ∀ᶠ n in atTop, P n) (hPQ : ∀ᶠ n in atTop, P n → Q n) :
    ∀ᶠ n in atTop, Q n := by
    filter_upwards [hP, hPQ] with n hp hpq using hpq hp

example (P Q R S : ℕ → Prop) (hP : ∀ᶠ n in atTop, P n) (hQ : ∀ᶠ n in atTop, Q n)
    (hR : ∀ᶠ n in atTop, R n) (hS : ∀ᶠ n in atTop, S n) : ∀ᶠ n in atTop, P n ∧ Q n ∧ R n ∧ S n := by
  filter_upwards [hP, hQ, hR, hS]
  tauto

-- Here is again a one line proof.
example (P Q R S : ℕ → Prop) (hP : ∀ᶠ n in atTop, P n) (hQ : ∀ᶠ n in atTop, Q n)
    (hR : ∀ᶠ n in atTop, R n) (hS : ∀ᶠ n in atTop, S n) : ∀ᶠ n in atTop, P n ∧ Q n ∧ R n ∧ S n := by
      apply hP.and (hQ.and (hR.and hS))

end limitsLogic

section derivatives

open Set Real

/-
We now move on to the last topic: derivatives.

Recall derivatives are defined as limits of difference quotients.
Lean already has a built-in definition of derivatives, which we will use.

We write `deriv` to compute the derivative of a function.
`simp` can compute the derivatives of standard functions.
 -/
#check deriv
#print deriv

example (x : ℝ) : deriv Real.sin x = Real.cos x := by simp

example (x : ℂ) : deriv (fun y ↦ Complex.sin (y + 3)) x = Complex.cos (x + 3) := by simp

/-
Not every function has a derivative.
As usual, in Mathlib we just define the derivative
of a non-differentiable function to be `0`.
-/

variable (f : ℝ → ℝ) (x : ℝ) in
#check (deriv_zero_of_not_differentiableAt : ¬ DifferentiableAt ℝ f x → deriv f x = 0)

/-
So proving that `deriv f x = y` doesn't necessarily mean that `f` is differentiable.
Often it is nicer to use the predicate `HasDerivAt f y x`,
which states that `f` is differentiable and `f'(x) = y`.
-/

#check HasDerivAt
#print HasDerivAt

#check HasDerivAtFilter
#print HasDerivAtFilter

#check HasFDerivAtFilter
#print HasFDerivAtFilter

example (x : ℝ) : HasDerivAt Real.sin (Real.cos x) x :=
  hasDerivAt_sin x

/-
We can also specify that a function has a derivative without specifying its derivative.
-/

example (x : ℝ) : DifferentiableAt ℝ sin x :=
  differentiableAt_sin

/-
Note: the argument `ℝ` is the field over which we are working,
not the domain of the sin function.
For instance, this is how to say "the Complex sin function is real differentiable".
-/

-- example (z : ℂ) : DifferentiableAt ℝ Complex.sin z := sorry

#check HasDerivAt.differentiableAt

/-
Mathlib contains lemmas stating that common operations satisfy
`HasDerivAt` and `DifferentiableAt` and to compute `deriv`.
-/

#check HasDerivAt.add
#check deriv_add
#check DifferentiableAt.add


example (x : ℝ) :
    HasDerivAt (fun x ↦ Real.cos x + Real.sin x)
    (Real.cos x - Real.sin x) x := by
  rw [sub_eq_neg_add]
  apply HasDerivAt.add
  · exact hasDerivAt_cos x
  · exact hasDerivAt_sin x


/- There are various variations of derivatives/being differentiable -/

/- A function is differentiable everywhere. -/
#check Differentiable

/- A function is differentiable on a subset. -/
#check DifferentiableOn

/- A function is differentiable at a point, considered only within the subset -/
#check DifferentiableWithinAt

/- We can also consider the derivative only within a subset. -/
#check HasDerivWithinAt
#check derivWithin


/-
Let us now look at some main results in Calculus regarding derivatives.

Recall Lean's notation for intervals:
- `Icc a b = [a, b]` is a closed interval
- `Ico a b = [a, b)` is a half-open interval
- `Ioc a b = (a, b]` is a half-open interval
- `Ioo a b = (a, b)` is an open interval

The **intermediate value theorem** states that if `f` is continuous and
`f a ≤ y ≤ f b`, then there is an `x ∈ [a, b]` with `f(x) = y`.
-/

example {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b)) :
    Icc (f a) (f b) ⊆ f '' Icc a b :=
  intermediate_value_Icc hab hf

/-
The mean value theorem states that if `f` is continous on `[a, b]`
and differentiable on `(a, b)` then there is a `c ∈ (a, b)` where `f'(c)` is the
average slope of `f` on `[a, b]`
-/
example (f : ℝ → ℝ) {a b : ℝ} (hab : a < b)
    (hf : ContinuousOn f (Icc a b))
    (hf' : DifferentiableOn ℝ f (Ioo a b)) :
    ∃ c ∈ Ioo a b, deriv f c = (f b - f a) / (b - a) :=
  exists_deriv_eq_slope f hab hf hf'


/-
Rolle's theorem is the special case where `f a = f b`.
-/
example {f : ℝ → ℝ} {a b : ℝ} (hab : a < b) (hfc : ContinuousOn f (Icc a b)) (hfI : f a = f b) :
    ∃ c ∈ Ioo a b, deriv f c = 0 :=
      exists_deriv_eq_zero hab hfc hfI

/-
Why is there no differentiability requirement on `f` here?
-/

end derivatives
