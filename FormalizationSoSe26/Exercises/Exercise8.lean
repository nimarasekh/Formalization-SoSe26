import Mathlib.Tactic
import FormalizationSoSe26.Lectures.Lecture8

section filter

open Filter Topology

variable {X Y Z : Type*}

/-
Show that the whole space belongs to every filter.
-/
example (F : Filter X) : (Set.univ : Set X) ∈ F.sets := by
  sorry

/-
Show that if `U` belongs to a filter and `U ⊆ V`, then `V` belongs to the filter.
-/
example (F : Filter X) {U V : Set X}
    (hU : U ∈ F.sets) (hUV : U ⊆ V) :
    V ∈ F.sets := by
  sorry

/-
Show that the intersection of two sets belonging to a filter also belongs to the filter.
-/
example (F : Filter X) {U V : Set X}
    (hU : U ∈ F.sets) (hV : V ∈ F.sets) :
    U ∩ V ∈ F.sets := by
  sorry

/-
Show that if `U` and `V` belong to a filter, and `U ∩ V ⊆ W`,
then `W` belongs to the filter.
-/
example (F : Filter X) {U V W : Set X}
    (hU : U ∈ F.sets) (hV : V ∈ F.sets)
    (hW : U ∩ V ⊆ W) :
    W ∈ F.sets := by
  sorry

/-
Show that if `s ⊆ t`, then `t` belongs to the principal filter `𝓟 s`.
-/
example {s t : Set X} (h : s ⊆ t) :
    t ∈ (𝓟 s : Filter X) := by
  sorry

/-
Show that if `t` belongs to the principal filter `𝓟 s`, then `s ⊆ t`.
-/
example {s t : Set X} (h : t ∈ (𝓟 s : Filter X)) :
    s ⊆ t := by
  sorry

/-
Use the explicit description of `atTop` on `ℕ`.
If `s` contains all natural numbers greater than or equal to some `N`, then `s ∈ atTop`.
-/
example {s : Set ℕ} (N : ℕ)
    (hN : ∀ n ≥ N, n ∈ s) :
    s ∈ (atTop : Filter ℕ) := by
  sorry

/-
If `U` is open and contains `3`, then `U` is a neighborhood of `3`.
-/
example {U : Set ℝ}
    (openU : IsOpen U) (h3 : (3 : ℝ) ∈ U) :
    U ∈ 𝓝 (3 : ℝ) := by
  sorry

/-
Unfold membership in the pushforward filter.
-/
example (f : X → Y) (F : Filter X) {V : Set Y}
    (hV : f ⁻¹' V ∈ F) :
    V ∈ Filter.map f F := by
  sorry

/-
Use the almost-everywhere filter for Lebesgue measure.
If the complement of `s` has volume zero, then `s` belongs to the almost-everywhere filter.
-/
example {s : Set (ℝ × ℝ × ℝ)}
    (h : MeasureTheory.volume (sᶜ) = 0) :
    s ∈ MeasureTheory.ae MeasureTheory.volume := by
  sorry

/-
This one is difficult!
Give an explicit elementwise description of membership in the image
of a principal filter.

Mathematically, this says:

`V ∈ Filter.map f (𝓟 s)`

if and only if every point of `s` is sent by `f` into `V`.

The following might help:
-/
#check map_principal
#check mem_principal

example (f : X → Y) {s : Set X} {V : Set Y} :
    V ∈ Filter.map f (𝓟 s) ↔ ∀ x ∈ s, f x ∈ V := by
  sorry


/-
This one is also difficult!
Give an explicit elementwise description of a double pullback of a principal filter.

Mathematically, this says:

`U ∈ Filter.comap f (Filter.comap g (𝓟 s))`

if and only if every `x : X` whose image `g (f x)` lies in `s` already lies in `U`.

The following might help:
-/
#check comap_principal
#check mem_principal

example (f : X → Y) (g : Y → Z) {s : Set Z} {U : Set X} :
    U ∈ Filter.comap f (Filter.comap g (𝓟 s)) ↔
      ∀ x : X, g (f x) ∈ s → x ∈ U := by
  sorry

end filter

section limits

open Filter Topology

-- We can state `MyTendsto` using the language of Filter.Eventually.
example (u : ℕ → ℝ) (x : ℝ) : MyTendsto u atTop (𝓝 x) ↔ ∀ s ∈ 𝓝 x, ∀ᶠ n in atTop, u n ∈ s := by
  sorry

variable {X Y Z : Type*}

-- Show that `MyTendsto` unfolds to the condition `map f F ≤ G`.
example (f : X → Y) (F : Filter X) (G : Filter Y) :
    MyTendsto f F G ↔ map f F ≤ G := by
  sorry

-- Show that `MyTendsto` is the same as Lean's built-in `Tendsto`.
example (f : X → Y) (F : Filter X) (G : Filter Y) :
    MyTendsto f F G ↔ Tendsto f F G := by
  sorry

/-
Use the interaction between `map` and `comap`.
If `f` tends from `F` to `G`, then `F ≤ comap f G`.
-/
example (f : X → Y) (F : Filter X) (G : Filter Y)
    (h : Tendsto f F G) :
    F ≤ comap f G := by
  sorry

-- Conversely, if `F ≤ comap f G`, then `f` tends from `F` to `G`.
example (f : X → Y) (F : Filter X) (G : Filter Y)
    (h : F ≤ comap f G) :
    Tendsto f F G := by
  sorry

-- Use the explicit description of `Tendsto`.
-- If `f` tends from `F` to `G`, then the preimage of every set in `G` belongs to `F`.
example (f : X → Y) (F : Filter X) (G : Filter Y)
    (h : Tendsto f F G) {S : Set Y} (hS : S ∈ G) :
    f ⁻¹' S ∈ F := by
  sorry

-- Construct a proof of `Tendsto` from the explicit preimage condition.
example (f : X → Y) (F : Filter X) (G : Filter Y)
    (h : ∀ S : Set Y, S ∈ G → f ⁻¹' S ∈ F) :
    Tendsto f F G := by
  sorry

-- Show that the identity function tends from any filter to itself.
example (F : Filter X) :
    Tendsto (fun x : X => x) F F := by
  sorry

-- Show that every function tends from `F` to the pushforward filter `map f F`.
example (f : X → Y) (F : Filter X) :
    Tendsto f F (map f F) := by
  sorry

/-
For an ordinary limit of functions `ℝ → ℝ`, show that the preimage of an
open neighborhood of the target point is a neighborhood of the source point.
-/
example (f : ℝ → ℝ) (x₀ y₀ : ℝ)
    (h : Tendsto f (𝓝 x₀) (𝓝 y₀)) {V : Set ℝ}
    (openV : IsOpen V) (hyV : y₀ ∈ V) :
    f ⁻¹' V ∈ 𝓝 x₀ := by
  sorry

/-
For a convergent sequence, show that every open neighborhood of the limit
eventually contains all terms of the sequence.
-/
example (u : ℕ → ℝ) (x : ℝ)
    (h : Tendsto u atTop (𝓝 x)) {U : Set ℝ}
    (openU : IsOpen U) (hxU : x ∈ U) :
    ∃ N, ∀ n ≥ N, u n ∈ U := by
  sorry


/-
This one is very difficult!
Give an explicit real-variable description of the statement

`Tendsto f atTop atTop`.

Mathematically, this says:

`f(x) → ∞` as `x → ∞`

if and only if for every bound `B`, eventually `f x ≥ B`.
-/
example (f : ℝ → ℝ) :
    Tendsto f atTop atTop ↔
      ∀ B : ℝ, ∃ A : ℝ, ∀ x ≥ A, f x ≥ B := by
  sorry


/-
This one is also difficult!
Prove the composition theorem for limits using the explicit preimage description of `Tendsto`.

Mathematically, if

`f` tends from `F` to `G`

and

`g` tends from `G` to `H`,

then `g ∘ f` tends from `F` to `H`.
-/
example {F : Filter X} {G : Filter Y} {H : Filter Z}
    {f : X → Y} {g : Y → Z}
    (hf : Tendsto f F G) (hg : Tendsto g G H) :
    Tendsto (g ∘ f) F H := by
  sorry

end limits

section limitsLogic
/-
Recall some exercises in this section will benefit from the
`filter_upwards` tactic, which allows you to combine multiple eventually statements
-/
open Filter

-- Show that `True` is eventually true along any filter.
example {X : Type*} (F : Filter X) :
    ∀ᶠ _ in F, True := by
  sorry


-- If `P n` is eventually true, then `P n ∧ True` is eventually true.
example (P : ℕ → Prop)
    (hP : ∀ᶠ n in atTop, P n) :
    ∀ᶠ n in atTop, P n ∧ True := by
  sorry

/- If `P n` holds for sufficiently large `n`, then clearly does `P n ∨ Q n`:
we can use `Filter.Eventually.mono` to express this: `P n` implies `P n ∨ Q n` -/
example (P Q : ℕ → Prop)
    (hP : ∀ᶠ n in atTop, P n)
    (_hQ : ∀ᶠ n in atTop, Q n) :
    ∀ᶠ n in atTop, P n ∨ Q n := by
  sorry

-- If `P n` and `Q n` are eventually true, then `Q n ∧ P n` is eventually true.
example (P Q : ℕ → Prop)
    (hP : ∀ᶠ n in atTop, P n)
    (hQ : ∀ᶠ n in atTop, Q n) :
    ∀ᶠ n in atTop, Q n ∧ P n := by
  sorry

-- If `P n` is eventually true, then `P n ∨ Q n` is eventually true.
example (P Q : ℕ → Prop)
    (hP : ∀ᶠ n in atTop, P n) :
    ∀ᶠ n in atTop, P n ∨ Q n := by
  sorry

/-
Use monotonicity of `Eventually`.

If `P n` is eventually true and `P n → Q n` for every `n`, then `Q n` is eventually true.
-/
example (P Q : ℕ → Prop)
    (hP : ∀ᶠ n in atTop, P n)
    (hPQ : ∀ n, P n → Q n) :
    ∀ᶠ n in atTop, Q n := by
  sorry

/-
If `P n` is eventually true and `P n → Q n` is eventually true, then `Q n` is eventually true.
-/
example (P Q : ℕ → Prop)
    (hP : ∀ᶠ n in atTop, P n)
    (hPQ : ∀ᶠ n in atTop, P n → Q n) :
    ∀ᶠ n in atTop, Q n := by
  sorry

/-
If `P n`, `Q n`, and `R n` are all eventually true,
then `P n ∧ Q n ∧ R n` is eventually true.
-/
example (P Q R : ℕ → Prop)
    (hP : ∀ᶠ n in atTop, P n)
    (hQ : ∀ᶠ n in atTop, Q n)
    (hR : ∀ᶠ n in atTop, R n) :
    ∀ᶠ n in atTop, P n ∧ Q n ∧ R n := by
  sorry

/-
Turn an explicit bound into an eventually statement.

If `P n` holds for all `n ≥ N`, then `P n` is eventually true along `atTop`.
-/
example (P : ℕ → Prop) (N : ℕ)
    (hN : ∀ n ≥ N, P n) :
    ∀ᶠ n in atTop, P n := by
  sorry


/-
Turn an eventually statement into an explicit bound.

If `P n` is eventually true along `atTop`, then there is some `N`
such that `P n` holds for all `n ≥ N`.
-/
example (P : ℕ → Prop)
    (hP : ∀ᶠ n in atTop, P n) :
    ∃ N, ∀ n ≥ N, P n := by
  sorry


/-
If `P n → Q n` holds for all sufficiently large `n`, and `P n`
is eventually true, then `Q n` is eventually true.
-/
example (P Q : ℕ → Prop) (N : ℕ)
    (hN : ∀ n ≥ N, P n → Q n)
    (hP : ∀ᶠ n in atTop, P n) :
    ∀ᶠ n in atTop, Q n := by
  sorry

/-
This one is very difficult!
Give an explicit bounded description of two eventually true statements.

Mathematically, this says:

`P n` is eventually true and `Q n` is eventually true

if and only if

there is some `N` such that for every `n ≥ N`,
both `P n` and `Q n` hold.
-/
example (P Q : ℕ → Prop) :
    ((∀ᶠ n in atTop, P n) ∧ (∀ᶠ n in atTop, Q n)) ↔
      ∃ N, ∀ n ≥ N, P n ∧ Q n := by
  sorry


/-
This one is very difficult!
Chain two eventually true implications with an eventually true hypothesis,
and then extract an explicit bound.

Assume:

* `P n` is eventually true;
* `P n → Q n` is eventually true;
* `Q n → R n` is eventually true.

Then there is some `N` such that for every `n ≥ N`, `R n` holds.
-/
example (P Q R : ℕ → Prop)
    (hP : ∀ᶠ n in atTop, P n)
    (hPQ : ∀ᶠ n in atTop, P n → Q n)
    (hQR : ∀ᶠ n in atTop, Q n → R n) :
    ∃ N, ∀ n ≥ N, R n := by
  sorry

end limitsLogic

section derivatives

open Set Real Filter Topology

/-
Use `simp` to compute the derivative of sine.
-/
example (x : ℝ) :
    deriv Real.sin x = Real.cos x := by
  sorry


/-
Use `simp` to compute the derivative of cosine.
-/
example (x : ℝ) :
    deriv Real.cos x = - Real.sin x := by
  sorry


/-
Use `simp` to compute the derivative of a shifted complex sine function.
-/
example (x : ℂ) :
    deriv (fun y ↦ Complex.sin (y + 3)) x = Complex.cos (x + 3) := by
  sorry


/-
If a real function is not differentiable at `x`, then Lean's `deriv`
at `x` is `0`.
-/
example {f : ℝ → ℝ} {x : ℝ}
    (h : ¬ DifferentiableAt ℝ f x) :
    deriv f x = 0 := by
  sorry


/-
State that sine has derivative `cos x` at `x`.
-/
example (x : ℝ) :
    HasDerivAt Real.sin (Real.cos x) x := by
  sorry


/-
State that sine is differentiable at every real number.
-/
example (x : ℝ) :
    DifferentiableAt ℝ Real.sin x := by
  sorry


/-
If a function has a derivative at a point, then it is differentiable
at that point.
-/
example {f : ℝ → ℝ} {x y : ℝ}
    (h : HasDerivAt f y x) :
    DifferentiableAt ℝ f x := by
  sorry


/-
Unfold the definition of `HasDerivAt`.

The ordinary derivative-at-a-point statement is the same as the
corresponding filter statement along `𝓝 x ×ˢ pure x`.
-/
example {f : ℝ → ℝ} {x y : ℝ} :
    HasDerivAt f y x ↔ HasDerivAtFilter f y (𝓝 x ×ˢ pure x) := by
  sorry


/-
Use `HasDerivAt.add` to compute the derivative of `cos x + sin x`.
-/
example (x : ℝ) :
    HasDerivAt (fun t ↦ Real.cos t + Real.sin t)
      (Real.cos x - Real.sin x) x := by
  sorry


/-
Use `deriv_add`.

If `f` and `g` are differentiable at `x`, then the derivative of
`f + g` at `x` is the sum of the derivatives.
-/
example {f g : ℝ → ℝ} {x : ℝ}
    (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) :
    deriv (fun y ↦ f y + g y) x = deriv f x + deriv g x := by
  sorry


/-
Use `DifferentiableAt.add`.

If `f` and `g` are differentiable at `x`, then `f + g` is differentiable
at `x`.
-/
example {f g : ℝ → ℝ} {x : ℝ}
    (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) :
    DifferentiableAt ℝ (fun y ↦ f y + g y) x := by
  sorry


/-
An open interval is contained in the corresponding closed interval.
-/
example {a b x : ℝ}
    (hx : x ∈ Ioo a b) :
    x ∈ Icc a b := by
  sorry


/-
Use the intermediate value theorem to extract an actual point.

If `y ∈ [f a, f b]`, then there is some `x ∈ [a, b]`
such that `f x = y`.
-/
example {f : ℝ → ℝ} {a b y : ℝ}
    (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b))
    (hy : y ∈ Icc (f a) (f b)) :
    ∃ x ∈ Icc a b, f x = y := by
  sorry


/-
Apply the mean value theorem directly.
-/
example (f : ℝ → ℝ) {a b : ℝ}
    (hab : a < b)
    (hf : ContinuousOn f (Icc a b))
    (hf' : DifferentiableOn ℝ f (Ioo a b)) :
    ∃ c ∈ Ioo a b, deriv f c = (f b - f a) / (b - a) := by
  sorry


/-
Apply Rolle's theorem directly.

Notice that this theorem has no differentiability assumption.
-/
example {f : ℝ → ℝ} {a b : ℝ}
    (hab : a < b)
    (hfc : ContinuousOn f (Icc a b))
    (hfI : f a = f b) :
    ∃ c ∈ Ioo a b, deriv f c = 0 := by
  sorry


/-
This one is difficult!
Derive Rolle's theorem from the mean value theorem, assuming
differentiability on `(a, b)`.

Mathematically, if `f a = f b`, then the average slope is

`(f b - f a) / (b - a) = 0`.

So the mean value theorem gives a point where `deriv f c = 0`.
-/
example {f : ℝ → ℝ} {a b : ℝ}
    (hab : a < b)
    (hfc : ContinuousOn f (Icc a b))
    (hfd : DifferentiableOn ℝ f (Ioo a b))
    (hfI : f a = f b) :
    ∃ c ∈ Ioo a b, deriv f c = 0 := by
  sorry

/-
This one is very difficult!
Explain why Mathlib's Rolle theorem does not need a differentiability
assumption.

Split into two cases:

* If `f` is differentiable on `(a, b)`, use the mean value theorem.
* If not, then there is some `c ∈ (a, b)` where `f` is not differentiable
  within `(a, b)`. In particular, `f` is not differentiable at `c`,
  so Lean's convention gives `deriv f c = 0`.
-/

example {f : ℝ → ℝ} {a b : ℝ}
    (hab : a < b)
    (hfc : ContinuousOn f (Icc a b))
    (hfI : f a = f b) :
    ∃ c ∈ Ioo a b, deriv f c = 0 := by
  sorry

end derivatives
