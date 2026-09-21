import Mathlib

/-!
# Long-interval existence for the Volterra system: definitions

This file sets up the area `Work.VolterraLong`.  It is the definitional layer
for the exponentially weighted Volterra argument which removes the
short-interval restriction `L_Θ (b - a) < 1` from the Volterra existence
theorems (see `Commons.Geometry.Ulam.volterra_perturbation_exists_v3*`).

The integro-differential system under study is

`(★)   G(s, Z(s)) = ∫_s^b Θ(s,σ,Z(σ)) dσ + Ξ(s)`   on `s ∈ [a,b]`,

for a Banach space `E` (in the Ulam application `E = ℝ⁴`), and the strategy is
the classical one: linearise around a base solution `Z₀` of the *base* data
`(G₀,Θ₀,Ξ₀)`, and solve the resulting fixed point equation in the
exponentially weighted supremum norm `‖W‖_λ = sup_s ‖W s‖ e^{-λ(b-s)}`, in
which the Volterra integral operator gains a factor `1/λ`.

## Conventions

* `wdist lam Z W` is the weighted distance `sup_s ‖Z s - W s‖ e^{-λ(b-s)}`.
* Functions on the interval are `BoundedContinuousFunction (Set.Icc a b) E`;
  `bcfExt` extends such a function to all of `ℝ` by a constant (via
  `Set.IccExtend`), and `zExt hab f` does the same for an arbitrary function
  `f : ℝ → E` which is only continuous on `Icc a b`.
* `defect` is the defect `Ξ̃` of the linearisation, `qrem` is the quadratic
  Taylor remainder `Q̃`, and `longOpFun` is (the underlying function of) the
  Volterra operator whose fixed points are exactly the solutions of `(★)`.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Set Filter MeasureTheory
open scoped Topology Interval

namespace Work.VolterraLong

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ## The exponentially weighted supremum distance -/

/-- The exponentially weighted supremum distance on `C([a,b], E)`:
`wdist lam Z W = sup_{s ∈ [a,b]} ‖Z s - W s‖ * exp (-(lam * (b - s)))`. -/
def wdist {a b : ℝ} (lam : ℝ) (Z W : BoundedContinuousFunction (Set.Icc a b) E) : ℝ :=
  sSup (Set.range fun s : Set.Icc a b => ‖Z s - W s‖ * Real.exp (-(lam * (b - (s : ℝ)))))

/-- The weighted norm of `Z`, i.e. its weighted distance to the zero function. -/
def wnorm {a b : ℝ} (lam : ℝ) (Z : BoundedContinuousFunction (Set.Icc a b) E) : ℝ :=
  wdist lam Z 0

/-! ## Extending functions on `[a,b]` to `ℝ` -/

/-- Extend a function on the interval `[a,b]` to all of `ℝ` by the constant
value at the nearest endpoint (`Set.IccExtend`). -/
def zExt {a b : ℝ} (hab : a ≤ b) (Z : ℝ → E) : ℝ → E :=
  Set.IccExtend hab fun s : Set.Icc a b => Z s

/-- Extend a `BoundedContinuousFunction` on `[a,b]` to all of `ℝ`. -/
def bcfExt {a b : ℝ} (hab : a ≤ b) (Z : BoundedContinuousFunction (Set.Icc a b) E) : ℝ → E :=
  Set.IccExtend hab fun s : Set.Icc a b => Z s

lemma zExt_of_mem {a b : ℝ} (hab : a ≤ b) {Z : ℝ → E} {s : ℝ} (hs : s ∈ Set.Icc a b) :
    zExt hab Z s = Z s := by
  dsimp [zExt]
  exact Set.IccExtend_of_mem hab (fun s : Set.Icc a b => Z s) hs

lemma bcfExt_of_mem {a b : ℝ} (hab : a ≤ b) {Z : BoundedContinuousFunction (Set.Icc a b) E}
    {s : ℝ} (hs : s ∈ Set.Icc a b) : bcfExt hab Z s = Z ⟨s, hs⟩ := by
  dsimp [bcfExt]
  exact Set.IccExtend_of_mem hab (fun s : Set.Icc a b => Z s) hs

lemma bcfExt_apply {a b : ℝ} (hab : a ≤ b) (Z : BoundedContinuousFunction (Set.Icc a b) E)
    (s : Set.Icc a b) : bcfExt hab Z (s : ℝ) = Z s := by
  dsimp [bcfExt]
  exact Set.IccExtend_val hab (fun s : Set.Icc a b => Z s) s

@[fun_prop]
lemma bcfExt_continuous {a b : ℝ} (hab : a ≤ b)
    (Z : BoundedContinuousFunction (Set.Icc a b) E) : Continuous (bcfExt hab Z) := by
  dsimp [bcfExt]
  exact Z.continuous.Icc_extend'

@[fun_prop]
lemma zExt_continuous {a b : ℝ} (hab : a ≤ b) {Z : ℝ → E}
    (hZ : ContinuousOn Z (Set.Icc a b)) : Continuous (zExt hab Z) := by
  have hsub : Continuous fun s : Set.Icc a b => Z s :=
    continuousOn_iff_continuous_domRestrict.mp hZ
  dsimp [zExt]
  exact hsub.Icc_extend'

/-! ## The linearisation data -/

/-- The defect of the linearisation,

`Ξ̃(s) = Ξ(s) - G(s, Z₀(s)) + ∫_s^b Θ(s,σ,Z₀(σ)) dσ`.

It measures the failure of `Z₀` to solve the perturbed equation, and is `O(ε)`
when the perturbed data is `ε`-close to the base data. -/
def defect (G : ℝ → E → E) (Θ : ℝ → ℝ → E → E) (Ξ : ℝ → E) (Z₀ : ℝ → E)
    (b s : ℝ) : E :=
  Ξ s - G s (Z₀ s) + ∫ σ in s..b, Θ s σ (Z₀ σ)

/-- The quadratic Taylor remainder of `G` around `Z₀(s)`, with linear part
`A`:

`Q̃(s,w) = G(s, Z₀(s) + w) - G(s, Z₀(s)) - A w`. -/
def qrem (G : ℝ → E → E) (A : E ≃L[ℝ] E) (Z₀ : ℝ → E) (s : ℝ) (w : E) : E :=
  G s (Z₀ s + w) - G s (Z₀ s) - A w

/-- The underlying function of the long-interval Volterra operator:

`T W s = W s - A(s)⁻¹ ( G(s, Z₀(s)+W(s)) - ∫_s^b Θ(s,σ,Z₀(σ)+W(σ)) dσ - Ξ(s) )`.

Fixed points of `T` are exactly the functions `W` with `Z₀ + W` solving `(★)`
(see `solves_of_isFixedPt`). -/
def longOpFun (A : ℝ → E ≃L[ℝ] E) (G : ℝ → E → E) (Θ : ℝ → ℝ → E → E) (Ξ : ℝ → E)
    (Z₀ W : ℝ → E) (b s : ℝ) : E :=
  W s - (A s).symm (G s (Z₀ s + W s) - (∫ σ in s..b, Θ s σ (Z₀ σ + W σ)) - Ξ s)

/-- The long-interval Volterra operator as a function on the closed interval
`[a,b]`, with `Z₀` and `W` extended to `ℝ` by `zExt`/`bcfExt`. -/
def longOpFunOn {a b : ℝ} (hab : a ≤ b) (A : ℝ → E ≃L[ℝ] E) (G : ℝ → E → E)
    (Θ : ℝ → ℝ → E → E) (Ξ : ℝ → E) (Z₀ : ℝ → E)
    (W : BoundedContinuousFunction (Set.Icc a b) E) : Set.Icc a b → E :=
  fun s => longOpFun A G Θ Ξ (zExt hab Z₀) (bcfExt hab W) b (s : ℝ)

/-- The solution predicate: `Z` solves `(★)` on `[a,b]`. -/
def SolvesOn (a b : ℝ) (G : ℝ → E → E) (Θ : ℝ → ℝ → E → E) (Ξ : ℝ → E)
    (Z : ℝ → E) : Prop :=
  ∀ s ∈ Set.Icc a b, G s (Z s) = (∫ σ in s..b, Θ s σ (Z σ)) + Ξ s

end Work.VolterraLong
