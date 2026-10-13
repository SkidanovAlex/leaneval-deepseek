/-
# `Work.FTS.RegPkgGal.R1` — the structural fields of the extension `g̃` (design §4, R1)

R1 of `FTS_PHYS_BRIDGE.md` §4 is the gluing of the extension `g̃ = extG g`:

> R1 `ext_hcont`:  `C¹` gluing across `z = 0`, using `g = ∂_zg = ∂_τg = 0` there and the Jets of
> R3/R5, and across `τ = 0`, using one-sided continuity of `∂_τg`.  Also covers `hvt`/`hquad0`/
> `hquad`.

Three of R1's clauses are **immediate from the definition** of `extG` and need *no* hypothesis on
`g`:  since `extG g z θ τ = 0` for every `z ≤ 0`, the extension vanishes at `z = 0`, its
`z`-derivative at `z = 0` is `0` (the one-sided derivative at `0` of a function that is `0` on
`(-∞,0]` is `0`, and `deriv` is the junk value `0` when the two-sided derivative does not exist),
and it vanishes on the two angular boundary lines as soon as the original slice does.  Those are
proved here (`extG_hquad0`, `extG_hquad`, `extG_hvt`).

The remaining clause, the joint `C¹`-smoothness `hcont : ContDiffOn ℝ 1 (fun q : ℝ × ℝ =>
g̃ q.1 θ q.2) (Ioi (-1) ×ˢ Ioo (-1) (S+1))` at each fixed `θ ∈ Iθ`, is the *gluing* statement: it
needs

* on `{z > 0}`: joint `C¹` of `(z,τ) ↦ g z θ τ`, which is `RegPkgMin.c1` on `τ > 0` and, at
  `τ ≤ 0`, the linear branch `g z θ 0 + τ·∂_τg(z,θ,0)` — so it also needs the `z`-regularity of
  `∂_τg(·,θ,0)`;
* at `z = 0` (with `τ ≠ 0`): the one-sided limits `g z θ τ → 0`, `∂_zg(z,θ,τ) → 0`,
  `∂_τg(z,θ,τ) → 0` as `z → 0⁺`;
* at `τ = 0`: the two-sided derivative `deriv (fun s => g z θ s) 0` must equal the one-sided value
  `dynLin + dynRHS` at `τ = 0` (`IsDynEqOn` only gives the within-derivative on `Ici 0`), plus the
  continuity in `τ` of that value.

It is delegated as `Submission.Work.FTS.RegPkgGal.R1.extG_cont`; the three clauses below are the
part of R1 that is proved here.
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.RegPkgGal.Defs
import Submission.Work.FTS.RegPkgGal.Basic
import Submission.Work.FTS.RegPkgGal.RVocab

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FiniteTimeSingularity Set Filter Topology MeasureTheory
open scoped Topology Real

namespace Work.FTS.RegPkgGal

open Work.FTS.Regularity

set_option autoImplicit false

/-- A function that vanishes on `(-∞,0]` has derivative `0` at `0`: if it is differentiable there
the two-sided derivative is the left one (which is `0`), and otherwise `deriv` is the junk value
`0`. -/
lemma deriv_zero_of_eq_zero_on_nonpos {f : ℝ → ℝ} (h : ∀ z : ℝ, z ≤ 0 → f z = 0) :
    deriv f 0 = 0 := by
  by_cases hd : DifferentiableAt ℝ f 0
  · have h1 : HasDerivWithinAt f (deriv f 0) (Set.Iic 0) 0 := hd.hasDerivAt.hasDerivWithinAt
    have h2 : HasDerivWithinAt f 0 (Set.Iic 0) 0 :=
      (hasDerivWithinAt_const (0 : ℝ) (Set.Iic 0) 0).congr (fun y hy => h y hy) (h 0 le_rfl)
    exact UniqueDiffWithinAt.eq_deriv (Set.Iic 0) (uniqueDiffWithinAt_Iic 0) h1 h2
  · exact deriv_zero_of_not_differentiableAt hd

/-- **R1 (axis clauses).**  The extension vanishes at `z = 0`, for every `θ`, `τ`: this is the
`z ≤ 0` branch of `extG`, and it needs nothing about `g`. -/
theorem extG_hquad0 (g : Fam) (τ θ : ℝ) : extG g 0 θ τ = 0 := extG_of_nonpos (le_refl 0)

/-- **R1 (axis clauses).**  The `z`-derivative of the extended slice vanishes at `z = 0`: the
slice of the extension is `0` on `(-∞,0]`, so its derivative at `0` is `0`. -/
theorem extG_hquad (g : Fam) (τ θ : ℝ) :
    Work.Spaces.pz (fun z θ => extG g z θ τ) 0 θ = 0 := by
  refine deriv_zero_of_eq_zero_on_nonpos (fun z hz => ?_)
  exact extG_of_nonpos hz

/-- **R1 (`hvt`).**  The extended slice vanishes on the two angular boundary lines as soon as the
original one does: on the left half-plane it is `0` by definition, and at `z > 0` and `τ ≥ 0` it
is `g`. -/
theorem extG_hvt {S : ℝ} {g : Fam}
    (hvan : ∀ τ, 0 ≤ τ → ∀ z : ℝ, 0 ≤ z → g z 0 τ = 0 ∧ g z (π / 2) τ = 0) :
    ∀ τ ∈ Set.Icc 0 S, Work.Spaces.VanishTheta (fun z θ => extG g z θ τ) := by
  intro τ hτ
  constructor
  · intro z
    show extG g z 0 τ = 0
    by_cases hz : z ≤ 0
    · exact extG_of_nonpos hz
    · rw [extG_of_pos (lt_of_not_ge hz) hτ.1]
      exact (hvan τ hτ.1 z (le_of_lt (lt_of_not_ge hz))).1
  · intro z
    show extG g z (π / 2) τ = 0
    by_cases hz : z ≤ 0
    · exact extG_of_nonpos hz
    · rw [extG_of_pos (lt_of_not_ge hz) hτ.1]
      exact (hvan τ hτ.1 z (le_of_lt (lt_of_not_ge hz))).2

end Work.FTS.RegPkgGal
