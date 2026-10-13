/-
# `Transfer/Profiles.lean` — the radial profiles of the transfer defect

The transfer between the clean operator `𝓛̂ = 𝓛 − Transport` (proved coercive at every level by
`Assembly.coerData2_four`) and the paper's operator `𝓛_Γ^T` is governed by two *radial*
profiles.  Indeed
`Corr α f = 𝓛_Γ^T f − 𝓛̂ f = Γ(θ)·radA α f (z)` (`Corr_eq_radA`), because both nonlocal pieces
of `𝓛_Γ^T` are an angular factor times a `z`-only factor.

The two identities that drive the transfer (proved in `Transfer/IdentDth.lean` and
`Transfer/IdentDz.lean`) are

* `D_θ (𝓛_Γ^T f) = 𝓛̂ (D_θ f) + E1 α f`,  `E1 α f = (D_θΓ)·radA α f`;
* `D_z (𝓛_Γ^T f) = 𝓛̂ (D_z f) + E2 α f`,  `E2 α f = Ê₂ f + Γ·radS α f`.

The *first* defect is `α`-small (`|D_θΓ| ≤ 2αΓ`, `Coer1T.gammaPointwiseBnd_fts`); the second is
absorbed by the small step coefficient `c₂`.  Neither involves `L₁₂` of a *differentiated* datum
(`L₁₂(D_θ f)(0)` is what makes the paper's own induction fail on `CoerAdm`); this is the whole
content of design `N45_DESIGN_LEAD.md` §5 T2.

Everything here rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Complex.Trigonometric
import Submission.Work.FTS.Vocab
import Submission.Work.FTS.CoercivityFix.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Transfer

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-! ## The radial shapes occurring in `𝓛_Γ^T` -/

/-- The `z`-factor `a(z) = 2z/(c(1+z)²)` of the nonlocal term of `𝓛_Γ`. -/
def ampA (α : ℝ) (z : ℝ) : ℝ := 2 * z / (Work.Spaces.c α * (1 + z) ^ 2)

/-- The `z`-factor `b(z) = 2z²/(1+z)³` of the projector correction. -/
def ampB (α : ℝ) (z : ℝ) : ℝ := 2 * z ^ 2 / (1 + z) ^ 3

/-- `D_z a = z·a'`, the `D_z`-derivative of the nonlocal `z`-factor. -/
def dAmpA (α : ℝ) (z : ℝ) : ℝ := z * deriv (ampA α) z

/-- `D_z b = z·b'`, the `D_z`-derivative of the projector correction's `z`-factor. -/
def dAmpB (α : ℝ) (z : ℝ) : ℝ := z * deriv (ampB α) z

/-- **The radial profile of the transfer defect**: `Corr α f = Γ(θ)·radA α f z`. -/
def radA (α : ℝ) (f : Fn) (z : ℝ) : ℝ :=
  -ampA α z * Work.Coercivity.L12f f z
    + (ampB α z / Work.Spaces.c α) * Work.Coercivity.L12f (Work.Coercivity.Transport f) 0

/-- **The radial profile produced by `D_z`**: with `C₀(f) = L₁₂(Transport f)(0)`,
`radS α f z = −(D_z a)(z)·L₁₂ f(z) − a(z)·z·(L₁₂ f)'(z) + (b'(z)/c)·C₀(f)`.

Note the middle term: by the fundamental theorem of calculus
`z·(L₁₂ f)'(z) = −⟨K, f(z,·)⟩` (`Transfer.L12_deriv_eq`), i.e. an angular moment of `f` and
**not** an `L₁₂` of the differentiated datum.  This is exactly the point of design
`N45_DESIGN_LEAD.md` §5 T2. -/
def radS (α : ℝ) (f : Fn) (z : ℝ) : ℝ :=
  -dAmpA α z * Work.Coercivity.L12f f z
    - ampA α z * (z * deriv (Work.Coercivity.L12f f) z)
    + (dAmpB α z / Work.Spaces.c α) * Work.Coercivity.L12f (Work.Coercivity.Transport f) 0

/-! ## The two defects -/

/-- **The `D_θ`-defect of the transfer.**  It is `α`-small: `|D_θΓ| ≤ 2αΓ` on `Iθ`. -/
def E1 (α : ℝ) (f : Fn) : Fn := fun z θ =>
  (Real.sin (2 * θ) * deriv (Work.Spaces.Gam α) θ) * radA α f z

/-- **The `D_z`-defect of the transfer**: the clean defect `Ê₂` of `𝓛̂` plus the angular factor
`Γ` times the radial profile `radS`. -/
def E2 (α : ℝ) (f : Fn) : Fn := fun z θ =>
  Work.FTS.CoercivityFix.E2hat f z θ + Work.Spaces.Gam α θ * radS α f z

/-! ## `Corr` is `Γ` times a radial profile -/

/-- **`Corr α f = Γ(θ)·radA α f z`**: the transfer defect is a product of an angular function
and a radial one.  This is the structural fact the whole transfer rests on. -/
theorem Corr_eq_radA (α : ℝ) (f : Fn) (z θ : ℝ) :
    Work.FTS.CoercivityFix.Corr α f z θ = Work.Spaces.Gam α θ * radA α f z := by
  rw [Work.FTS.CoercivityFix.Corr_eq]
  simp only [radA, ampA, ampB]
  ring

/-- `radA` unfolded. -/
theorem radA_eq (α : ℝ) (f : Fn) (z : ℝ) :
    radA α f z = -(2 * z / (Work.Spaces.c α * (1 + z) ^ 2))
        * Work.Coercivity.L12f f z
      + (2 * z ^ 2 / (1 + z) ^ 3 / Work.Spaces.c α)
        * Work.Coercivity.L12f (Work.Coercivity.Transport f) 0 := rfl

/-- `E1` unfolded. -/
theorem E1_eq (α : ℝ) (f : Fn) (z θ : ℝ) :
    E1 α f z θ = (Real.sin (2 * θ) * deriv (Work.Spaces.Gam α) θ) * radA α f z := rfl

/-- `E2` unfolded. -/
theorem E2_eq (α : ℝ) (f : Fn) (z θ : ℝ) :
    E2 α f z θ = Work.FTS.CoercivityFix.E2hat f z θ + Work.Spaces.Gam α θ * radS α f z := rfl

end Work.FTS.CoercivityFix.Transfer
