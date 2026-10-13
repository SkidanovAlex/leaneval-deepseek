/-
# `Work.FTS.PhiStar.Linv23Aux.Defs` — the zero-moment inverse `Linv` in regularised form

`Work.FTS.PhiStar.Linv h θ` is defined as

`-((sin θ ^ 2 * cos θ ^ 3)⁻¹ * ∫ θ' in 0..θ, sin θ' ^ 2 * cos θ' ^ 3 * h θ' / sin (2 θ'))`.

The *integrand* of that primitive is a `0/0` expression at `θ' = 0`; the algebraic identity
`sin (2t) = 2 sin t cos t` shows pointwise (with Lean's junk-value convention `x/0 = 0`) that

`sin t ^ 2 * cos t ^ 3 * h t / sin (2t) = sin t * cos t ^ 2 / 2 * h t`

for **every** `t : ℝ` (both sides vanish when `sin t * cos t = 0`).  This file records that
identity (`sin_sq_cos_cube_div_s2`) and the resulting *regularised* description of `Linv`:

`Linv h θ = -((sin θ ^ 2 * cos θ ^ 3)⁻¹ * LinvPhi h θ)`,
`LinvPhi h θ = ∫ t in 0..θ, LinvPhiInt h t`,
`LinvPhiInt h t = sin t * cos t ^ 2 / 2 * h t`.

On `(0, π/2)` the factor `sin t cos² t / 2` is smooth, so all smoothness/boundedness questions
for `Linv` reduce to those for the primitive `LinvPhi` and for the multiplicative weight
`(sin² θ cos³ θ)⁻¹`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.PhiStar.StarDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ContDiff
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar

set_option autoImplicit false

/-- The regularised integrand `sin t · cos² t · h t / 2` of the primitive entering `Linv h`. -/
def LinvPhiInt (h : ℝ → ℝ) : ℝ → ℝ := fun t => Real.sin t * Real.cos t ^ 2 / 2 * h t

/-- The primitive `θ ↦ ∫_0^θ sin t cos² t h t / 2`; `Linv h` is its `σ`-normalisation
`-(sin² θ cos³ θ)⁻¹ · LinvPhi h θ` (`Linv_eq`). -/
def LinvPhi (h : ℝ → ℝ) : ℝ → ℝ := fun θ => ∫ t in (0 : ℝ)..θ, LinvPhiInt h t

/-- The quotient integrand of `Linv` equals the regular one **everywhere**:
`sin² t cos³ t / sin (2t) = sin t cos² t / 2` (both sides are `0` when `sin t · cos t = 0`). -/
theorem sin_sq_cos_cube_div_s2 (t : ℝ) :
    Real.sin t ^ 2 * Real.cos t ^ 3 / Work.Construction.s2 t
      = Real.sin t * Real.cos t ^ 2 / 2 := by
  rw [Work.Construction.s2_eq, Real.sin_two_mul]
  by_cases hs : Real.sin t = 0
  · simp [hs]
  by_cases hc : Real.cos t = 0
  · simp [hc]
  · field_simp

/-- The definitional content of `Linv`, in regularised form.
(Named `Linv_eq_phi` — **not** `Linv_eq` — because the pointwise zero-moment inverse identity
`Linv_eq` already exists in `Work.FTS.PhiStar` (`PhiStar/LinvI_solves.lean`, in the function
form `Linv h = fun θ => ...`); two declarations of the same name would make it impossible to
import `Linv23Aux` and `LinvI_solves` together.) -/
theorem Linv_eq_phi (h : ℝ → ℝ) (θ : ℝ) :
    Linv h θ = -((Real.sin θ ^ 2 * Real.cos θ ^ 3)⁻¹ * LinvPhi h θ) := by
  have key : (∫ t in (0 : ℝ)..θ,
        Real.sin t ^ 2 * Real.cos t ^ 3 * h t / Work.Construction.s2 t)
      = ∫ t in (0 : ℝ)..θ, LinvPhiInt h t := by
    apply intervalIntegral.integral_congr
    intro t _
    change Real.sin t ^ 2 * Real.cos t ^ 3 * h t / Work.Construction.s2 t
      = Real.sin t * Real.cos t ^ 2 / 2 * h t
    rw [show Real.sin t ^ 2 * Real.cos t ^ 3 * h t / Work.Construction.s2 t
          = (Real.sin t ^ 2 * Real.cos t ^ 3 / Work.Construction.s2 t) * h t from by ring,
      sin_sq_cos_cube_div_s2 t]
  simp only [Linv, LinvPhi, LinvPhiInt, key]

end Work.FTS.PhiStar
