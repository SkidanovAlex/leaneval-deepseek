import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.Nonlinear.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.Nonlinear.FstarPkg

/-- The angular moment of the fundamental profile `F_*`:
`(F_*, K)_{L²_θ}(z) = α · F_*(z)`, because `F_*(z,θ) = α (Γ(θ)/c(α)) F_*(z)` and
`c(α) = ∫_θ Γ(θ) K(θ)` is non-zero (`Work.Spaces.c_bounds`). -/
theorem FK_Fstar {α z : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    Work.Construction.FK (Work.Construction.Fstar α) z = α * (2 * z / (1 + z) ^ 2) := by
  have hc : Work.Spaces.c α ≠ 0 := by
    have h := (Work.Spaces.c_bounds α hα hα1).1
    linarith
  rw [Work.Construction.FK]
  have h1 : ∀ θ ∈ Work.Spaces.Iθ,
      Work.Construction.Fstar α z θ * Work.Spaces.K θ
        = (α * Work.FM.Fstar z / Work.Spaces.c α) * (Work.Spaces.Gam α θ * Work.Spaces.K θ) := by
    intro θ _
    simp only [Work.Construction.Fstar]
    ring
  rw [MeasureTheory.setIntegral_congr_fun (s := Work.Spaces.Iθ) measurableSet_Icc h1]
  rw [MeasureTheory.integral_const_mul]
  rw [show (∫ θ in Work.Spaces.Iθ, Work.Spaces.Gam α θ * Work.Spaces.K θ) = Work.Spaces.c α
      from rfl]
  rw [div_mul_cancel₀ (α * Work.FM.Fstar z) hc, Work.FM.Fstar]

end Work.FTS.Nonlinear.FstarPkg
