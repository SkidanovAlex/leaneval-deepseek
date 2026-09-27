import Mathlib
import Submission.Work.Drive.stripData

/-!
# The boundary value of the band datum `M` on the seam

At `τ = 0` and on the unit circle the band datum `M` of the configuration strip is the complexified
curve point: `M (e^{iσ}, 0) = symmC (curve γ σ)`.  Indeed `hMval` evaluates `M` at the chord
midpoint `dataMid γ x (√τ)`, and at `√0 = 0` that midpoint is the single point `x e^{i·0} = x`
(`curvePtAt_exp` with `sClamp 0 = 0`).
-/

namespace Work.Drive

/-- **Boundary value of the band datum.**  At `τ = 0` and on the unit circle, `M` is the
complexified curve point. -/
theorem dstripU_boundary_val {γ : Circle → ℝ × ℝ} {M : ℂ × ℝ → ℂ}
    (hMval : ∀ x : ℂ, ∀ τ : ℝ, 0 ≤ τ → ‖x‖ = 1 → M (x, τ) = Neutral.dataMid γ x (Real.sqrt τ))
    (s : ℝ) : M (dstripU s, 0) = Neutral.symmC (curve γ s) := by
  have hpt : Neutral.curvePtAt γ (dstripU s) 0 = Neutral.symmC (curve γ s) := by
    rw [show dstripU s = Complex.exp ((s : ℂ) * Complex.I) from rfl,
      Neutral.curvePtAt_exp, Neutral.sClamp_zero, add_zero]
  rw [hMval (dstripU s) 0 le_rfl (norm_dstripU s), Real.sqrt_zero]
  rw [Neutral.dataMid, Neutral.endPlus, Neutral.endMinus, neg_zero, hpt]
  field_simp
  ring

end Work.Drive
