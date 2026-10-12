import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseB4.BoxChi
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB4.realIP_thetaFun_eq_box`

The sharp box indicator `θ_Λ = 1_{Λ(ℓ)}` (`Work.BoseB4.BoxData.thetaFun`) is the
identity of the box Hilbert space on functions supported in the box: for any
`f` with `Function.support f ⊆ B.boxL ℓ` (FS's `f ∈ L²(Λ)` read as a support
condition on the ambient `ℝ³`),

  `⟨θ_Λ, f⟩ = ∫ Re(conj θ_Λ · f) = ∫ Re f`.

This is the pointwise statement `Re(conj θ_Λ(x) f(x)) = Re f(x)`: on the box
`θ_Λ = 1`, so the factor is `1`; off the box `f x = 0` by the support hypothesis,
so both sides vanish (there `θ_Λ = 0` as well).  In particular no integrability
of `f` has to be assumed -- the two integrands agree as *functions*, and the
Bochner integral is congruent.
-/

noncomputable section

open scoped BigOperators Pointwise
open MeasureTheory Classical

namespace Work.BoseB4

/-- **`θ_Λ` is the identity on the box.**  If `f` is supported in `Λ(ℓ)` then
`⟨θ_Λ, f⟩ = ∫ Re f`. -/
theorem realIP_thetaFun_eq_box (B : Work.BoseB4.BoxData) {ℓ : ℝ}
    {f : EuclideanSpace ℝ (Fin 3) → ℂ} (hf : Function.support f ⊆ B.boxL ℓ) :
    B.realIP (B.thetaFun ℓ) f = ∫ x, (f x).re := by
  -- The two integrands agree pointwise.
  have hpt : ∀ x : EuclideanSpace ℝ (Fin 3),
      ((starRingEnd ℂ) (B.thetaFun ℓ x) * f x).re = (f x).re := by
    intro x
    by_cases hx : x ∈ B.boxL ℓ
    · -- on the box `θ_Λ x = 1`
      simp [BoxData.thetaFun_apply, hx]
    · -- off the box `θ_Λ x = 0` and `f x = 0` by the support hypothesis
      have hfx : f x = 0 := by
        by_contra h
        exact hx (hf (Function.mem_support.mpr h))
      simp [BoxData.thetaFun_apply, hx, hfx]
  rw [BoxData.realIP_apply]
  exact integral_congr_ae (Filter.Eventually.of_forall hpt)

end Work.BoseB4
