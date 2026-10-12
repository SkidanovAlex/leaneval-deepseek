import ChallengeDeps
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Submission.Work.BoseBogFS.integrand_reduction
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBogFS

open MeasureTheory

/-- **Integrability of the scaled clean bracket from that of the honest clean integrand.**

The pointwise scaling identity `cleanFun_scaled_eq` gives
`psiSc t = (ρ·a v)⁻¹ * cleanFun (√(ρ·a v) • t)`; integrability is preserved by composing
with the (nonzero) linear scaling `√(ρ·a v) • ·` (`MeasureTheory.Integrable.comp_smul`)
and multiplying by the constant `(ρ·a v)⁻¹`. -/
theorem integrable_psiSc_of_cleanFun {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {ρ μ : ℝ}
    (hP : 0 < ρ * _root_.BoseGases.a v)
    (hW : MeasureTheory.Integrable (Work.BoseFixR.W1fun v h (Work.BoseFixR.ell v μ)))
    (hc : MeasureTheory.Integrable (fun k : EuclideanSpace ℝ (Fin 3) => Work.BoseBogFS.cleanFun v h ρ μ k)) :
    MeasureTheory.Integrable (fun t : EuclideanSpace ℝ (Fin 3) => Work.BoseBogFS.psiSc v h ρ μ t) := by
  have hfun : (fun t : EuclideanSpace ℝ (Fin 3) => Work.BoseBogFS.psiSc v h ρ μ t)
      = fun t : EuclideanSpace ℝ (Fin 3) => (ρ * _root_.BoseGases.a v)⁻¹ *
          Work.BoseBogFS.cleanFun v h ρ μ (Real.sqrt (ρ * _root_.BoseGases.a v) • t) := by
    funext t
    rw [cleanFun_scaled_eq hP t, ← mul_assoc, inv_mul_cancel₀ (ne_of_gt hP), one_mul]
  rw [hfun]
  have hcomp : MeasureTheory.Integrable
      (fun t : EuclideanSpace ℝ (Fin 3) =>
        Work.BoseBogFS.cleanFun v h ρ μ (Real.sqrt (ρ * _root_.BoseGases.a v) • t)) :=
    hc.comp_smul (ne_of_gt (Real.sqrt_pos.mpr hP))
  simpa [smul_eq_mul] using hcomp.const_mul ((ρ * _root_.BoseGases.a v)⁻¹)

end Work.BoseBogFS
