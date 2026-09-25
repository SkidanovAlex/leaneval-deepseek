import Mathlib
import Submission.Work.NN.Core.fiberBeurling
import Submission.Work.NN.Core.fiberPot_dbarCoord

namespace Work.NN.Core

/-- The fixed-disc potential commutes with the `(1,0)`-derivatives in the other coordinates: for `k ≠ j`, `∂_k (fiberPot R j u) z = fiberPot R j (∂_k u) z`. This is the `(1,0)`-mirror of `Work.NN.Core.fiberPot_dbarCoord` and follows from `Work.NN.Core.fiberPot_fderiv_apply` (differentiation under the integral for directions with vanishing `j`-th component) and the definition of `dCoord`; the proof is the same computation as `fiberPot_dbarCoord` with the sign flipped. -/
theorem dCoord_fiberPot {n : ℕ} (R : ℝ) (j : Fin n) {k : Fin n} (hkj : k ≠ j)
    {u : Cn n → ℂ} (hu : ContDiff ℝ 1 u) (z : Cn n)
    (hdiff : DifferentiableAt ℝ (fiberPot R j u) z) :
    Work.CR.Flat.dCoord k (fiberPot R j u) z = fiberPot R j (Work.CR.Flat.dCoord k u) z := by
  have hv1 : (Pi.single k (1 : ℂ) : Fin n → ℂ) j = 0 :=
    Pi.single_eq_of_ne (Ne.symm hkj) 1
  have hv2 : (Pi.single k (Complex.I : ℂ) : Fin n → ℂ) j = 0 := by
    rw [Pi.single_eq_of_ne (Ne.symm hkj)]
  have h1 := fiberPot_fderiv_apply R j hu z (Pi.single k 1) hv1 hdiff
  have h2 := fiberPot_fderiv_apply R j hu z (Pi.single k Complex.I) hv2 hdiff
  have hL : Work.CR.Flat.dCoord k (fiberPot R j u) z
      = (1 / 2) * ((-(Real.pi : ℂ)⁻¹ *
            ∫ w in Metric.ball (0 : ℂ) R,
              (fderiv ℝ u (Function.update z j w)) (Pi.single k 1) / (w - z j))
          - Complex.I * (-(Real.pi : ℂ)⁻¹ *
            ∫ w in Metric.ball (0 : ℂ) R,
              (fderiv ℝ u (Function.update z j w)) (Pi.single k Complex.I) / (w - z j))) := by
    rw [Work.CR.Flat.dCoord, h1, h2]
  have hA1 := integrableOn_fderiv_apply_fiber R j hu z (Pi.single k 1)
  have hA2 := integrableOn_fderiv_apply_fiber R j hu z (Pi.single k Complex.I)
  have hB : (∫ w in Metric.ball (0 : ℂ) R,
        Work.CR.Flat.dCoord k u (Function.update z j w) / (w - z j))
      = (1 / 2) * ((∫ w in Metric.ball (0 : ℂ) R,
              (fderiv ℝ u (Function.update z j w)) (Pi.single k 1) / (w - z j))
          - Complex.I * (∫ w in Metric.ball (0 : ℂ) R,
              (fderiv ℝ u (Function.update z j w)) (Pi.single k Complex.I) / (w - z j))) := by
    have hgt : (fun w : ℂ => Work.CR.Flat.dCoord k u (Function.update z j w) / (w - z j))
        = fun w : ℂ =>
            (1 / 2) * ((fderiv ℝ u (Function.update z j w)) (Pi.single k 1) / (w - z j))
            - (1 / 2) * (Complex.I *
                ((fderiv ℝ u (Function.update z j w)) (Pi.single k Complex.I) / (w - z j))) := by
      funext w
      rw [Work.CR.Flat.dCoord]
      ring
    rw [hgt]
    rw [MeasureTheory.integral_sub (hA1.const_mul (1 / 2)) ((hA2.const_mul Complex.I).const_mul (1 / 2))]
    simp only [MeasureTheory.integral_const_mul]
    ring
  rw [hL, fiberPot_apply, hB]
  ring

end Work.NN.Core
