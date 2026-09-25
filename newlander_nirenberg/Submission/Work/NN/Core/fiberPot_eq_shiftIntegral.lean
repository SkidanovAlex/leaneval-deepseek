/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# Shifting the fixed-disc potential to a disc centred at the fibre variable

The fixed-disc Cauchy potential

  `fiberPot R j u z = -(1/π) ∫_{‖w‖ < R} u (z with z j replaced by w) / (w - z j) dw`

integrates over the *fixed* disc `‖w‖ < R` with the pole placed at `z j`.  Replacing `w` by
`s + z j` turns this into an integral over the disc `‖s + z j‖ < R` centred at `-(z j)`, with the
pole at the origin:

  `fiberPot R j u z = -(1/π) ∫_{‖s - (−z j)‖ < R} u (z + s e_j) / s ds`.

This is the form in which the potential is compared with the translation-invariant
`∂̄`-transform, and it is used in `Work.NN.Core.fiberPot_dbarCoord_self`.
-/
import Mathlib
import Submission.Work.NN.Core.fiberPot

noncomputable section

open MeasureTheory Set

namespace Work.NN.Core

/-- The translation `w ↦ w + z j` sends `Function.update z j w` to `z + Function.update 0 j w`,
and the pole `w - z j` to `w`. -/
theorem fiberPot_eq_shiftIntegral {n : ℕ} (R : ℝ) (j : Fin n) {v : (Fin n → ℂ) → ℂ}
    (hv : Continuous v) (z : Fin n → ℂ) :
    Work.NN.Core.fiberPot R j v z = -((Real.pi:ℂ))⁻¹ *
      ∫ s in Metric.ball (-(z j)) R, v (z + Function.update (0:Fin n→ℂ) j s) / s := by
  have hfun : ∀ x : ℂ, Function.update z j (x + z j) = z + Function.update (0 : Fin n → ℂ) j x := by
    intro x
    funext l
    by_cases hl : l = j
    · subst hl
      simp only [Function.update_self, Pi.add_apply]
      ring
    · simp only [Function.update_of_ne hl, Pi.add_apply, Pi.zero_apply, add_zero]
  have hpre : (fun x : ℂ => x + z j) ⁻¹' Metric.ball (0:ℂ) R = Metric.ball (-(z j)) R := by
    ext x
    simp only [Set.mem_preimage, Metric.mem_ball, dist_eq_norm, sub_zero, sub_neg_eq_add]
  have hmp : MeasurePreserving (fun x : ℂ => x + z j) volume volume :=
    MeasureTheory.measurePreserving_add_right volume (z j)
  have hemb : MeasurableEmbedding (fun x : ℂ => x + z j) :=
    (MeasurableEquiv.addRight (z j)).measurableEmbedding
  have hkey : ∫ w in Metric.ball (0:ℂ) R, v (Function.update z j w) / (w - z j)
      = ∫ s in Metric.ball (-(z j)) R, v (z + Function.update (0:Fin n→ℂ) j s) / s := by
    have hpre_int := hmp.setIntegral_preimage_emb hemb
        (fun w : ℂ => v (Function.update z j w) / (w - z j)) (Metric.ball (0:ℂ) R)
    rw [← hpre_int, hpre]
    refine setIntegral_congr_fun measurableSet_ball (fun x _ => ?_)
    rw [hfun x, add_sub_cancel_right]
  rw [Work.NN.Core.fiberPot_apply, hkey]

end Work.NN.Core
