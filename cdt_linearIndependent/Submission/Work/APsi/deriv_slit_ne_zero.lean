import Mathlib
import Submission.Work.APsi.defs
import Submission.Work.APsi.slit_facts
import Submission.Work.APsi.slit_norm_eq_one
import Submission.Work.ANum.slit_deriv_zero

/-!
# Area `Ψ_A`: the slit map has no critical point on the unit disc

For `0 < r < 1` the slit map `slit r : 𝔻 → 𝔻 ∖ (-1,-r]` of Calegari--Dimitrov--Tang
(arXiv:2408.15403, eq. `(slit)`) is a conformal isomorphism of the open unit disc onto the
slitted disc, hence in particular has non-vanishing derivative there.  We prove this
elementarily from the Joukowski relation

  `slit r w + (slit r w)⁻¹ = ((1+r)²/(4r)) (w + w⁻¹) - (r-1)²/(2r)`,   `w ≠ 0`

(`slit_joukowski_ab`): differentiating it on the punctured disc and using
`slit r z ≠ 0` for `z ≠ 0` gives, at any `z ≠ 0`,

  `slit r '(z) · (1 - 1/(slit r z)²) = ((1+r)²/(4r)) · (1 - 1/z²)`.

If `slit r '(z) = 0` the right-hand side would vanish, forcing `z² = 1` and hence
`‖z‖ = 1`, contradicting `‖z‖ < 1`.  At `z = 0` the derivative is the explicit positive
number `4r/(1+r)²` (`Submission.Work.ANum.slit_deriv_zero`).
-/

namespace Work.APsi

open Submission.CDTPlan Complex Filter Metric

theorem deriv_slit_ne_zero (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    ∀ z : ℂ, ‖z‖ < 1 → deriv (Submission.CDTPlan.slit r) z ≠ 0 := by
  intro z hz
  rcases eq_or_ne z 0 with hz0 | hz0
  · -- at the origin the derivative is the explicit positive slope `4r/(1+r)²`
    subst hz0
    rw [(Work.ANum.slit_deriv_zero r hr0 hr1).deriv]
    apply div_ne_zero
    · exact mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr (ne_of_gt hr0))
    · exact pow_ne_zero 2 (by
        have hh : (1 : ℂ) + (r : ℂ) = ((1 + r : ℝ) : ℂ) := by push_cast; ring
        rw [hh]; exact Complex.ofReal_ne_zero.mpr (by linarith))
  · -- away from the origin: differentiate the Joukowski relation
    intro hd
    have hzmem : z ∈ Metric.ball (0 : ℂ) 1 := by
      rw [Metric.mem_ball, dist_zero_right]; exact hz
    have hf_diff : DifferentiableAt ℂ (slit r) z :=
      (differentiableOn_slit r hr0 hr1).differentiableAt (Metric.isOpen_ball.mem_nhds hzmem)
    have hfz : slit r z ≠ 0 := slit_ne_zero r hr0 z hz0
    -- derivative of the left-hand side `w ↦ slit r w + (slit r w)⁻¹`
    have hL : HasDerivAt (fun w : ℂ => slit r w + (slit r w)⁻¹)
        (deriv (slit r) z + (-(deriv (slit r) z) / (slit r z)^2)) z :=
      (hf_diff.hasDerivAt).add ((hf_diff.hasDerivAt).inv hfz)
    have hbase : HasDerivAt (fun w : ℂ => w + w⁻¹) (1 - (z^2)⁻¹) z := by
      have h := (hasDerivAt_id' z).add ((hasDerivAt_id z).inv hz0)
      refine h.congr_deriv ?_
      simp only [id_eq]
      ring
    -- derivative of the right-hand side `w ↦ ((1+r)²/(4r)) (w + w⁻¹) - (r-1)²/(2r)`
    have hg : HasDerivAt
        (fun w : ℂ => ((1 + (r:ℂ))^2/(4*(r:ℂ))) * (w + w⁻¹) - (((r:ℂ)-1)^2/(2*(r:ℂ))))
        ((((1 + (r:ℂ))^2/(4*(r:ℂ)))) * (1 - (z^2)⁻¹)) z :=
      (hbase.const_mul (((1 + (r:ℂ))^2/(4*(r:ℂ))))).sub_const ((((r:ℂ)-1)^2/(2*(r:ℂ))))
    -- the two functions agree on a punctured neighbourhood of `z`
    have hEq : (fun w : ℂ => slit r w + (slit r w)⁻¹) =ᶠ[nhds z]
        (fun w : ℂ => ((1 + (r:ℂ))^2/(4*(r:ℂ))) * (w + w⁻¹)
          - (((r:ℂ)-1)^2/(2*(r:ℂ)))) := by
      filter_upwards [eventually_ne_nhds hz0] with w hw
      exact slit_joukowski_ab r hr0 w hw
    have huniq := hL.unique (hg.congr_of_eventuallyEq hEq)
    rw [hd] at huniq
    simp only [neg_zero, zero_div, zero_add] at huniq
    have hαne : ((1 + (r:ℂ))^2/(4*(r:ℂ))) ≠ 0 := by
      apply div_ne_zero
      · exact pow_ne_zero 2 (by
          have hh : (1 : ℂ) + (r : ℂ) = ((1 + r : ℝ) : ℂ) := by push_cast; ring
          rw [hh]; exact Complex.ofReal_ne_zero.mpr (by linarith))
      · exact mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr (ne_of_gt hr0))
    have h1 : (1 : ℂ) - (z^2)⁻¹ = 0 := (mul_eq_zero.mp huniq.symm).resolve_left hαne
    have h2 : (z^2)⁻¹ = 1 := (sub_eq_zero.mp h1).symm
    have h3 : z^2 = 1 := by
      have hz2 : z^2 ≠ 0 := pow_ne_zero 2 hz0
      have h4 : z^2 * (z^2)⁻¹ = z^2 * (1 : ℂ) := congrArg (fun t => z^2 * t) h2
      rw [mul_inv_cancel₀ hz2, mul_one] at h4
      exact h4.symm
    have key : ‖z‖^2 = 1 := by
      have h := congrArg norm h3
      rw [norm_one, norm_pow] at h
      exact h
    have hnorm : ‖z‖ = 1 := by nlinarith [norm_nonneg z]
    linarith

end Work.APsi
