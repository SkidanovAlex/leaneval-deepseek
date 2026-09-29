import Mathlib
import Submission.Work.APsi.psiA_facts
import Submission.Work.APsi.defs

/-!
# `APull` — injectivity of the Theorem-A contour map `ψ_A` on the unit disc

`ψ_A(z) = -(4/5) · lune (36/5) (-(w₄ z))`, where `w₄ = slitsA` is the four-fold composition of
slit maps and rotations of Calegari--Dimitrov--Tang, arXiv:2408.15403 (Theorem A contour).

The contour map is a conformal map of the unit disc (the paper's normalization of the
`l = 2` holonomy argument needs it to be univalent).  Here we only prove injectivity:

* the lune map is *globally* injective, with explicit left inverse `luneF c`
  (`Work.APsi.luneF_lune`), so `lune c` may be cancelled;
* each slit map `slit r`, `0 < r < 1`, is injective on the unit disc: if
  `slit r z = slit r w ≠ 0` then the Joukowski relation `slit_joukowski_ab` forces
  `z + z⁻¹ = w + w⁻¹`, i.e. `(z-w)(zw-1) = 0`, and `zw = 1` is impossible for
  `‖z‖, ‖w‖ < 1`; the value `0` is attained only at `z = 0`;
* the four slit stages `Work.APsi.psiA_st1, …, psiA_st5` each map the disc to itself
  (`Work.APsi.psiA_st*_maps_ball`), so the chain can be peeled off one stage at a time,
  cancelling the rotations `rot t ≠ 0` and the factor `491/500 ≠ 0`.
-/

namespace Work.APull

open Submission.CDTPlan Complex Metric

noncomputable section

/-- The lune map `lune c`, `c > 1`, is injective (its explicit left inverse is `luneF c`). -/
lemma psiA_aux_lune_injective (c : ℝ) (hc : 1 < c) : Function.Injective (lune c) := by
  intro z w h
  have h1 := Work.APsi.luneF_lune c hc z
  rw [h] at h1
  exact h1.symm.trans (Work.APsi.luneF_lune c hc w)

/-- The slit map `slit r`, `0 < r < 1`, is injective on the unit disc.

Both arguments lie in the disc, where `slit r` is univalent; the proof uses the Joukowski
relation `slit_joukowski_ab` of `Work.APsi.defs` and the fact that `slit r z + (slit r z)⁻¹`
determines `z` uniquely in the disc (`z ↦ z + z⁻¹` is injective there, the two preimages
`z, z⁻¹` being separated by the unit circle). -/
lemma psiA_aux_slit_injective_ball (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    ∀ z w : ℂ, z ∈ ball (0 : ℂ) 1 → w ∈ ball (0 : ℂ) 1 → slit r z = slit r w → z = w := by
  intro z w hz hw h
  rw [Work.APsi.psiA_mem_ball_one] at hz hw
  rcases eq_or_ne z 0 with hz0 | hz0
  · subst hz0
    have : slit r w = 0 := by rw [← h]; simp [Submission.CDTPlan.slit]
    exact (Work.APsi.slit_eq_zero r hr0 w this).symm
  · have hw0 : w ≠ 0 := by
      intro hw0
      rw [hw0] at h
      exact Work.APsi.slit_ne_zero r hr0 z hz0 (by simpa [Submission.CDTPlan.slit] using h)
    have h1 := Work.APsi.slit_joukowski_ab r hr0 z hz0
    have h2 := Work.APsi.slit_joukowski_ab r hr0 w hw0
    rw [h] at h1
    have h3 : z + z⁻¹ = w + w⁻¹ := by
      have hα : ((1 + (r : ℂ)) ^ 2 / (4 * (r : ℂ))) ≠ 0 := by
        have hrC : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hr0)
        have h1r : (1 + (r : ℂ)) ≠ 0 := by
          intro hh
          have hh' : (1 : ℝ) + r = 0 := by exact_mod_cast hh
          linarith
        exact div_ne_zero (pow_ne_zero 2 h1r) (mul_ne_zero (by norm_num) hrC)
      have heq : ((1 + (r : ℂ)) ^ 2 / (4 * (r : ℂ))) * (z + z⁻¹)
            - ((r : ℂ) - 1) ^ 2 / (2 * (r : ℂ))
          = ((1 + (r : ℂ)) ^ 2 / (4 * (r : ℂ))) * (w + w⁻¹)
            - ((r : ℂ) - 1) ^ 2 / (2 * (r : ℂ)) := by
        rw [← h1, ← h2]
      have hA : ((1 + (r : ℂ)) ^ 2 / (4 * (r : ℂ))) * (z + z⁻¹) =
                ((1 + (r : ℂ)) ^ 2 / (4 * (r : ℂ))) * (w + w⁻¹) := by
        linear_combination heq
      exact mul_left_cancel₀ hα hA
    have hmain : (z - w) * (z * w - 1) = 0 := by
      have h5 : (z + z⁻¹) * (z * w) = (w + w⁻¹) * (z * w) :=
        congrArg (fun u : ℂ => u * (z * w)) h3
      have hL : (z + z⁻¹) * (z * w) = z ^ 2 * w + w := by field_simp [hz0]
      have hR : (w + w⁻¹) * (z * w) = w ^ 2 * z + z := by field_simp [hw0]
      have h5' : z ^ 2 * w + w = w ^ 2 * z + z := by rw [← hL, ← hR]; exact h5
      linear_combination h5'
    rcases mul_eq_zero.mp hmain with h6 | h6
    · exact sub_eq_zero.mp h6
    · exfalso
      have hzw : z * w = 1 := sub_eq_zero.mp h6
      have hnorm : ‖z‖ * ‖w‖ = 1 := by rw [← norm_mul, hzw, norm_one]
      nlinarith [norm_nonneg z, norm_nonneg w]

/-- `ψ_A` is injective on the unit disc: it is the composite of the (globally) injective lune
map `lune (36/5)` with the four-fold slit chain `slitsA = psiA_st5`, each stage of which is
injective on the disc. -/
theorem psiA_injective_ball :
    ∀ z w : ℂ, z ∈ Metric.ball (0 : ℂ) 1 → w ∈ Metric.ball (0 : ℂ) 1 →
      Submission.CDTPlan.psiA z = Submission.CDTPlan.psiA w → z = w := by
  intro z w hz hw h
  -- cancel the constant `-4/5` and the injective lune map
  have hlune : lune (36 / 5) (-slitsA z) = lune (36 / 5) (-slitsA w) := by
    have h' : -(4 / 5 : ℂ) * lune (36 / 5) (-slitsA z)
        = -(4 / 5 : ℂ) * lune (36 / 5) (-slitsA w) := h
    exact mul_left_cancel₀ (by norm_num) h'
  have hneg : -slitsA z = -slitsA w := psiA_aux_lune_injective (36 / 5) (by norm_num) hlune
  have h3 : slitsA z = slitsA w := neg_inj.mp hneg
  rw [Work.APsi.psiA_slitsA_eq] at h3
  -- peel off the slit chain, one stage at a time
  have h45 : Work.APsi.psiA_st4 z = Work.APsi.psiA_st4 w := by
    have h' : rot (-1971 / 25000) * Work.APsi.psiA_st4 z
        = rot (-1971 / 25000) * Work.APsi.psiA_st4 w := by
      simpa only [Work.APsi.psiA_st5] using h3
    exact mul_left_cancel₀ (Work.APsi.rot_ne_zero _) h'
  have h34 : Work.APsi.psiA_st3 z = Work.APsi.psiA_st3 w := by
    have h' : slit (7487 / 10000) (rot (453 / 12500) * Work.APsi.psiA_st3 z)
        = slit (7487 / 10000) (rot (453 / 12500) * Work.APsi.psiA_st3 w) := by
      simpa only [Work.APsi.psiA_st4] using h45
    have hmz := Work.APsi.psiA_mapsTo_rot_ball Work.APsi.psiA_st3_maps_ball (453 / 12500) hz
    have hmw := Work.APsi.psiA_mapsTo_rot_ball Work.APsi.psiA_st3_maps_ball (453 / 12500) hw
    have h'' := psiA_aux_slit_injective_ball (7487 / 10000) (by norm_num) (by norm_num)
      _ _ hmz hmw h'
    exact mul_left_cancel₀ (Work.APsi.rot_ne_zero _) h''
  have h23 : Work.APsi.psiA_st2 z = Work.APsi.psiA_st2 w := by
    have h' : slit (673 / 1250) (rot (2927 / 25000) * Work.APsi.psiA_st2 z)
        = slit (673 / 1250) (rot (2927 / 25000) * Work.APsi.psiA_st2 w) := by
      simpa only [Work.APsi.psiA_st3] using h34
    have hmz := Work.APsi.psiA_mapsTo_rot_ball Work.APsi.psiA_st2_maps_ball (2927 / 25000) hz
    have hmw := Work.APsi.psiA_mapsTo_rot_ball Work.APsi.psiA_st2_maps_ball (2927 / 25000) hw
    have h'' := psiA_aux_slit_injective_ball (673 / 1250) (by norm_num) (by norm_num)
      _ _ hmz hmw h'
    exact mul_left_cancel₀ (Work.APsi.rot_ne_zero _) h''
  have h12 : Work.APsi.psiA_st1 z = Work.APsi.psiA_st1 w := by
    have h' : slit (379 / 625) (rot (2033 / 25000) * Work.APsi.psiA_st1 z)
        = slit (379 / 625) (rot (2033 / 25000) * Work.APsi.psiA_st1 w) := by
      simpa only [Work.APsi.psiA_st2] using h23
    have hmz := Work.APsi.psiA_mapsTo_rot_ball Work.APsi.psiA_st1_maps_ball (2033 / 25000) hz
    have hmw := Work.APsi.psiA_mapsTo_rot_ball Work.APsi.psiA_st1_maps_ball (2033 / 25000) hw
    have h'' := psiA_aux_slit_injective_ball (379 / 625) (by norm_num) (by norm_num)
      _ _ hmz hmw h'
    exact mul_left_cancel₀ (Work.APsi.rot_ne_zero _) h''
  have h' : slit (9 / 10) ((491 / 500 : ℂ) * z) = slit (9 / 10) ((491 / 500 : ℂ) * w) := by
    simpa only [Work.APsi.psiA_st1] using h12
  have hmz := Work.APsi.psiA_mapsTo_ball_const_mul _
    (Work.APsi.psiA_norm_div_le_one 491 500 (by norm_num) (by norm_num)) hz
  have hmw := Work.APsi.psiA_mapsTo_ball_const_mul _
    (Work.APsi.psiA_norm_div_le_one 491 500 (by norm_num) (by norm_num)) hw
  have h'' := psiA_aux_slit_injective_ball (9 / 10) (by norm_num) (by norm_num) _ _ hmz hmw h'
  exact mul_left_cancel₀ (by norm_num : (491 / 500 : ℂ) ≠ 0) h''

end

end Work.APull
