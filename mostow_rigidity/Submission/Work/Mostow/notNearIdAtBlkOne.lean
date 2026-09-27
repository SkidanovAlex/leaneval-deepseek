import Mathlib
import Submission.Work.Mostow.ftbPivotAux
import Submission.Work.Mostow.nearId_rotN_bound

/-!
# `Work.Mostow.notNearIdAtBlkOne`

The block isometry `blk j 1 1 R` with `j` arbitrary and `R : E 1 ≃ₗᵢ[ℝ] E 1` a *fixed-point-free*
linear isometry (i.e. `R = -1`, the antipodal map of the one-dimensional normal fibre) is
**nowhere** `η`-near the identity for `η ≤ 1`.

Reason.  In the raw chart coordinates `E (j + 1) = E j × E 1` the block map fixes the tangential
coordinate and negates the normal one, so the displacement of `u` is governed by

  `cosh (hdist u (blk j 1 1 R • u)) = 1 + ‖R W - W‖² / 2`,  `W = nrmC j 1 u`,

(`Work.Mostow.nrb_cosh_hdist_blk_mk`), and `‖R W - W‖ = 2 ‖W‖`.  Given the centre `z` with normal
coordinate `W₀`, move the normal coordinate by `sinh (1/2)` *away from the origin*: the new point
`u` is still within hyperbolic distance `1` of `z` (`Work.Mostow.nrb_hdist_spread`), while its
normal coordinate has norm `≥ sinh (1/2)`.  Hence

  `cosh (hdist u (blk j 1 1 R • u)) ≥ 1 + (2 sinh (1/2))²/2 = cosh 1`,

so the displacement of `u` is `≥ 1 ≥ η`, contradicting `NearIdAt`.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

noncomputable section

/-- In the one-dimensional normal fibre one can always shift a vector by `sinh (1/2)` (measured in
the norm) so that the shifted vector has norm at least `sinh (1/2)`: shift away from the origin
when the vector is nonzero, and in an arbitrary direction when it vanishes. -/
lemma nrb_one_shift (W : E 1) :
    ∃ W' : E 1, ‖W - W'‖ ≤ 2 * Real.sinh (1 / 2) ∧ Real.sinh (1 / 2) ≤ ‖W'‖ := by
  have hs : 0 ≤ Real.sinh (1 / 2) := Real.sinh_nonneg_iff.mpr (by norm_num)
  by_cases hW : W = 0
  · subst hW
    refine ⟨Real.sinh (1 / 2) • EuclideanSpace.single (0 : Fin 1) (1 : ℝ), ?_, ?_⟩
    · rw [zero_sub, norm_neg, norm_smul, PiLp.norm_single]
      rw [Real.norm_eq_abs, abs_of_nonneg hs]
      norm_num
    · rw [norm_smul, PiLp.norm_single]
      rw [Real.norm_eq_abs, abs_of_nonneg hs]
      norm_num
  · have hWpos : 0 < ‖W‖ := norm_pos_iff.mpr hW
    refine ⟨W + Real.sinh (1 / 2) • (‖W‖⁻¹ • W), ?_, ?_⟩
    · have h1 : W - (W + Real.sinh (1 / 2) • (‖W‖⁻¹ • W))
          = -(Real.sinh (1 / 2) • (‖W‖⁻¹ • W)) := by abel
      rw [h1, norm_neg, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg hs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg W)),
        inv_mul_cancel₀ hWpos.ne']
      linarith
    · have h2 : W + Real.sinh (1 / 2) • (‖W‖⁻¹ • W)
          = (1 + Real.sinh (1 / 2) * ‖W‖⁻¹) • W := by
        rw [add_smul, one_smul, smul_smul]
      rw [h2, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 + Real.sinh (1 / 2) * ‖W‖⁻¹)]
      have h3 : (1 + Real.sinh (1 / 2) * ‖W‖⁻¹) * ‖W‖ = ‖W‖ + Real.sinh (1 / 2) := by
        field_simp
      rw [h3]; linarith

theorem notNearIdAtBlkOne (j : ℕ) (hAj : Submission.Mostow.POActionProp j)
    (hIj : Submission.Mostow.HypIsometryProp j) (hAj1 : Submission.Mostow.POActionProp (j + 1))
    (hIj1 : Submission.Mostow.HypIsometryProp (j + 1))
    (R : Submission.Mostow.E 1 ≃ₗᵢ[ℝ] Submission.Mostow.E 1)
    (hRfree : ∀ w : Submission.Mostow.E 1, R w = w → w = 0)
    (z : Submission.Mostow.E (j + 1)) (η : ℝ) (hη1 : η ≤ 1) :
    ¬ Submission.Mostow.NearIdAt (Submission.Mostow.blk j 1 1 R) z η := by
  intro hni
  -- a fixed-point-free isometry of the one-dimensional normal fibre is the antipodal map
  have hRneg : ∀ w : E 1, R w = -w := eq_neg_of_fixedFree R hRfree
  obtain ⟨W', hWd, hWn⟩ := nrb_one_shift (nrmC j 1 z)
  -- the shifted point `u`, still inside the unit ball about `z`
  have hzu : hdist z (nrb_mk j 1 (tanC j 1 z) W') ≤ 1 := by
    have h := nrb_hdist_spread j 1 (tanC j 1 z) (nrmC j 1 z) W' hWd
    rwa [nrb_mk_tanC_nrmC j 1 z] at h
  have hdisp := hni (nrb_mk j 1 (tanC j 1 z) W') hzu
  have hcosh := nrb_cosh_hdist_blk_mk j 1 hAj hIj hAj1 hIj1 R (tanC j 1 z) W'
  -- the displacement of `u` is at least `1`
  have hDge : 1 ≤ hdist (nrb_mk j 1 (tanC j 1 z) W')
      (blk j 1 1 R • nrb_mk j 1 (tanC j 1 z) W') := by
    have hnn : 0 ≤ hdist (nrb_mk j 1 (tanC j 1 z) W')
        (blk j 1 1 R • nrb_mk j 1 (tanC j 1 z) W') := nib_hdist_nonneg _ _
    have hc1 : Real.cosh 1 ≤ Real.cosh (hdist (nrb_mk j 1 (tanC j 1 z) W')
        (blk j 1 1 R • nrb_mk j 1 (tanC j 1 z) W')) := by
      rw [hcosh]
      have hc : Real.cosh 1 = 1 + 2 * Real.sinh (1 / 2) ^ 2 := by
        have h2 := Real.cosh_two_mul (1 / 2)
        rw [show (2 : ℝ) * (1 / 2) = 1 by norm_num] at h2
        rw [h2, Real.cosh_sq]
        ring
      rw [hc]
      have hRn : ‖R W' - W'‖ = 2 * ‖W'‖ := by
        rw [hRneg W']
        have h3 : -W' - W' = (-2 : ℝ) • W' := by module
        rw [h3, norm_smul]; simp
      rw [hRn]
      nlinarith [hWn, Real.sinh_nonneg_iff.mpr (by norm_num : (0 : ℝ) ≤ 1 / 2), norm_nonneg W']
    have h := Real.cosh_le_cosh.mp hc1
    rwa [abs_one, abs_of_nonneg hnn] at h
  linarith

end

end Work.Mostow
