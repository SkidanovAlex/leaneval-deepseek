import Mathlib
import Submission.Work.Drive.EpsForm.SweepGenericity
import Submission.Work.Drive.EpsForm.tiltedSweepGenericity_holds

namespace Work.Drive.EpsForm

open LeanEval.KnotTheory.PardonDistortion

/-- Given a unit vector `e` and a nonzero vector `n` whose direction makes an angle with `e` of
cosine at most `ε/2` (`|⟪n,e⟫| ≤ ‖n‖·ε/2`), there is a unit vector `v` orthogonal to `n` within
distance `ε` of `e`.

This is the quantitative "tilt direction near a normal" input: the projection of `e` to the plane
`n^⊥`, normalised, is the closest unit normal to `n`, and `|⟪n,e⟫| ≤ ‖n‖·ε/2` says precisely that
`e` is close enough to that plane.  For `ε ≥ 2` the angle hypothesis is irrelevant and *any* unit
normal to `n ≠ 0` is within `2 ≤ ε` of `e`. -/
theorem tiltVector_of_small_angle {e n : LeanEval.KnotTheory.PardonDistortion.R3} (he : ‖e‖ = 1)
    (hn : 0 < ‖n‖) (ε : ℝ) (hε : 0 < ε) (hc : |inner ℝ n e| ≤ ‖n‖ * ε / 2) :
    ∃ v : LeanEval.KnotTheory.PardonDistortion.R3,
      ‖v‖ = 1 ∧ inner ℝ n v = 0 ∧ ‖v - e‖ ≤ ε := by
  by_cases h2 : ε < 2
  · -- ## Small `ε`: the orthogonal projection of `e` away from `span n`, normalised.
    set w : R3 := e - (inner ℝ n e / ‖n‖ ^ 2) • n with hw
    have hN2 : (0 : ℝ) < ‖n‖ ^ 2 := by positivity
    have hN2ne : ‖n‖ ^ 2 ≠ 0 := ne_of_gt hN2
    have hwn : inner ℝ n w = 0 := by
      rw [hw, inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq n,
        div_mul_cancel₀ _ hN2ne, sub_self]
    have hwwn : inner ℝ w n = 0 := by rw [real_inner_comm]; exact hwn
    have hwe : inner ℝ w e = 1 - (inner ℝ n e) ^ 2 / ‖n‖ ^ 2 := by
      rw [hw, inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq e, he]
      field_simp
    have hwwe : inner ℝ w w = inner ℝ w e := by
      nth_rewrite 2 [hw]
      rw [inner_sub_right, inner_smul_right, hwwn, mul_zero, sub_zero]
    have hwself : inner ℝ w w = 1 - (inner ℝ n e) ^ 2 / ‖n‖ ^ 2 := by rw [hwwe, hwe]
    have hwnorm : ‖w‖ ^ 2 = 1 - (inner ℝ n e) ^ 2 / ‖n‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq w]; exact hwself
    -- the angle bound in squared form
    have ha2 : (inner ℝ n e) ^ 2 ≤ (‖n‖ * ε / 2) ^ 2 := by
      rw [sq_le_sq, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖n‖ * ε / 2)]
      exact_mod_cast hc
    have ht : (inner ℝ n e) ^ 2 / ‖n‖ ^ 2 ≤ ε ^ 2 / 4 := by
      rw [div_le_iff₀ hN2]; nlinarith [ha2]
    have hpos : 0 < 1 - (inner ℝ n e) ^ 2 / ‖n‖ ^ 2 := by nlinarith [ht, h2, hε]
    have hwpos : 0 < ‖w‖ := by
      refine lt_of_le_of_ne (norm_nonneg w) (Ne.symm ?_)
      intro h
      have h2' : (0 : ℝ) < ‖w‖ ^ 2 := by rw [hwnorm]; exact hpos
      rw [h] at h2'; norm_num at h2'
    have hq0 : 0 ≤ (inner ℝ n e) ^ 2 / ‖n‖ ^ 2 :=
      div_nonneg (sq_nonneg (inner ℝ n e)) (by positivity : (0 : ℝ) ≤ ‖n‖ ^ 2)
    have hu2 : ‖w‖ ^ 2 ≤ 1 := by rw [hwnorm]; linarith
    have hu1 : ‖w‖ ≤ 1 := by nlinarith [hu2, norm_nonneg w]
    have htu : 1 - ‖w‖ ≤ (inner ℝ n e) ^ 2 / ‖n‖ ^ 2 := by
      have h1 : 1 - ‖w‖ ^ 2 = (inner ℝ n e) ^ 2 / ‖n‖ ^ 2 := by rw [hwnorm]; ring
      nlinarith [h1, norm_nonneg w, hu1]
    have hv1 : ‖(‖w‖)⁻¹ • w‖ = 1 := by
      rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg w)]
      exact inv_mul_cancel₀ (ne_of_gt hwpos)
    have hv2 : inner ℝ n ((‖w‖)⁻¹ • w) = 0 := by
      rw [inner_smul_right, hwn, mul_zero]
    have hve : inner ℝ ((‖w‖)⁻¹ • w) e = ‖w‖ := by
      rw [real_inner_smul_left, hwe, ← hwnorm, sq, ← mul_assoc,
        inv_mul_cancel₀ (ne_of_gt hwpos), one_mul]
    refine ⟨(‖w‖)⁻¹ • w, hv1, hv2, ?_⟩
    -- `‖v - e‖² = 2 - 2‖w‖ ≤ 2t ≤ ε²` since `1 - ‖w‖ ≤ t = 1 - ‖w‖²`
    have hsq : ‖(‖w‖)⁻¹ • w - e‖ ^ 2 ≤ ε ^ 2 := by
      rw [norm_sub_sq_real, hv1, he, hve]
      nlinarith [htu, ht, hε]
    have hfinal := sq_le_sq.mp hsq
    rwa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (le_of_lt hε)] at hfinal
  · -- ## Large `ε ≥ 2`: any unit normal to `n` is within `2 ≤ ε` of `e`.
    push Not at h2
    have hnne : n ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt hn)
    let S : Submodule ℝ R3 := Submodule.span ℝ ({n} : Set R3)
    have hnS : n ∈ S := Submodule.subset_span (Set.mem_singleton n)
    have hdimS : Module.finrank ℝ S = 1 := by
      have h := finrank_span_singleton (K := ℝ) (V := R3) hnne
      simpa [S] using h
    have hdimE : Module.finrank ℝ R3 = 3 := by
      simp
    have hdimW : Module.finrank ℝ (Sᗮ) = 2 := by
      have h := Submodule.finrank_add_finrank_orthogonal S
      rw [hdimS, hdimE] at h
      omega
    have hWne : Sᗮ ≠ ⊥ := by
      intro hbot
      rw [hbot] at hdimW
      have hz : Module.finrank ℝ (⊥ : Submodule ℝ R3) = 0 :=
        (Submodule.finrank_eq_zero).mpr rfl
      omega
    obtain ⟨w', hw'mem, hw'ne⟩ := (Submodule.ne_bot_iff Sᗮ).mp hWne
    have hmem : (‖w'‖)⁻¹ • w' ∈ Sᗮ := Submodule.smul_mem _ _ hw'mem
    have hnor : ‖(‖w'‖)⁻¹ • w'‖ = 1 := norm_smul_inv_norm hw'ne
    have horth : inner ℝ n ((‖w'‖)⁻¹ • w') = 0 :=
      (Submodule.mem_orthogonal S _).mp hmem n hnS
    refine ⟨(‖w'‖)⁻¹ • w', hnor, horth, ?_⟩
    calc ‖(‖w'‖)⁻¹ • w' - e‖ ≤ ‖(‖w'‖)⁻¹ • w'‖ + ‖e‖ := norm_sub_le _ _
      _ = 2 := by rw [hnor, he]; norm_num
      _ ≤ ε := h2

end Work.Drive.EpsForm
