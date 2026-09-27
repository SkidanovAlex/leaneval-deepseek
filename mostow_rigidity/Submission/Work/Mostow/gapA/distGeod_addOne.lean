import Mathlib
import Submission.Work.Mostow.gapA.defs
import Submission.Work.Mostow.gapA.geodFacts
import Submission.Work.Mostow.gapA.shiftDefs

namespace Work.Mostow.gapA

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

noncomputable section

variable {n : ℕ}

/-- For `w` off the geodesic with endpoints `a ≠ b`, the Minkowski norm of the normal component
`gcN a b w` is `sinh²` of the hyperbolic distance from `w` to that geodesic. -/
lemma gcN_sinh_sq_aux (a b w : E n) (ha : a ∈ Sph n) (hb : b ∈ Sph n) (hab : a ≠ b)
    (hN : gcN a b w ≠ 0) :
    mink (gcN a b w) (gcN a b w) = Real.sinh (distGeod a b w) ^ 2 ∧
    Real.cosh (distGeod a b w) ^ 2 = 1 + mink (gcN a b w) (gcN a b w) ∧
    0 < distGeod a b w ∧ 0 < mink (gcN a b w) (gcN a b w) := by
  have hL : 0 < gcL a b := gcL_pos a b ha hb hab
  have hlevmul : lev a w * lev b w / gcL a b = 1 + mink (gcN a b w) (gcN a b w) := by
    have h := gcN_self_mink a b ha hb hab w
    linarith
  have hcosh : Real.cosh (distGeod a b w) ^ 2 = 1 + mink (gcN a b w) (gcN a b w) := by
    have hC : Real.cosh (distGeod a b w) = Real.sqrt (lev a w * lev b w / gcL a b) := by
      rw [distGeod_eq a b ha hb w]
      exact Real.cosh_arcosh (sqrt_levdiv_ge_one a b ha hb hab w)
    rw [hC, Real.sq_sqrt (div_nonneg
      (mul_nonneg (le_of_lt (lev_pos a ha w)) (le_of_lt (lev_pos b hb w))) (le_of_lt hL)), hlevmul]
  have hqpos : 0 < mink (gcN a b w) (gcN a b w) := by
    rcases lt_or_eq_of_le (gcN_self_nonneg a b ha hb hab w) with h | h
    · exact h
    · exact absurd (gcN_eq_zero_of_self a b ha hb hab w h.symm) hN
  have hddpos : 0 < distGeod a b w := by
    rcases lt_or_eq_of_le (distGeod_nonneg a b ha hb hab w) with h | h
    · exact h
    · exfalso
      exact hN ((gcN_eq_zero_iff a b ha hb hab w).mpr
        ((distGeod_eq_zero_iff a b ha hb hab w).mp h.symm))
  exact ⟨by rw [Real.sinh_sq, hcosh]; ring, hcosh, hddpos, hqpos⟩

/-- Scaling `hlift w` as in `shiftVec` gives a point of the hyperboloid at distance `1` from `w`. -/
lemma shiftVec_mink_aux (w : E n) (N : Fin n ⊕ Fin 1 → ℝ) (d : ℝ)
    (hq : 0 < mink N N) (hUN : mink (hlift w) N = mink N N)
    (hcosh : Real.cosh d ^ 2 = 1 + mink N N) :
    mink (shiftVec w N d) (shiftVec w N d) = -1 ∧
    mink (hlift w) (shiftVec w N d) = -Real.cosh 1 := by
  set X : Fin n ⊕ Fin 1 → ℝ := hlift w - N with hX
  have hUU : mink (hlift w) (hlift w) = -1 := by
    rw [mink_hlift_hlift, real_inner_self_eq_norm_sq]
    nlinarith [tpart_sq w]
  have hXX : mink X X = -(1 + mink N N) := by
    rw [hX, mink_sub_left', mink_sub_right', mink_sub_right', minkSeg_comm N (hlift w),
      hUU, hUN]
    ring
  have hXN : mink X N = 0 := by
    rw [hX, mink_sub_left', hUN]
    ring
  have hNX : mink N X = 0 := by rw [minkSeg_comm]; exact hXN
  have hUX : mink (hlift w) X = -(1 + mink N N) := by
    rw [hX, mink_sub_right', hUU, hUN]
    ring
  have hYeq : shiftVec w N d
      = (Real.cosh (d + 1) * (Real.cosh d)⁻¹) • X
        + (Real.sinh (d + 1) * (Real.sinh d)⁻¹) • N := by
    unfold shiftVec
    rw [← hX, smul_smul, smul_smul]
  have hYY : mink (shiftVec w N d) (shiftVec w N d)
      = (Real.cosh (d + 1) * (Real.cosh d)⁻¹) ^ 2 * mink X X
        + (Real.sinh (d + 1) * (Real.sinh d)⁻¹) ^ 2 * mink N N := by
    rw [hYeq, mink_expand2, hXX, hXN, hNX]
    ring
  have hUY : mink (hlift w) (shiftVec w N d)
      = (Real.cosh (d + 1) * (Real.cosh d)⁻¹) * mink (hlift w) X
        + (Real.sinh (d + 1) * (Real.sinh d)⁻¹) * mink (hlift w) N := by
    rw [hYeq, minkSeg_add_right, mink_smul_right'', mink_smul_right'']
  have hsinh2 : Real.sinh d ^ 2 = mink N N := by
    rw [Real.sinh_sq, hcosh]
    ring
  have hsne : Real.sinh d ≠ 0 := by
    intro h
    rw [h] at hsinh2
    simp at hsinh2
    linarith [hq, hsinh2]
  constructor
  · rw [hYY, hXX, ← hcosh, ← hsinh2]
    have h1 : (Real.cosh (d + 1) * (Real.cosh d)⁻¹) ^ 2 * Real.cosh d ^ 2
        = Real.cosh (d + 1) ^ 2 := by
      field_simp
    have h2 : (Real.sinh (d + 1) * (Real.sinh d)⁻¹) ^ 2 * Real.sinh d ^ 2
        = Real.sinh (d + 1) ^ 2 := by
      field_simp
    linarith [h1, h2, Real.cosh_sq_sub_sinh_sq (d + 1)]
  · rw [hUY, hUX, hUN, ← hcosh, ← hsinh2]
    have h3 : (Real.cosh (d + 1) * (Real.cosh d)⁻¹) * Real.cosh d ^ 2
        = Real.cosh (d + 1) * Real.cosh d := by
      field_simp
    have h4 : (Real.sinh (d + 1) * (Real.sinh d)⁻¹) * Real.sinh d ^ 2
        = Real.sinh (d + 1) * Real.sinh d := by
      field_simp
    have h5 : Real.cosh (d + 1) * Real.cosh d - Real.sinh (d + 1) * Real.sinh d
        = Real.cosh 1 := by
      rw [← Real.cosh_sub (d + 1) d]
      norm_num
    linarith [h3, h4, h5]

/-- `shiftPt` realises the lev-scaling: for every `ξ` whose null vector is orthogonal to `N`,
the level `lev ξ` is multiplied by `cosh (d+1)/cosh d`. -/
lemma shiftPt_lev_aux (ξ : E n) (hξ : ξ ∈ Sph n) (w : E n)
    (N : Fin n ⊕ Fin 1 → ℝ) (d : ℝ)
    (hNξ : mink (nvec ξ) N = 0)
    (hq : 0 < mink N N) (hUN : mink (hlift w) N = mink N N)
    (hcosh : Real.cosh d ^ 2 = 1 + mink N N) :
    lev ξ (shiftPt w N d) = (Real.cosh d)⁻¹ * Real.cosh (d + 1) * lev ξ w := by
  obtain ⟨hYY, hUY⟩ := shiftVec_mink_aux w N d hq hUN hcosh
  have htime : 0 < shiftVec w N d (Sum.inr 0) :=
    upper_of_mink_neg w (shiftVec w N d) hYY
      (by rw [hUY]; exact neg_lt_zero.mpr (Real.cosh_pos 1))
  have hlifteq : hlift (shiftPt w N d) = shiftVec w N d :=
    (eq_hlift_of_upper (shiftVec w N d) (by rw [← mink_eq_mform]; exact hYY) htime).symm
  have hXeq : shiftVec w N d = (Real.cosh (d + 1) * (Real.cosh d)⁻¹) • (hlift w - N)
      + (Real.sinh (d + 1) * (Real.sinh d)⁻¹) • N := by
    unfold shiftVec
    rw [smul_smul, smul_smul]
  rw [lev_eq_neg_mink, hlifteq, hXeq, minkSeg_add_right, mink_smul_right'', mink_smul_right'']
  rw [show mink (nvec ξ) (hlift w - N) = -lev ξ w from by
    rw [mink_sub_right', mink_nvec_hlift n ξ w, hNξ]
    ring]
  rw [hNξ]
  ring

theorem distGeod_addOne (n : ℕ) (hn : 2 ≤ n) (hA : Submission.Mostow.POActionProp n)
    (hI : Submission.Mostow.HypIsometryProp n) (a b : Submission.Mostow.E n)
    (ha : a ∈ Submission.Mostow.Sph n) (hb : b ∈ Submission.Mostow.Sph n) (hab : a ≠ b)
    (w : Submission.Mostow.E n) :
    ∃ u : Submission.Mostow.E n, Submission.Mostow.hdist w u ≤ 1 ∧
      Work.Mostow.distGeod a b w + 1 ≤ Work.Mostow.distGeod a b u := by
  by_cases hN : gcN a b w = 0
  · obtain ⟨u, hu1, hu2⟩ := exists_near_distGeod_ge_one a b hn ha hb hab w
    have h0 : distGeod a b w = 0 :=
      (distGeod_eq_zero_iff a b ha hb hab w).mpr ((gcN_eq_zero_iff a b ha hb hab w).mp hN)
    exact ⟨u, hu1, by rw [h0]; linarith⟩
  · obtain ⟨-, hch, hddpos, hqpos⟩ := gcN_sinh_sq_aux a b w ha hb hab hN
    have hUN : mink (hlift w) (gcN a b w) = mink (gcN a b w) (gcN a b w) :=
      mink_hlift_gcN a b ha hb hab w
    obtain ⟨hYself, hYw⟩ := shiftVec_mink_aux w (gcN a b w) (distGeod a b w) hqpos hUN hch
    have hleva := shiftPt_lev_aux a ha w (gcN a b w) (distGeod a b w)
      (mink_nvec_a_gcN a b ha hb hab w) hqpos hUN hch
    have hlevb := shiftPt_lev_aux b hb w (gcN a b w) (distGeod a b w)
      (mink_nvec_b_gcN a b ha hb hab w) hqpos hUN hch
    have htime : 0 < shiftVec w (gcN a b w) (distGeod a b w) (Sum.inr 0) :=
      upper_of_mink_neg w (shiftVec w (gcN a b w) (distGeod a b w)) hYself
        (by rw [hYw]; exact neg_lt_zero.mpr (Real.cosh_pos 1))
    have hlifteq : hlift (shiftPt w (gcN a b w) (distGeod a b w))
        = shiftVec w (gcN a b w) (distGeod a b w) :=
      (eq_hlift_of_upper (shiftVec w (gcN a b w) (distGeod a b w))
        (by rw [← mink_eq_mform]; exact hYself) htime).symm
    refine ⟨shiftPt w (gcN a b w) (distGeod a b w), ?_, ?_⟩
    · rw [hdist_eq_arcosh_mink, hlifteq, hYw, neg_neg,
        Real.arcosh_cosh (by norm_num : (0 : ℝ) ≤ 1)]
    · have hlvwb : lev a w * lev b w / gcL a b = Real.cosh (distGeod a b w) ^ 2 := by
        have h := gcN_self_mink a b ha hb hab w
        linarith [hch]
      have hfac : lev a (shiftPt w (gcN a b w) (distGeod a b w))
            * lev b (shiftPt w (gcN a b w) (distGeod a b w)) / gcL a b
          = ((Real.cosh (distGeod a b w))⁻¹ * Real.cosh (distGeod a b w + 1)) ^ 2
            * (lev a w * lev b w / gcL a b) := by
        rw [hleva, hlevb]
        ring
      have hval : Real.sqrt (lev a (shiftPt w (gcN a b w) (distGeod a b w))
            * lev b (shiftPt w (gcN a b w) (distGeod a b w)) / gcL a b)
          = Real.cosh (distGeod a b w + 1) := by
        rw [hfac, hlvwb]
        have hsq : ((Real.cosh (distGeod a b w))⁻¹ * Real.cosh (distGeod a b w + 1)) ^ 2
            * Real.cosh (distGeod a b w) ^ 2 = Real.cosh (distGeod a b w + 1) ^ 2 := by
          rw [mul_pow, inv_pow]
          field_simp
        rw [hsq, Real.sqrt_sq (le_of_lt (Real.cosh_pos (distGeod a b w + 1)))]
      rw [distGeod_eq a b ha hb (shiftPt w (gcN a b w) (distGeod a b w)), hval,
        Real.arcosh_cosh (by linarith [hddpos] : (0 : ℝ) ≤ distGeod a b w + 1)]

end

end Work.Mostow.gapA
