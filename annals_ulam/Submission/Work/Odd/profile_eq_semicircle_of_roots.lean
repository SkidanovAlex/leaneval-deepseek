import Mathlib

namespace Work.Odd

lemma profile_eq_semicircle_of_roots {f h x y : ℝ → ℝ} {a : ℝ} (ha : 0 < a)
    (hx_eq : ∀ s : ℝ, a ≤ s → x s = 1 / Real.sqrt (1 + s ^ 2))
    (hy_eq : ∀ s : ℝ, a ≤ s → y s = 1 / Real.sqrt (1 + s ^ 2))
    (hh_zero : ∀ s : ℝ, a ≤ s → h s = 0)
    (hroot_l : ∀ s : ℝ, 0 < s → f (-x s) = -(s * (-x s) + h s))
    (hroot_r : ∀ s : ℝ, 0 < s → f (y s) = s * y s + h s)
    (hf_cont : ContinuousOn f (Set.Icc (-1 : ℝ) 1)) :
    ∀ t ∈ Set.Icc (-(1 / Real.sqrt (1 + a ^ 2))) (1 / Real.sqrt (1 + a ^ 2)),
      f t = Real.sqrt (1 - t ^ 2) := by
  set c : ℝ := 1 / Real.sqrt (1 + a ^ 2) with hc_def
  have ha2 : 0 < 1 + a ^ 2 := by positivity
  have hspos : 0 < Real.sqrt (1 + a ^ 2) := Real.sqrt_pos.mpr ha2
  have hsq : (Real.sqrt (1 + a ^ 2)) ^ 2 = 1 + a ^ 2 := Real.sq_sqrt (le_of_lt ha2)
  have hcpos : 0 < c := by rw [hc_def]; exact one_div_pos.mpr hspos
  have hcsq : c ^ 2 = 1 / (1 + a ^ 2) := by rw [hc_def, div_pow, one_pow, hsq]
  have hsqrtone : 1 < Real.sqrt (1 + a ^ 2) := by
    have h := Real.sqrt_lt_sqrt (show (0 : ℝ) ≤ 1 by norm_num) (show (1 : ℝ) < 1 + a ^ 2 by nlinarith [ha])
    simpa using h
  have hclt : c < 1 := by
    rw [hc_def, div_lt_one hspos]
    exact hsqrtone
  -- The core computation: at every point of `(0, c]` the two root equations pin `f`.
  have key : ∀ t : ℝ, 0 < t → t ≤ c →
      f t = Real.sqrt (1 - t ^ 2) ∧ f (-t) = Real.sqrt (1 - t ^ 2) := by
    intro t ht0 htc
    have ht1 : t ≤ 1 := le_of_lt (lt_of_le_of_lt htc hclt)
    have htsq : 0 < t ^ 2 := pow_pos ht0 2
    have hle1 : 1 ≤ 1 / t ^ 2 := by
      rw [le_div_iff₀ htsq, one_mul]
      nlinarith
    let s : ℝ := Real.sqrt (1 / t ^ 2 - 1)
    have hs_def : s = Real.sqrt (1 / t ^ 2 - 1) := rfl
    have hsub_nonneg : 0 ≤ 1 / t ^ 2 - 1 := by linarith
    have hs_sq : s ^ 2 = 1 / t ^ 2 - 1 := Real.sq_sqrt hsub_nonneg
    have hs_nonneg : 0 ≤ s := Real.sqrt_nonneg _
    have h1s : 1 + s ^ 2 = 1 / t ^ 2 := by rw [hs_sq]; ring
    have hsqrt_s : Real.sqrt (1 + s ^ 2) = 1 / t := by
      rw [h1s]
      have he : (1 : ℝ) / t ^ 2 = (1 / t) ^ 2 := by ring
      rw [he, Real.sqrt_sq (by positivity)]
    have htsq_le : t ^ 2 ≤ c ^ 2 := pow_le_pow_left₀ (le_of_lt ht0) htc 2
    have h1t2 : (1 + a ^ 2) ≤ 1 / t ^ 2 := by
      have h : 1 / c ^ 2 ≤ 1 / t ^ 2 := one_div_le_one_div_of_le htsq htsq_le
      have hc2 : 1 / c ^ 2 = 1 + a ^ 2 := by rw [hcsq, one_div_one_div]
      rwa [hc2] at h
    have hs_ge : a ≤ s := by
      rw [hs_def, Real.le_sqrt (le_of_lt ha) hsub_nonneg]
      linarith
    have hs_pos : 0 < s := lt_of_lt_of_le ha hs_ge
    have hxs : x s = t := by
      rw [hx_eq s hs_ge, hsqrt_s, one_div_one_div]
    have hys : y s = t := by
      rw [hy_eq s hs_ge, hsqrt_s, one_div_one_div]
    have hhs : h s = 0 := hh_zero s hs_ge
    have hfr : f t = s * t := by
      have h := hroot_r s hs_pos
      rw [hys, hhs, add_zero] at h
      exact h
    have hfl : f (-t) = s * t := by
      have h := hroot_l s hs_pos
      rw [hxs, hhs, add_zero] at h
      simpa using h
    have hst : s * t = Real.sqrt (1 - t ^ 2) := by
      have hsqt : (s * t) ^ 2 = 1 - t ^ 2 := by
        rw [mul_pow, hs_sq, sub_mul, one_div_mul_cancel (ne_of_gt htsq), one_mul]
      have hnn : 0 ≤ s * t := mul_nonneg hs_nonneg (le_of_lt ht0)
      rw [← Real.sqrt_sq hnn, hsqt]
    exact ⟨by rw [hfr, hst], by rw [hfl, hst]⟩
  -- Closedness argument to recover the limit points `0` and `±c`.
  have hcont : ContinuousOn (fun t : ℝ => f t - Real.sqrt (1 - t ^ 2)) (Set.Icc (-1 : ℝ) 1) :=
    hf_cont.sub
      ((Real.continuous_sqrt.comp (continuous_const.sub (continuous_id.pow 2))).continuousOn)
  have hclosed : IsClosed
      (Set.Icc (-1 : ℝ) 1 ∩ (fun t : ℝ => f t - Real.sqrt (1 - t ^ 2)) ⁻¹' {0}) :=
    hcont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
  have hsub : Set.Ioo (-c) 0 ∪ Set.Ioo 0 c ⊆
      Set.Icc (-1 : ℝ) 1 ∩ (fun t : ℝ => f t - Real.sqrt (1 - t ^ 2)) ⁻¹' {0} := by
    intro t ht
    rcases ht with ht | ht
    · obtain ⟨ht1, ht2⟩ := ht
      obtain ⟨_, h2⟩ := key (-t) (by linarith) (by linarith)
      have h3 : 1 - (-t) ^ 2 = 1 - t ^ 2 := by ring
      rw [h3] at h2
      simp only [neg_neg] at h2
      refine ⟨⟨by linarith, by linarith⟩, ?_⟩
      show f t - Real.sqrt (1 - t ^ 2) = 0
      rw [h2, sub_self]
    · obtain ⟨ht1, ht2⟩ := ht
      obtain ⟨h1, _⟩ := key t ht1 (le_of_lt ht2)
      refine ⟨⟨by linarith, by linarith⟩, ?_⟩
      show f t - Real.sqrt (1 - t ^ 2) = 0
      rw [h1, sub_self]
  have hIcc : Set.Icc (-c) c ⊆
      Set.Icc (-1 : ℝ) 1 ∩ (fun t : ℝ => f t - Real.sqrt (1 - t ^ 2)) ⁻¹' {0} := by
    have hcl : closure (Set.Ioo (-c) 0 ∪ Set.Ioo 0 c) = Set.Icc (-c) c := by
      rw [closure_union, closure_Ioo (by linarith : -c ≠ (0 : ℝ)),
        closure_Ioo (by linarith : (0 : ℝ) ≠ c)]
      ext t
      simp only [Set.mem_union, Set.mem_Icc]
      constructor
      · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> exact ⟨by linarith, by linarith⟩
      · rintro ⟨h1, h2⟩
        rcases le_total t 0 with h | h
        · exact Or.inl ⟨h1, h⟩
        · exact Or.inr ⟨h, h2⟩
    rw [← hcl]
    exact hclosed.closure_subset_iff.mpr hsub
  intro t ht
  have ht' := hIcc ht
  simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_preimage, Set.mem_singleton_iff] at ht'
  exact sub_eq_zero.mp ht'.2

end Work.Odd
