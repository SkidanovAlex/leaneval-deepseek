import Submission.Work.WilG1.OneDim.thin_osc

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilG1.OneDim

open WilkiesDesign

/-! ## 8. Combining the trichotomies -/

theorem cover_from_trichotomy {g : ℝ → ℝ} {x : ℝ} (hbad : ¬ DifferentiableAt ℝ g x)
    (hR : (∀ M : ℚ, 0 < M → x ∈ evRgt g (M:ℝ)) ∨
          (∀ M : ℚ, 0 < M → x ∈ evRlt g (-(M:ℝ))) ∨
          (∃ L : ℝ, ∀ r s : ℚ, (r:ℝ) < L → L < (s:ℝ) →
            x ∈ evRge g (r:ℝ) ∧ x ∈ evRle g (s:ℝ)))
    (hL : (∀ M : ℚ, 0 < M → x ∈ evLgt g (M:ℝ)) ∨
          (∀ M : ℚ, 0 < M → x ∈ evLlt g (-(M:ℝ))) ∨
          (∃ L : ℝ, ∀ r s : ℚ, (r:ℝ) < L → L < (s:ℝ) →
            x ∈ evLge g (r:ℝ) ∧ x ∈ evLle g (s:ℝ))) :
    (∃ q : ℚ, x ∈ cornerMax g (q:ℝ) ∨ x ∈ cornerMin g (q:ℝ)) ∨
      x ∈ infDeriv g 1 ∨ x ∈ infDeriv g (-1) := by
  rcases hR with hR1 | hR2 | ⟨LR, hRL⟩
  · rcases hL with hL1 | hL2 | ⟨LL, hLL⟩
    · exact Or.inr (Or.inl (infDeriv_one_of hR1 hL1))
    · refine Or.inl ⟨0, Or.inr ?_⟩
      rw [cornerMin_eq]
      refine ⟨?_, ?_⟩
      · obtain ⟨δ, hδ, hδ'⟩ := hR1 1 (by norm_num)
        refine ⟨δ, hδ, fun y hy1 hy2 => ?_⟩
        have h := hδ' y hy1 hy2
        have h1 : y - x < g y - g x := by simpa using h
        have hyx : (0:ℝ) < y - x := by linarith
        have h2 : 0 < g y - g x := by linarith
        simpa using h2
      · obtain ⟨δ, hδ, hδ'⟩ := hL2 1 (by norm_num)
        refine ⟨δ, hδ, fun y hy1 hy2 => ?_⟩
        have h := hδ' y hy1 hy2
        have h1 : -(y - x) < g y - g x := by simpa using h
        have hyx : y - x < 0 := by linarith
        have h2 : 0 < g y - g x := by linarith
        simpa using h2
    · obtain ⟨q, hq⟩ := exists_rat_gt (max LL 0)
      have hqL : LL < (q:ℝ) := lt_of_le_of_lt (le_max_left _ _) hq
      have hq0 : (0:ℚ) < q := by
        have hq0' : (0:ℝ) < (q:ℝ) := lt_of_le_of_lt (le_max_right _ _) hq
        exact_mod_cast hq0'
      obtain ⟨s, hs1, hs2⟩ := exists_rat_btwn hqL
      refine Or.inl ⟨q, Or.inr ?_⟩
      rw [cornerMin_eq]
      exact ⟨hR1 q hq0, evLle_subset_evLlt hs2 (evLle_of_left_limit hLL hs1)⟩
  · rcases hL with hL1 | hL2 | ⟨LL, hLL⟩
    · refine Or.inl ⟨0, Or.inl ?_⟩
      rw [cornerMax_eq]
      refine ⟨?_, ?_⟩
      · obtain ⟨δ, hδ, hδ'⟩ := hR2 1 (by norm_num)
        refine ⟨δ, hδ, fun y hy1 hy2 => ?_⟩
        have h := hδ' y hy1 hy2
        have h1 : g y - g x < -(y - x) := by simpa using h
        have hyx : (0:ℝ) < y - x := by linarith
        have h2 : g y - g x < 0 := by linarith
        simpa using h2
      · obtain ⟨δ, hδ, hδ'⟩ := hL1 1 (by norm_num)
        refine ⟨δ, hδ, fun y hy1 hy2 => ?_⟩
        have h := hδ' y hy1 hy2
        have h1 : g y - g x < y - x := by simpa using h
        have hyx : y - x < 0 := by linarith
        have h2 : g y - g x < 0 := by linarith
        simpa using h2
    · exact Or.inr (Or.inr (infDeriv_neg_one_of hR2 hL2))
    · obtain ⟨q, hq⟩ := exists_rat_lt (min LL 0)
      have hqL : (q:ℝ) < LL := lt_of_lt_of_le hq (min_le_left _ _)
      obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn hqL
      obtain ⟨M, hM⟩ := exists_rat_gt (max (-(q:ℝ)) 0)
      have hM0 : (0:ℚ) < M := by
        have hM0' : (0:ℝ) < (M:ℝ) := lt_of_le_of_lt (le_max_right _ _) hM
        exact_mod_cast hM0'
      have hMq : -((M:ℚ):ℝ) ≤ (q:ℝ) := by
        have h : -(q:ℝ) < (M:ℝ) := lt_of_le_of_lt (le_max_left _ _) hM
        linarith
      refine Or.inl ⟨q, Or.inl ?_⟩
      rw [cornerMax_eq]
      exact ⟨evRlt_mono (g := g) hMq (hR2 M hM0),
             evLge_subset_evLgt (g := g) hr1 (evLge_of_left_limit hLL hr2)⟩
  · rcases hL with hL1 | hL2 | ⟨LL, hLL⟩
    · obtain ⟨q, hq⟩ := exists_rat_gt (max LR 0)
      have hqL : LR < (q:ℝ) := lt_of_le_of_lt (le_max_left _ _) hq
      have hq0 : (0:ℚ) < q := by
        have hq0' : (0:ℝ) < (q:ℝ) := lt_of_le_of_lt (le_max_right _ _) hq
        exact_mod_cast hq0'
      obtain ⟨s, hs1, hs2⟩ := exists_rat_btwn hqL
      refine Or.inl ⟨q, Or.inl ?_⟩
      rw [cornerMax_eq]
      exact ⟨evRle_subset_evRlt hs2 (evRle_of_right_limit hRL hs1), hL1 q hq0⟩
    · obtain ⟨q, hq⟩ := exists_rat_lt LR
      obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn hq
      obtain ⟨M, hM⟩ := exists_rat_gt (max (-(q:ℝ)) 0)
      have hM0 : (0:ℚ) < M := by
        have hM0' : (0:ℝ) < (M:ℝ) := lt_of_le_of_lt (le_max_right _ _) hM
        exact_mod_cast hM0'
      have hMq : -((M:ℚ):ℝ) ≤ (q:ℝ) := by
        have h : -(q:ℝ) < (M:ℝ) := lt_of_le_of_lt (le_max_left _ _) hM
        linarith
      refine Or.inl ⟨q, Or.inr ?_⟩
      rw [cornerMin_eq]
      exact ⟨evRge_subset_evRgt (g := g) hr1 (evRge_of_right_limit hRL hr2),
             evLlt_mono (g := g) hMq (hL2 M hM0)⟩
    · rcases lt_trichotomy LR LL with hlt | heq | hgt
      · obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hlt
        obtain ⟨s, hs1, hs2⟩ := exists_rat_btwn hq1
        obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn hq2
        refine Or.inl ⟨q, Or.inl ?_⟩
        rw [cornerMax_eq]
        exact ⟨evRle_subset_evRlt hs2 (evRle_of_right_limit hRL hs1),
               evLge_subset_evLgt hr1 (evLge_of_left_limit hLL hr2)⟩
      · exact absurd (differentiableAt_of_same_limit hRL (heq.symm ▸ hLL)) hbad
      · obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hgt
        obtain ⟨s, hs1, hs2⟩ := exists_rat_btwn hq2
        obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn hq1
        refine Or.inl ⟨q, Or.inr ?_⟩
        rw [cornerMin_eq]
        exact ⟨evRge_subset_evRgt hs1 (evRge_of_right_limit hRL hs2),
               evLle_subset_evLlt hr2 (evLle_of_left_limit hLL hr1)⟩

/-- **Cover.**  A point at which `g` is not differentiable is either an oscillation point, or a
corner point, or a point of infinite two-sided derivative. -/
theorem bad_covered_cont {g : ℝ → ℝ} {x : ℝ} (hbad : ¬ DifferentiableAt ℝ g x) :
    (∃ q : ℚ, x ∈ oscR g (q:ℝ) ∨ x ∈ oscL g (q:ℝ)) ∨
      (∃ q : ℚ, x ∈ cornerMax g (q:ℝ) ∨ x ∈ cornerMin g (q:ℝ)) ∨
      x ∈ infDeriv g 1 ∨ x ∈ infDeriv g (-1) := by
  by_cases hRgood : ∀ r : ℚ, x ∈ evRle g (r:ℝ) ∨ x ∈ evRge g (r:ℝ)
  · by_cases hLgood : ∀ r : ℚ, x ∈ evLle g (r:ℝ) ∨ x ∈ evLge g (r:ℝ)
    · rcases cover_from_trichotomy hbad (right_trichotomy hRgood) (left_trichotomy hLgood) with
        ⟨q, hq⟩ | h1 | h2
      · exact Or.inr (Or.inl ⟨q, hq⟩)
      · exact Or.inr (Or.inr (Or.inl h1))
      · exact Or.inr (Or.inr (Or.inr h2))
    · push_neg at hLgood
      obtain ⟨q, hq⟩ := hLgood
      exact Or.inl ⟨q, Or.inr (mem_oscL_iff.mpr ⟨hq.1, hq.2⟩)⟩
  · push_neg at hRgood
    obtain ⟨q, hq⟩ := hRgood
    exact Or.inl ⟨q, Or.inl (mem_oscR_iff.mpr ⟨hq.1, hq.2⟩)⟩

end Work.WilG1.OneDim
