import Mathlib
import Submission.Commons.Geometry.Ulam.moment_h_bounds

namespace Commons.Geometry.Ulam

open MeasureTheory
open scoped BigOperators ContDiff Pointwise RealInnerProductSpace Interval

set_option autoImplicit false
set_option maxHeartbeats 800000

lemma active_nonneg_outside_of_roots_inside_general
    {f : ℝ → ℝ} {s h u v α β : ℝ} (hs : 0 < s)
    (hu_mem : u ∈ Set.Ioo α β) (hv_mem : v ∈ Set.Ioo α β)
    (hu_neg : u < 0) (hv_pos : 0 < v)
    (hf_conc : ConcaveOn ℝ (Set.Icc α β) f)
    (hf_nonneg : ∀ t ∈ Set.Icc α β, 0 ≤ f t)
    (hf_pos : ∀ t ∈ Set.Ioo α β, 0 < f t)
    (hfu_sq : f u ^ 2 = (s * u + h) ^ 2)
    (hfv_sq : f v ^ 2 = (s * v + h) ^ 2) :
    (∀ t ∈ Set.Icc α β, (-f t < s * t + h ∧ s * t + h < f t) → u ≤ t ∧ t ≤ v) ∧
    (∀ t ∈ Set.Icc u v, 0 ≤ f t - (s * t + h) ∧ 0 ≤ f t + (s * t + h)) := by
  let L : ℝ → ℝ := fun t => s * t + h
  have hLmono : Monotone L := by
    intro p q hpq
    dsimp [L]
    have hle : s * p ≤ s * q := mul_le_mul_of_nonneg_left hpq (le_of_lt hs)
    linarith
  have hg_conc : ConcaveOn ℝ (Set.Icc α β) (fun t => f t - L t) := by
    dsimp [L]
    exact concaveOn_sub_affine f s h α β hf_conc
  have hq_conc : ConcaveOn ℝ (Set.Icc α β) (fun t => f t + L t) := by
    dsimp [L]
    exact concaveOn_add_affine f s h α β hf_conc
  have hu_Icc : u ∈ Set.Icc α β := Set.Ioo_subset_Icc_self hu_mem
  have hv_Icc : v ∈ Set.Icc α β := Set.Ioo_subset_Icc_self hv_mem
  have hfu_nonneg : 0 ≤ f u := hf_nonneg u hu_Icc
  have hfv_nonneg : 0 ≤ f v := hf_nonneg v hv_Icc
  have hfu_pos : 0 < f u := hf_pos u hu_mem
  have hfv_pos : 0 < f v := hf_pos v hv_mem
  have hLu : L u = s * u + h := rfl
  have hLv : L v = s * v + h := rfl
  have huv : u < v := lt_trans hu_neg hv_pos
  have hsq_u : f u ^ 2 = (L u) ^ 2 := by simpa [L] using hfu_sq
  have hsq_v : f v ^ 2 = (L v) ^ 2 := by simpa [L] using hfv_sq
  by_cases hLu_nonpos : L u ≤ 0
  · by_cases hLv_nonpos : L v ≤ 0
    · have hLu_neg : L u < 0 := lt_of_le_of_ne hLu_nonpos (by
        intro hLu0
        have hfu0 : f u = 0 := by
          have h := eq_neg_of_sq_eq_sq_of_nonneg_of_nonpos hsq_u hfu_nonneg hLu_nonpos
          linarith
        linarith)
      have hLv_neg : L v < 0 := lt_of_le_of_ne hLv_nonpos (by
        intro hLv0
        have hfv0 : f v = 0 := by
          have h := eq_neg_of_sq_eq_sq_of_nonneg_of_nonpos hsq_v hfv_nonneg hLv_nonpos
          linarith
        linarith)
      have hqu : (fun t => f t + L t) u = 0 := by
        dsimp
        have hfu := eq_neg_of_sq_eq_sq_of_nonneg_of_nonpos hsq_u hfu_nonneg (le_of_lt hLu_neg)
        linarith
      have hqv : (fun t => f t + L t) v = 0 := by
        dsimp
        have hfv := eq_neg_of_sq_eq_sq_of_nonneg_of_nonpos hsq_v hfv_nonneg (le_of_lt hLv_neg)
        linarith
      have hq := concave_nonneg_between_of_zero (α := α) (β := β) (u := u) (v := v)
        (hαu := hu_Icc.1) (huv := huv) (hvβ := hv_Icc.2) hq_conc hqu hqv
      constructor
      · intro t ht hact
        by_cases htu : u ≤ t
        · by_cases htv : t ≤ v
          · exact ⟨htu, htv⟩
          · have hgt : v < t := lt_of_not_ge htv
            have hq_le : (fun t => f t + L t) t ≤ 0 := hq.2.2 t ⟨le_of_lt hgt, ht.2⟩
            have hq_pos : 0 < (fun t => f t + L t) t := by dsimp; linarith [hact.1]
            linarith
        · have hlt : t < u := lt_of_not_ge htu
          have hq_le : (fun t => f t + L t) t ≤ 0 := hq.2.1 t ⟨ht.1, le_of_lt hlt⟩
          have hq_pos : 0 < (fun t => f t + L t) t := by dsimp; linarith [hact.1]
          linarith
      · intro t ht
        have hLt_nonpos : L t ≤ 0 := le_trans (hLmono ht.2) hLv_nonpos
        have ht_Icc : t ∈ Set.Icc α β := ⟨le_trans hu_Icc.1 ht.1, le_trans ht.2 hv_Icc.2⟩
        have hft_nonneg : 0 ≤ f t := hf_nonneg t ht_Icc
        have hg_nonneg : 0 ≤ f t - L t := by linarith
        exact ⟨by simpa [L] using hg_nonneg, hq.1 t ht⟩
    · have hLu_neg : L u < 0 := lt_of_le_of_ne hLu_nonpos (by
        intro hLu0
        have hfu0 : f u = 0 := by
          have h := eq_neg_of_sq_eq_sq_of_nonneg_of_nonpos hsq_u hfu_nonneg hLu_nonpos
          linarith
        linarith)
      have hLv_pos : 0 < L v := lt_of_not_ge hLv_nonpos
      have hqu : (fun t => f t + L t) u = 0 := by
        dsimp
        have hfu := eq_neg_of_sq_eq_sq_of_nonneg_of_nonpos hsq_u hfu_nonneg (le_of_lt hLu_neg)
        linarith
      have hgv : (fun t => f t - L t) v = 0 := by
        dsimp
        have hfv := eq_of_sq_eq_sq_of_nonneg_of_nonneg hsq_v hfv_nonneg (le_of_lt hLv_pos)
        linarith
      have hq_v_pos : 0 < (fun t => f t + L t) v := by
        dsimp [L]
        have hfv := eq_of_sq_eq_sq_of_nonneg_of_nonneg hsq_v hfv_nonneg (le_of_lt hLv_pos)
        linarith
      have hg_u_pos : 0 < (fun t => f t - L t) u := by
        dsimp [L]
        have hfu := eq_neg_of_sq_eq_sq_of_nonneg_of_nonpos hsq_u hfu_nonneg (le_of_lt hLu_neg)
        linarith
      have hq := concave_nonneg_between_of_zero_left (α := α) (β := β) (u := u) (v := v)
        (hαu := hu_Icc.1) (huv := huv) (hvβ := hv_Icc.2) hq_conc hqu hq_v_pos
      have hg := concave_nonneg_between_of_zero_right (α := α) (β := β) (u := u) (v := v)
        (hαu := hu_Icc.1) (huv := huv) (hvβ := hv_Icc.2) hg_conc hg_u_pos hgv
      constructor
      · intro t ht hact
        by_cases htu : u ≤ t
        · by_cases htv : t ≤ v
          · exact ⟨htu, htv⟩
          · have hgt : v < t := lt_of_not_ge htv
            have hg_le : (fun t => f t - L t) t ≤ 0 := hg.2 t ⟨le_of_lt hgt, ht.2⟩
            have hg_pos : 0 < (fun t => f t - L t) t := by dsimp; linarith [hact.2]
            linarith
        · have hlt : t < u := lt_of_not_ge htu
          have hq_le : (fun t => f t + L t) t ≤ 0 := hq.2 t ⟨ht.1, le_of_lt hlt⟩
          have hq_pos : 0 < (fun t => f t + L t) t := by dsimp; linarith [hact.1]
          linarith
      · intro t ht
        exact ⟨hg.1 t ht, hq.1 t ht⟩
  · have hLu_pos : 0 < L u := lt_of_not_ge hLu_nonpos
    have hLv_pos : 0 < L v := lt_of_lt_of_le hLu_pos (hLmono (le_of_lt huv))
    have hgu : (fun t => f t - L t) u = 0 := by
      dsimp
      have hfu := eq_of_sq_eq_sq_of_nonneg_of_nonneg hsq_u hfu_nonneg (le_of_lt hLu_pos)
      linarith
    have hgv : (fun t => f t - L t) v = 0 := by
      dsimp
      have hfv := eq_of_sq_eq_sq_of_nonneg_of_nonneg hsq_v hfv_nonneg (le_of_lt hLv_pos)
      linarith
    have hg := concave_nonneg_between_of_zero (α := α) (β := β) (u := u) (v := v)
      (hαu := hu_Icc.1) (huv := huv) (hvβ := hv_Icc.2) hg_conc hgu hgv
    constructor
    · intro t ht hact
      by_cases htu : u ≤ t
      · by_cases htv : t ≤ v
        · exact ⟨htu, htv⟩
        · have hgt : v < t := lt_of_not_ge htv
          have hg_le : (fun t => f t - L t) t ≤ 0 := hg.2.2 t ⟨le_of_lt hgt, ht.2⟩
          have hg_pos : 0 < (fun t => f t - L t) t := by dsimp; linarith [hact.2]
          linarith
      · have hlt : t < u := lt_of_not_ge htu
        have hg_le : (fun t => f t - L t) t ≤ 0 := hg.2.1 t ⟨ht.1, le_of_lt hlt⟩
        have hg_pos : 0 < (fun t => f t - L t) t := by dsimp; linarith [hact.2]
        linarith
    · intro t ht
      have hLt_nonneg : 0 ≤ L t := le_trans hLu_pos.le (hLmono ht.1)
      have ht_Icc : t ∈ Set.Icc α β := ⟨le_trans hu_Icc.1 ht.1, le_trans ht.2 hv_Icc.2⟩
      have hft_nonneg : 0 ≤ f t := hf_nonneg t ht_Icc
      have hq_nonneg : 0 ≤ f t + L t := by linarith
      exact ⟨hg.1 t ht, by simpa [L] using hq_nonneg⟩


end Commons.Geometry.Ulam
