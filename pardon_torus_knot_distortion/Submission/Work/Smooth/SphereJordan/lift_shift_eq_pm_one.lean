import Mathlib

namespace Work.Smooth.SphereJordan

/-- If `v` is strictly between the two endpoint values of a continuous function on `[c1,c2]`,
then it is attained at an interior point. -/
lemma ex_between_of_extremes (Ψ : ℝ → ℝ) (hcont : Continuous Ψ) {c1 c2 : ℝ} (hc12 : c1 ≤ c2)
    {v : ℝ} (hlo : min (Ψ c1) (Ψ c2) < v) (hhi : v < max (Ψ c1) (Ψ c2)) :
    ∃ c ∈ Set.Ioo c1 c2, Ψ c = v := by
  have hc : ContinuousOn Ψ (Set.Icc c1 c2) := hcont.continuousOn
  rcases le_total (Ψ c1) (Ψ c2) with h | h
  · have hv : v ∈ Set.Ioo (Ψ c1) (Ψ c2) :=
      ⟨by rwa [min_eq_left h] at hlo, by rwa [max_eq_right h] at hhi⟩
    exact (intermediate_value_Ioo hc12 hc) hv
  · have hv : v ∈ Set.Ioo (Ψ c2) (Ψ c1) :=
      ⟨by rwa [min_eq_right h] at hlo, by rwa [max_eq_left h] at hhi⟩
    exact (intermediate_value_Ioo' hc12 hc) hv

/-- An integer multiple of a positive real lying in `[0,L]` has multiplier `0` or `1`. -/
lemma int_eq_zero_or_one_of_mul_mem {L : ℝ} (hL : 0 < L) {k : ℤ}
    (hlo : 0 ≤ (k : ℝ) * L) (hhi : (k : ℝ) * L ≤ L) : k = 0 ∨ k = 1 := by
  have hk0 : (0 : ℤ) ≤ k := by
    have : (0 : ℝ) ≤ (k : ℝ) := (mul_nonneg_iff_of_pos_right hL).mp hlo
    exact_mod_cast this
  have hk1 : k ≤ 1 := by
    have h' : (k : ℝ) ≤ (1 : ℝ) :=
      (mul_le_mul_iff_of_pos_right hL).mp (by simpa using hhi)
    exact_mod_cast h'
  omega

theorem lift_shift_eq_pm_one (Ψ : ℝ → ℝ) (hcont : Continuous Ψ) (d : ℤ)
    (hshift : ∀ θ : ℝ, Ψ (θ + 2 * Real.pi) = Ψ θ + (d : ℝ) * (2 * Real.pi))
    (hmod : ∀ x y : ℝ, (∃ k : ℤ, Ψ x - Ψ y = (k : ℝ) * (2 * Real.pi)) →
      (∃ k : ℤ, x - y = (k : ℝ) * (2 * Real.pi))) :
    d = 1 ∨ d = -1 := by
  set L : ℝ := 2 * Real.pi with hLdef
  have hLpos : 0 < L := by rw [hLdef]; positivity
  have hLne : L ≠ 0 := ne_of_gt hLpos
  have hshiftL : ∀ θ : ℝ, Ψ (θ + L) = Ψ θ + (d : ℝ) * L := by
    intro θ; simpa [hLdef] using hshift θ
  have hmodL : ∀ x y : ℝ, (∃ k : ℤ, Ψ x - Ψ y = (k : ℝ) * L) →
      (∃ k : ℤ, x - y = (k : ℝ) * L) := by
    intro x y h
    obtain ⟨k, hk⟩ := h
    obtain ⟨k', hk'⟩ := hmod x y ⟨k, by simpa [hLdef] using hk⟩
    exact ⟨k', by simpa [hLdef] using hk'⟩
  rcases lt_trichotomy d 0 with hd | hd | hd
  · -- d < 0
    have hd1 : (d : ℝ) ≤ -1 := by exact_mod_cast (show d ≤ (-1 : ℤ) by omega)
    have hf : Continuous fun t : ℝ => Ψ 0 - Ψ t := continuous_const.sub hcont
    have hfL : (fun t : ℝ => Ψ 0 - Ψ t) L = -(d : ℝ) * L := by
      have h := hshiftL 0; simp only [zero_add] at h
      simp only []
      rw [h]; ring
    have hmem : L ∈ Set.Icc ((fun t : ℝ => Ψ 0 - Ψ t) 0) ((fun t : ℝ => Ψ 0 - Ψ t) L) := by
      have e1 : (fun t : ℝ => Ψ 0 - Ψ t) 0 = 0 := by simp
      rw [e1, hfL]
      exact ⟨le_of_lt hLpos, by nlinarith [hLpos, hd1]⟩
    obtain ⟨t, ht_mem, ht_val⟩ :=
      (intermediate_value_Icc (le_of_lt hLpos) hf.continuousOn) hmem
    have ht_val' : Ψ 0 - Ψ t = L := ht_val
    obtain ⟨k, hk⟩ := hmodL t 0 ⟨-1, by push_cast; linarith⟩
    have htk : t = (k : ℝ) * L := by linarith
    have ht_cases : t = 0 ∨ t = L := by
      rcases int_eq_zero_or_one_of_mul_mem hLpos (by rw [← htk]; exact ht_mem.1)
          (by rw [← htk]; exact ht_mem.2) with hk0 | hk1
      · left; rw [htk, hk0]; push_cast; ring
      · right; rw [htk, hk1]; push_cast; ring
    rcases ht_cases with h0 | hL
    · rw [h0] at ht_val'; simp only [sub_self] at ht_val'
      exact absurd ht_val' (ne_of_gt hLpos).symm
    · rw [hL] at ht_val'
      have hshift0 := hshiftL 0; simp only [zero_add] at hshift0
      have hdL : (d : ℝ) * L = -L := by linarith [hshift0, ht_val']
      have hdR : (d : ℝ) = -1 := by
        have h1 : (d : ℝ) * L = (-1 : ℝ) * L := by rw [hdL]; ring
        exact mul_right_cancel₀ hLne h1
      right; exact_mod_cast hdR
  · -- d = 0
    have hper : ∀ θ : ℝ, Ψ (θ + L) = Ψ θ := by
      intro θ; have h := hshiftL θ; rw [hd] at h; simpa using h
    obtain ⟨a, ha_mem, ha_max⟩ :=
      isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.mpr (le_of_lt hLpos)) hcont.continuousOn
    obtain ⟨b, hb_mem, hb_min⟩ :=
      isCompact_Icc.exists_isMinOn (Set.nonempty_Icc.mpr (le_of_lt hLpos)) hcont.continuousOn
    have hle : Ψ b ≤ Ψ a := hb_min ha_mem
    rcases lt_or_eq_of_le hle with hlt | heq
    · -- nonconstant: two points of the period carry the same value, giving a contradiction
      set c1 := min a b with hc1
      set c2 := max a b with hc2
      have hc12 : c1 < c2 := by
        rw [hc1, hc2, min_lt_max]
        intro hab
        exact (ne_of_lt hlt).symm (by rw [hab])
      have hc1_mem : c1 ∈ Set.Icc (0 : ℝ) L :=
        ⟨le_min ha_mem.1 hb_mem.1, le_trans (min_le_left _ _) ha_mem.2⟩
      have hc2_mem : c2 ∈ Set.Icc (0 : ℝ) L :=
        ⟨le_trans ha_mem.1 (le_max_left _ _), max_le ha_mem.2 hb_mem.2⟩
      have hmin_eq : min (Ψ c1) (Ψ c2) = Ψ b := by
        rcases le_total a b with hab | hba
        · rw [hc1, hc2, min_eq_left hab, max_eq_right hab]; exact min_eq_right hlt.le
        · rw [hc1, hc2, min_eq_right hba, max_eq_left hba]; exact min_eq_left hlt.le
      have hmax_eq : max (Ψ c1) (Ψ c2) = Ψ a := by
        rcases le_total a b with hab | hba
        · rw [hc1, hc2, min_eq_left hab, max_eq_right hab]; exact max_eq_left hlt.le
        · rw [hc1, hc2, min_eq_right hba, max_eq_left hba]; exact max_eq_right hlt.le
      set mid := (Ψ a + Ψ b) / 2 with hmid
      have hmid_low : min (Ψ c1) (Ψ c2) < mid := by rw [hmin_eq, hmid]; linarith
      have hmid_high : mid < max (Ψ c1) (Ψ c2) := by rw [hmax_eq, hmid]; linarith
      obtain ⟨c, hc_mem, hc_val⟩ := ex_between_of_extremes Ψ hcont hc12.le hmid_low hmid_high
      have hc2_le : c2 ≤ c1 + L := by
        have h1 : 0 ≤ c1 := hc1_mem.1
        have h2 : c2 ≤ L := hc2_mem.2
        linarith
      have hcL : Ψ (c1 + L) = Ψ c1 := hper c1
      have hmid_low2 : min (Ψ c2) (Ψ (c1 + L)) < mid := by rw [hcL, min_comm]; exact hmid_low
      have hmid_high2 : mid < max (Ψ c2) (Ψ (c1 + L)) := by rw [hcL, max_comm]; exact hmid_high
      obtain ⟨dd, hdd_mem, hdd_val⟩ :=
        ex_between_of_extremes Ψ hcont hc2_le hmid_low2 hmid_high2
      have hcd : Ψ c - Ψ dd = ((0 : ℤ) : ℝ) * L := by rw [hc_val, hdd_val]; push_cast; ring
      obtain ⟨k, hk⟩ := hmodL c dd ⟨0, hcd⟩
      have hneg : (-1 : ℝ) * L < (k : ℝ) * L := by
        rw [← hk]; linarith [hc_mem.1, hdd_mem.2]
      have hpos : (k : ℝ) * L < (0 : ℝ) * L := by
        rw [← hk]; linarith [hc_mem.2, hdd_mem.1]
      have hk1 : ((-1 : ℤ) : ℝ) < (k : ℝ) := by
        have h := (mul_lt_mul_iff_of_pos_right hLpos).mp hneg
        push_cast
        exact h
      have hk2 : (k : ℝ) < ((0 : ℤ) : ℝ) := by
        have h := (mul_lt_mul_iff_of_pos_right hLpos).mp hpos
        push_cast
        exact h
      have hk1' : (-1 : ℤ) < k := by exact_mod_cast hk1
      have hk2' : k < (0 : ℤ) := by exact_mod_cast hk2
      omega
    · -- constant case
      have hconst : ∀ y ∈ Set.Icc (0 : ℝ) L, Ψ y = Ψ a := by
        intro y hy
        have h1 : Ψ b ≤ Ψ y := hb_min hy
        have h2 : Ψ y ≤ Ψ a := ha_max hy
        linarith
      have hL2mem : L / 2 ∈ Set.Icc (0 : ℝ) L := ⟨by linarith [hLpos], by linarith [hLpos]⟩
      have h0mem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) L := ⟨le_refl 0, le_of_lt hLpos⟩
      have hzero : Ψ (L / 2) - Ψ 0 = ((0 : ℤ) : ℝ) * L := by
        rw [hconst (L / 2) hL2mem, hconst 0 h0mem]; push_cast; ring
      obtain ⟨k, hk⟩ := hmodL (L / 2) 0 ⟨0, hzero⟩
      have hk' : L / 2 = (k : ℝ) * L := by linarith
      have h1 : (k : ℝ) * L = (1 / 2 : ℝ) * L := by linarith [hk']
      have h2 : (k : ℝ) = 1 / 2 := mul_right_cancel₀ hLne h1
      have h3 : ((2 * k : ℤ) : ℝ) = ((1 : ℤ) : ℝ) := by push_cast; linarith
      have h4 : 2 * k = (1 : ℤ) := by exact_mod_cast h3
      omega
  · -- d > 0
    have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast (show (1 : ℤ) ≤ d by omega)
    have hf : Continuous fun t : ℝ => Ψ t - Ψ 0 := hcont.sub continuous_const
    have hfL : (fun t : ℝ => Ψ t - Ψ 0) L = (d : ℝ) * L := by
      have h := hshiftL 0; simp only [zero_add] at h
      simp only []
      rw [h]; ring
    have hmem : L ∈ Set.Icc ((fun t : ℝ => Ψ t - Ψ 0) 0) ((fun t : ℝ => Ψ t - Ψ 0) L) := by
      have e1 : (fun t : ℝ => Ψ t - Ψ 0) 0 = 0 := by simp
      rw [e1, hfL]
      exact ⟨le_of_lt hLpos, by nlinarith [hLpos, hd1]⟩
    obtain ⟨t, ht_mem, ht_val⟩ :=
      (intermediate_value_Icc (le_of_lt hLpos) hf.continuousOn) hmem
    have ht_val' : Ψ t - Ψ 0 = L := ht_val
    obtain ⟨k, hk⟩ := hmodL t 0 ⟨1, by rw [ht_val']; ring⟩
    have htk : t = (k : ℝ) * L := by linarith
    have ht_cases : t = 0 ∨ t = L := by
      rcases int_eq_zero_or_one_of_mul_mem hLpos (by rw [← htk]; exact ht_mem.1)
          (by rw [← htk]; exact ht_mem.2) with hk0 | hk1
      · left; rw [htk, hk0]; push_cast; ring
      · right; rw [htk, hk1]; push_cast; ring
    rcases ht_cases with h0 | hL
    · rw [h0] at ht_val'; simp only [sub_self] at ht_val'
      exact absurd ht_val' (ne_of_gt hLpos).symm
    · rw [hL] at ht_val'
      have hshift0 := hshiftL 0; simp only [zero_add] at hshift0
      have hdL : (d : ℝ) * L = L := by linarith [hshift0, ht_val']
      have hdR : (d : ℝ) = 1 := by
        have h1 : (d : ℝ) * L = (1 : ℝ) * L := by rw [hdL]; ring
        exact mul_right_cancel₀ hLne h1
      left; exact_mod_cast hdR

end Work.Smooth.SphereJordan
