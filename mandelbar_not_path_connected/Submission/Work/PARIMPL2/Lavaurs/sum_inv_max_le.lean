import Mathlib
import Submission.Work.FlowerGlue2.sum_one_div_le_aux

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.PARIMPL2.Lavaurs

open Finset

/-- The majorant `(max κ (k/2 - Babs))⁻¹` dominating `(max κ |a k|)⁻¹`. -/
noncomputable def maj (κ Babs : ℝ) (k : ℕ) : ℝ := (max κ ((k : ℝ) / 2 - Babs))⁻¹

/-- The majorant `(max κ (k/2))⁻¹` used to bound the tail. -/
noncomputable def maj0 (κ : ℝ) (k : ℕ) : ℝ := (max κ ((k : ℝ) / 2))⁻¹

/-- If the increments of `a` are at least `1/2`, then `a m - a j ≥ (m - j)/2`. -/
lemma step_sub_ge {a : ℕ → ℝ} {m : ℕ}
    (hstep : ∀ j, j < m → a (j + 1) - a j ≥ 1 / 2) {j : ℕ} (hj : j ≤ m) :
    a m - a j ≥ ((m - j : ℕ) : ℝ) / 2 := by
  have hjm : j + (m - j) = m := Nat.add_sub_cancel' hj
  have htel := Finset.sum_range_sub (fun t => a (j + t)) (m - j)
  rw [hjm, Nat.add_zero] at htel
  rw [← htel]
  have hterm : ∀ t ∈ Finset.range (m - j),
      a (j + (t + 1)) - a (j + t) ≥ (1 : ℝ) / 2 := by
    intro t ht
    have hlt : j + t < m := by
      have := Finset.mem_range.mp ht; omega
    have hs := hstep (j + t) hlt
    rwa [show j + t + 1 = j + (t + 1) from by omega] at hs
  have h1 : ∑ t ∈ Finset.range (m - j), ((1 : ℝ) / 2)
      ≤ ∑ t ∈ Finset.range (m - j), (a (j + (t + 1)) - a (j + t)) :=
    Finset.sum_le_sum hterm
  have h2 : ∑ t ∈ Finset.range (m - j), ((1 : ℝ) / 2) = ((m - j : ℕ) : ℝ) * (1 / 2) := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  linarith

/-- Pointwise domination of each summand by `maj`. -/
lemma term_le_maj {a : ℕ → ℝ} {κ Babs : ℝ} (hκ : 0 < κ) {m j : ℕ}
    (hstep : ∀ j, j < m → a (j + 1) - a j ≥ 1 / 2) (hbm : |a m| ≤ Babs) (hj : j < m) :
    (max κ |a j|)⁻¹ ≤ maj κ Babs (m - j) := by
  have hjle : j ≤ m := le_of_lt hj
  have hstepj := step_sub_ge hstep hjle
  have ham : a m ≤ Babs := (abs_le.mp hbm).2
  have haj : a j ≤ Babs - ((m - j : ℕ) : ℝ) / 2 := by linarith
  have hkey : max 0 (((m - j : ℕ) : ℝ) / 2 - Babs) ≤ |a j| := by
    rcases le_or_gt (((m - j : ℕ) : ℝ) / 2 - Babs) 0 with h | h
    · rw [max_eq_left h]; exact abs_nonneg _
    · rw [max_eq_right (le_of_lt h)]
      have hneg : a j < 0 := by linarith
      rw [abs_of_neg hneg]
      linarith
  have hden : max κ (((m - j : ℕ) : ℝ) / 2 - Babs) ≤ max κ |a j| :=
    max_le_max le_rfl (le_trans (le_max_right _ _) hkey)
  have hpos : (0 : ℝ) < max κ (((m - j : ℕ) : ℝ) / 2 - Babs) :=
    lt_of_lt_of_le hκ (le_max_left _ _)
  simpa [maj] using inv_anti₀ hpos hden

/-- Bound for the tail sum. -/
lemma sum_maj0_le {κ : ℝ} (hκ : 0 < κ) (m : ℕ) :
    ∑ x ∈ Finset.range m, maj0 κ x ≤ 1 / κ + 2 * (1 + Real.log (1 + m)) := by
  have hf0 : maj0 κ 0 = 1 / κ := by
    rw [maj0, Nat.cast_zero, zero_div, max_eq_left (le_of_lt hκ), one_div]
  have hnonneg : ∀ x : ℕ, 0 ≤ maj0 κ x := by
    intro x
    rw [maj0]
    exact inv_nonneg.mpr (le_of_lt (lt_of_lt_of_le hκ (le_max_left _ _)))
  have hstep1 : ∑ x ∈ Finset.range m, maj0 κ x ≤ ∑ x ∈ Finset.range (m + 1), maj0 κ x :=
    Finset.sum_le_sum_of_subset_of_nonneg
      (by intro x hx; simp only [Finset.mem_range] at hx ⊢; omega)
      (by intro x _ _; exact hnonneg x)
  have hstep2 : ∑ x ∈ Finset.range (m + 1), maj0 κ x
      = ∑ x ∈ Finset.range m, maj0 κ (x + 1) + 1 / κ := by
    rw [Finset.sum_range_succ', hf0]
  have hstep3 : ∑ x ∈ Finset.range m, maj0 κ (x + 1)
      ≤ ∑ x ∈ Finset.range m, (2 : ℝ) / ((x : ℕ) + 1) := by
    apply Finset.sum_le_sum
    intro x _
    rw [maj0]
    have hpos : (0 : ℝ) < ((x + 1 : ℕ) : ℝ) / 2 := by positivity
    have hle : ((x + 1 : ℕ) : ℝ) / 2 ≤ max κ (((x + 1 : ℕ) : ℝ) / 2) := le_max_right _ _
    have := inv_anti₀ hpos hle
    rw [inv_div] at this
    simpa using this
  have hharm : ∑ x ∈ Finset.range m, (2 : ℝ) / ((x : ℕ) + 1)
      = 2 * ∑ x ∈ Finset.range m, (1 : ℝ) / ((x : ℕ) + 1) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring
  have hbase : ∑ x ∈ Finset.range m, (1 : ℝ) / ((x : ℕ) + 1) ≤ 1 + Real.log (1 + m) := by
    have h := Work.FlowerGlue2.sum_one_div_le_aux (a := 1) (by norm_num) m
    have he : ∑ x ∈ Finset.range m, (1 : ℝ) / (1 + (x : ℝ))
        = ∑ x ∈ Finset.range m, (1 : ℝ) / ((x : ℕ) + 1) := by
      apply Finset.sum_congr rfl
      intro x _
      ring
    rw [he] at h
    simpa using h
  linarith [hstep1, hstep2, hstep3, hharm, hbase]

/-- Bound for `∑_{i<m} maj κ Babs (i+1)`. -/
lemma sum_maj_le {κ Babs : ℝ} (hκ : 0 < κ) (hBabs : 0 ≤ Babs) (m : ℕ) :
    ∑ i ∈ Finset.range m, maj κ Babs (i + 1) ≤
      ((2 * Babs + 2) / κ + 4) * (1 + Real.log (2 + m)) := by
  set c : ℕ := Nat.floor (2 * Babs) with hc
  have hc_le : (c : ℝ) ≤ 2 * Babs := by
    have := Nat.floor_le (show (0:ℝ) ≤ 2 * Babs by linarith)
    rwa [hc]
  have hc_lt : 2 * Babs < (c : ℝ) + 1 := by
    have h := Nat.lt_floor_add_one (2 * Babs)
    rw [← hc] at h
    exact h
  set C : ℕ := min c m with hC
  have hCm : C ≤ m := min_le_right _ _
  have hCc : C ≤ c := min_le_left _ _
  have hsplit : ∑ i ∈ Finset.range m, maj κ Babs (i + 1)
      = ∑ i ∈ Finset.range C, maj κ Babs (i + 1)
        + ∑ x ∈ Finset.range (m - C), maj κ Babs (C + x + 1) := by
    have h := Finset.sum_range_add (fun i => maj κ Babs (i + 1)) C (m - C)
    rw [Nat.add_sub_cancel' hCm] at h
    exact h
  -- head
  have hhead : ∑ i ∈ Finset.range C, maj κ Babs (i + 1) ≤ 2 * Babs / κ := by
    have hpt : ∀ i ∈ Finset.range C, maj κ Babs (i + 1) = 1 / κ := by
      intro i hi
      have hiC : i < C := Finset.mem_range.mp hi
      have hile : ((i + 1 : ℕ) : ℝ) ≤ 2 * Babs := by
        have h1 : (i + 1 : ℕ) ≤ c := by omega
        calc ((i + 1 : ℕ) : ℝ) ≤ (c : ℝ) := by exact_mod_cast h1
          _ ≤ 2 * Babs := hc_le
      have hx : ((i + 1 : ℕ) : ℝ) / 2 - Babs ≤ 0 := by linarith
      rw [maj, max_eq_left (le_trans hx (le_of_lt hκ)), one_div]
    have hconst : ∑ i ∈ Finset.range C, maj κ Babs (i + 1) = (C : ℝ) * (1 / κ) := by
      rw [Finset.sum_congr rfl hpt, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [hconst, mul_one_div]
    have hC2 : (C : ℝ) ≤ 2 * Babs := le_trans (by exact_mod_cast hCc) hc_le
    exact div_le_div_of_nonneg_right hC2 (le_of_lt hκ)
  -- tail
  have htail : ∑ x ∈ Finset.range (m - C), maj κ Babs (C + x + 1)
      ≤ 1 / κ + 2 * (1 + Real.log (1 + m)) := by
    have hpt : ∀ x ∈ Finset.range (m - C), maj κ Babs (C + x + 1) ≤ maj0 κ x := by
      intro x hx
      have hxlt : x < m - C := Finset.mem_range.mp hx
      have hClt : C < m := by omega
      have hCc' : C = c := by
        by_cases hcm : c ≤ m
        · rw [hC]; exact min_eq_left hcm
        · exfalso
          have hm : C = m := by rw [hC]; exact min_eq_right (le_of_lt (not_le.mp hcm))
          omega
      rw [hCc', maj, maj0]
      apply inv_anti₀
      · exact lt_of_lt_of_le hκ (le_max_left _ _)
      · apply max_le_max le_rfl
        have hcast : (((c + x + 1 : ℕ)) : ℝ) = (c : ℝ) + (x : ℝ) + 1 := by push_cast; ring
        have hδ : 0 < (c : ℝ) + 1 - 2 * Babs := by linarith
        rw [hcast]; linarith
    have hstep1 : ∑ x ∈ Finset.range (m - C), maj κ Babs (C + x + 1)
        ≤ ∑ x ∈ Finset.range (m - C), maj0 κ x := Finset.sum_le_sum hpt
    have hnonneg : ∀ x : ℕ, 0 ≤ maj0 κ x := by
      intro x
      rw [maj0]
      exact inv_nonneg.mpr (le_of_lt (lt_of_lt_of_le hκ (le_max_left _ _)))
    have hstep2 : ∑ x ∈ Finset.range (m - C), maj0 κ x ≤ ∑ x ∈ Finset.range m, maj0 κ x :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (by intro x hx; simp only [Finset.mem_range] at hx ⊢; omega)
        (by intro x _ _; exact hnonneg x)
    have hstep3 := sum_maj0_le hκ m
    linarith
  have hsum : ∑ i ∈ Finset.range m, maj κ Babs (i + 1)
      ≤ 2 * Babs / κ + (1 / κ + 2 * (1 + Real.log (1 + m))) := by
    rw [hsplit]; linarith
  have hL : 0 ≤ Real.log (2 + (m : ℝ)) := Real.log_nonneg (by linarith)
  have hM : Real.log (1 + (m : ℝ)) ≤ Real.log (2 + (m : ℝ)) :=
    Real.log_le_log (by linarith) (by linarith)
  have hKge : (2 : ℝ) ≤ (2 * Babs + 2) / κ + 4 := by
    have h0 : (0 : ℝ) ≤ (2 * Babs + 2) / κ := by
      apply div_nonneg <;> linarith
    linarith
  have hKdiv : 2 * Babs / κ + 1 / κ + 2 ≤ (2 * Babs + 2) / κ + 4 := by
    have heq : 2 * Babs / κ + 1 / κ = (2 * Babs + 1) / κ := by rw [add_div]
    have hle : (2 * Babs + 1) / κ ≤ (2 * Babs + 2) / κ :=
      div_le_div_of_nonneg_right (by linarith) (le_of_lt hκ)
    linarith
  have hKL : (2 : ℝ) * Real.log (2 + (m : ℝ))
      ≤ ((2 * Babs + 2) / κ + 4) * Real.log (2 + (m : ℝ)) :=
    mul_le_mul_of_nonneg_right hKge hL
  have hM2 : 2 * Real.log (1 + (m : ℝ)) ≤ 2 * Real.log (2 + (m : ℝ)) := by linarith
  calc ∑ i ∈ Finset.range m, maj κ Babs (i + 1)
      ≤ 2 * Babs / κ + (1 / κ + 2 * (1 + Real.log (1 + m))) := hsum
    _ ≤ ((2 * Babs + 2) / κ + 4) * (1 + Real.log (2 + m)) := by
        nlinarith [hKdiv, hM2, hKL]

theorem sum_inv_max_le {κ Babs : ℝ} (hκ : 0 < κ) (hBabs : 0 ≤ Babs) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (a : ℕ → ℝ) (m : ℕ),
      (∀ j, j < m → a (j + 1) - a j ≥ 1 / 2) → |a m| ≤ Babs →
      ∑ j ∈ Finset.range m, (max κ |a j|)⁻¹ ≤ K * (1 + Real.log (2 + m)) := by
  refine ⟨(2 * Babs + 2) / κ + 4, ?_, ?_⟩
  · have h0 : (0 : ℝ) ≤ (2 * Babs + 2) / κ := by
      apply div_nonneg <;> linarith
    linarith
  · intro a m hstep hbm
    have hpt : ∀ j ∈ Finset.range m, (max κ |a j|)⁻¹ ≤ maj κ Babs (m - j) := by
      intro j hj
      exact term_le_maj hκ hstep hbm (Finset.mem_range.mp hj)
    have h1 := Finset.sum_le_sum hpt
    have h2 : ∑ j ∈ Finset.range m, maj κ Babs (m - j)
        = ∑ i ∈ Finset.range m, maj κ Babs (i + 1) := by
      rw [← Finset.sum_range_reflect (fun s => maj κ Babs (s + 1)) m]
      apply Finset.sum_congr rfl
      intro j hj
      have hjm : j < m := Finset.mem_range.mp hj
      have hidx : m - j = m - 1 - j + 1 := by omega
      rw [hidx]
    have h3 := sum_maj_le hκ hBabs m
    calc ∑ j ∈ Finset.range m, (max κ |a j|)⁻¹
        ≤ ∑ j ∈ Finset.range m, maj κ Babs (m - j) := h1
      _ = ∑ i ∈ Finset.range m, maj κ Babs (i + 1) := h2
      _ ≤ ((2 * Babs + 2) / κ + 4) * (1 + Real.log (2 + m)) := h3

end Work.PARIMPL2.Lavaurs
