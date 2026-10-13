import Mathlib

namespace Work.WilE2

/-- Covering of `[0, N]` by the `N` unit intervals `[j, j+1]`, `j : Fin N`:
every `x` with `0 ≤ x ≤ N` lies in one of them. -/
lemma exists_fin_unit_cover {N : ℕ} (hN : 0 < N) {x : ℝ} (hx0 : 0 ≤ x) (hxN : x ≤ (N : ℝ)) :
    ∃ j : Fin N, (j : ℝ) ≤ x ∧ x ≤ (j : ℝ) + 1 := by
  by_cases h : ⌊x⌋₊ < N
  · refine ⟨⟨⌊x⌋₊, h⟩, Nat.floor_le hx0, ?_⟩
    have := Nat.lt_floor_add_one x
    push_cast
    linarith
  · simp only [not_lt] at h
    have hx_eq : x = (N : ℝ) := by
      have hle : (N : ℝ) ≤ (⌊x⌋₊ : ℝ) := by exact_mod_cast h
      linarith [Nat.floor_le hx0]
    refine ⟨⟨N - 1, Nat.sub_one_lt hN.ne'⟩, ?_, ?_⟩
    · rw [hx_eq]
      exact_mod_cast Nat.sub_le N 1
    · rw [hx_eq]
      have hc : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : (1:ℕ) ≤ N)]; norm_num
      rw [hc]; linarith

theorem exists_fin_Icc_cover {M : ℝ} (hM : 0 < M) {N : ℕ} (hN : 0 < N) {t : ℝ} (ht : |t| ≤ M) :
    ∃ j : Fin N, -M + 2 * M * (j : ℝ) / N ≤ t ∧ t ≤ -M + 2 * M * ((j : ℝ) + 1) / N := by
  have hNpos : (0:ℝ) < N := by exact_mod_cast hN
  have h2M : (0:ℝ) < 2*M := by linarith
  obtain ⟨ht1, ht2⟩ := abs_le.mp ht
  -- rescale the interval `[-M, M]` to `[0, N]`
  set x : ℝ := (t + M) * (N:ℝ) / (2*M) with hxdef
  have hx0 : 0 ≤ x := by
    rw [hxdef]
    exact div_nonneg (mul_nonneg (by linarith) (le_of_lt hNpos)) (le_of_lt h2M)
  have hxN : x ≤ (N:ℝ) := by
    rw [hxdef, div_le_iff₀ h2M]
    have hmul := mul_le_mul_of_nonneg_right (by linarith : t + M ≤ 2*M) (le_of_lt hNpos)
    linarith
  obtain ⟨j, hj1, hj2⟩ := exists_fin_unit_cover hN hx0 hxN
  have hj1' : (j:ℝ) ≤ (t + M) * (N:ℝ) / (2*M) := by simpa only [hxdef] using hj1
  have hj2' : (t + M) * (N:ℝ) / (2*M) ≤ (j:ℝ) + 1 := by simpa only [hxdef] using hj2
  refine ⟨j, ?_, ?_⟩
  · have key : 2*M*(j:ℝ) ≤ (t + M)*(N:ℝ) := by
      have hk := (le_div_iff₀ h2M).mp hj1'
      linarith
    have key2 : 2 * M * (j : ℝ) / N ≤ t + M := by
      rw [div_le_iff₀ hNpos]
      exact key
    linarith
  · have key : (t + M)*(N:ℝ) ≤ 2*M*((j:ℝ) + 1) := by
      have hk := (div_le_iff₀ h2M).mp hj2'
      linarith
    have key2 : t + M ≤ 2 * M * ((j : ℝ) + 1) / N := by
      rw [le_div_iff₀ hNpos]
      exact key
    linarith

end Work.WilE2
