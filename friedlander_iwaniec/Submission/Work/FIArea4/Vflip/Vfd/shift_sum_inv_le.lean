import Mathlib

namespace Work.FIArea4.Vflip.Vfd

/-- For `1 ≤ ρ`, the shifted sum `∑_{r ≤ N} F (ρ * r)` is at most the full sum
`∑_{n ≤ N} F n`, because the map `r ↦ ρ * r` is injective and the terms with
`ρ * r > N` vanish by the support hypothesis. -/
private lemma sum_mul_shift_le (N : ℕ) (F : ℕ → ℝ) (hnn : ∀ n, 0 ≤ F n)
    (hsupp : ∀ n, N < n → F n = 0) {ρ : ℕ} (hρ1 : 1 ≤ ρ) :
    ∑ r ∈ Finset.Icc 1 N, F (ρ * r) ≤ ∑ n ∈ Finset.Icc 1 N, F n := by
  have hρpos : 0 < ρ := hρ1
  set s : Finset ℕ := (Finset.Icc 1 N).filter (fun r => ρ * r ≤ N) with hs
  have h_eq : ∑ r ∈ Finset.Icc 1 N, F (ρ * r) = ∑ r ∈ s, F (ρ * r) := by
    rw [hs, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro r hr
    by_cases h : ρ * r ≤ N
    · simp [h]
    · rw [if_neg h]
      exact hsupp _ (lt_of_not_ge h)
  have h_inj : Set.InjOn (fun r => ρ * r) ↑s := by
    intro a ha b hb hab
    simp only [Finset.mem_coe] at ha hb
    exact Nat.mul_left_cancel hρpos hab
  have h_img : ∑ r ∈ s, F (ρ * r) = ∑ n ∈ s.image (fun r => ρ * r), F n :=
    (Finset.sum_image h_inj).symm
  have h_sub : s.image (fun r => ρ * r) ⊆ Finset.Icc 1 N := by
    intro n hn
    rw [Finset.mem_image] at hn
    obtain ⟨r, hr, rfl⟩ := hn
    rw [hs, Finset.mem_filter, Finset.mem_Icc] at hr
    rw [Finset.mem_Icc]
    exact ⟨Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega)), hr.2⟩
  calc ∑ r ∈ Finset.Icc 1 N, F (ρ * r)
      = ∑ r ∈ s, F (ρ * r) := h_eq
    _ = ∑ n ∈ s.image (fun r => ρ * r), F n := h_img
    _ ≤ ∑ n ∈ Finset.Icc 1 N, F n :=
        Finset.sum_le_sum_of_subset_of_nonneg h_sub (fun n _ _ => hnn n)

/-- Weighted version of the shift bound: `∑_ρ (1/ρ) ∑_r F (ρ r) ≤ (log N + 1) ∑_n F n`
for a nonnegative `F` supported on `[1, N]`.

Indeed every inner sum is at most the full sum, and the harmonic sum
`∑_{ρ ≤ N} 1/ρ` is at most `log N + 1`. -/
theorem shift_sum_inv_le {N : ℕ} (hN : 1 ≤ N) (F : ℕ → ℝ)
    (hnn : ∀ n, 0 ≤ F n) (hsupp : ∀ n, N < n → F n = 0) :
    ∑ ρ ∈ Finset.Icc 1 N, ((ρ:ℝ))⁻¹ * ∑ r ∈ Finset.Icc 1 N, F (ρ * r)
      ≤ (Real.log N + 1) * ∑ n ∈ Finset.Icc 1 N, F n := by
  have hNpos : 0 < N := by omega
  have hterm : ∀ ρ ∈ Finset.Icc 1 N,
      ((ρ:ℝ))⁻¹ * ∑ r ∈ Finset.Icc 1 N, F (ρ * r)
        ≤ ((ρ:ℝ))⁻¹ * ∑ n ∈ Finset.Icc 1 N, F n := by
    intro ρ hρ
    rw [Finset.mem_Icc] at hρ
    refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr (by positivity))
    exact sum_mul_shift_le N F hnn hsupp hρ.1
  have hS : 0 ≤ ∑ n ∈ Finset.Icc 1 N, F n := Finset.sum_nonneg (fun n _ => hnn n)
  have hharm : ∑ k ∈ Finset.Icc 1 N, ((k:ℝ))⁻¹ ≤ Real.log N + 1 := by
    have h := harmonic_le_one_add_log N
    have hcast : ((harmonic N : ℚ) : ℝ) = ∑ k ∈ Finset.Icc 1 N, ((k:ℝ))⁻¹ := by
      rw [harmonic_eq_sum_Icc, Rat.cast_sum]
      apply Finset.sum_congr rfl
      intro k hk
      simp
    rw [← hcast]
    linarith
  calc ∑ ρ ∈ Finset.Icc 1 N, ((ρ:ℝ))⁻¹ * ∑ r ∈ Finset.Icc 1 N, F (ρ * r)
      ≤ ∑ ρ ∈ Finset.Icc 1 N, ((ρ:ℝ))⁻¹ * ∑ n ∈ Finset.Icc 1 N, F n :=
        Finset.sum_le_sum hterm
    _ = (∑ ρ ∈ Finset.Icc 1 N, ((ρ:ℝ))⁻¹) * (∑ n ∈ Finset.Icc 1 N, F n) := by
        rw [Finset.sum_mul]
    _ ≤ (Real.log N + 1) * ∑ n ∈ Finset.Icc 1 N, F n :=
        mul_le_mul_of_nonneg_right hharm hS

end Work.FIArea4.Vflip.Vfd
