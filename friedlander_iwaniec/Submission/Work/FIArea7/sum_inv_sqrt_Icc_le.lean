import Mathlib

namespace Work.FIArea7

/-- Pointwise telescoping inequality: for `x ≥ 1`, `1/√x ≤ 2(√x - √(x-1))`.
This is the local input to the `O(√N)` bound for `∑_{n ≤ N} 1/√n`. -/
private lemma inv_sqrt_le_sub (x : ℝ) (hx : 1 ≤ x) :
    (Real.sqrt x)⁻¹ ≤ 2 * (Real.sqrt x - Real.sqrt (x - 1)) := by
  have hxm1 : (0:ℝ) ≤ x - 1 := by linarith
  have hsx_pos : (0:ℝ) < Real.sqrt x := Real.sqrt_pos_of_pos (by linarith)
  have hsum_pos : (0:ℝ) < Real.sqrt x + Real.sqrt (x-1) := by
    have := Real.sqrt_nonneg (x-1); linarith
  have h1 : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt (by linarith)
  have h2 : Real.sqrt (x-1) * Real.sqrt (x-1) = x-1 := Real.mul_self_sqrt hxm1
  have hprod : (Real.sqrt x - Real.sqrt (x-1)) * (Real.sqrt x + Real.sqrt (x-1)) = 1 := by
    nlinarith [h1, h2]
  have hdiff : Real.sqrt x - Real.sqrt (x-1) = (Real.sqrt x + Real.sqrt (x-1))⁻¹ :=
    eq_inv_of_mul_eq_one_left hprod
  rw [hdiff]
  rw [show (2:ℝ) * (Real.sqrt x + Real.sqrt (x-1))⁻¹
        = 2 / (Real.sqrt x + Real.sqrt (x-1)) by rw [div_eq_mul_inv]]
  rw [inv_eq_one_div]
  rw [div_le_div_iff₀ hsx_pos hsum_pos]
  have : Real.sqrt (x-1) ≤ Real.sqrt x := Real.sqrt_le_sqrt (by linarith)
  linarith

/-- `∑_{n=1}^{N} 1/√n ≤ 2√N` by the telescoping bound `1/√n ≤ 2(√n - √(n-1))`. -/
private lemma sum_Icc_inv_sqrt_le (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, (Real.sqrt ((n:ℝ)))⁻¹) ≤ 2 * Real.sqrt (N:ℝ) := by
  set f : ℕ → ℝ := fun n => 2 * Real.sqrt (n:ℝ) with hf
  have hb : ∀ n ∈ Finset.Icc 1 N, (Real.sqrt ((n:ℝ)))⁻¹ ≤ f n - f (n-1) := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    have hn1 : 1 ≤ n := hn.1
    have hx : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn1
    have h := inv_sqrt_le_sub (n:ℝ) hx
    simp only [hf]
    have hcast : ((n-1 : ℕ) : ℝ) = (n:ℝ) - 1 := by
      rw [Nat.cast_sub hn1]; norm_num
    rw [hcast]
    linarith
  calc ∑ n ∈ Finset.Icc 1 N, (Real.sqrt ((n:ℝ)))⁻¹
      ≤ ∑ n ∈ Finset.Icc 1 N, (f n - f (n-1)) := Finset.sum_le_sum hb
    _ = ∑ k ∈ Finset.range N, (f (k+1) - f k) := by
        rw [show Finset.Icc 1 N = Finset.Ico 1 (N+1) from by
              ext k; simp [Finset.mem_Icc, Finset.mem_Ico]]
        rw [Finset.sum_Ico_eq_sum_range]
        refine Finset.sum_congr rfl (fun k hk => ?_)
        have h1 : (1 + k : ℕ) = k + 1 := by omega
        have h2 : (k + 1 : ℕ) - 1 = k := by omega
        rw [h1, h2]
    _ = f N - f 0 := Finset.sum_range_sub f N
    _ = 2 * Real.sqrt (N:ℝ) := by simp [hf]

/-- `∑_{|r| ≤ Rz, r odd, r ≠ 0} 1/√|r| ≪ Rz^{1/2}` — the companion of `sum_sqrt_Icc_le`; it is
the loss with which the *sector* difference bound `|k|·2L/|r|` (see `Work.FIArea7.sector_diff_le`)
sums over `r` in the proof of *FI* (22.3). -/
theorem sum_inv_sqrt_Icc_le (Rz : ℤ) :
    (∑ r ∈ (Finset.Icc (-Rz) Rz).filter (fun r : ℤ => Odd r ∧ r ≠ 0),
        (Real.sqrt (|(r : ℝ)|))⁻¹)
      ≤ 4 * Real.sqrt (((max Rz 0).toNat : ℝ)) + 8 := by
  set N : ℕ := (max Rz 0).toNat with hN
  set A : Finset ℤ := (Finset.Icc (-Rz) Rz).filter (fun r : ℤ => Odd r ∧ r ≠ 0) with hA
  -- every `r ∈ A` has `|r| ∈ [1, N]`
  have hmaps : ∀ r ∈ A, r.natAbs ∈ Finset.Icc 1 N := by
    intro r hr
    rw [hA, Finset.mem_filter, Finset.mem_Icc] at hr
    obtain ⟨⟨hrlo, hrhi⟩, hodd, hrne⟩ := hr
    rw [Finset.mem_Icc]
    refine ⟨?_, ?_⟩
    · exact Int.natAbs_pos.mpr hrne
    · rw [hN, Int.le_toNat (le_max_right Rz 0)]
      omega
  -- fibre bound: each level `n` is hit by at most the two integers `±n`
  have hfiber : ∀ n ∈ Finset.Icc 1 N,
      ∑ r ∈ A.filter (fun r => r.natAbs = n), (Real.sqrt |(r:ℝ)|)⁻¹
        ≤ 2 * (Real.sqrt ((n:ℝ)))⁻¹ := by
    intro n hn
    have hsub : A.filter (fun r => r.natAbs = n) ⊆ ({((n:ℤ)), -((n:ℤ))} : Finset ℤ) := by
      intro r hr
      rw [Finset.mem_filter] at hr
      have hkn : r.natAbs = n := hr.2
      rcases Int.natAbs_eq r with h | h
      · rw [h, hkn]; simp
      · rw [h, hkn]; simp
    have hcard : (A.filter (fun r => r.natAbs = n)).card ≤ 2 := by
      calc (A.filter (fun r => r.natAbs = n)).card ≤ ({((n:ℤ)), -((n:ℤ))} : Finset ℤ).card :=
            Finset.card_le_card hsub
        _ ≤ 2 := by
            have := Finset.card_insert_le (n:ℤ) ({-(n:ℤ)} : Finset ℤ)
            simpa using this
    calc ∑ r ∈ A.filter (fun r => r.natAbs = n), (Real.sqrt |(r:ℝ)|)⁻¹
        = ∑ r ∈ A.filter (fun r => r.natAbs = n), (Real.sqrt ((n:ℝ)))⁻¹ := by
            refine Finset.sum_congr rfl (fun r hr => ?_)
            have hrn : r.natAbs = n := (Finset.mem_filter.mp hr).2
            rw [← Int.cast_abs, ← Nat.cast_natAbs, hrn]
      _ = (A.filter (fun r => r.natAbs = n)).card • (Real.sqrt ((n:ℝ)))⁻¹ := Finset.sum_const _
      _ ≤ 2 • (Real.sqrt ((n:ℝ)))⁻¹ := by
            rw [nsmul_eq_mul, nsmul_eq_mul]
            exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by positivity)
      _ = 2 * (Real.sqrt ((n:ℝ)))⁻¹ := by norm_num [nsmul_eq_mul]
  calc ∑ r ∈ A, (Real.sqrt |(r:ℝ)|)⁻¹
      = ∑ n ∈ Finset.Icc 1 N, ∑ r ∈ A.filter (fun r => r.natAbs = n), (Real.sqrt |(r:ℝ)|)⁻¹ :=
          (Finset.sum_fiberwise_of_maps_to hmaps (fun r => (Real.sqrt |(r:ℝ)|)⁻¹)).symm
    _ ≤ ∑ n ∈ Finset.Icc 1 N, 2 * (Real.sqrt ((n:ℝ)))⁻¹ := Finset.sum_le_sum hfiber
    _ = 2 * ∑ n ∈ Finset.Icc 1 N, (Real.sqrt ((n:ℝ)))⁻¹ := by rw [Finset.mul_sum]
    _ ≤ 2 * (2 * Real.sqrt (N:ℝ)) := mul_le_mul_of_nonneg_left (sum_Icc_inv_sqrt_le N) (by norm_num)
    _ = 4 * Real.sqrt (N:ℝ) := by ring
    _ ≤ 4 * Real.sqrt (N:ℝ) + 8 := by linarith

end Work.FIArea7
