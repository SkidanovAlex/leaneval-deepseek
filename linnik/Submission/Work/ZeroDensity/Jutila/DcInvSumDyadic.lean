import Mathlib
import Submission.Work.ZeroDensity.Jutila.KappaMertensDefs

namespace Work.ZeroDensity.Jutila

open Finset

/-- **Harmonic mass of a `Nat.log 2`-dyadic fiber.** For every `M k : ℕ`,
`Σ_{m ∈ [1,M], Nat.log 2 m = k} 1/m ≤ 1`. -/
lemma harmonicFiberMassNatLog (M k : ℕ) :
    (∑ m ∈ (Finset.Icc 1 M).filter (fun m => Nat.log 2 m = k), (1 : ℝ) / (m : ℝ)) ≤ 1 := by
  have hsub : (Finset.Icc 1 M).filter (fun m => Nat.log 2 m = k)
      ⊆ Finset.Icc (2 ^ k : ℕ) (2 ^ (k + 1) - 1) := by
    intro m hm
    rw [Finset.mem_filter, Finset.mem_Icc] at hm
    obtain ⟨⟨hm1, _⟩, hlog⟩ := hm
    rw [Finset.mem_Icc]
    have hm0 : m ≠ 0 := by omega
    refine ⟨?_, ?_⟩
    · have h := Nat.pow_log_le_self 2 hm0
      rwa [hlog] at h
    · have h := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) m
      rw [hlog] at h
      have h' : m < 2 ^ (k + 1) := by simpa [Nat.succ_eq_add_one] using h
      omega
  have hterm : ∀ m ∈ Finset.Icc (2 ^ k : ℕ) (2 ^ (k + 1) - 1),
      (1 : ℝ) / (m : ℝ) ≤ 1 / (2 ^ k : ℝ) := by
    intro m hm
    rw [Finset.mem_Icc] at hm
    have hpos : (0 : ℝ) < (2 ^ k : ℝ) := by positivity
    have hle : (2 ^ k : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm.1
    exact one_div_le_one_div_of_le hpos hle
  have hcard : (Finset.Icc (2 ^ k : ℕ) (2 ^ (k + 1) - 1)).card = 2 ^ k := by
    rw [Nat.card_Icc]
    have h1 : 2 ^ (k + 1) - 1 + 1 = 2 ^ (k + 1) := by
      have hpos : 0 < (2 : ℕ) ^ (k + 1) := pow_pos (by norm_num) _
      omega
    rw [h1, pow_succ]
    omega
  have hk : (((2 : ℕ) ^ k : ℕ) : ℝ) = ((2 : ℝ) ^ k) := by
    rw [Nat.cast_pow]; norm_num
  calc (∑ m ∈ (Finset.Icc 1 M).filter (fun m => Nat.log 2 m = k), (1 : ℝ) / (m : ℝ))
      ≤ ∑ m ∈ Finset.Icc (2 ^ k : ℕ) (2 ^ (k + 1) - 1), (1 : ℝ) / (m : ℝ) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hsub
        intro i _ _
        exact div_nonneg zero_le_one (Nat.cast_nonneg i)
    _ ≤ ∑ m ∈ Finset.Icc (2 ^ k : ℕ) (2 ^ (k + 1) - 1), (1 : ℝ) / (2 ^ k : ℝ) :=
        Finset.sum_le_sum hterm
    _ = ((Finset.Icc (2 ^ k : ℕ) (2 ^ (k + 1) - 1)).card : ℝ) * (1 / (2 ^ k : ℝ)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ = 1 := by
        rw [hcard, hk, mul_one_div]
        exact div_self (ne_of_gt (pow_pos (by norm_num : (0 : ℝ) < 2) k))

/-- **Pointwise dyadic decay bound.** If `1 ≤ m` and `Nat.log 2 m = k` then
`Dc d m ≤ exp(−d√(k log 2))`. -/
lemma Dc_le_exp_log2 {d : ℝ} (hd : 0 < d) {m k : ℕ} (hm1 : 1 ≤ m)
    (hlog : Nat.log 2 m = k) :
    Dc d m ≤ Real.exp (-(d * Real.sqrt ((k : ℝ) * Real.log 2))) := by
  rw [Dc, Real.exp_le_exp, neg_le_neg_iff]
  refine mul_le_mul_of_nonneg_left ?_ hd.le
  apply Real.sqrt_le_sqrt
  rw [← hlog]
  have hm0 : m ≠ 0 := by omega
  have hle : (2 : ℝ) ^ Nat.log 2 m ≤ (m : ℝ) := by
    have h := Nat.pow_log_le_self 2 hm0
    have hcast : (((2 : ℕ) ^ Nat.log 2 m : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast h
    simpa using hcast
  have hpos : (0 : ℝ) < (2 : ℝ) ^ Nat.log 2 m := by positivity
  calc ((Nat.log 2 m : ℕ) : ℝ) * Real.log 2
      = Real.log ((2 : ℝ) ^ Nat.log 2 m) := (Real.log_pow 2 (Nat.log 2 m)).symm
    _ ≤ Real.log (m : ℝ) := Real.log_le_log hpos hle

theorem DcInvSumDyadic {d : ℝ} (hd : 0 < d) (M : ℕ) :
    (∑ m ∈ Finset.Icc 1 M, Dc d m / (m : ℝ))
      ≤ ∑ k ∈ Finset.range (Nat.log 2 M + 1), Real.exp (-(d * Real.sqrt ((k : ℝ) * Real.log 2))) := by
  have hmap : ∀ m ∈ Finset.Icc 1 M, Nat.log 2 m ∈ Finset.range (Nat.log 2 M + 1) := by
    intro m hm
    rw [Finset.mem_range]
    exact Nat.lt_succ_of_le (Nat.log_mono_right (Finset.mem_Icc.mp hm).2)
  rw [← Finset.sum_fiberwise_of_maps_to hmap (fun m => Dc d m / (m : ℝ))]
  apply Finset.sum_le_sum
  intro k hk
  have hpoint : ∀ m ∈ (Finset.Icc 1 M).filter (fun m => Nat.log 2 m = k),
      Dc d m / (m : ℝ)
        ≤ Real.exp (-(d * Real.sqrt ((k : ℝ) * Real.log 2))) * (1 / (m : ℝ)) := by
    intro m hm
    rw [Finset.mem_filter, Finset.mem_Icc] at hm
    obtain ⟨⟨hm1, _⟩, hlog⟩ := hm
    have hDc := Dc_le_exp_log2 hd hm1 hlog
    have hdiv : Dc d m / (m : ℝ) = Dc d m * (1 / (m : ℝ)) := div_eq_mul_one_div _ _
    rw [hdiv]
    exact mul_le_mul_of_nonneg_right hDc (div_nonneg zero_le_one (Nat.cast_nonneg m))
  calc (∑ m ∈ (Finset.Icc 1 M).filter (fun m => Nat.log 2 m = k), Dc d m / (m : ℝ))
      ≤ ∑ m ∈ (Finset.Icc 1 M).filter (fun m => Nat.log 2 m = k),
          Real.exp (-(d * Real.sqrt ((k : ℝ) * Real.log 2))) * (1 / (m : ℝ)) :=
        Finset.sum_le_sum hpoint
    _ = Real.exp (-(d * Real.sqrt ((k : ℝ) * Real.log 2))) *
          ∑ m ∈ (Finset.Icc 1 M).filter (fun m => Nat.log 2 m = k), (1 / (m : ℝ)) := by
        rw [Finset.mul_sum]
    _ ≤ Real.exp (-(d * Real.sqrt ((k : ℝ) * Real.log 2))) * 1 := by
        apply mul_le_mul_of_nonneg_left (harmonicFiberMassNatLog M k)
        exact (Real.exp_pos _).le
    _ = Real.exp (-(d * Real.sqrt ((k : ℝ) * Real.log 2))) := mul_one _

end Work.ZeroDensity.Jutila
