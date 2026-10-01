import Mathlib
import Submission.Work.ZeroDensity.Jutila.KappaMertensDefs

namespace Work.ZeroDensity.Jutila.LzDiffAux

open Finset
open Work.ZeroDensity.Jutila

/-! Self-contained proof of the dyadic bound `Σ_{m ≤ M} Dc d m / m ≤ Σ_{k ≤ log₂M} e^{-d√(k log 2)}`.
Each dyadic block `[2^k, 2^{k+1})` contributes at most `e^{-d√(k log 2)}`: the terms are
`≤ e^{-d√(k log 2)}` (because `m ≥ 2^k` gives `log m ≥ k log 2`) and their reciprocals sum to
`≤ 1`. -/

/-- The `k`-th dyadic block contributes at most the `k`-th dyadic sample. -/
lemma dyadic_block_le {d : ℝ} (hd : 0 < d) (k : ℕ) :
    (∑ m ∈ Finset.Icc (2 ^ k) (2 ^ (k + 1) - 1), Dc d m / (m : ℝ))
      ≤ Real.exp (-(d * Real.sqrt ((k : ℝ) * Real.log 2))) := by
  have hEpos : 0 < Real.exp (-(d * Real.sqrt ((k : ℝ) * Real.log 2))) := Real.exp_pos _
  have hcard : (Finset.Icc (2 ^ k) (2 ^ (k + 1) - 1)).card ≤ 2 ^ k := by
    rw [Nat.card_Icc]
    have h1 : 1 ≤ 2 ^ (k + 1) := Nat.one_le_two_pow
    rw [Nat.sub_add_cancel h1]
    have h2 : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [pow_succ]; ring
    omega
  have hterm : ∀ m ∈ Finset.Icc (2 ^ k) (2 ^ (k + 1) - 1),
      Dc d m / (m : ℝ) ≤ (1 / (2 : ℝ) ^ k) * Real.exp (-(d * Real.sqrt ((k : ℝ) * Real.log 2))) := by
    intro m hm
    obtain ⟨hm1, hm2⟩ := Finset.mem_Icc.mp hm
    have hmpos : 0 < m := lt_of_lt_of_le (by positivity : 0 < 2 ^ k) hm1
    have hmp : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hmpos
    have h2k : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
    have hmge : (2 : ℝ) ^ k ≤ (m : ℝ) := by
      have h : ((2 ^ k : ℕ) : ℝ) ≤ ((m : ℕ) : ℝ) := by exact_mod_cast hm1
      simpa [Nat.cast_pow] using h
    have hlog : (k : ℝ) * Real.log 2 ≤ Real.log (m : ℝ) := by
      have h := Real.log_le_log (by positivity : (0:ℝ) < (2:ℝ)^k) hmge
      rw [Real.log_pow] at h
      exact h
    have hDc : Dc d m ≤ Real.exp (-(d * Real.sqrt ((k : ℝ) * Real.log 2))) := by
      rw [Dc]
      apply Real.exp_le_exp.mpr
      exact neg_le_neg (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hlog) hd.le)
    have hinv : 1 / (m : ℝ) ≤ 1 / (2 : ℝ) ^ k := one_div_le_one_div_of_le h2k hmge
    calc Dc d m / (m : ℝ) = Dc d m * (1 / (m : ℝ)) := by ring
      _ ≤ Real.exp (-(d * Real.sqrt ((k : ℝ) * Real.log 2))) * (1 / (2 : ℝ) ^ k) :=
          mul_le_mul hDc hinv (by positivity) (le_of_lt hEpos)
      _ = (1 / (2 : ℝ) ^ k) * Real.exp (-(d * Real.sqrt ((k : ℝ) * Real.log 2))) := by ring
  calc (∑ m ∈ Finset.Icc (2 ^ k) (2 ^ (k + 1) - 1), Dc d m / (m : ℝ))
      ≤ ∑ _m ∈ Finset.Icc (2 ^ k) (2 ^ (k + 1) - 1),
          (1 / (2 : ℝ) ^ k) * Real.exp (-(d * Real.sqrt ((k : ℝ) * Real.log 2))) :=
        Finset.sum_le_sum hterm
    _ = ((Finset.Icc (2 ^ k) (2 ^ (k + 1) - 1)).card : ℝ)
          * ((1 / (2 : ℝ) ^ k) * Real.exp (-(d * Real.sqrt ((k : ℝ) * Real.log 2)))) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((2 : ℝ) ^ k) * ((1 / (2 : ℝ) ^ k) * Real.exp (-(d * Real.sqrt ((k : ℝ) * Real.log 2)))) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        have := hcard
        have : ((Finset.Icc (2 ^ k) (2 ^ (k + 1) - 1)).card : ℝ) ≤ ((2 : ℝ) ^ k) := by
          exact_mod_cast this
        exact this
    _ = Real.exp (-(d * Real.sqrt ((k : ℝ) * Real.log 2))) := by
        field_simp

/-- The dyadic sample sum dominates `Σ_{m ≤ M} Dc d m / m`. -/
theorem DcInvSumDyadic {d : ℝ} (hd : 0 < d) (M : ℕ) :
    (∑ m ∈ Finset.Icc 1 M, Dc d m / (m : ℝ))
      ≤ ∑ k ∈ Finset.range (Nat.log 2 M + 1),
          Real.exp (-(d * Real.sqrt ((k : ℝ) * Real.log 2))) := by
  have hmap : ∀ m ∈ Finset.Icc 1 M, Nat.log 2 m ∈ Finset.range (Nat.log 2 M + 1) := by
    intro m hm
    rw [Finset.mem_range]
    have hmM : m ≤ M := (Finset.mem_Icc.mp hm).2
    exact Nat.lt_succ_of_le (Nat.log_mono_right hmM)
  have hfib := Finset.sum_fiberwise_of_maps_to hmap (f := fun m : ℕ => Dc d m / (m : ℝ))
  rw [← hfib]
  apply Finset.sum_le_sum
  intro k _
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_) (dyadic_block_le hd k)
  · intro m hm
    rw [Finset.mem_filter] at hm
    obtain ⟨hmI, hmlog⟩ := hm
    obtain ⟨hm1, hmM⟩ := Finset.mem_Icc.mp hmI
    refine Finset.mem_Icc.mpr ⟨?_, ?_⟩
    · rw [← hmlog]
      exact Nat.pow_log_le_self 2 (by omega)
    · have h := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) m
      rw [hmlog] at h
      omega
  · intro x hx _
    have hx1 : 1 ≤ x := le_trans Nat.one_le_two_pow (Finset.mem_Icc.mp hx).1
    have hxpos : (0 : ℝ) < (x : ℝ) := by exact_mod_cast hx1
    exact div_nonneg (le_of_lt (Real.exp_pos _)) (le_of_lt hxpos)

end Work.ZeroDensity.Jutila.LzDiffAux
