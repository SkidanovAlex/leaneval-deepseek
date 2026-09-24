import Mathlib
import Submission.Work.GM.Energy.EnergyCore.Setup2

/-!
# The sum `Σ_{d ∈ [A, 2N]} ⌈N/d⌉²`

We bound the second moment of the "scale" `Md N d = ⌈N/d⌉` over the range
`d ∈ [A, 2N]`, where `A ≥ N²/N^{6/5} = N^{4/5}`.  The estimate is the
elementary one used in §11 of Guth–Maynard:

* for `1 ≤ d ≤ 2N` one has `⌈N/d⌉² ≤ 4N²/d²` (for `d ≤ N` this is
  `⌈N/d⌉ ≤ N/d + 1 ≤ 2N/d`, and for `d > N` the ceiling is `1` while
  `4N²/d² ≥ 1`);
* the divergent-free harmonic-type bound `Σ_{d=A}^{M} 1/d² ≤ 2/A`, obtained by
  telescoping `1/d² ≤ 1/(d(d-1)) = 1/(d-1) - 1/d`.

Hence `Σ ≤ 4N² · 2/A = 8N²/A ≤ 8 N^{6/5} ≤ 20 N^{6/5}`.
-/

namespace Work.GM.Energy.EnergyCore

open Finset
open scoped BigOperators

/-- Pointwise bound: for `1 ≤ d ≤ 2N`, `⌈N/d⌉² ≤ 4 N² / d²`. -/
private lemma Md_sq_le (N d : ℕ) (hN : 1 ≤ N) (hd1 : 1 ≤ d) (hd2 : d ≤ 2 * N) :
    ((Md N d : ℕ) : ℝ) ^ 2 ≤ 4 * (N : ℝ) ^ 2 * (((d : ℝ)) ^ 2)⁻¹ := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    have : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    linarith
  have hdpos : (0 : ℝ) < (d : ℝ) := by
    have : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd1
    linarith
  by_cases hdN : d ≤ N
  · -- `d ≤ N`, so `N/d ≥ 1` and `⌈N/d⌉ ≤ N/d + 1 ≤ 2 N/d`.
    have hx1 : (1 : ℝ) ≤ (N : ℝ) / (d : ℝ) := by
      rw [le_div_iff₀ hdpos]
      simpa using (show (d : ℝ) ≤ (N : ℝ) by exact_mod_cast hdN)
    have hMd : (Md N d : ℝ) ≤ 2 * ((N : ℝ) / (d : ℝ)) := by
      have h := Md_le_div_add_one N d
      linarith
    have hsq : (Md N d : ℝ) ^ 2 ≤ (2 * ((N : ℝ) / (d : ℝ))) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hMd 2
    have hconv : (2 * ((N : ℝ) / (d : ℝ))) ^ 2 = 4 * (N : ℝ) ^ 2 * (((d : ℝ)) ^ 2)⁻¹ := by
      rw [mul_pow, div_pow, div_eq_mul_inv]
      ring
    calc (Md N d : ℝ) ^ 2 ≤ (2 * ((N : ℝ) / (d : ℝ))) ^ 2 := hsq
      _ = 4 * (N : ℝ) ^ 2 * (((d : ℝ)) ^ 2)⁻¹ := hconv
  · -- `d > N`, so `⌈N/d⌉ = 1` and `d ≤ 2N` gives `4N²/d² ≥ 1`.
    have hdNgt : N < d := by omega
    have hx0 : (0 : ℝ) < (N : ℝ) / (d : ℝ) := div_pos hNpos hdpos
    have hx1 : (N : ℝ) / (d : ℝ) ≤ 1 := by
      rw [div_le_one hdpos]
      exact_mod_cast (le_of_lt hdNgt)
    have hMd1 : Md N d = 1 := by
      rw [Md]
      exact (Nat.ceil_eq_iff (by norm_num : (1 : ℕ) ≠ 0)).mpr
        ⟨by simpa using hx0, by simpa using hx1⟩
    rw [hMd1]
    norm_num
    rw [← div_eq_mul_inv]
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < (d : ℝ) ^ 2)]
    have hd2' : (d : ℝ) ≤ 2 * (N : ℝ) := by exact_mod_cast hd2
    have hpow : (d : ℝ) ^ 2 ≤ (2 * (N : ℝ)) ^ 2 := pow_le_pow_left₀ (by positivity) hd2' 2
    nlinarith [hpow]

/-- `Σ_{d=A}^{M} 1/d² ≤ 2/A` for `A ≥ 1`. -/
private lemma sum_Icc_inv_sq_le (A M : ℕ) (hA : 1 ≤ A) :
    ∑ i ∈ Finset.Icc A M, (((i : ℕ) : ℝ) ^ 2)⁻¹ ≤ 2 * (A : ℝ)⁻¹ := by
  by_cases hMA : M < A
  · rw [Finset.Icc_eq_empty (by omega : ¬ A ≤ M)]
    simp
  · have hAM : A ≤ M := by omega
    rw [Finset.Icc_eq_cons_Ioc hAM, Finset.sum_cons]
    have hAne : A ≠ 0 := by omega
    have hIoc := sum_Ioc_inv_sq_le_sub (α := ℝ) (k := A) (n := M) hAne hAM
    have hApos : (0 : ℝ) < (A : ℝ) := by
      have : (0 : ℕ) < A := by omega
      exact_mod_cast this
    have hA1 : (1 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA
    have hAsq : ((A : ℝ) ^ 2)⁻¹ ≤ (A : ℝ)⁻¹ :=
      (inv_le_inv₀ (by positivity : (0 : ℝ) < (A : ℝ) ^ 2) hApos).mpr (by nlinarith)
    have hkey : ((A : ℝ) ^ 2)⁻¹ + ((A : ℝ)⁻¹ - (M : ℝ)⁻¹) ≤ 2 * (A : ℝ)⁻¹ := by
      have hMnn : (0 : ℝ) ≤ (M : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg M)
      linarith
    linarith

/-- `Σ_{d ∈ [A, 2N]} ⌈N/d⌉² ≤ 20 N^{6/5}`, for `A ≥ N²/N^{6/5} = N^{4/5}`
(so that `N²/A ≤ N^{6/5}`). -/
theorem sum_Md_sq_le (N A : ℕ) (hN : 1 ≤ N) (hA : 1 ≤ A)
    (hD : (N : ℝ) ^ 2 / Submission.LargeValues.M N ≤ (A : ℝ)) :
    ∑ d ∈ Finset.Icc A (2 * N), (Work.GM.Energy.EnergyCore.Md N d : ℝ) ^ 2
      ≤ 20 * Submission.LargeValues.M N := by
  have hMNpos : 0 < Submission.LargeValues.M N := lt_of_lt_of_le zero_lt_one (one_le_MN hN)
  have hApos : (0 : ℝ) < (A : ℝ) := by
    have : (0 : ℕ) < A := by omega
    exact_mod_cast this
  have hstep1 : ∑ d ∈ Finset.Icc A (2 * N), (Md N d : ℝ) ^ 2
      ≤ 4 * (N : ℝ) ^ 2 * ∑ d ∈ Finset.Icc A (2 * N), (((d : ℕ) : ℝ) ^ 2)⁻¹ := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro d hd
    exact Md_sq_le N d hN (le_trans hA (Finset.mem_Icc.mp hd).1) (Finset.mem_Icc.mp hd).2
  have hstep2 : ∑ d ∈ Finset.Icc A (2 * N), (((d : ℕ) : ℝ) ^ 2)⁻¹ ≤ 2 * (A : ℝ)⁻¹ :=
    sum_Icc_inv_sq_le A (2 * N) hA
  have hbound : ∑ d ∈ Finset.Icc A (2 * N), (Md N d : ℝ) ^ 2
      ≤ 8 * ((N : ℝ) ^ 2 * (A : ℝ)⁻¹) := by
    calc ∑ d ∈ Finset.Icc A (2 * N), (Md N d : ℝ) ^ 2
        ≤ 4 * (N : ℝ) ^ 2 * ∑ d ∈ Finset.Icc A (2 * N), (((d : ℕ) : ℝ) ^ 2)⁻¹ := hstep1
      _ ≤ 4 * (N : ℝ) ^ 2 * (2 * (A : ℝ)⁻¹) := by
            apply mul_le_mul_of_nonneg_left hstep2; positivity
      _ = 8 * ((N : ℝ) ^ 2 * (A : ℝ)⁻¹) := by ring
  have hNA : (N : ℝ) ^ 2 * (A : ℝ)⁻¹ ≤ Submission.LargeValues.M N := by
    rw [← div_eq_mul_inv, div_le_iff₀ hApos]
    rw [div_le_iff₀ hMNpos] at hD
    linarith
  have h1 : 8 * ((N : ℝ) ^ 2 * (A : ℝ)⁻¹) ≤ 8 * Submission.LargeValues.M N :=
    mul_le_mul_of_nonneg_left hNA (by norm_num)
  have h2 : 8 * Submission.LargeValues.M N ≤ 20 * Submission.LargeValues.M N := by linarith
  linarith [hbound, h1, h2]

end Work.GM.Energy.EnergyCore
