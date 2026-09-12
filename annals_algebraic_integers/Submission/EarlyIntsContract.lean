import Submission.EarlyAssembly

/-!
# Absorption: eventual per-n data ⇒ `Contracts.EarlyIntsContract`

`EarlyAssembly.early_ints_eventual` gives, for every `B > 0`, a `C > 3` with
`EarlyPolynomialData B C n` for all SUFFICIENTLY large `n` with
`2 ≤ n − mFloor B n`.  This module converts it to the universal form of the
contract: some `C₁ > 3` with the data for EVERY `n > C₁` with `2 ≤ n − m`.

Two facts are needed:
* monotonicity of the data in the constant: `EarlyPolynomialData B C n` with
  `C ≤ C₁` implies `EarlyPolynomialData B C₁ n` (the only `C`-dependent
  clauses are the two inequalities `… ≥ n^{-C}κ^m` and `… ≤ n^Cκ^m`, and for
  `n ≥ 1` we have `n^{-C₁} ≤ n^{-C}` and `n^C ≤ n^{C₁}`);
* thresholds: taking `C₁ = max C N₀ 4 + 1`, every `n > C₁` satisfies the
  eventual threshold `N₀ ≤ n`.
-/

noncomputable section

open Filter
open scoped Real BigOperators
open Polynomial

namespace Submission.EarlyAssembly

open Submission.Contracts

/-- Data at a smaller constant implies data at a larger constant. -/
lemma early_data_mono {B C C1 Cm : ℝ} (hCC1 : C ≤ C1) {n : ℕ} (hn : 1 ≤ n)
    (h : EarlyPolynomialData B C Cm n) : EarlyPolynomialData B C1 Cm n := by
  classical
  let m := mFloor B n
  rcases h with ⟨P, hPmon, hPdeg, hPbig⟩
  rcases hPbig with ⟨hPαxy, hzeven, hPnorm⟩
  refine ⟨P, hPmon, hPdeg, ?_, hzeven, ?_⟩
  · rcases hPαxy with ⟨α, x, y, hfac, hαab, hαmono, hxyIcc, hxy, hxαy, hsep, hwv, hαmean⟩
    refine ⟨α, x, y, hfac, hαab, hαmono, hxyIcc, hxy, hxαy, hsep, ?_, hαmean⟩
    intro i
    rcases (hwv i) with ⟨hwx, hwy, hpx, hpy⟩
    refine ⟨?_, ?_, hpx, hpy⟩
    · have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      have hnegpow : (n : ℝ) ^ (-C1) ≤ (n : ℝ) ^ (-C) := by
        rw [Real.rpow_def_of_pos (lt_of_lt_of_le zero_lt_one hnR),
          Real.rpow_def_of_pos (lt_of_lt_of_le zero_lt_one hnR)]
        exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (by linarith)
          (Real.log_nonneg hnR))
      have hκm0 : 0 ≤ kappa ^ mFloor B n := pow_nonneg (le_of_lt (lt_trans zero_lt_one kappa_gt_one)) _
      exact le_trans (mul_le_mul_of_nonneg_right hnegpow hκm0) hwx
    · have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      have hnegpow : (n : ℝ) ^ (-C1) ≤ (n : ℝ) ^ (-C) := by
        rw [Real.rpow_def_of_pos (lt_of_lt_of_le zero_lt_one hnR),
          Real.rpow_def_of_pos (lt_of_lt_of_le zero_lt_one hnR)]
        exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (by linarith)
          (Real.log_nonneg hnR))
      have hκm0 : 0 ≤ kappa ^ mFloor B n := pow_nonneg (le_of_lt (lt_trans zero_lt_one kappa_gt_one)) _
      exact le_trans (mul_le_mul_of_nonneg_right hnegpow hκm0) hwy
  · have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hpow : (n : ℝ) ^ C ≤ (n : ℝ) ^ C1 := by
      rw [Real.rpow_def_of_pos (lt_of_lt_of_le zero_lt_one hnR),
          Real.rpow_def_of_pos (lt_of_lt_of_le zero_lt_one hnR)]
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hCC1 (Real.log_nonneg hnR))
    have hkappa0 : 0 ≤ kappa ^ mFloor B n := pow_nonneg (le_of_lt (lt_trans zero_lt_one kappa_gt_one)) _
    exact le_trans hPnorm (mul_le_mul_of_nonneg_right hpow hkappa0)

/-- Contract 3: Proposition early_ints_better (universal form). -/
theorem early_ints_contract : EarlyIntsContract := by
  intro B hB
  rcases early_ints_eventual B hB with ⟨C, Cm, hC3, hCm0, hev⟩
  rcases (Filter.eventually_atTop.1 hev) with ⟨N0, hN0⟩
  let C1 : ℝ := max C (max (N0 : ℝ) 4) + 1
  have hC1gt3 : 3 < C1 := by
    dsimp [C1]
    have h4 : (4 : ℝ) ≤ max C (max (N0 : ℝ) 4) := by
      exact le_trans (le_max_right (N0 : ℝ) (4 : ℝ)) (le_max_right C (max (N0 : ℝ) 4))
    linarith
  refine ⟨C1, Cm, hC1gt3, hCm0, ?_⟩
  intro n hn hnm
  have hC1n : C1 < (n : ℝ) := hn
  have hn1 : 1 ≤ n := by
    have h3n : 3 < n := by
      have hnRgt : (3 : ℝ) < (n : ℝ) := lt_trans hC1gt3 hC1n
      exact_mod_cast hnRgt
    omega
  have hCC1 : C ≤ C1 := by
    dsimp [C1]
    have h1 : C ≤ max C (max (N0 : ℝ) 4) := le_max_left C (max (N0 : ℝ) 4)
    have h2 : max C (max (N0 : ℝ) 4) ≤ max C (max (N0 : ℝ) 4) + 1 := by linarith
    exact le_trans h1 h2
  have hN0leC1 : (N0 : ℝ) ≤ C1 := by
    dsimp [C1]
    have h1 : (N0 : ℝ) ≤ max C (max (N0 : ℝ) 4) :=
      le_trans (le_max_left (N0 : ℝ) 4) (le_max_right C (max (N0 : ℝ) 4))
    have h2 : max C (max (N0 : ℝ) 4) ≤ max C (max (N0 : ℝ) 4) + 1 := by linarith
    exact le_trans h1 h2
  have hge' : (N0 : ℝ) < (n : ℝ) := lt_of_le_of_lt hN0leC1 hC1n
  have hge : N0 ≤ n := by
    by_contra hgec
    have hnlt : (n : ℝ) < (N0 : ℝ) := by
      exact_mod_cast (Nat.lt_of_not_ge hgec)
    linarith
  have hdata := hN0 n hge hnm
  exact early_data_mono (B := B) (C := C) (C1 := C1) (Cm := Cm) hCC1 hn1 hdata

end Submission.EarlyAssembly
