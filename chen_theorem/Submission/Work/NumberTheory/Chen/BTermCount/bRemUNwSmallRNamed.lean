import Mathlib
import Submission.Work.NumberTheory.Chen.BTermCount.BLodSmallRSum
import Submission.Work.NumberTheory.Chen.BTermCount.primeCharSumBound
import Submission.Work.NumberTheory.Chen.BTermCount.sumInvTotientLogBound

open Finset Filter
open scoped BigOperators

namespace Work.NumberTheory.Chen.BTermCount

attribute [local instance] Classical.propDecidable

/-!
# The unweighted small-conductor sum

`BLodSmallRSum` proves the bound for the `3^{ω}`-weighted small-conductor double sum

  `Σ_{t ≤ D} (3^{ω t}/φ t) Σ_{2 ≤ r ≤ R₀} (3^{ω r}/φ r) · bProdCharSumDivSum x M Y t r`.

Here we deduce the *unweighted* version (weights `1/φ t`, `1/φ r`), which is the statement
actually consumed by the unweighted reduction of the level of distribution.  Since
`1 ≤ 3^{ω n}` and every summand is nonnegative, the unweighted sum is at most the weighted
one, and the extra factor `(log x)^{2C'+20} log log x` of the weighted bound is absorbed by
choosing the level exponent `A' = A + 100` and the conductor exponent `C' = 1`.
-/

/-- **The unweighted sum is at most the `3^{ω}`-weighted one.**  Pointwise
`(φ n)⁻¹ ≤ 3^{ω n}/φ n`, and the concentration sums are nonnegative. -/
lemma bls_unw_le_wtd (x M Y D R₀ : ℕ) :
    (∑ t ∈ Finset.Icc 1 D, (Nat.totient t : ℝ)⁻¹ *
      ∑ r ∈ (Finset.Icc 1 D).filter (fun r => 2 ≤ r ∧ r ≤ R₀),
        (Nat.totient r : ℝ)⁻¹ * bProdCharSumDivSum x M Y t r)
    ≤ ∑ t ∈ Finset.Icc 1 D, ((3 : ℝ) ^ (t.primeFactors.card) / (Nat.totient t : ℝ)) *
      ∑ r ∈ (Finset.Icc 1 D).filter (fun r => 2 ≤ r ∧ r ≤ R₀),
        ((3 : ℝ) ^ (r.primeFactors.card) / (Nat.totient r : ℝ)) *
          bProdCharSumDivSum x M Y t r := by
  refine Finset.sum_le_sum (fun t ht => ?_)
  have ht1 : 1 ≤ t := (Finset.mem_Icc.mp ht).1
  have hφtpos : (0 : ℝ) < (Nat.totient t : ℝ) := by
    exact_mod_cast (Nat.totient_pos.mpr (by omega : 0 < t))
  have hcoef : (Nat.totient t : ℝ)⁻¹
      ≤ (3 : ℝ) ^ (t.primeFactors.card) / (Nat.totient t : ℝ) := by
    rw [inv_eq_one_div, div_le_div_iff_of_pos_right hφtpos]
    exact one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 3)
  have hinner : (∑ r ∈ (Finset.Icc 1 D).filter (fun r => 2 ≤ r ∧ r ≤ R₀),
        (Nat.totient r : ℝ)⁻¹ * bProdCharSumDivSum x M Y t r)
      ≤ ∑ r ∈ (Finset.Icc 1 D).filter (fun r => 2 ≤ r ∧ r ≤ R₀),
        ((3 : ℝ) ^ (r.primeFactors.card) / (Nat.totient r : ℝ)) *
          bProdCharSumDivSum x M Y t r := by
    refine Finset.sum_le_sum (fun r hr => ?_)
    have hr2 : 2 ≤ r := (Finset.mem_filter.mp hr).2.1
    have hφrpos : (0 : ℝ) < (Nat.totient r : ℝ) := by
      exact_mod_cast (Nat.totient_pos.mpr (by omega : 0 < r))
    have hcoefr : (Nat.totient r : ℝ)⁻¹
        ≤ (3 : ℝ) ^ (r.primeFactors.card) / (Nat.totient r : ℝ) := by
      rw [inv_eq_one_div, div_le_div_iff_of_pos_right hφrpos]
      exact one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 3)
    exact mul_le_mul_of_nonneg_right hcoefr (bProdCharSumDivSum_nonneg x M Y t r)
  have hinnernn : 0 ≤ ∑ r ∈ (Finset.Icc 1 D).filter (fun r => 2 ≤ r ∧ r ≤ R₀),
        (Nat.totient r : ℝ)⁻¹ * bProdCharSumDivSum x M Y t r :=
    Finset.sum_nonneg (fun r _ =>
      mul_nonneg (by positivity) (bProdCharSumDivSum_nonneg x M Y t r))
  have hcoefnn : 0 ≤ (3 : ℝ) ^ (t.primeFactors.card) / (Nat.totient t : ℝ) :=
    div_nonneg (by positivity) (by positivity)
  exact mul_le_mul hcoef hinner hinnernn hcoefnn

/-- **Absorption of the weighted-bound overhead.**  For `C > 0` and `A > 0`, eventually

  `C x (log x + 2)^{22} log log x / (log x)^{A+100} ≤ x / (log x)^A`.

The exponent gap `100` dwarfs the polynomial overhead `22`. -/
lemma bls_absorb (A C : ℝ) (hA : 0 < A) (hC : 0 < C) :
    ∀ᶠ x : ℕ in Filter.atTop,
      C * (x : ℝ) * (Real.log (x : ℝ) + 2) ^ (2 * (1 : ℝ) + 20) *
          Real.log (Real.log (x : ℝ) + 3) / (Real.log (x : ℝ)) ^ (A + ((100 : ℕ) : ℝ))
        ≤ (x : ℝ) / (Real.log (x : ℝ)) ^ A := by
  have hlogtop : Filter.Tendsto (fun x : ℕ => Real.log (x : ℝ)) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hK : ∀ᶠ x : ℕ in Filter.atTop,
      max 2 (C * 2 ^ 23) ≤ Real.log (x : ℝ) :=
    hlogtop.eventually (Filter.eventually_ge_atTop (max 2 (C * 2 ^ 23)))
  filter_upwards [hK, Filter.eventually_ge_atTop (1 : ℕ)] with x hKx hx1
  set L : ℝ := Real.log (x : ℝ) with hLdef
  rw [show (2 * (1 : ℝ) + 20) = ((22 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hL2 : 2 ≤ L := le_trans (le_max_left _ _) hKx
  have hLK : C * 2 ^ 23 ≤ L := le_trans (le_max_right _ _) hKx
  have hLpos : 0 < L := by linarith
  have hxpos : (0 : ℝ) < (x : ℝ) := by
    exact_mod_cast (by omega : 0 < x)
  have hcore : C * (L + 2) ^ (22 : ℕ) * Real.log (L + 3) ≤ L ^ (100 : ℕ) := by
    have hlog3 : Real.log (L + 3) ≤ L + 2 := by
      have h := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < L + 3)
      linarith
    have hL2nn : (0 : ℝ) ≤ L + 2 := by linarith
    have hstep1 : (L + 2) ^ (22 : ℕ) * Real.log (L + 3)
        ≤ (L + 2) ^ (22 : ℕ) * (L + 2) :=
      mul_le_mul_of_nonneg_left hlog3 (by positivity)
    have hstep2 : (L + 2) ^ (23 : ℕ) ≤ (2 * L) ^ (23 : ℕ) :=
      pow_le_pow_left₀ hL2nn (by linarith) 23
    have hC23 : C * 2 ^ (23 : ℕ) ≤ L ^ (77 : ℕ) := by
      have h1 : L ≤ L ^ (77 : ℕ) := by
        simpa using pow_le_pow_right₀ (show (1 : ℝ) ≤ L by linarith) (show 1 ≤ 77 by norm_num)
      exact le_trans hLK h1
    have hL23nn : (0 : ℝ) ≤ L ^ (23 : ℕ) := by positivity
    calc C * (L + 2) ^ (22 : ℕ) * Real.log (L + 3)
        = C * ((L + 2) ^ (22 : ℕ) * Real.log (L + 3)) := by ring
      _ ≤ C * ((L + 2) ^ (22 : ℕ) * (L + 2)) := mul_le_mul_of_nonneg_left hstep1 hC.le
      _ = C * (L + 2) ^ (23 : ℕ) := by ring
      _ ≤ C * (2 * L) ^ (23 : ℕ) := mul_le_mul_of_nonneg_left hstep2 hC.le
      _ = C * (2 ^ (23 : ℕ) * L ^ (23 : ℕ)) := by ring
      _ = (C * 2 ^ (23 : ℕ)) * L ^ (23 : ℕ) := by ring
      _ ≤ L ^ (77 : ℕ) * L ^ (23 : ℕ) := mul_le_mul_of_nonneg_right hC23 hL23nn
      _ = L ^ (100 : ℕ) := by rw [← pow_add]
  have hLpow : L ^ (A + ((100 : ℕ) : ℝ)) = L ^ A * L ^ ((100 : ℕ) : ℝ) :=
    Real.rpow_add hLpos A _
  have h100 : L ^ ((100 : ℕ) : ℝ) = L ^ (100 : ℕ) := Real.rpow_natCast L 100
  have hTpos : 0 < L ^ (A + ((100 : ℕ) : ℝ)) := Real.rpow_pos_of_pos hLpos _
  calc C * (x : ℝ) * (L + 2) ^ (22 : ℕ) * Real.log (L + 3) / L ^ (A + ((100 : ℕ) : ℝ))
      = (x : ℝ) * (C * (L + 2) ^ (22 : ℕ) * Real.log (L + 3)) /
          L ^ (A + ((100 : ℕ) : ℝ)) := by ring
    _ ≤ (x : ℝ) * L ^ (100 : ℕ) / L ^ (A + ((100 : ℕ) : ℝ)) := by
        refine div_le_div_of_nonneg_right ?_ hTpos.le
        exact mul_le_mul_of_nonneg_left hcore hxpos.le
    _ = (x : ℝ) / L ^ A := by
        rw [hLpow, ← h100]
        exact mul_div_mul_right _ _ (ne_of_gt (Real.rpow_pos_of_pos hLpos ((100 : ℕ) : ℝ)))

theorem bRemUNwSmallRNamed (A : ℝ) (hA : 0 < A) :
    ∃ C' : ℝ, 0 < C' ∧ ∀ᶠ x : ℕ in Filter.atTop,
      ∀ (M Y D R₀ : ℕ), (x : ℝ) ^ ((1 : ℝ) / 14) ≤ M → 2 ≤ D →
        R₀ ≤ ⌊(Real.log (x : ℝ)) ^ C'⌋₊ →
        (∑ t ∈ Finset.Icc 1 D, (Nat.totient t : ℝ)⁻¹ *
          ∑ r ∈ (Finset.Icc 1 D).filter (fun r => 2 ≤ r ∧ r ≤ R₀),
            (Nat.totient r : ℝ)⁻¹ * bProdCharSumDivSum x M Y t r)
        ≤ (x : ℝ) / (Real.log (x : ℝ)) ^ A := by
  obtain ⟨C, hCpos, hBL⟩ :=
    BLodSmallRSum (A + ((100 : ℕ) : ℝ)) 1 (by positivity) (by norm_num)
      (by have h100 : (1 : ℝ) ≤ ((100 : ℕ) : ℝ) := by norm_num
          linarith)
  refine ⟨1, by norm_num, ?_⟩
  filter_upwards [hBL, bls_absorb A C hA hCpos] with x hx habs
  intro M Y D R₀ hM hD hR₀
  have hR₀' : R₀ ≤ ⌊(Real.log (x : ℝ)) ^ (1 : ℝ)⌋₊ := by
    simpa [Real.rpow_one] using hR₀
  calc (∑ t ∈ Finset.Icc 1 D, (Nat.totient t : ℝ)⁻¹ *
        ∑ r ∈ (Finset.Icc 1 D).filter (fun r => 2 ≤ r ∧ r ≤ R₀),
          (Nat.totient r : ℝ)⁻¹ * bProdCharSumDivSum x M Y t r)
      ≤ ∑ t ∈ Finset.Icc 1 D, ((3 : ℝ) ^ (t.primeFactors.card) / (Nat.totient t : ℝ)) *
        ∑ r ∈ (Finset.Icc 1 D).filter (fun r => 2 ≤ r ∧ r ≤ R₀),
          ((3 : ℝ) ^ (r.primeFactors.card) / (Nat.totient r : ℝ)) *
            bProdCharSumDivSum x M Y t r := bls_unw_le_wtd x M Y D R₀
    _ ≤ C * (x : ℝ) * (Real.log (x : ℝ) + 2) ^ (2 * (1 : ℝ) + 20) *
          Real.log (Real.log (x : ℝ) + 3) / (Real.log (x : ℝ)) ^ (A + ((100 : ℕ) : ℝ)) :=
        hx M Y D R₀ hM hR₀' hD
    _ ≤ (x : ℝ) / (Real.log (x : ℝ)) ^ A := habs

end Work.NumberTheory.Chen.BTermCount
