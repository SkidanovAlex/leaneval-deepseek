import Mathlib
import Submission.Work.NumberTheory.Chen.BTermCount.BLodUnweightedDefs

namespace Work.NumberTheory.Chen.BTermCount

open Finset

/-!
# The `V·√U` block sum for the unweighted bilinear level of distribution

`blodU M j = 2 · M · 2^j` and `blodV x M j = (x+2)/(M·2^j) + 1` are the `a`- and
`b`-ranges of the `j`-th dyadic block.  Here we bound

  `∑_{j < blockCount M Y} V_j · √U_j`

by `8 (x+2) / x^{1/28} + 12 x^{1/6} log x`, under the standing hypotheses
`x ≥ 32`, `1 ≤ M ≤ Y`, `Y ≤ 2 x^{1/3}` and `M ≥ x^{1/14}`.

The mechanism is elementary: `V_j ≤ (x+2)/(M 2^j) + 1` and
`√U_j = √2 · √M · (√2)^j`, so the summand splits into a *decreasing* geometric
piece with ratio `1/√2` (producing the `(x+2)/x^{1/28}` term, since the small
divisor `√M` is at least `x^{1/28}`) and an *increasing* geometric piece with
ratio `√2` (producing the `x^{1/6} log x` term, since `2^{blockCount} ≤ 2(Y/M+1)`).
-/

/-- `√(2^j) = (√2)^j`. -/
private lemma sqrt_two_pow (j : ℕ) : Real.sqrt ((2:ℝ)^j) = (Real.sqrt 2)^j := by
  induction j with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2), ih, pow_succ']

/-- Termwise bound: the `j`-th summand splits into a decreasing geometric piece with rati
`(√2)⁻¹` and an increasing geometric piece with ratio `√2`. -/
private lemma blod_term_le (x M j : ℕ) (hM : 1 ≤ M) :
    (blodV x M j : ℝ) * Real.sqrt (blodU M j : ℝ)
      ≤ (x + 2 : ℝ) * (Real.sqrt 2 / Real.sqrt (M : ℝ)) * ((Real.sqrt 2)⁻¹)^j
        + Real.sqrt 2 * Real.sqrt (M : ℝ) * (Real.sqrt 2)^j := by
  have hU : Real.sqrt (blodU M j : ℝ) = Real.sqrt 2 * Real.sqrt (M:ℝ) * (Real.sqrt 2)^j := by
    unfold blodU blockStart
    push_cast
    rw [show (2:ℝ) * ((M:ℝ) * 2^j) = (2 * (M:ℝ)) * (2:ℝ)^j by ring]
    rw [Real.sqrt_mul (by positivity : (0:ℝ) ≤ 2 * (M:ℝ)),
      Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
    rw [sqrt_two_pow j]
  have hV : (blodV x M j : ℝ) ≤ (x+2:ℝ)/((M:ℝ)*(2:ℝ)^j) + 1 := by
    unfold blodV blockStart
    push_cast
    have h := Nat.cast_div_le (α := ℝ) (m := x+2) (n := M * 2^j)
    push_cast at h
    linarith
  have hU0 : 0 ≤ Real.sqrt 2 * Real.sqrt (M:ℝ) * (Real.sqrt 2)^j := by positivity
  have hkey : ((x+2:ℝ)/((M:ℝ)*(2:ℝ)^j)) * (Real.sqrt 2 * Real.sqrt (M:ℝ) * (Real.sqrt 2)^j)
      = (x+2:ℝ) * (Real.sqrt 2 / Real.sqrt (M:ℝ)) * ((Real.sqrt 2)⁻¹)^j := by
    have hMpos : (0:ℝ) < (M:ℝ) := by exact_mod_cast hM
    have hs2 : (Real.sqrt 2)^2 = (2:ℝ) := Real.sq_sqrt (by norm_num)
    have hm2 : (Real.sqrt (M:ℝ))^2 = (M:ℝ) := Real.sq_sqrt hMpos.le
    have hA : ((Real.sqrt 2)^j)^2 = (2:ℝ)^j := by
      rw [← pow_mul, Nat.mul_comm j 2, pow_mul, hs2]
    rw [inv_pow, ← hA, ← hm2]
    rw [Real.sqrt_sq (by positivity)]
    field_simp
  calc (blodV x M j : ℝ) * Real.sqrt (blodU M j : ℝ)
      ≤ ((x+2:ℝ)/((M:ℝ)*(2:ℝ)^j) + 1)
          * (Real.sqrt 2 * Real.sqrt (M:ℝ) * (Real.sqrt 2)^j) := by
        rw [hU]
        exact mul_le_mul_of_nonneg_right hV hU0
    _ = (x+2:ℝ) * (Real.sqrt 2 / Real.sqrt (M:ℝ)) * ((Real.sqrt 2)⁻¹)^j
          + Real.sqrt 2 * Real.sqrt (M:ℝ) * (Real.sqrt 2)^j := by
        rw [add_mul, one_mul, hkey]

/-- The finite geometric sum with ratio `r ∈ [0,1)` is at most its infinite value. -/
private lemma geom_sum_range_le_inv (r : ℝ) (h0 : 0 ≤ r) (h1 : r < 1) (n : ℕ) :
    ∑ k ∈ Finset.range n, r ^ k ≤ 1 / (1 - r) := by
  have hpos : 0 < 1 - r := by linarith
  rw [le_div_iff₀ hpos, geom_sum_mul_neg]
  have : 0 ≤ r ^ n := pow_nonneg h0 n
  linarith

/-- The truncated geometric sum with ratio `q ≥ 4/3` is at most `3 q^n`. -/
private lemma geom_sum_range_one_le (q : ℝ) (h1 : 1 < q) (h43 : (4:ℝ)/3 ≤ q) (n : ℕ) :
    ∑ j ∈ Finset.range n, q^j ≤ 3 * q^n := by
  have hq0 : (0:ℝ) < q := by linarith
  have hq1 : q ≠ 1 := ne_of_gt h1
  rw [geom_sum_eq hq1]
  have hqpos : 0 < q - 1 := by linarith
  rw [div_le_iff₀ hqpos]
  have hqnn : (0:ℝ) ≤ q^n := pow_nonneg hq0.le n
  nlinarith [hqnn, h43]

/-- `1/(1 - (√2)⁻¹) = 2 + √2`. -/
private lemma one_div_one_sub_inv_sqrt_two :
    (1:ℝ) / (1 - (Real.sqrt 2)⁻¹) = 2 + Real.sqrt 2 := by
  have hs2 : (Real.sqrt 2)^2 = (2:ℝ) := Real.sq_sqrt (by norm_num)
  have hlt : (1:ℝ) < Real.sqrt 2 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  have hlt' : (1:ℝ) / Real.sqrt 2 < 1 := (div_lt_one (by positivity)).mpr hlt
  rw [inv_eq_one_div]
  rw [div_eq_iff (ne_of_gt (by linarith : (0:ℝ) < 1 - 1 / Real.sqrt 2))]
  field_simp
  nlinarith [hs2]

/-- `√(X^{1/14}) = X^{1/28}` for `X ≥ 0`. -/
private lemma sqrt_rpow_fourteen {X : ℝ} (hX : 0 ≤ X) :
    Real.sqrt (X ^ ((1:ℝ)/14)) = X ^ ((1:ℝ)/28) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hX]
  norm_num

/-- `√(X^{1/3}) = X^{1/6}` for `X ≥ 0`. -/
private lemma sqrt_rpow_three {X : ℝ} (hX : 0 ≤ X) :
    Real.sqrt (X ^ ((1:ℝ)/3)) = X ^ ((1:ℝ)/6) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hX]
  norm_num

theorem blodSumVSqrtULe (x M Y : ℕ) (hx : 32 ≤ x) (hM : 1 ≤ M) (hMY : M ≤ Y)
    (hY : (Y : ℝ) ≤ 2 * (x : ℝ) ^ ((1:ℝ)/3)) (hMlo : (x : ℝ) ^ ((1:ℝ)/14) ≤ (M : ℝ)) :
    (∑ j ∈ Finset.range (blockCount M Y),
        (blodV x M j : ℝ) * Real.sqrt (blodU M j : ℝ))
      ≤ 8 * ((x : ℝ) + 2) / (x : ℝ) ^ ((1:ℝ)/28)
        + 12 * (x : ℝ) ^ ((1:ℝ)/6) * Real.log (x : ℝ) := by
  classical
  set n : ℕ := blockCount M Y with hn
  have hX32 : (32:ℝ) ≤ (x:ℝ) := by exact_mod_cast hx
  have hXpos : (0:ℝ) < (x:ℝ) := by linarith
  have hX0 : (0:ℝ) ≤ (x:ℝ) := hXpos.le
  have hMpos : (0:ℝ) < (M:ℝ) := by exact_mod_cast hM
  have hMY' : (M:ℝ) ≤ (Y:ℝ) := by exact_mod_cast hMY
  have hYpos : (0:ℝ) < (Y:ℝ) := by linarith
  have hY0 : (0:ℝ) ≤ (Y:ℝ) := hYpos.le
  have hs2 : (Real.sqrt 2)^2 = (2:ℝ) := Real.sq_sqrt (by norm_num)
  have hs0 : (0:ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hs1 : (1:ℝ) < Real.sqrt 2 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  have hmsqrt : (0:ℝ) < Real.sqrt (M:ℝ) := Real.sqrt_pos_of_pos hMpos
  -- ### Step 1: the sum splits at each term
  have hsum : (∑ j ∈ Finset.range n, (blodV x M j : ℝ) * Real.sqrt (blodU M j : ℝ))
      ≤ (x + 2 : ℝ) * (Real.sqrt 2 / Real.sqrt (M : ℝ))
            * (∑ j ∈ Finset.range n, ((Real.sqrt 2)⁻¹)^j)
        + Real.sqrt 2 * Real.sqrt (M : ℝ) * (∑ j ∈ Finset.range n, (Real.sqrt 2)^j) := by
    calc (∑ j ∈ Finset.range n, (blodV x M j : ℝ) * Real.sqrt (blodU M j : ℝ))
        ≤ ∑ j ∈ Finset.range n,
            ((x + 2 : ℝ) * (Real.sqrt 2 / Real.sqrt (M : ℝ)) * ((Real.sqrt 2)⁻¹)^j
              + Real.sqrt 2 * Real.sqrt (M : ℝ) * (Real.sqrt 2)^j) :=
          Finset.sum_le_sum (fun j _ => blod_term_le x M j hM)
      _ = (∑ j ∈ Finset.range n,
              (x + 2 : ℝ) * (Real.sqrt 2 / Real.sqrt (M : ℝ)) * ((Real.sqrt 2)⁻¹)^j)
            + ∑ j ∈ Finset.range n,
              (Real.sqrt 2 * Real.sqrt (M : ℝ) * (Real.sqrt 2)^j) :=
          Finset.sum_add_distrib
      _ = (x + 2 : ℝ) * (Real.sqrt 2 / Real.sqrt (M : ℝ))
            * (∑ j ∈ Finset.range n, ((Real.sqrt 2)⁻¹)^j)
          + Real.sqrt 2 * Real.sqrt (M : ℝ) * (∑ j ∈ Finset.range n, (Real.sqrt 2)^j) := by
          rw [← Finset.mul_sum, ← Finset.mul_sum]
  -- ### Step 2: the two geometric sums
  have hgeo1 : (∑ j ∈ Finset.range n, ((Real.sqrt 2)⁻¹)^j) ≤ 2 + Real.sqrt 2 := by
    have h0 : (0:ℝ) ≤ (Real.sqrt 2)⁻¹ := by positivity
    have h1 : (Real.sqrt 2)⁻¹ < 1 := by
      rw [inv_lt_one_iff₀]; right; exact hs1
    calc (∑ j ∈ Finset.range n, ((Real.sqrt 2)⁻¹)^j) ≤ 1 / (1 - (Real.sqrt 2)⁻¹) :=
          geom_sum_range_le_inv _ h0 h1 n
      _ = 2 + Real.sqrt 2 := one_div_one_sub_inv_sqrt_two
  have hgeo2 : (∑ j ∈ Finset.range n, (Real.sqrt 2)^j) ≤ 3 * (Real.sqrt 2)^n :=
    geom_sum_range_one_le _ hs1 (by nlinarith [hs2, hs0]) n
  -- ### Step 3: bound `(√2)^n`
  have hn' : n = Nat.log 2 (Y / M + 1) + 1 := by
    rw [hn]; rfl
  have hlog2 : (2:ℝ)^(Nat.log 2 (Y / M + 1)) ≤ (Y:ℝ)/M + 1 := by
    have h1 : (2:ℝ)^(Nat.log 2 (Y / M + 1)) ≤ ((Y / M + 1 : ℕ) : ℝ) := by
      exact_mod_cast (Nat.pow_log_le_self 2 (Nat.succ_ne_zero (Y / M)))
    have h2 : ((Y / M + 1 : ℕ) : ℝ) ≤ (Y:ℝ)/M + 1 := by
      have h := Nat.cast_div_le (α := ℝ) (m := Y) (n := M)
      push_cast
      linarith
    linarith
  have h2n : (2:ℝ)^n ≤ 2 * ((Y:ℝ)/M + 1) := by
    rw [hn', pow_succ]
    linarith
  have hMdivY : (1:ℝ) ≤ (Y:ℝ)/M := by
    rw [le_div_iff₀ hMpos]; linarith
  have hsqrt2n : (Real.sqrt 2)^n ≤ 2 * Real.sqrt ((Y:ℝ)/M) := by
    calc (Real.sqrt 2)^n = Real.sqrt ((2:ℝ)^n) := (sqrt_two_pow n).symm
      _ ≤ Real.sqrt (2 * ((Y:ℝ)/M + 1)) := Real.sqrt_le_sqrt h2n
      _ ≤ 2 * Real.sqrt ((Y:ℝ)/M) := by
          have hle : 2 * ((Y:ℝ)/M + 1) ≤ 4 * ((Y:ℝ)/M) := by linarith
          have h4 : Real.sqrt (4 * ((Y:ℝ)/M)) = 2 * Real.sqrt ((Y:ℝ)/M) := by
            rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4)]
            congr 1
            have h := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 4)
            have h' := Real.sqrt_nonneg 4
            nlinarith
          calc Real.sqrt (2 * ((Y:ℝ)/M + 1)) ≤ Real.sqrt (4 * ((Y:ℝ)/M)) :=
                Real.sqrt_le_sqrt hle
            _ = 2 * Real.sqrt ((Y:ℝ)/M) := h4
  -- ### Step 4: the two halves of the bound
  have hA : (x + 2 : ℝ) * (Real.sqrt 2 / Real.sqrt (M : ℝ))
        * (∑ j ∈ Finset.range n, ((Real.sqrt 2)⁻¹)^j)
      ≤ 8 * ((x:ℝ) + 2) / (x:ℝ) ^ ((1:ℝ)/28) := by
    have hstep1 : (x + 2 : ℝ) * (Real.sqrt 2 / Real.sqrt (M : ℝ))
          * (∑ j ∈ Finset.range n, ((Real.sqrt 2)⁻¹)^j)
        ≤ (x + 2 : ℝ) * (Real.sqrt 2 / Real.sqrt (M : ℝ)) * (2 + Real.sqrt 2) := by
      apply mul_le_mul_of_nonneg_left hgeo1
      positivity
    have hstep2 : (x + 2 : ℝ) * (Real.sqrt 2 / Real.sqrt (M : ℝ)) * (2 + Real.sqrt 2)
        ≤ 8 * ((x:ℝ) + 2) / Real.sqrt (M : ℝ) := by
      have h8 : Real.sqrt 2 * (2 + Real.sqrt 2) ≤ 8 := by nlinarith [hs2, hs0]
      have hx2 : (0:ℝ) ≤ ((x:ℝ) + 2) / Real.sqrt (M:ℝ) := by positivity
      have heq : (x + 2 : ℝ) * (Real.sqrt 2 / Real.sqrt (M : ℝ)) * (2 + Real.sqrt 2)
          = (((x:ℝ) + 2) / Real.sqrt (M:ℝ)) * (Real.sqrt 2 * (2 + Real.sqrt 2)) := by ring
      rw [heq]
      calc (((x:ℝ) + 2) / Real.sqrt (M:ℝ)) * (Real.sqrt 2 * (2 + Real.sqrt 2))
          ≤ (((x:ℝ) + 2) / Real.sqrt (M:ℝ)) * 8 := mul_le_mul_of_nonneg_left h8 hx2
        _ = 8 * ((x:ℝ) + 2) / Real.sqrt (M : ℝ) := by ring
    have hMsqrt : (x:ℝ) ^ ((1:ℝ)/28) ≤ Real.sqrt (M:ℝ) := by
      have h := Real.sqrt_le_sqrt hMlo
      rwa [sqrt_rpow_fourteen hX0] at h
    have hpos28 : (0:ℝ) < (x:ℝ) ^ ((1:ℝ)/28) := Real.rpow_pos_of_pos hXpos _
    calc (x + 2 : ℝ) * (Real.sqrt 2 / Real.sqrt (M : ℝ))
          * (∑ j ∈ Finset.range n, ((Real.sqrt 2)⁻¹)^j)
        ≤ 8 * ((x:ℝ) + 2) / Real.sqrt (M : ℝ) := le_trans hstep1 hstep2
      _ ≤ 8 * ((x:ℝ) + 2) / (x:ℝ) ^ ((1:ℝ)/28) :=
          div_le_div_of_nonneg_left (by positivity) hpos28 hMsqrt
  have hB : Real.sqrt 2 * Real.sqrt (M : ℝ) * (∑ j ∈ Finset.range n, (Real.sqrt 2)^j)
      ≤ 12 * (x:ℝ) ^ ((1:ℝ)/6) := by
    have hstep1 : Real.sqrt 2 * Real.sqrt (M : ℝ) * (∑ j ∈ Finset.range n, (Real.sqrt 2)^j)
        ≤ Real.sqrt 2 * Real.sqrt (M : ℝ) * (3 * (Real.sqrt 2)^n) :=
      mul_le_mul_of_nonneg_left hgeo2 (by positivity)
    have hstep2 : Real.sqrt 2 * Real.sqrt (M : ℝ) * (3 * (Real.sqrt 2)^n)
        ≤ Real.sqrt 2 * Real.sqrt (M : ℝ) * (3 * (2 * Real.sqrt ((Y:ℝ)/M))) :=
      mul_le_mul_of_nonneg_left (by linarith [hsqrt2n]) (by positivity)
    have hmul : Real.sqrt (M:ℝ) * Real.sqrt ((Y:ℝ)/M) = Real.sqrt (Y:ℝ) := by
      rw [← Real.sqrt_mul hMpos.le]
      congr 1
      field_simp
    have hYsqrt : Real.sqrt (Y:ℝ) ≤ Real.sqrt 2 * (x:ℝ) ^ ((1:ℝ)/6) := by
      calc Real.sqrt (Y:ℝ) ≤ Real.sqrt (2 * (x:ℝ) ^ ((1:ℝ)/3)) := Real.sqrt_le_sqrt hY
        _ = Real.sqrt 2 * Real.sqrt ((x:ℝ) ^ ((1:ℝ)/3)) :=
              Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2) _
        _ = Real.sqrt 2 * (x:ℝ) ^ ((1:ℝ)/6) := by rw [sqrt_rpow_three hX0]
    have hfin : Real.sqrt 2 * Real.sqrt (M : ℝ) * (3 * (2 * Real.sqrt ((Y:ℝ)/M)))
        ≤ 12 * (x:ℝ) ^ ((1:ℝ)/6) := by
      have h1 : Real.sqrt 2 * Real.sqrt (M : ℝ) * (3 * (2 * Real.sqrt ((Y:ℝ)/M)))
          = 6 * Real.sqrt 2 * (Real.sqrt (M:ℝ) * Real.sqrt ((Y:ℝ)/M)) := by ring
      rw [h1, hmul]
      have h2 : 6 * Real.sqrt 2 * Real.sqrt (Y:ℝ) ≤ 6 * Real.sqrt 2 * (Real.sqrt 2 * (x:ℝ) ^ ((1:ℝ)/6)) :=
        mul_le_mul_of_nonneg_left hYsqrt (by positivity)
      have h22 : Real.sqrt 2 * Real.sqrt 2 = 2 := by
        rw [← sq]; exact hs2
      have h3 : 6 * Real.sqrt 2 * (Real.sqrt 2 * (x:ℝ) ^ ((1:ℝ)/6))
          = 12 * (x:ℝ) ^ ((1:ℝ)/6) := by
        rw [show 6 * Real.sqrt 2 * (Real.sqrt 2 * (x:ℝ) ^ ((1:ℝ)/6))
              = 6 * (Real.sqrt 2 * Real.sqrt 2) * (x:ℝ) ^ ((1:ℝ)/6) by ring, h22]
        ring
      linarith [h2, le_of_eq h3]
    calc Real.sqrt 2 * Real.sqrt (M : ℝ) * (∑ j ∈ Finset.range n, (Real.sqrt 2)^j)
        ≤ Real.sqrt 2 * Real.sqrt (M : ℝ) * (3 * (Real.sqrt 2)^n) := hstep1
      _ ≤ Real.sqrt 2 * Real.sqrt (M : ℝ) * (3 * (2 * Real.sqrt ((Y:ℝ)/M))) := hstep2
      _ ≤ 12 * (x:ℝ) ^ ((1:ℝ)/6) := hfin
  -- ### Step 5: assemble
  have hlog1 : (1:ℝ) ≤ Real.log (x:ℝ) := by
    rw [Real.le_log_iff_exp_le hXpos]
    linarith [Real.exp_one_lt_three, hX32]
  have hlast : 12 * (x:ℝ) ^ ((1:ℝ)/6) ≤ 12 * (x:ℝ) ^ ((1:ℝ)/6) * Real.log (x:ℝ) := by
    have h6 : (0:ℝ) ≤ (x:ℝ) ^ ((1:ℝ)/6) := Real.rpow_nonneg hX0 _
    nlinarith [hlog1, h6]
  linarith [hsum, hA, hB, hlast]

end Work.NumberTheory.Chen.BTermCount
