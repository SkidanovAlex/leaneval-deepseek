import Mathlib
import Submission.Commons.Analysis.ExponentialSums.quadratic_weyl_bound

namespace Commons.Analysis.ExponentialSums

/-- Minor-arc decay for the quadratic Weyl sum.  Away from the `N^δ`-major arcs (the
neighbourhoods of radius `N^(-2+δ)` of the rationals `a/q` with `q ≤ N^δ`), the normalized
quadratic exponential sum over `n < N` decays like a negative power of `N`.

The proof is Dirichlet's approximation theorem (`Real.exists_rat_abs_sub_le_and_den_le`,
Mathlib) followed by Weyl's inequality for quadratics
(`Commons.Analysis.ExponentialSums.quadratic_weyl_bound`): apply Dirichlet with parameter
`N^(2-δ)`; if the reduced denominator `y` of the approximation is `≤ N^δ` then `α` lies in a
major arc, contradiction, so `y > N^δ`, while `y ≤ N^(2-δ)` gives
`y/N^2 ≤ N^(-δ)`; Weyl's bound then gives `N^(-δ/2 + ε)`. -/
theorem quadratic_minor_arc_decay (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 4) :
    ∃ (C ν : ℝ), 0 < C ∧ 0 < ν ∧
      ∀ (N : ℕ) (α : ℝ), 2 ≤ N →
        (∀ (q : ℕ) (a : ℤ), 1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ δ →
          (N : ℝ) ^ (-(2 : ℝ) + δ) < |α - (a : ℝ) / (q : ℝ)|) →
        ‖(N : ℂ)⁻¹ * ∑ n ∈ Finset.range N,
            Complex.exp (2 * Real.pi * Complex.I * ((α * (n : ℝ) ^ 2 : ℝ) : ℂ))‖
          ≤ C * (N : ℝ) ^ (-ν) := by
  obtain ⟨Cw, hCwpos, hCw⟩ := quadratic_weyl_bound (e := δ / 4) (by linarith)
  refine ⟨3 * Cw, δ / 4, by positivity, by linarith, ?_⟩
  intro N α hN hminor
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hN1 : (1 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 1 < N)
  have hN2 : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hexp_pos : 0 < (2 : ℝ) - δ := by linarith
  have hNrpow_pos : 0 < (N : ℝ) ^ ((2 : ℝ) - δ) := Real.rpow_pos_of_pos hNpos _
  have hNrpow_ge2 : 2 ≤ (N : ℝ) ^ ((2 : ℝ) - δ) := by
    have h4 : ((7 : ℝ) / 4) ≤ (2 : ℝ) - δ := by linarith
    have h1' : (N : ℝ) ^ ((7 : ℝ) / 4) ≤ (N : ℝ) ^ ((2 : ℝ) - δ) :=
      Real.rpow_le_rpow_of_exponent_le (x := (N : ℝ)) hN1.le h4
    have h2 : (2 : ℝ) ^ ((7 : ℝ) / 4) ≤ (N : ℝ) ^ ((7 : ℝ) / 4) :=
      Real.rpow_le_rpow (x := (2 : ℝ)) (y := (N : ℝ)) (z := ((7 : ℝ) / 4))
        (by norm_num) hN2 (by norm_num)
    have h3 : (2 : ℝ) ≤ (2 : ℝ) ^ ((7 : ℝ) / 4) := by
      calc (2 : ℝ) = (2 : ℝ) ^ (1 : ℝ) := (Real.rpow_one 2).symm
        _ ≤ (2 : ℝ) ^ ((7 : ℝ) / 4) :=
              Real.rpow_le_rpow_of_exponent_le (x := (2 : ℝ)) (by norm_num) (by norm_num)
    linarith
  -- The Dirichlet parameter.
  set M : ℕ := Nat.ceil (2 * (N : ℝ) ^ ((2 : ℝ) - δ)) + 1 with hMdef
  have hM_ge : 2 * (N : ℝ) ^ ((2 : ℝ) - δ) + 1 ≤ (M : ℝ) := by
    have h := Nat.le_ceil (2 * (N : ℝ) ^ ((2 : ℝ) - δ))
    rw [hMdef]; push_cast; linarith
  have hM_gt : (N : ℝ) ^ ((2 : ℝ) - δ) < (M : ℝ) := by linarith [hM_ge, hNrpow_pos]
  have hM_le : (M : ℝ) ≤ 3 * (N : ℝ) ^ ((2 : ℝ) - δ) := by
    have h := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ 2 * (N : ℝ) ^ ((2 : ℝ) - δ) by positivity)
    rw [hMdef]; push_cast; linarith [h, hNrpow_ge2]
  have hMpos : 0 < M := by
    rw [hMdef]; exact Nat.succ_pos _
  -- Dirichlet approximation.
  obtain ⟨q, hqbound, hqden⟩ := Real.exists_rat_abs_sub_le_and_den_le α (n := M) hMpos
  have hqcast : (q : ℝ) = (q.num : ℝ) / (q.den : ℝ) := Rat.cast_def q
  have hdenpos : (0 : ℝ) < (q.den : ℝ) := by exact_mod_cast q.pos
  have hden1 : (1 : ℝ) ≤ (q.den : ℝ) := by exact_mod_cast q.pos
  -- y > N^δ (otherwise a major arc).
  have hy_gt : (N : ℝ) ^ δ < (q.den : ℝ) := by
    by_contra hle
    rw [not_lt] at hle
    have hmin := hminor q.den q.num (by have h := q.pos; omega) hle
    have hb1 : |α - (q.num : ℝ) / (q.den : ℝ)| ≤ 1 / (((M : ℝ) + 1) * (q.den : ℝ)) := by
      rw [← hqcast]; exact hqbound
    have hb2 : 1 / (((M : ℝ) + 1) * (q.den : ℝ)) ≤ 1 / ((M : ℝ) + 1) := by
      apply one_div_le_one_div_of_le (by positivity)
      nlinarith [hden1, hMpos]
    have hMN : 2 * (N : ℝ) ^ ((2 : ℝ) - δ) < (M : ℝ) + 1 := by linarith [hM_ge]
    have hstep : 1 / ((M : ℝ) + 1) < 1 / (2 * (N : ℝ) ^ ((2 : ℝ) - δ)) :=
      one_div_lt_one_div_of_lt (by positivity) hMN
    have hhalf : 1 / (2 * (N : ℝ) ^ ((2 : ℝ) - δ)) < (N : ℝ) ^ (-((2 : ℝ) - δ)) := by
      rw [show (1 : ℝ) / (2 * (N : ℝ) ^ ((2 : ℝ) - δ))
            = (1 / 2) * ((N : ℝ) ^ ((2 : ℝ) - δ))⁻¹ by field_simp]
      rw [← Real.rpow_neg hNpos.le]
      have hpos : 0 < (N : ℝ) ^ (-((2 : ℝ) - δ)) := Real.rpow_pos_of_pos hNpos _
      nlinarith [hpos]
    have hb3 : 1 / ((M : ℝ) + 1) < (N : ℝ) ^ (-(2 : ℝ) + δ) := by
      have heq : (-(2 : ℝ) + δ) = -((2 : ℝ) - δ) := by ring
      rw [heq]; exact lt_trans hstep hhalf
    have hlt : |α - (q.num : ℝ) / (q.den : ℝ)| < (N : ℝ) ^ (-(2 : ℝ) + δ) := by
      calc |α - (q.num : ℝ) / (q.den : ℝ)| ≤ 1 / (((M : ℝ) + 1) * (q.den : ℝ)) := hb1
        _ ≤ 1 / ((M : ℝ) + 1) := hb2
        _ < (N : ℝ) ^ (-(2 : ℝ) + δ) := hb3
    linarith [hmin, hlt]
  -- gcd coprimality
  have hgcd : Int.gcd q.num (q.den : ℤ) = 1 := by
    rw [Int.gcd_eq_natAbs]
    exact Nat.Coprime.gcd_eq_one (by simpa using q.reduced)
  -- Weyl applies.
  have hb : ‖α - (q.num : ℝ) / (q.den : ℝ)‖ ≤ 1 / (q.den : ℝ) ^ 2 := by
    rw [Real.norm_eq_abs]
    have hb1 : |α - (q.num : ℝ) / (q.den : ℝ)| ≤ 1 / (((M : ℝ) + 1) * (q.den : ℝ)) := by
      rw [← hqcast]; exact hqbound
    have hdenM : (q.den : ℝ) ≤ (M : ℝ) + 1 := by
      have : (q.den : ℝ) ≤ (M : ℝ) := by exact_mod_cast hqden
      linarith
    have hle : 1 / (((M : ℝ) + 1) * (q.den : ℝ)) ≤ 1 / (q.den : ℝ) ^ 2 := by
      apply one_div_le_one_div_of_le (by positivity)
      nlinarith [hdenM, hdenpos]
    linarith [hb1, hle]
  have hWeyl := hCw N α q.num q.den (by omega) (by positivity) hgcd hb
  -- bound the bracket
  have hA : 1 / (q.den : ℝ) ≤ (N : ℝ) ^ (-δ) := by
    have hδpos : 0 < (N : ℝ) ^ δ := Real.rpow_pos_of_pos hNpos _
    have hlt : 1 / (q.den : ℝ) < (N : ℝ) ^ (-δ) := by
      rw [show (N : ℝ) ^ (-δ) = 1 / (N : ℝ) ^ δ by rw [Real.rpow_neg hNpos.le, one_div]]
      exact one_div_lt_one_div_of_lt hδpos hy_gt
    exact le_of_lt hlt
  have hB : 1 / (N : ℝ) ≤ (N : ℝ) ^ (-δ) := by
    have h1 : (N : ℝ) ^ (-1 : ℝ) ≤ (N : ℝ) ^ (-δ) :=
      Real.rpow_le_rpow_of_exponent_le (x := (N : ℝ)) hN1.le (by linarith)
    simpa [Real.rpow_neg_one, one_div] using h1
  have hC : (q.den : ℝ) / (N : ℝ) ^ 2 ≤ 3 * (N : ℝ) ^ (-δ) := by
    have hyden : (q.den : ℝ) ≤ 3 * (N : ℝ) ^ ((2 : ℝ) - δ) :=
      le_trans (by exact_mod_cast hqden) hM_le
    calc (q.den : ℝ) / (N : ℝ) ^ 2
        ≤ (3 * (N : ℝ) ^ ((2 : ℝ) - δ)) / (N : ℝ) ^ 2 :=
          div_le_div_of_nonneg_right hyden (by positivity)
      _ = 3 * (N : ℝ) ^ (-δ) := by
          rw [mul_div_assoc]
          have hsq : (N : ℝ) ^ 2 = (N : ℝ) ^ ((2 : ℝ)) := (Real.rpow_natCast (N : ℝ) 2).symm
          rw [hsq, ← Real.rpow_sub hNpos ((2 : ℝ) - δ) (2 : ℝ),
            show (((2 : ℝ) - δ) - 2) = -δ by ring]
  have hbracket_le : (1 / (q.den : ℝ) + 1 / (N : ℝ) + (q.den : ℝ) / (N : ℝ) ^ 2)
      ≤ 5 * (N : ℝ) ^ (-δ) := by linarith [hA, hB, hC]
  have hbracket_nn : 0 ≤ (1 / (q.den : ℝ) + 1 / (N : ℝ) + (q.den : ℝ) / (N : ℝ) ^ 2) := by
    positivity
  have hsqrt_le : (1 / (q.den : ℝ) + 1 / (N : ℝ) + (q.den : ℝ) / (N : ℝ) ^ 2) ^ ((1 : ℝ) / 2)
      ≤ 3 * (N : ℝ) ^ (-(δ / 2)) := by
    have h5nn : (0 : ℝ) ≤ 5 * (N : ℝ) ^ (-δ) := by positivity
    calc (1 / (q.den : ℝ) + 1 / (N : ℝ) + (q.den : ℝ) / (N : ℝ) ^ 2) ^ ((1 : ℝ) / 2)
        ≤ (5 * (N : ℝ) ^ (-δ)) ^ ((1 : ℝ) / 2) :=
          Real.rpow_le_rpow hbracket_nn hbracket_le (by norm_num)
      _ = (5 : ℝ) ^ ((1 : ℝ) / 2) * ((N : ℝ) ^ (-δ)) ^ ((1 : ℝ) / 2) := by
          rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hNpos.le _)]
      _ = (5 : ℝ) ^ ((1 : ℝ) / 2) * (N : ℝ) ^ (-(δ / 2)) := by
          rw [← Real.rpow_mul hNpos.le]
          congr 1
          ring_nf
      _ ≤ 3 * (N : ℝ) ^ (-(δ / 2)) := by
          apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hNpos.le _)
          rw [← Real.sqrt_eq_rpow, Real.sqrt_le_iff]
          exact ⟨by norm_num, by norm_num⟩
  calc ‖(N : ℂ)⁻¹ * ∑ n ∈ Finset.range N,
          Complex.exp (2 * Real.pi * Complex.I * ((α * (n : ℝ) ^ 2 : ℝ) : ℂ))‖
      ≤ Cw * (N : ℝ) ^ (δ / 4)
          * (1 / (q.den : ℝ) + 1 / (N : ℝ) + (q.den : ℝ) / (N : ℝ) ^ 2) ^ ((1 : ℝ) / 2) := hWeyl
    _ ≤ Cw * (N : ℝ) ^ (δ / 4) * (3 * (N : ℝ) ^ (-(δ / 2))) := by
        apply mul_le_mul_of_nonneg_left hsqrt_le
        positivity
    _ = 3 * Cw * (N : ℝ) ^ (-(δ / 4)) := by
        have hpow : (N : ℝ) ^ (δ / 4) * (N : ℝ) ^ (-(δ / 2)) = (N : ℝ) ^ (-(δ / 4)) := by
          rw [← Real.rpow_add hNpos]
          congr 1
          ring
        calc Cw * (N : ℝ) ^ (δ / 4) * (3 * (N : ℝ) ^ (-(δ / 2)))
            = 3 * Cw * ((N : ℝ) ^ (δ / 4) * (N : ℝ) ^ (-(δ / 2))) := by ring
          _ = 3 * Cw * (N : ℝ) ^ (-(δ / 4)) := by rw [hpow]

end Commons.Analysis.ExponentialSums
