import Mathlib
import Submission.Commons.Analysis.ExponentialSums.weyl_inequality

open Finset
open scoped BigOperators

namespace Commons.Analysis.ExponentialSums

/-- A single term of a complete Weyl sum for an integer polynomial scaled by a rational
number has unit modulus.  (Immediate from `Complex.norm_exp_ofReal_mul_I`.) -/
lemma norm_exp_two_pi_I_mul_ratPoly (q : ℕ) (a : ℤ) (P : Polynomial ℤ) (r : ℕ) :
    ‖Complex.exp (2 * Real.pi * Complex.I *
      ((a : ℝ) / (q : ℝ) * ((Polynomial.eval (r : ℤ) P : ℤ) : ℝ) : ℂ))‖ = 1 := by
  rw [show 2 * Real.pi * Complex.I *
        ((a : ℝ) / (q : ℝ) * ((Polynomial.eval (r : ℤ) P : ℤ) : ℝ) : ℂ)
      = (((2 * Real.pi * ((a : ℝ) / (q : ℝ)
          * ((Polynomial.eval (r : ℤ) P : ℤ) : ℝ))) : ℝ) : ℂ) * Complex.I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

/-- **Hua-type bound for the complete Weyl sum of a monic integer polynomial.**  For
`P : ℤ[X]` monic of degree `d ≥ 2`, `q ≥ 1`, `gcd a q = 1` and any `ε > 0`,

`‖q⁻¹ ∑_{r<q} e(a P(r)/q)‖ ≤ C q^{−1/2^{d−1} + ε}`.

This follows from Weyl's inequality (Commons.Analysis.ExponentialSums.weyl_inequality) applied
with `N = q` to the real polynomial `f = (a/q) P`: its leading coefficient is exactly `a/q`, so
any `t ≥ 1` is admissible and the four terms become `(t/q + 1/q + t/q^{d−1} + q/q^d)^{2^{1−d}}
≲ q^{−1/2^{d−1}}`.  It generalises the pure-power bound
Commons.Analysis.ExponentialSums.hua_bound and supplies the weight `S(a/q)` of the major-arc
approximation for a general monic polynomial. -/
theorem monic_poly_complete_sum_bound (d : ℕ) (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) (a : ℤ) (P : Polynomial ℤ),
      P.Monic → P.natDegree = d → 1 ≤ q → Int.gcd a (q : ℤ) = 1 →
      ‖((q : ℂ))⁻¹ * ∑ r ∈ Finset.range q,
          Complex.exp (2 * Real.pi * Complex.I *
            ((a : ℝ) / (q : ℝ) * ((Polynomial.eval (r : ℤ) P : ℤ) : ℝ) : ℂ))‖
        ≤ C * (q : ℝ) ^ (-(1 / (2 : ℝ) ^ (d - 1)) + ε) := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨C0, hC0pos, hC0⟩ := weyl_inequality d hd1 hε (t := 1) (by norm_num)
  set θ : ℝ := (2:ℝ)^(1-(d:ℝ)) with hθdef
  have hθpos : 0 < θ := by rw [hθdef]; positivity
  have hθnonneg : 0 ≤ θ := le_of_lt hθpos
  have hθ_eq : θ = 1 / (2:ℝ)^(d-1) := by
    rw [hθdef]
    have h1 : (1:ℝ) - (d:ℝ) = -(((d-1:ℕ):ℝ)) := by
      rw [Nat.cast_sub (by omega : 1 ≤ d)]; ring
    rw [h1, Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2), Real.rpow_natCast, one_div]
  refine ⟨max 1 (C0 * (4:ℝ)^θ), lt_max_iff.mpr (Or.inl one_pos), ?_⟩
  intro q a P hPmonic hPnat hq hgcd
  by_cases ha0 : a = 0
  · -- degenerate case a = 0, which forces q = 1
    have hq1 : q = 1 := by
      have h := hgcd
      rw [ha0, Int.gcd_zero_left, Int.natAbs_natCast] at h
      omega
    subst hq1
    have hS : ‖∑ r ∈ Finset.range 1, Complex.exp (2 * Real.pi * Complex.I *
        ((a : ℝ) / ((1:ℕ) : ℝ) * ((Polynomial.eval (r : ℤ) P : ℤ) : ℝ) : ℂ))‖ ≤ 1 := by
      calc ‖∑ r ∈ Finset.range 1, Complex.exp (2 * Real.pi * Complex.I *
            ((a : ℝ) / ((1:ℕ) : ℝ) * ((Polynomial.eval (r : ℤ) P : ℤ) : ℝ) : ℂ))‖
          ≤ ∑ r ∈ Finset.range 1, ‖Complex.exp (2 * Real.pi * Complex.I *
              ((a : ℝ) / ((1:ℕ) : ℝ) * ((Polynomial.eval (r : ℤ) P : ℤ) : ℝ) : ℂ))‖ :=
            norm_sum_le _ _
        _ = 1 := by rw [Finset.sum_range_one, norm_exp_two_pi_I_mul_ratPoly 1 a P 0]
    rw [norm_mul, norm_inv, Complex.norm_natCast]
    rw [show (((1:ℕ)) : ℝ) ^ (-(1 / (2 : ℝ) ^ (d - 1)) + ε) = 1 by
      rw [show (((1:ℕ)) : ℝ) = 1 by norm_num, Real.one_rpow], mul_one]
    rw [show ((((1:ℕ)) : ℝ))⁻¹ = 1 by norm_num, one_mul]
    exact le_trans hS (le_max_left _ _)
  · -- main case: a ≠ 0
    have haR : (a:ℝ) ≠ 0 := by
      intro h; exact ha0 (by exact_mod_cast h)
    have hq1R : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq
    have hqpos : (0:ℝ) < (q:ℝ) := by linarith
    have hc_ne : ((a:ℝ)/(q:ℝ)) ≠ 0 := div_ne_zero haR (ne_of_gt hqpos)
    set f : Polynomial ℝ := Polynomial.C ((a:ℝ)/(q:ℝ)) * P.map (Int.castRingHom ℝ) with hfdef
    have hf_nat : f.natDegree = d := by
      rw [hfdef, Polynomial.natDegree_C_mul hc_ne, hPmonic.natDegree_map, hPnat]
    have hf_lc : f.leadingCoeff = (a:ℝ)/(q:ℝ) := by
      rw [hfdef, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C,
        (hPmonic.map (Int.castRingHom ℝ)).leadingCoeff, mul_one]
    have hcastq : ((q:ℤ):ℝ) = (q:ℝ) := by push_cast; ring
    have hlc : |f.leadingCoeff - (a:ℝ)/(q:ℤ)| ≤ (1:ℝ) / (((q:ℤ)) : ℝ)^2 := by
      rw [hf_lc, hcastq, sub_self, abs_zero]
      positivity
    have hqge : (q:ℤ) ≥ 1 := by exact_mod_cast hq
    have hweyl := hC0 (0:ℤ) q a (q:ℤ) f hqge hgcd hf_nat hlc
    have hsum_eq : (∑ r ∈ Finset.range q, Complex.exp (2 * Real.pi * Complex.I *
        ((a : ℝ) / (q : ℝ) * ((Polynomial.eval (r : ℤ) P : ℤ) : ℝ) : ℂ)))
        = ∑ x ∈ Finset.range q,
            Complex.exp (↑(2 * Real.pi * f.eval (((0:ℤ):ℝ) + (x : ℝ))) * Complex.I) := by
      apply Finset.sum_congr rfl
      intro r hr
      congr 1
      rw [show (((0:ℤ):ℝ) + (r:ℝ)) = (r:ℝ) by norm_num]
      have hev : f.eval ((r:ℝ)) = (a:ℝ)/(q:ℝ) * ((P.eval (r:ℤ):ℤ):ℝ) := by
        rw [hfdef, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_map,
          Polynomial.eval₂_at_natCast]
        rfl
      rw [hev]
      push_cast
      ring
    have hS : ‖∑ r ∈ Finset.range q, Complex.exp (2 * Real.pi * Complex.I *
        ((a : ℝ) / (q : ℝ) * ((Polynomial.eval (r : ℤ) P : ℤ) : ℝ) : ℂ))‖
        ≤ C0 * (q:ℝ)^(1+ε) *
            (1/(q:ℝ) + 1/(q:ℝ) + 1/(q:ℝ)^(d-1) + (q:ℝ)/(q:ℝ)^d)^θ := by
      rw [hsum_eq]
      have h := hweyl
      rw [hcastq] at h
      exact h
    have hB0 : 0 ≤ 1/(q:ℝ) + 1/(q:ℝ) + 1/(q:ℝ)^(d-1) + (q:ℝ)/(q:ℝ)^d := by positivity
    have hp : (q:ℝ)^d = (q:ℝ)^(d-1) * (q:ℝ) := by
      rw [← pow_succ (q:ℝ) (d-1)]
      congr 1
      omega
    have hqd : (q:ℝ)/(q:ℝ)^d = 1/(q:ℝ)^(d-1) := by
      rw [hp, mul_comm ((q:ℝ)^(d-1)) ((q:ℝ)), ← div_div, div_self (ne_of_gt hqpos)]
    have h1 : (1:ℝ)/(q:ℝ)^(d-1) ≤ 1/(q:ℝ) := by
      apply one_div_le_one_div_of_le hqpos
      calc (q:ℝ) = (q:ℝ)^1 := (pow_one _).symm
        _ ≤ (q:ℝ)^(d-1) := pow_le_pow_right₀ hq1R (by omega)
    have hB_le : 1/(q:ℝ) + 1/(q:ℝ) + 1/(q:ℝ)^(d-1) + (q:ℝ)/(q:ℝ)^d ≤ 4 * (q:ℝ)⁻¹ := by
      rw [hqd]
      have h4 : (1:ℝ)/(q:ℝ)+1/(q:ℝ)+1/(q:ℝ)+1/(q:ℝ) = 4 * (q:ℝ)⁻¹ := by ring
      linarith
    have hBpow : (1/(q:ℝ) + 1/(q:ℝ) + 1/(q:ℝ)^(d-1) + (q:ℝ)/(q:ℝ)^d)^θ
        ≤ (4 * (q:ℝ)⁻¹)^θ := Real.rpow_le_rpow hB0 hB_le hθnonneg
    have key2 : (q:ℝ)⁻¹ * (C0 * (q:ℝ)^(1+ε) * (4 * (q:ℝ)⁻¹)^θ)
        = C0 * (4:ℝ)^θ * ((q:ℝ)^((-1:ℝ)) * (q:ℝ)^(1+ε) * (q:ℝ)^(-θ)) := by
      rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 4) (by positivity : (0:ℝ) ≤ (q:ℝ)⁻¹),
        Real.inv_rpow hqpos.le θ, ← Real.rpow_neg hqpos.le θ, ← Real.rpow_neg_one (q:ℝ)]
      ring
    have key3 : (q:ℝ)^((-1:ℝ)) * (q:ℝ)^(1+ε) * (q:ℝ)^(-θ) = (q:ℝ)^(ε-θ) := by
      rw [← Real.rpow_add hqpos, ← Real.rpow_add hqpos]
      congr 1
      ring
    have hstep : (q:ℝ)⁻¹ * (C0 * (q:ℝ)^(1+ε) *
          (1/(q:ℝ) + 1/(q:ℝ) + 1/(q:ℝ)^(d-1) + (q:ℝ)/(q:ℝ)^d)^θ)
        ≤ (q:ℝ)⁻¹ * (C0 * (q:ℝ)^(1+ε) * (4 * (q:ℝ)⁻¹)^θ) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_mul_of_nonneg_left hBpow (by positivity)
    calc ‖((q : ℂ))⁻¹ * ∑ r ∈ Finset.range q, Complex.exp (2 * Real.pi * Complex.I *
          ((a : ℝ) / (q : ℝ) * ((Polynomial.eval (r : ℤ) P : ℤ) : ℝ) : ℂ))‖
        = (q:ℝ)⁻¹ * ‖∑ r ∈ Finset.range q, Complex.exp (2 * Real.pi * Complex.I *
          ((a : ℝ) / (q : ℝ) * ((Polynomial.eval (r : ℤ) P : ℤ) : ℝ) : ℂ))‖ := by
          rw [norm_mul, norm_inv, Complex.norm_natCast]
      _ ≤ (q:ℝ)⁻¹ * (C0 * (q:ℝ)^(1+ε) *
            (1/(q:ℝ) + 1/(q:ℝ) + 1/(q:ℝ)^(d-1) + (q:ℝ)/(q:ℝ)^d)^θ) :=
          mul_le_mul_of_nonneg_left hS (by positivity)
      _ ≤ (q:ℝ)⁻¹ * (C0 * (q:ℝ)^(1+ε) * (4 * (q:ℝ)⁻¹)^θ) := hstep
      _ = C0 * (4:ℝ)^θ * (q:ℝ)^(ε-θ) := by rw [key2, key3]
      _ ≤ max 1 (C0 * (4:ℝ)^θ) * (q:ℝ)^(ε-θ) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hqpos.le _)
      _ = max 1 (C0 * (4:ℝ)^θ) * (q:ℝ)^(-(1 / (2 : ℝ) ^ (d - 1)) + ε) := by
          rw [show ε - θ = -(1 / (2 : ℝ) ^ (d - 1)) + ε by rw [hθ_eq]; ring]

end Commons.Analysis.ExponentialSums
