import Mathlib
import Submission.Work.A3.Weil.gcdReduction

/-!
# Passage from a rational approximation of `θ` to one of the leading-coefficient phase
(Area A3, `Weil`)

For the polynomial Weyl inequality one repeatedly has to apply the Dirichlet/geometric-sum
bound to the *phase* `Λ = -θ · d! · lc Q` (the slope of the affine phase obtained after
`d - 1`-fold Weyl differencing, `d = natDegree Q`) rather than to `θ` itself.  This file
performs the elementary bookkeeping: an approximation `|θ - a/q| ≤ 1/q²` with `IsCoprime a q`
is converted into an approximation `|Λ - a'/q'| ≤ M³/q'²` where `M = weylConst Q = d!·|lc Q|`
and the new denominator satisfies `q' ≤ q ≤ M·q'`.

The arithmetic input is `Work.A3.Weil.gcdReduction`: writing `g = gcd(M, q)`, `q' = q/g` and
`b = (M/g)·a`, the rational number `b/q' = M·a/q` is in lowest terms, both `b` and `-b` are
coprime to `q'`, and `q' ≤ q ≤ M·q'`.  Depending on the sign of the leading coefficient of `Q`
one of `b`, `-b` is the required numerator, and since `M ≥ 1` the resulting error
`M·|θ - a/q| ≤ M/q² ≤ M³/q'²` is within the bound of the statement.
-/

set_option autoImplicit false

namespace Work.A3.Weil

open Polynomial

/-- Elementary comparison of the two error terms: a larger numerator and a smaller denominator
both increase `L/q²`, and `L ≤ L³` for `L ≥ 1`. -/
private lemma div_sq_le (L : ℝ) (q : ℤ) (q' : ℕ) (hL : 1 ≤ L) (hq' : 1 ≤ q')
    (hqq' : (q' : ℝ) ≤ (q : ℝ)) :
    L / (q : ℝ) ^ 2 ≤ L ^ 3 / (q' : ℝ) ^ 2 := by
  have hq'pos : (0 : ℝ) < (q' : ℝ) := by exact_mod_cast hq'
  have hsq : (q' : ℝ) ^ 2 ≤ (q : ℝ) ^ 2 := pow_le_pow_left₀ (le_of_lt hq'pos) hqq' 2
  have h1 : L / (q : ℝ) ^ 2 ≤ L / (q' : ℝ) ^ 2 :=
    div_le_div_of_nonneg_left (by linarith) (pow_pos hq'pos 2) hsq
  have h2 : L / (q' : ℝ) ^ 2 ≤ L ^ 3 / (q' : ℝ) ^ 2 :=
    div_le_div_of_nonneg_right (le_self_pow₀ hL (by norm_num)) (sq_nonneg _)
  linarith

theorem exists_approx_leading (Q : Polynomial ℤ) (θ : ℝ) (a q : ℤ) (hq : 1 ≤ q)
    (hcop : IsCoprime a q) (hd : 2 ≤ Q.natDegree)
    (h : |θ - (a : ℝ) / (q : ℝ)| ≤ 1 / (q : ℝ) ^ 2) :
    ∃ (a' : ℤ) (q' : ℕ), 1 ≤ q' ∧ IsCoprime a' q' ∧ (q' : ℤ) ≤ q ∧
      q ≤ (Work.A3.Weil.weylConst Q : ℤ) * (q' : ℤ) ∧
      |(-θ * ((Nat.factorial Q.natDegree : ℝ) * ((Q.coeff Q.natDegree : ℤ) : ℝ))) - (a' : ℝ) / (q' : ℝ)|
        ≤ ((Work.A3.Weil.weylConst Q : ℝ)) ^ 3 / (q' : ℝ) ^ 2 := by
  -- `M = weylConst Q = d! · |lc Q|` is at least `1`, since `Q ≠ 0` and `d ≥ 2`.
  have hQne : Q ≠ 0 := by
    intro h0; rw [h0] at hd; simp at hd
  have hcne : Q.coeff Q.natDegree ≠ 0 := by
    rw [Polynomial.coeff_natDegree]
    exact Polynomial.leadingCoeff_ne_zero.mpr hQne
  have hM1 : 1 ≤ weylConst Q := by
    have : 0 < weylConst Q := by
      rw [weylConst]
      exact Nat.mul_pos (Nat.factorial_pos _) (Int.natAbs_pos.mpr hcne)
    omega
  -- `d! · lc Q = ± M`.
  have hMabs : ((weylConst Q : ℕ) : ℝ)
      = (Nat.factorial Q.natDegree : ℝ) * |((Q.coeff Q.natDegree : ℤ) : ℝ)| := by
    rw [weylConst, Nat.cast_mul, Nat.cast_natAbs, Int.cast_abs]
  -- The denominator reduction of `M·a/q`.
  obtain ⟨b, q', hq'1, hq'le, hq'leM, hcopb, hcopbneg, hbq⟩ :=
    gcdReduction (weylConst Q) a q hq hcop hM1
  have hL1 : (1 : ℝ) ≤ (weylConst Q : ℝ) := by exact_mod_cast hM1
  have hqq'R : (q' : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq'le
  rcases le_or_gt (0 : ℤ) (Q.coeff Q.natDegree) with hc | hc
  · -- the leading coefficient is non-negative: `Λ = -M·θ`, so `a' = -b`
    refine ⟨-b, q', hq'1, hcopbneg, hq'le, hq'leM, ?_⟩
    have hsign : (Nat.factorial Q.natDegree : ℝ) * ((Q.coeff Q.natDegree : ℤ) : ℝ)
        = (weylConst Q : ℝ) := by
      rw [hMabs, abs_of_nonneg (by exact_mod_cast hc)]
    have hbq' : ((-b : ℤ) : ℝ) / (q' : ℝ)
        = -((weylConst Q : ℝ) * ((a : ℝ) / (q : ℝ))) := by
      rw [show ((-b : ℤ) : ℝ) = -(b : ℝ) by rw [Int.cast_neg]]
      rw [neg_div, hbq]
    have hdiff : |(-θ * ((Nat.factorial Q.natDegree : ℝ) * ((Q.coeff Q.natDegree : ℤ) : ℝ)))
          - ((-b : ℤ) : ℝ) / (q' : ℝ)|
        = (weylConst Q : ℝ) * |θ - (a : ℝ) / (q : ℝ)| := by
      rw [hsign, hbq']
      rw [show -θ * (weylConst Q : ℝ) - -((weylConst Q : ℝ) * ((a : ℝ) / (q : ℝ)))
            = -((weylConst Q : ℝ) * (θ - (a : ℝ) / (q : ℝ))) by ring]
      rw [abs_neg, abs_mul, abs_of_nonneg (by positivity)]
    calc |(-θ * ((Nat.factorial Q.natDegree : ℝ) * ((Q.coeff Q.natDegree : ℤ) : ℝ)))
            - ((-b : ℤ) : ℝ) / (q' : ℝ)|
        = (weylConst Q : ℝ) * |θ - (a : ℝ) / (q : ℝ)| := hdiff
      _ ≤ (weylConst Q : ℝ) * (1 / (q : ℝ) ^ 2) := mul_le_mul_of_nonneg_left h (by positivity)
      _ = (weylConst Q : ℝ) / (q : ℝ) ^ 2 := by ring
      _ ≤ (weylConst Q : ℝ) ^ 3 / (q' : ℝ) ^ 2 := div_sq_le _ _ _ hL1 hq'1 hqq'R
  · -- the leading coefficient is negative: `Λ = M·θ`, so `a' = b`
    refine ⟨b, q', hq'1, hcopb, hq'le, hq'leM, ?_⟩
    have hsign : (Nat.factorial Q.natDegree : ℝ) * ((Q.coeff Q.natDegree : ℤ) : ℝ)
        = -(weylConst Q : ℝ) := by
      rw [hMabs, abs_of_neg (by exact_mod_cast hc)]
      ring
    have hdiff : |(-θ * ((Nat.factorial Q.natDegree : ℝ) * ((Q.coeff Q.natDegree : ℤ) : ℝ)))
          - (b : ℝ) / (q' : ℝ)|
        = (weylConst Q : ℝ) * |θ - (a : ℝ) / (q : ℝ)| := by
      rw [hsign, hbq]
      rw [show -θ * -(weylConst Q : ℝ) - (weylConst Q : ℝ) * ((a : ℝ) / (q : ℝ))
            = (weylConst Q : ℝ) * (θ - (a : ℝ) / (q : ℝ)) by ring]
      rw [abs_mul, abs_of_nonneg (by positivity)]
    calc |(-θ * ((Nat.factorial Q.natDegree : ℝ) * ((Q.coeff Q.natDegree : ℤ) : ℝ)))
            - (b : ℝ) / (q' : ℝ)|
        = (weylConst Q : ℝ) * |θ - (a : ℝ) / (q : ℝ)| := hdiff
      _ ≤ (weylConst Q : ℝ) * (1 / (q : ℝ) ^ 2) := mul_le_mul_of_nonneg_left h (by positivity)
      _ = (weylConst Q : ℝ) / (q : ℝ) ^ 2 := by ring
      _ ≤ (weylConst Q : ℝ) ^ 3 / (q' : ℝ) ^ 2 := div_sq_le _ _ _ hL1 hq'1 hqq'R

end Work.A3.Weil
