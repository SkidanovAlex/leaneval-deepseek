import Mathlib

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotV5.CensusAux

/-- `fAS = X ^ 3 + X` is not of the form `b ^ 5 - b` in `RatFunc 𝕜` (characteristic 5). -/
theorem fAS_notMem_pe (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5] :
    ¬ ∃ b : RatFunc 𝕜, b ^ 5 - b = RatFunc.X ^ 3 + RatFunc.X := by
  -- Write `b = n / d` with `n = b.num`, `d = b.denom` in lowest terms.
  -- A clean rational function cannot be of the form `℘(b) = b ^ 5 - b`:
  -- in lowest terms `℘(b) = (n ^ 5 - n * d ^ 4) / d ^ 5`, so `d ∣ n ^ 5`, and
  -- coprimality forces `d` to be a unit; hence `d = 1` and `b` is a polynomial `n`.
  -- But for a polynomial of degree `e`, `b ^ 5 - b` has degree `5 * e`, never `3`.
  rintro ⟨b, hb⟩
  have hb' : b ^ 5 - b = algebraMap (Polynomial 𝕜) (RatFunc 𝕜)
      (Polynomial.X ^ 3 + Polynomial.X) := by
    rw [map_add, map_pow, RatFunc.algebraMap_X]
    exact hb
  have hAd : (algebraMap (Polynomial 𝕜) (RatFunc 𝕜)) b.denom ≠ 0 :=
    RatFunc.algebraMap_ne_zero (RatFunc.denom_ne_zero b)
  have hgen : ∀ x y : RatFunc 𝕜, y ≠ 0 → (x / y) ^ 5 - x / y = (x ^ 5 - x * y ^ 4) / y ^ 5 := by
    intro x y hy
    field_simp
  have step : b ^ 5 - b =
      (algebraMap (Polynomial 𝕜) (RatFunc 𝕜) (b.num ^ 5 - b.num * b.denom ^ 4)) /
        (algebraMap (Polynomial 𝕜) (RatFunc 𝕜) (b.denom ^ 5)) := by
    conv_lhs => rw [show b = (algebraMap (Polynomial 𝕜) (RatFunc 𝕜)) b.num /
        (algebraMap (Polynomial 𝕜) (RatFunc 𝕜)) b.denom from (RatFunc.num_div_denom b).symm]
    simp only [map_pow, map_sub, map_mul]
    exact hgen _ _ hAd
  have key : algebraMap (Polynomial 𝕜) (RatFunc 𝕜) (Polynomial.X ^ 3 + Polynomial.X) =
      (algebraMap (Polynomial 𝕜) (RatFunc 𝕜) (b.num ^ 5 - b.num * b.denom ^ 4)) /
        (algebraMap (Polynomial 𝕜) (RatFunc 𝕜) (b.denom ^ 5)) := by
    rw [← hb', step]
  have h5 : (algebraMap (Polynomial 𝕜) (RatFunc 𝕜)) (b.denom ^ 5) ≠ 0 :=
    RatFunc.algebraMap_ne_zero (pow_ne_zero 5 (RatFunc.denom_ne_zero b))
  have hmul : (algebraMap (Polynomial 𝕜) (RatFunc 𝕜)) (Polynomial.X ^ 3 + Polynomial.X) *
      (algebraMap (Polynomial 𝕜) (RatFunc 𝕜)) (b.denom ^ 5) =
      (algebraMap (Polynomial 𝕜) (RatFunc 𝕜)) (b.num ^ 5 - b.num * b.denom ^ 4) := by
    rw [key, div_mul_cancel₀ _ h5]
  -- Clearing denominators gives a polynomial identity.
  have hpoly : (Polynomial.X ^ 3 + Polynomial.X) * b.denom ^ 5 =
      b.num ^ 5 - b.num * b.denom ^ 4 := by
    apply RatFunc.algebraMap_injective 𝕜
    rw [map_mul]
    exact hmul
  have hdvd : b.denom ∣ b.num ^ 5 := by
    have h : b.num ^ 5 = (Polynomial.X ^ 3 + Polynomial.X) * b.denom ^ 5 +
        b.num * b.denom ^ 4 := by
      rw [hpoly]; ring
    rw [h]
    exact dvd_add (dvd_mul_of_dvd_right (dvd_pow_self b.denom (by norm_num)) _)
      (dvd_mul_of_dvd_right (dvd_pow_self b.denom (by norm_num)) _)
  have hunit : IsUnit b.denom :=
    IsCoprime.isUnit_of_dvd (IsCoprime.pow_left (m := 5) (RatFunc.isCoprime_num_denom b)).symm hdvd
  have hd1 : b.denom = 1 := (RatFunc.monic_denom b).eq_one_of_isUnit hunit
  have hbA : b = (algebraMap (Polynomial 𝕜) (RatFunc 𝕜)) b.num := by
    conv_lhs => rw [← RatFunc.num_div_denom b]
    rw [hd1, map_one, div_one]
  -- So `b` is the polynomial `n`, and `n ^ 5 - n = X ^ 3 + X`.
  have hp : b.num ^ 5 - b.num = Polynomial.X ^ 3 + Polynomial.X := by
    apply RatFunc.algebraMap_injective 𝕜
    rw [map_sub, map_pow, ← hbA]
    exact hb'
  have h3 : (Polynomial.X ^ 3 + Polynomial.X : Polynomial 𝕜).natDegree = 3 := by
    rw [Polynomial.natDegree_add_eq_left_of_natDegree_lt
      (by rw [Polynomial.natDegree_X, Polynomial.natDegree_X_pow]; norm_num)]
    exact Polynomial.natDegree_X_pow 3
  have hn5 : (b.num ^ 5 - b.num).natDegree = 3 := by rw [hp, h3]
  -- A degree count: `natDegree (n ^ 5 - n)` is `0` (for constant `n`) or `5 * natDegree n`.
  rcases eq_or_ne b.num 0 with h0 | h0
  · rw [h0] at hn5; simp at hn5
  · rcases eq_or_ne b.num.natDegree 0 with hc | hc
    · have hnC : b.num = Polynomial.C (b.num.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hc
      rw [hnC] at hn5
      simp at hn5
    · have hlt : b.num.natDegree < (b.num ^ 5).natDegree := by
        rw [Polynomial.natDegree_pow]; nlinarith [Nat.pos_of_ne_zero hc]
      rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt hlt, Polynomial.natDegree_pow] at hn5
      omega

end Work.MotV5.CensusAux
