import Mathlib
import Submission.Work.C17.seventeen_defs

/-!
# The low part (`i ≤ 2`) of the six `J`-data identities

For `i : Fin 6` with `(i : ℕ) ≤ 2` the exponent `(i : ℤ) - 4` is `-4`, `-3`, `-2`, and the
rational function `yQ ^ ((i:ℤ)-4) * dyQ ∈ ℚ(x)` has the explicit reduced forms

* `yQ⁻⁴ · dyQ = (x-1)²(x-2)/x⁷`,
* `yQ⁻³ · dyQ = (x-1)(x-2)/x⁵`,
* `yQ⁻² · dyQ = (x-2)/x³`.

Each is written below as a quotient `P / Q` of honest polynomials over `ℚ`, with the denominator
nonvanishing away from `0` (which is where the pole of `yQ⁻ᵏ` sits); the accompanying *value*
identity `P(z)/Q(z) = yC z ^ ((i:ℤ)-4) · (z²-2z)/(z-1)²` holds for every `z ≠ 0, 1`.
-/

namespace Work.C17I

private lemma ratX_ne_zero : (RatFunc.X : RatFunc ℚ) ≠ 0 := RatFunc.X_ne_zero

private lemma ratX_sub_one_ne_zero : (RatFunc.X : RatFunc ℚ) - 1 ≠ 0 := by
  intro h
  have h2 : (RatFunc.X : RatFunc ℚ) = 1 := sub_eq_zero.mp h
  rw [← RatFunc.algebraMap_X, ← map_one (algebraMap (Polynomial ℚ) (RatFunc ℚ))] at h2
  have h3 : (Polynomial.X : Polynomial ℚ) = 1 :=
    IsFractionRing.injective (Polynomial ℚ) (RatFunc ℚ) h2
  have h4 : (Polynomial.X - 1 : Polynomial ℚ) ≠ 0 := by
    intro hh
    have hc := congrArg (fun p : Polynomial ℚ => p.eval 0) hh
    norm_num at hc
  exact h4 (sub_eq_zero.mpr h3)

private lemma low_R2 :
    Work.C17.yQ ^ ((-2 : ℤ)) * Work.C17.dyQ
      = algebraMap (Polynomial ℚ) (RatFunc ℚ) (Polynomial.X - 2)
        / algebraMap (Polynomial ℚ) (RatFunc ℚ) (Polynomial.X ^ 3) := by
  have hx : (RatFunc.X : RatFunc ℚ) ≠ 0 := ratX_ne_zero
  have hx1 : (RatFunc.X : RatFunc ℚ) - 1 ≠ 0 := ratX_sub_one_ne_zero
  have hyQ : Work.C17.yQ ≠ 0 := by
    rw [Work.C17.yQ, Work.C17.xQ]
    exact div_ne_zero (pow_ne_zero 2 hx) hx1
  rw [zpow_neg]
  simp only [Work.C17.yQ, Work.C17.xQ, Work.C17.dyQ, RatFunc.algebraMap_X, map_sub, map_pow,
    map_ofNat]
  field_simp

private lemma low_R3 :
    Work.C17.yQ ^ ((-3 : ℤ)) * Work.C17.dyQ
      = algebraMap (Polynomial ℚ) (RatFunc ℚ) ((Polynomial.X - 1) * (Polynomial.X - 2))
        / algebraMap (Polynomial ℚ) (RatFunc ℚ) (Polynomial.X ^ 5) := by
  have hx : (RatFunc.X : RatFunc ℚ) ≠ 0 := ratX_ne_zero
  have hx1 : (RatFunc.X : RatFunc ℚ) - 1 ≠ 0 := ratX_sub_one_ne_zero
  have hyQ : Work.C17.yQ ≠ 0 := by
    rw [Work.C17.yQ, Work.C17.xQ]
    exact div_ne_zero (pow_ne_zero 2 hx) hx1
  rw [zpow_neg]
  simp only [Work.C17.yQ, Work.C17.xQ, Work.C17.dyQ, RatFunc.algebraMap_X, map_sub, map_pow,
    map_ofNat, map_mul, map_one]
  field_simp

private lemma low_R4 :
    Work.C17.yQ ^ ((-4 : ℤ)) * Work.C17.dyQ
      = algebraMap (Polynomial ℚ) (RatFunc ℚ) ((Polynomial.X - 1) ^ 2 * (Polynomial.X - 2))
        / algebraMap (Polynomial ℚ) (RatFunc ℚ) (Polynomial.X ^ 7) := by
  have hx : (RatFunc.X : RatFunc ℚ) ≠ 0 := ratX_ne_zero
  have hx1 : (RatFunc.X : RatFunc ℚ) - 1 ≠ 0 := ratX_sub_one_ne_zero
  have hyQ : Work.C17.yQ ≠ 0 := by
    rw [Work.C17.yQ, Work.C17.xQ]
    exact div_ne_zero (pow_ne_zero 2 hx) hx1
  rw [zpow_neg]
  simp only [Work.C17.yQ, Work.C17.xQ, Work.C17.dyQ, RatFunc.algebraMap_X, map_sub, map_pow,
    map_ofNat, map_mul, map_one]
  field_simp

private lemma low_F2 {z : ℂ} (hz0 : z ≠ 0) (hz1 : z ≠ 1) :
    ((Polynomial.X - 2 : Polynomial ℚ)).eval₂ (algebraMap ℚ ℂ) z
        / ((Polynomial.X ^ 3 : Polynomial ℚ)).eval₂ (algebraMap ℚ ℂ) z
      = Work.C17.yC z ^ ((-2 : ℤ)) * ((z ^ 2 - 2 * z) / (z - 1) ^ 2) := by
  simp only [Polynomial.eval₂_sub, Polynomial.eval₂_X, Polynomial.eval₂_pow, Polynomial.eval₂_ofNat]
  rw [Work.C17.yC]
  have hy : z ^ 2 / (z - 1) ≠ 0 := div_ne_zero (pow_ne_zero 2 hz0) (sub_ne_zero.mpr hz1)
  rw [zpow_neg]
  field_simp

private lemma low_F3 {z : ℂ} (hz0 : z ≠ 0) (hz1 : z ≠ 1) :
    (((Polynomial.X - 1) * (Polynomial.X - 2) : Polynomial ℚ)).eval₂ (algebraMap ℚ ℂ) z
        / ((Polynomial.X ^ 5 : Polynomial ℚ)).eval₂ (algebraMap ℚ ℂ) z
      = Work.C17.yC z ^ ((-3 : ℤ)) * ((z ^ 2 - 2 * z) / (z - 1) ^ 2) := by
  simp only [Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_X,
    Polynomial.eval₂_one, Polynomial.eval₂_ofNat, Polynomial.eval₂_pow]
  rw [Work.C17.yC]
  have hy : z ^ 2 / (z - 1) ≠ 0 := div_ne_zero (pow_ne_zero 2 hz0) (sub_ne_zero.mpr hz1)
  rw [zpow_neg]
  field_simp

private lemma low_F4 {z : ℂ} (hz0 : z ≠ 0) (hz1 : z ≠ 1) :
    (((Polynomial.X - 1) ^ 2 * (Polynomial.X - 2) : Polynomial ℚ)).eval₂ (algebraMap ℚ ℂ) z
        / ((Polynomial.X ^ 7 : Polynomial ℚ)).eval₂ (algebraMap ℚ ℂ) z
      = Work.C17.yC z ^ ((-4 : ℤ)) * ((z ^ 2 - 2 * z) / (z - 1) ^ 2) := by
  simp only [Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_X,
    Polynomial.eval₂_one, Polynomial.eval₂_ofNat, Polynomial.eval₂_pow]
  rw [Work.C17.yC]
  have hy : z ^ 2 / (z - 1) ≠ 0 := div_ne_zero (pow_ne_zero 2 hz0) (sub_ne_zero.mpr hz1)
  rw [zpow_neg]
  field_simp

theorem J_data_low (i : Fin 6) (hi : (i : ℕ) ≤ 2) {U : Set ℂ}
    (h0 : ∀ z ∈ U, z ≠ 0) (h1 : ∀ z ∈ U, z ≠ 1) :
    ∃ P Q : Polynomial ℚ, Q ≠ 0 ∧
      (∀ z ∈ U, Q.eval₂ (algebraMap ℚ ℂ) z ≠ 0) ∧
      Work.C17.yQ ^ ((i : ℤ) - 4) * Work.C17.dyQ
        = algebraMap (Polynomial ℚ) (RatFunc ℚ) P / algebraMap (Polynomial ℚ) (RatFunc ℚ) Q ∧
      (∀ z ∈ U, P.eval₂ (algebraMap ℚ ℂ) z / Q.eval₂ (algebraMap ℚ ℂ) z
        = Work.C17.yC z ^ ((i : ℤ) - 4) * ((z ^ 2 - 2 * z) / (z - 1) ^ 2)) := by
  have hi' : (i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ (i : ℕ) = 2 := by omega
  rcases hi' with h | h | h
  · have hz : (i : ℤ) - 4 = -4 := by
      rw [show (i : ℤ) = ((i : ℕ) : ℤ) from rfl, h]; norm_num
    refine ⟨(Polynomial.X - 1) ^ 2 * (Polynomial.X - 2), Polynomial.X ^ 7, ?_, ?_, ?_, ?_⟩
    · exact pow_ne_zero 7 Polynomial.X_ne_zero
    · intro z hzU
      simp only [Polynomial.eval₂_pow, Polynomial.eval₂_X]
      exact pow_ne_zero 7 (h0 z hzU)
    · rw [hz]; exact low_R4
    · intro z hzU
      rw [hz]; exact low_F4 (h0 z hzU) (h1 z hzU)
  · have hz : (i : ℤ) - 4 = -3 := by
      rw [show (i : ℤ) = ((i : ℕ) : ℤ) from rfl, h]; norm_num
    refine ⟨(Polynomial.X - 1) * (Polynomial.X - 2), Polynomial.X ^ 5, ?_, ?_, ?_, ?_⟩
    · exact pow_ne_zero 5 Polynomial.X_ne_zero
    · intro z hzU
      simp only [Polynomial.eval₂_pow, Polynomial.eval₂_X]
      exact pow_ne_zero 5 (h0 z hzU)
    · rw [hz]; exact low_R3
    · intro z hzU
      rw [hz]; exact low_F3 (h0 z hzU) (h1 z hzU)
  · have hz : (i : ℤ) - 4 = -2 := by
      rw [show (i : ℤ) = ((i : ℕ) : ℤ) from rfl, h]; norm_num
    refine ⟨Polynomial.X - 2, Polynomial.X ^ 3, ?_, ?_, ?_, ?_⟩
    · exact pow_ne_zero 3 Polynomial.X_ne_zero
    · intro z hzU
      simp only [Polynomial.eval₂_pow, Polynomial.eval₂_X]
      exact pow_ne_zero 3 (h0 z hzU)
    · rw [hz]; exact low_R2
    · intro z hzU
      rw [hz]; exact low_F2 (h0 z hzU) (h1 z hzU)

end Work.C17I
