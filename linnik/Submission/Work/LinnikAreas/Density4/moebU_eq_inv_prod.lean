import Mathlib
import Submission.Work.LinnikAreas.Density4.SqfreeCoprimeDefs
import Submission.Work.LinnikAreas.Density4.tprod_dvd_ite_eq

namespace Work.LinnikAreas.Density4

open Finset

/-!
# The value of the Möbius reciprocal sum restricted to `(m, r) = 1`

We prove `moebU r = ζ(2)⁻¹ · ∏_{p ∣ r} (1 - p⁻²)⁻¹`, i.e. the coprimality-restricted
Möbius reciprocal sum equals the Euler product `∏_{p ∤ r} (1 - p⁻²)`.

The strategy is the standard Euler-product expansion: the arithmetic function
`moebRestrict r n = [n ⟂ r] · μ(n)/n²` is multiplicative, its series is absolutely
convergent, and the Euler product of its local factors `1` (for `p ∣ r`) and
`1 - p⁻²` (for `p ∤ r`) is `moebU r`.  Splitting the infinite product over the finite
set `r.primeFactors` and using the Euler product for `ζ(2)` finishes the computation.
-/

/-- The multiplicative arithmetic function `n ↦ [n ⟂ r] · μ(n)/n²`, whose series is
`moebU r`. -/
noncomputable def moebRestrict (r : ℕ) : ArithmeticFunction ℝ where
  toFun n := if Nat.Coprime n r then (ArithmeticFunction.moebius n : ℝ) / (n : ℝ) ^ 2 else 0
  map_zero' := by
    by_cases h : Nat.Coprime 0 r
    · rw [if_pos h]; simp
    · rw [if_neg h]

lemma moebRestrict_apply (r n : ℕ) :
    moebRestrict r n =
      if Nat.Coprime n r then (ArithmeticFunction.moebius n : ℝ) / (n : ℝ) ^ 2 else 0 := rfl

lemma moebU_eq_tsum_restrict (r : ℕ) :
    moebU r = ∑' n : ℕ, moebRestrict r n := rfl

lemma moebRestrict_one (r : ℕ) : moebRestrict r 1 = 1 := by
  rw [moebRestrict_apply, if_pos (Nat.coprime_one_left r)]
  simp

lemma moebRestrict_mul {r m n : ℕ} (hmn : Nat.Coprime m n) :
    moebRestrict r (m * n) = moebRestrict r m * moebRestrict r n := by
  rw [moebRestrict_apply, moebRestrict_apply, moebRestrict_apply]
  by_cases h : Nat.Coprime (m * n) r
  · have hm : Nat.Coprime m r := (Nat.coprime_mul_iff_left.mp h).1
    have hn : Nat.Coprime n r := (Nat.coprime_mul_iff_left.mp h).2
    rw [if_pos h, if_pos hm, if_pos hn,
      ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime
        (Nat.coprime_iff_gcd_eq_one.mp hmn)]
    push_cast
    ring
  · rw [if_neg h]
    by_cases hm : Nat.Coprime m r
    · by_cases hn : Nat.Coprime n r
      · exact absurd (Nat.coprime_mul_iff_left.mpr ⟨hm, hn⟩) h
      · rw [if_pos hm, if_neg hn, mul_zero]
    · rw [if_neg hm, zero_mul]

lemma moebRestrict_multiplicative (r : ℕ) : (moebRestrict r).IsMultiplicative :=
  ⟨moebRestrict_one r, fun {_ _} hmn => moebRestrict_mul hmn⟩

lemma moebRestrict_summable (r : ℕ) : Summable (fun n : ℕ => ‖moebRestrict r n‖) := by
  rw [summable_norm_iff]
  refine Summable.of_norm_bounded hasSum_zeta_two.summable (fun n => ?_)
  rw [moebRestrict_apply]
  by_cases h : Nat.Coprime n r
  · rw [if_pos h, Real.norm_eq_abs, abs_div, abs_of_nonneg (sq_nonneg (n : ℝ))]
    rw [div_eq_mul_inv, div_eq_mul_inv, one_mul]
    have h1 : |((ArithmeticFunction.moebius n : ℤ) : ℝ)| ≤ 1 := by
      rw [← Int.cast_abs]; exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    calc |((ArithmeticFunction.moebius n : ℤ) : ℝ)| * (↑n ^ 2)⁻¹
        ≤ 1 * (↑n ^ 2)⁻¹ :=
          mul_le_mul_of_nonneg_right h1 (inv_nonneg.mpr (sq_nonneg (n : ℝ)))
      _ = (↑n ^ 2)⁻¹ := one_mul _
  · rw [if_neg h, norm_zero]
    exact div_nonneg zero_le_one (sq_nonneg (n : ℝ))

/-- The local Euler factor of `moebRestrict r` at a prime `p`. -/
lemma moebRestrict_local (r : ℕ) {p : ℕ} (hp : Nat.Prime p) :
    (∑' e : ℕ, moebRestrict r (p ^ e)) = if p ∣ r then 1 else 1 - 1 / (p : ℝ) ^ 2 := by
  have hsupp : ∀ e ∉ ({0, 1} : Finset ℕ), moebRestrict r (p ^ e) = 0 := by
    intro e he
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at he
    obtain ⟨he0, he1⟩ := he
    rw [moebRestrict_apply]
    have hz : ((ArithmeticFunction.moebius (p ^ e) : ℤ) : ℝ) = 0 := by
      rw [ArithmeticFunction.moebius_apply_prime_pow hp (by omega : e ≠ 0), if_neg he1]
      simp
    rw [hz]
    by_cases hc : Nat.Coprime (p ^ e) r <;> simp [hc]
  rw [tsum_eq_sum hsupp, Finset.sum_pair (by norm_num : (0 : ℕ) ≠ 1)]
  rw [pow_zero, pow_one, moebRestrict_one]
  have hpM : moebRestrict r p = if p ∣ r then 0 else -1 / (p : ℝ) ^ 2 := by
    rw [moebRestrict_apply]
    by_cases h : p ∣ r
    · rw [if_neg (fun hc => ((hp.coprime_iff_not_dvd).mp hc) h)]
      simp [h]
    · rw [if_pos ((hp.coprime_iff_not_dvd).mpr h), ArithmeticFunction.moebius_apply_prime hp]
      push_cast
      simp [h]
  rw [hpM]
  by_cases h : p ∣ r
  · simp [h]
  · rw [if_neg h, if_neg h]; ring

/-- The Euler product for the coprimality-restricted Möbius reciprocal sum. -/
lemma moebU_euler (r : ℕ) :
    moebU r = ∏' p : Nat.Primes,
      (if (p : ℕ) ∣ r then (1 : ℝ) else 1 - 1 / ((p : ℕ) : ℝ) ^ 2) := by
  have h := ArithmeticFunction.IsMultiplicative.eulerProduct_tprod (f := moebRestrict r)
        (moebRestrict_multiplicative r) (moebRestrict_summable r)
  have h2 : moebU r = ∏' p : Nat.Primes, ∑' e : ℕ, moebRestrict r ((p : ℕ) ^ e) := by
    rw [moebU_eq_tsum_restrict]; exact h.symm
  exact h2.trans (tprod_congr (fun p => moebRestrict_local r p.2))

/-- `zeta2 = π²/6` as a real number. -/
lemma zeta2_eq_pi_sq_div_six : zeta2 = Real.pi ^ 2 / 6 := by
  unfold zeta2
  have hcast : riemannZeta 2 = ((Real.pi ^ 2 / 6 : ℝ) : ℂ) := by
    rw [riemannZeta_two]; push_cast; ring
  rw [hcast, Complex.ofReal_re]

/-- The Euler product `∏'_p (1 - p⁻²) = ζ(2)⁻¹` for the Riemann zeta value at `2`. -/
lemma tprod_primes_one_sub_inv_sq :
    ∏' p : Nat.Primes, (1 - 1 / ((p : ℕ) : ℝ) ^ 2) = zeta2⁻¹ := by
  have key : ∏' p : Nat.Primes, (1 - 1 / ((p : ℕ) : ℝ) ^ 2) = (Real.pi ^ 2 / 6)⁻¹ := by
    let f : ℕ →*₀ ℝ :=
      { toFun := fun n => ((n : ℝ) ^ 2)⁻¹
        map_zero' := by simp
        map_one' := by simp
        map_mul' := by
          intro a b
          push_cast
          rw [mul_pow, mul_inv] }
    have hsum : Summable (fun n : ℕ => ‖f n‖) := by
      rw [summable_norm_iff]
      exact hasSum_zeta_two.summable.congr fun n => by simp [f]
    have hval : ∑' n : ℕ, f n = Real.pi ^ 2 / 6 := by
      rw [← hasSum_zeta_two.tsum_eq]
      exact tsum_congr fun n => by simp [f]
    have hne : (∑' n : ℕ, f n) ≠ 0 := by
      rw [hval]; positivity
    have h2 := (EulerProduct.eulerProduct_completely_multiplicative_hasProd hsum).inv₀ hne
    have h3 : ∏' p : Nat.Primes, (((1 - f ↑p)⁻¹)⁻¹) = (∑' n : ℕ, f n)⁻¹ := h2.tprod_eq
    simp only [inv_inv] at h3
    rw [← hval, ← h3]
    exact tprod_congr fun p => by simp [f]
  rw [key, zeta2_eq_pi_sq_div_six]

theorem moebU_eq_inv_prod (r : ℕ) (hr : 1 ≤ r) :
    moebU r = zeta2⁻¹ * ∏ p ∈ r.primeFactors, (1 - 1 / (p : ℝ) ^ 2)⁻¹ := by
  rw [moebU_euler r, tprod_dvd_ite_eq r hr, tprod_primes_one_sub_inv_sq,
    Finset.prod_inv_distrib]

end Work.LinnikAreas.Density4
