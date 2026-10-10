import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Submission.Commons.NumberTheory.NumberField.Completion.card_residueField_adicCompletionIntegers_eq_pow_inertiaDeg
import Submission.Commons.NumberTheory.NumberField.Completion.exists_isPrimitiveRoot_lift_adicCompletionB
import Submission.Commons.NumberTheory.NumberField.Completion.exists_uniformizer_val_eq_exp_neg_one
import Submission.Commons.NumberTheory.NumberField.Completion.module_free_adicCompletionIntegers
import Submission.Commons.NumberTheory.NumberField.Completion.val_le_exp_neg_iff_mem_maximalIdeal_pow
import Submission.Commons.NumberTheory.NumberField.finrank_adicCompletion_eq_ramificationIdx_mul_inertiaDeg
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The additive `ℤ`-valued valuation exponent on a completed number field

For a number field `K` and a height one prime `q` of `𝓞 K`, the `q`-adic completion `K_q` carries
Mathlib's valuation `Valued.v : K_q → ℤᵐ⁰` (values in `WithZero (Multiplicative ℤ)`).  We define
the corresponding additive exponent

`adicValExp q x = - log (Valued.v x)`

so that `Valued.v x = exp (- adicValExp q x)` for `x ≠ 0`.  For `x` in the ring of integers
`𝒪_q = q.adicCompletionIntegers K` the exponent is the exponent of the maximal ideal in the
principal ideal `(x)` (i.e. the `𝔪`-adic order, "`v x = exp (-n)`"), and for a uniformiser it is
`1`.  The basic API (`adicValExp_mul`, `adicValExp_pow`, the order/membership dictionary
`mem_maximalIdeal_pow_iff_le_adicValExp`) is developed here, together with the arithmetic fact
`adicValExp_intCast` giving the exponent of an integer as `e · v_p (n)`.
-/

namespace Work.SSGRoute.TatePoitouRoute.FinitenessHM

open scoped NumberField WithZero

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

/-- The additive `ℤ`-valued valuation exponent of an element of the `q`-adic completion of a
number field, with junk value `0` at `0`. -/
noncomputable def adicValExp (q : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (x : q.adicCompletion K) : ℤ :=
  - WithZero.log (Valued.v x)

@[simp]
theorem adicValExp_zero (q : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    adicValExp q (0 : q.adicCompletion K) = 0 := by
  simp [adicValExp]

@[simp]
theorem adicValExp_one (q : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    adicValExp q (1 : q.adicCompletion K) = 0 := by
  simp [adicValExp]

theorem exp_neg_adicValExp (q : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    {x : q.adicCompletion K} (hx : x ≠ 0) :
    WithZero.exp (-(adicValExp q x)) = Valued.v x := by
  have h : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
  rw [adicValExp, neg_neg, WithZero.exp_log h]

theorem adicValExp_eq_zero_iff (q : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    {x : q.adicCompletion K} (hx : x ≠ 0) :
    adicValExp q x = 0 ↔ Valued.v x = 1 := by
  have h : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
  rw [adicValExp, neg_eq_zero, ← WithZero.exp_inj (M := ℤ), WithZero.exp_log h,
    WithZero.exp_zero]

theorem adicValExp_mul (q : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    {x y : q.adicCompletion K} (hx : x ≠ 0) (hy : y ≠ 0) :
    adicValExp q (x * y) = adicValExp q x + adicValExp q y := by
  have hx' : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
  have hy' : Valued.v y ≠ 0 := (Valuation.ne_zero_iff _).2 hy
  rw [adicValExp, adicValExp, adicValExp, map_mul, WithZero.log_mul hx' hy']
  ring

theorem adicValExp_pow (q : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    {x : q.adicCompletion K} (hx : x ≠ 0) (n : ℕ) :
    adicValExp q (x ^ n) = (n : ℤ) * adicValExp q x := by
  rw [adicValExp, adicValExp, map_pow, WithZero.log_pow, nsmul_eq_mul]
  ring

theorem adicValExp_neg (q : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    {x : q.adicCompletion K} (hx : x ≠ 0) :
    adicValExp q x⁻¹ = -adicValExp q x := by
  have hprod : x * x⁻¹ = (1 : q.adicCompletion K) := mul_inv_cancel₀ hx
  have h1 : adicValExp q (x * x⁻¹) = adicValExp q (1 : q.adicCompletion K) := by rw [hprod]
  rw [adicValExp_mul q hx (inv_ne_zero hx), adicValExp_one] at h1
  omega

/-- The dictionary between membership in the powers of the maximal ideal of the ring of integers
and the additive exponent. -/
theorem mem_maximalIdeal_pow_iff_le_adicValExp (q : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    {x : q.adicCompletionIntegers K} (hx : (x : q.adicCompletion K) ≠ 0) (n : ℕ) :
    x ∈ IsLocalRing.maximalIdeal (q.adicCompletionIntegers K) ^ n ↔
      (n : ℤ) ≤ adicValExp q (x : q.adicCompletion K) := by
  rw [← Commons.NumberTheory.NumberField.Completion.val_le_exp_neg_iff_mem_maximalIdeal_pow
    q x n, ← exp_neg_adicValExp q hx, WithZero.exp_le_exp, neg_le_neg_iff]

/-- The exponent of a uniformiser is `1`. -/
theorem adicValExp_eq_one_of_uniformizer (q : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    {π : q.adicCompletionIntegers K}
    (hπ : Valued.v (π : q.adicCompletion K) = WithZero.exp (-1 : ℤ)) :
    adicValExp q (π : q.adicCompletion K) = 1 := by
  have hne : (π : q.adicCompletion K) ≠ 0 := by
    rintro h
    rw [h, Valuation.map_zero] at hπ
    exact WithZero.exp_ne_zero hπ.symm
  rw [adicValExp, hπ, WithZero.log_exp]
  ring

/-! ## The derivative of the minimal polynomial of a root of unity, evaluated at it -/

section MinpolyDerivative

variable {A K S : Type*} [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [Field K] [Algebra A K]
  [IsFractionRing A K] [CommRing S] [IsDomain S] [Algebra A S] [Algebra K S] [IsScalarTower A K S]

/-- In a domain, a left factor of a unit is a unit. -/
theorem isUnit_of_mul_isUnit {a b : S} (h : IsUnit (a * b)) : IsUnit a := by
  obtain ⟨u, hu⟩ := h
  have ha0 : a ≠ 0 := fun h0 => u.ne_zero (by rw [hu, h0, zero_mul])
  have h1 : a * (b * ↑u⁻¹) = 1 := by
    rw [← mul_assoc, ← hu, Units.mul_inv]
  have h2 : b * ↑u⁻¹ * a = 1 := by
    have hy : (b * ↑u⁻¹ * a) * (b * ↑u⁻¹ * a - 1) = 0 := by
      have hring : (b * ↑u⁻¹ * a) * (b * ↑u⁻¹ * a - 1)
          = (b * ↑u⁻¹) * (a * (b * ↑u⁻¹)) * a - b * ↑u⁻¹ * a := by ring
      rw [hring, h1, mul_one, sub_self]
    rcases mul_eq_zero.mp hy with h3 | h3
    · exact absurd (by
        calc a = (a * (b * ↑u⁻¹)) * a := by rw [h1, one_mul]
          _ = a * ((b * ↑u⁻¹) * a) := mul_assoc a (b * ↑u⁻¹) a
          _ = 0 := by rw [h3, mul_zero]) ha0
    · exact sub_eq_zero.mp h3
  exact ⟨Units.mkOfMulEqOne a (b * ↑u⁻¹) h1, rfl⟩

variable (x : S)

/-- **The derivative of the minimal polynomial of a root of unity.**  If `x` satisfies `x ^ N = 1`
with `N` a unit in `S` and `x` a unit, then the value at `x` of the derivative of the minimal
polynomial of `x` over `A` (equivalently, over the fraction field `K`) is a unit of `S`. -/
theorem isUnit_aeval_derivative_minpoly (hx : IsIntegral A x) (N : ℕ) (hN : 0 < N)
    (hxN : x ^ N = 1) (hunit : IsUnit ((N : S) * x ^ (N - 1))) :
    IsUnit ((Polynomial.aeval x) (Polynomial.derivative (minpoly A x))) ∧
      IsUnit ((Polynomial.aeval x) (Polynomial.derivative (minpoly K x))) := by
  have hgK : minpoly K x = (minpoly A x).map (algebraMap A K) :=
    minpoly.isIntegrallyClosed_eq_field_fractions' K hx
  have hdvd : minpoly K x ∣ (Polynomial.X ^ N - 1 : Polynomial K) := by
    refine minpoly.dvd (A := K) x ?_
    rw [Polynomial.aeval_sub, Polynomial.aeval_one, Polynomial.aeval_X_pow, hxN, sub_self]
  obtain ⟨hK, hhK⟩ := hdvd
  -- differentiating `X ^ N - 1 = minpoly K x * hK` and evaluating at `x`
  have hderiv : Polynomial.derivative (Polynomial.X ^ N - 1 : Polynomial K)
      = Polynomial.derivative (minpoly K x) * hK + minpoly K x * Polynomial.derivative hK := by
    rw [hhK, Polynomial.derivative_mul]
  have hval : (N : S) * x ^ (N - 1)
      = (Polynomial.aeval x) (Polynomial.derivative (minpoly K x)) * (Polynomial.aeval x) hK := by
    have h1 : (Polynomial.aeval x) (Polynomial.derivative (Polynomial.X ^ N - 1 : Polynomial K))
        = (Polynomial.aeval x) (Polynomial.derivative (minpoly K x) * hK
            + minpoly K x * Polynomial.derivative hK) := by rw [hderiv]
    rw [map_add, map_mul, map_mul, minpoly.aeval, zero_mul, add_zero] at h1
    rw [← h1]
    rw [Polynomial.derivative_sub, Polynomial.derivative_one, sub_zero,
      Polynomial.derivative_X_pow, Polynomial.aeval_mul, Polynomial.aeval_C,
      Polynomial.aeval_X_pow]
    simp
  have h2 : IsUnit ((Polynomial.aeval x) (Polynomial.derivative (minpoly K x))
      * (Polynomial.aeval x) hK) := by
    rw [← hval]; exact hunit
  have h3 : IsUnit ((Polynomial.aeval x) (Polynomial.derivative (minpoly K x))) :=
    isUnit_of_mul_isUnit h2
  have h4 : (Polynomial.aeval x) (Polynomial.derivative (minpoly K x))
      = (Polynomial.aeval x) (Polynomial.derivative (minpoly A x)) := by
    conv_lhs => rw [hgK]
    rw [Polynomial.derivative_map, Polynomial.aeval_map_algebraMap]
  exact ⟨h4 ▸ h3, h3⟩

end MinpolyDerivative

end

end Work.SSGRoute.TatePoitouRoute.FinitenessHM
