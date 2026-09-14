import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.RingTheory.SimpleRing.Principal

open Polynomial

namespace Commons.Algebra.Polynomial

set_option linter.style.haveILetI false

/-
**Vanishing Wronskian of two polynomials.**  If `p' * q = p * q'` and `q ≠ 0` over a field of
characteristic zero, then `p` is a constant multiple of `q`.

Suggested proof: if `p = 0` take `k = 0`.  Otherwise let `d = gcd p q`, `p₁ = p / d`,
`q₁ = q / d` (so `IsCoprime p₁ q₁`, e.g. `EuclideanDomain.isCoprime_div_gcd_div_gcd`).  Then
`wronskian p q = d^2 * wronskian p₁ q₁`, so `wronskian p₁ q₁ = 0`; by
`IsCoprime.wronskian_eq_zero_iff` both `p₁` and `q₁` have zero derivative, hence are constants
(`Polynomial.eq_C_of_derivative_eq_zero`); finally `p = (a/b) • q`. -/
theorem wronskian_eq_zero_ratio {K : Type*} [Field K] [CharZero K]
    {p q : Polynomial K} (hq : q ≠ 0)
    (h : Polynomial.derivative p * q = p * Polynomial.derivative q) :
    ∃ k : K, p = Polynomial.C k * q := by
  classical
  by_cases hp : p = 0
  · exact ⟨0, by rw [hp]; simp⟩
  haveI : GCDMonoid (Polynomial K) := EuclideanDomain.gcdMonoid (Polynomial K)
  let d : Polynomial K := GCDMonoid.gcd p q
  let p₁ : Polynomial K := p / d
  let q₁ : Polynomial K := q / d
  have hdvd_p : d ∣ p := GCDMonoid.gcd_dvd_left p q
  have hdvd_q : d ∣ q := GCDMonoid.gcd_dvd_right p q
  have hd_ne : d ≠ 0 := by
    intro h0
    obtain ⟨c, hc⟩ := hdvd_p
    rw [h0, zero_mul] at hc
    exact hp hc
  have hp_eq : d * p₁ = p := by
    dsimp only [p₁, d]
    exact EuclideanDomain.mul_div_cancel' hd_ne hdvd_p
  have hq_eq : d * q₁ = q := by
    dsimp only [q₁, d]
    exact EuclideanDomain.mul_div_cancel' hd_ne hdvd_q
  have hq₁_ne : q₁ ≠ 0 := by
    intro h0
    apply hq
    rw [← hq_eq, h0, mul_zero]
  have hcop : IsCoprime p₁ q₁ := by
    have h' := isCoprime_div_gcd_div_gcd (p := p) (q := q) hq
    simpa only [p₁, q₁, d] using h'
  -- the wronskian identity descends through the common factor `d`
  have hderiv : Polynomial.derivative p₁ * q₁ = p₁ * Polynomial.derivative q₁ := by
    have key : Polynomial.derivative p * q - p * Polynomial.derivative q
        = d ^ 2 * (Polynomial.derivative p₁ * q₁ - p₁ * Polynomial.derivative q₁) := by
      have e1 : Polynomial.derivative p
          = Polynomial.derivative d * p₁ + d * Polynomial.derivative p₁ := by
        rw [← hp_eq, Polynomial.derivative_mul]
      have e2 : Polynomial.derivative q
          = Polynomial.derivative d * q₁ + d * Polynomial.derivative q₁ := by
        rw [← hq_eq, Polynomial.derivative_mul]
      rw [e1, e2, ← hp_eq, ← hq_eq]
      ring
    have h0 : Polynomial.derivative p * q - p * Polynomial.derivative q = 0 := by rw [h, sub_self]
    rw [key] at h0
    have hd2 : d ^ 2 ≠ 0 := pow_ne_zero 2 hd_ne
    exact sub_eq_zero.mp ((mul_eq_zero.mp h0).resolve_left hd2)
  have hq₁' : Polynomial.derivative q₁ = 0 := by
    by_cases hconst : q₁.natDegree = 0
    · rw [Polynomial.eq_C_of_natDegree_eq_zero hconst, Polynomial.derivative_C]
    · by_contra hne
      have hlt : (Polynomial.derivative q₁).natDegree < q₁.natDegree :=
        Polynomial.natDegree_derivative_lt hconst
      have hdvd : q₁ ∣ p₁ * Polynomial.derivative q₁ :=
        ⟨Polynomial.derivative p₁, by rw [← hderiv, mul_comm]⟩
      have hdvd' : q₁ ∣ Polynomial.derivative q₁ := hcop.symm.dvd_of_dvd_mul_left hdvd
      have hle : q₁.natDegree ≤ (Polynomial.derivative q₁).natDegree :=
        Polynomial.natDegree_le_of_dvd hdvd' hne
      omega
  have hp₁' : Polynomial.derivative p₁ = 0 := by
    have hzero : Polynomial.derivative p₁ * q₁ = 0 := by rw [hderiv, hq₁', mul_zero]
    exact (mul_eq_zero.mp hzero).resolve_right hq₁_ne
  obtain ⟨a, ha⟩ : ∃ a : K, p₁ = Polynomial.C a :=
    ⟨p₁.coeff 0, Polynomial.eq_C_of_derivative_eq_zero hp₁'⟩
  obtain ⟨b, hb⟩ : ∃ b : K, q₁ = Polynomial.C b :=
    ⟨q₁.coeff 0, Polynomial.eq_C_of_derivative_eq_zero hq₁'⟩
  have hb_ne : b ≠ 0 := by
    intro h0
    apply hq₁_ne
    rw [hb, h0, Polynomial.C_0]
  have hCb : Polynomial.C (a / b) * Polynomial.C b = Polynomial.C a := by
    rw [← Polynomial.C_mul, div_mul_cancel₀ a hb_ne]
  refine ⟨a / b, ?_⟩
  rw [← hp_eq, ← hq_eq, ha, hb]
  calc d * Polynomial.C a = Polynomial.C a * d := mul_comm _ _
    _ = (Polynomial.C (a / b) * Polynomial.C b) * d := by rw [hCb]
    _ = Polynomial.C (a / b) * (Polynomial.C b * d) := by rw [mul_assoc]
    _ = Polynomial.C (a / b) * (d * Polynomial.C b) := by rw [mul_comm (Polynomial.C b) d]

end Commons.Algebra.Polynomial