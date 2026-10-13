import Mathlib

/-!
# `π ^ e * X - q` is a nonzerodivisor in `C[X]`

Let `C` be a commutative ring, `π q q₀ : C` with `q - q₀ ∈ (π)` and `q₀` a nonzerodivisor
of `C`.  Then `π ^ e * X - q` is a nonzerodivisor of the polynomial ring `C[X]`.

The mathematical content is the following "climbing" argument.  If `c π ^ e = 0` and
`c q = 0`, write `q = q₀ + π r` (possible since `q - q₀ ∈ (π)`).  Then
`c q₀ = - (c π) r`, so `q₀ (c π ^ k) = -(c π ^ (k+1)) r`; thus `c π ^ (k+1) = 0` forces
`c π ^ k = 0` because `q₀` is a nonzerodivisor.  Descending from `k = e` gives `c = 0`.
By McCoy's theorem (`Polynomial.mem_nonZeroDivisors_iff`) this is exactly the statement
that `π ^ e * X - q` is a nonzerodivisor.
-/

namespace Work.DSM2p

/-- Coefficient `1` of `C u * X - C v`. -/
private lemma coeff_one_CmulX_sub_C {R : Type*} [CommRing R] (u v : R) :
    (Polynomial.C u * Polynomial.X - Polynomial.C v).coeff 1 = u := by simp

/-- Coefficient `0` of `C u * X - C v`. -/
private lemma coeff_zero_CmulX_sub_C {R : Type*} [CommRing R] (u v : R) :
    (Polynomial.C u * Polynomial.X - Polynomial.C v).coeff 0 = -v := by simp

theorem ureg_isSMulRegular {C : Type*} [CommRing C] (π q q₀ : C) (e : ℕ)
    (hq : q - q₀ ∈ Ideal.span {π}) (hq₀ : IsSMulRegular C q₀) :
    IsSMulRegular (Polynomial C) (Polynomial.C (π ^ e) * Polynomial.X - Polynomial.C q) := by
  -- No nonzero constant annihilates `π ^ e * X - q`.
  have key : ∀ c : C, c * π ^ e = 0 → c * q = 0 → c = 0 := by
    intro c
    induction e with
    | zero => intro h1 _; simpa using h1
    | succ e ih =>
        intro h1 h2
        obtain ⟨r, hr⟩ := Ideal.mem_span_singleton.mp hq
        -- `q = q₀ + π * r`
        have hq₀eq : q₀ = q - π * r := by rw [← hr]; ring
        have hcq₀ : c * q₀ = -(c * π) * r := by
          rw [hq₀eq, mul_sub, h2]; ring
        -- peeling one power of `π` off the annihilation
        have hpeel : c * π ^ e = 0 := by
          have h3 : q₀ * (c * π ^ e) = 0 := by
            have e1 : q₀ * (c * π ^ e) = (c * q₀) * π ^ e := by ring
            rw [e1, hcq₀]
            have e2 : (-(c * π) * r) * π ^ e = -(c * π ^ (e + 1)) * r := by
              rw [pow_succ]; ring
            rw [e2, h1]; ring
          exact (IsLeftRegular.mul_left_eq_zero_iff (show IsLeftRegular q₀ from hq₀)).mp h3
        exact ih hpeel h2
  -- McCoy's theorem reduces nonzerodivisor-ness to the statement above.
  have hmem : (Polynomial.C (π ^ e) * Polynomial.X - Polynomial.C q) ∈
      nonZeroDivisors (Polynomial C) := by
    rw [Polynomial.mem_nonZeroDivisors_iff]
    intro a ha
    rw [Polynomial.smul_eq_C_mul] at ha
    have hP' : Polynomial.C (a * π ^ e) * Polynomial.X - Polynomial.C (a * q) = 0 := by
      rw [← ha, Polynomial.C_mul, Polynomial.C_mul]
      ring
    have h1 : a * π ^ e = 0 := by
      have hc : (Polynomial.C (a * π ^ e) * Polynomial.X - Polynomial.C (a * q)).coeff 1 = 0 := by
        rw [hP', Polynomial.coeff_zero]
      rw [coeff_one_CmulX_sub_C] at hc
      exact hc
    have h2 : a * q = 0 := by
      have hc : (Polynomial.C (a * π ^ e) * Polynomial.X - Polynomial.C (a * q)).coeff 0 = 0 := by
        rw [hP', Polynomial.coeff_zero]
      rw [coeff_zero_CmulX_sub_C] at hc
      exact neg_eq_zero.mp hc
    exact key a h1 h2
  have hreg : IsLeftRegular (Polynomial.C (π ^ e) * Polynomial.X - Polynomial.C q) := by
    intro x y hxy
    have hxy' : (Polynomial.C (π ^ e) * Polynomial.X - Polynomial.C q) * x =
        (Polynomial.C (π ^ e) * Polynomial.X - Polynomial.C q) * y := hxy
    have hz : (Polynomial.C (π ^ e) * Polynomial.X - Polynomial.C q) * (x - y) = 0 := by
      rw [mul_sub, hxy', sub_self]
    have hzy : x - y = 0 := (mem_nonZeroDivisors_iff_left.mp hmem) (x - y) hz
    exact sub_eq_zero.mp hzy
  exact hreg

end Work.DSM2p
