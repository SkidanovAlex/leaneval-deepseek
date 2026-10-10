import Mathlib
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotC2

/-- If `(X - a)²` divides a polynomial `p` over a commutative ring, then `p` and its derivative
both vanish at `a`.  Proof: substituting `X ↦ X + a` (`Polynomial.taylor`) turns the factor
`X - C a` into `X`, so `X² ∣ p.taylor a`; the coefficients `0` and `1` of `p.taylor a` are
`p.eval a` and `p.derivative.eval a`. -/
lemma sq_dvd_eval_derivative {R : Type*} [CommRing R] {p : Polynomial R} {a : R}
    (h : (Polynomial.X - Polynomial.C a) ^ 2 ∣ p) :
    p.eval a = 0 ∧ (Polynomial.derivative p).eval a = 0 := by
  obtain ⟨g, rfl⟩ := h
  have ht : Polynomial.taylor a (Polynomial.X - Polynomial.C a : Polynomial R) = Polynomial.X := by
    simp [Polynomial.taylor_apply]
  have h2 : Polynomial.X ^ 2 ∣ Polynomial.taylor a ((Polynomial.X - Polynomial.C a) ^ 2 * g) := by
    rw [Polynomial.taylor_mul, Polynomial.taylor_pow, ht]
    exact dvd_mul_right _ _
  have h0 := Polynomial.X_pow_dvd_iff.mp h2 0 (by norm_num)
  have h1 := Polynomial.X_pow_dvd_iff.mp h2 1 (by norm_num)
  rw [Polynomial.taylor_coeff_zero] at h0
  rw [Polynomial.taylor_coeff_one] at h1
  exact ⟨h0, h1⟩

/-- In characteristic two, the nonsingularity of an elliptic Weierstrass curve with `a₁ ≠ 0`
implies that there is no constant `s ∈ L` with `e² ∣ c - s² - s·e`, where
`e = a₁X + a₃` and `c = X³ + a₂X² + a₄X + a₆` in `L[X]`.

Route.  Suppose `s` is such a constant, and put `x₀ := -a₃/a₁`, so `e(x₀) = 0` and
`e = C a₁ * (X - C x₀)`.  Since `e² ∣ (c - s² - s·e)`, this polynomial vanishes at `x₀` and so
does its derivative, giving `c(x₀) = s²` and `c'(x₀) = a₁·s`.  Put `y₀ := s`.  Then
`y₀² + a₁x₀y₀ + a₃y₀ = c(x₀)` because `a₁x₀ + a₃ = 0`, i.e. `Equation E x₀ y₀` holds.  But
`E.Nonsingular x₀ y₀` fails: by `WeierstrassCurve.Affine.nonsingular_iff` it would require
either `E.a₁ * y₀ ≠ 3 * x₀ ^ 2 + 2 * E.a₂ * x₀ + E.a₄` (false since `a₁y₀ = c'(x₀)` and `h2`
identifies `3 = 1`, `2 = 0`), or `y₀ ≠ -y₀ - E.a₁ * x₀ - E.a₃` (false since `h2` gives
`2y₀ = 0` and `a₁x₀ + a₃ = 0`).  Contradiction with
`WeierstrassCurve.Affine.equation_iff_nonsingular` (valid because `E.IsElliptic`). -/
theorem EllipticCharTwoNonsingular (L : Type*) [Field L] (E : WeierstrassCurve L) [E.IsElliptic]
    (h2 : (2 : L) = 0) (ha₁ : E.a₁ ≠ 0) :
    ¬ ∃ s : L, (Polynomial.C E.a₁ * Polynomial.X + Polynomial.C E.a₃ : Polynomial L) ^ 2 ∣
        (Polynomial.X ^ 3 + Polynomial.C E.a₂ * Polynomial.X ^ 2 + Polynomial.C E.a₄ * Polynomial.X
            + Polynomial.C E.a₆) - Polynomial.C s * Polynomial.C s
          - Polynomial.C s * (Polynomial.C E.a₁ * Polynomial.X + Polynomial.C E.a₃) := by
  rintro ⟨s, hs⟩
  -- the root of `e = a₁X + a₃`
  set x₀ : L := -E.a₃ / E.a₁ with hx₀def
  have hax : E.a₁ * x₀ = -E.a₃ := by
    rw [hx₀def]; field_simp
  set e : Polynomial L := Polynomial.C E.a₁ * Polynomial.X + Polynomial.C E.a₃ with hedef
  set c : Polynomial L := Polynomial.X ^ 3 + Polynomial.C E.a₂ * Polynomial.X ^ 2
      + Polynomial.C E.a₄ * Polynomial.X + Polynomial.C E.a₆ with hcdef
  have hs' : e ^ 2 ∣ c - Polynomial.C s * Polynomial.C s - Polynomial.C s * e := by
    rw [hedef, hcdef]; exact hs
  -- `e` is a constant times `X - x₀`
  have he : e = Polynomial.C E.a₁ * (Polynomial.X - Polynomial.C x₀) := by
    rw [hedef]
    have hC : (Polynomial.C (E.a₁ * x₀) : Polynomial L) = -Polynomial.C E.a₃ := by
      rw [hax]; simp
    rw [mul_sub, ← Polynomial.C_mul, hC]
    first | refl_ring1 | ring
  -- hence `(X - x₀)²` divides `c - s² - s·e`
  have h1 : (Polynomial.X - Polynomial.C x₀) ^ 2 ∣ e ^ 2 := by
    rw [he]
    exact ⟨(Polynomial.C E.a₁) ^ 2, by ring⟩
  have hsq : (Polynomial.X - Polynomial.C x₀) ^ 2 ∣
      c - Polynomial.C s * Polynomial.C s - Polynomial.C s * e := h1.trans hs'
  obtain ⟨hfeval, hfderiv⟩ := sq_dvd_eval_derivative hsq
  have hev : e.eval x₀ = 0 := by rw [he]; simp
  -- `c(x₀) = s²`
  have hfeval' : c.eval x₀ - s * s = 0 := by
    have hh := hfeval
    simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, hev, mul_zero,
      sub_zero] at hh
    exact hh
  have hceval : c.eval x₀ = s ^ 2 := by
    rw [pow_two, ← sub_eq_zero]; exact hfeval'
  -- `c'(x₀) = a₁s`
  have hederiv : Polynomial.derivative e = Polynomial.C E.a₁ := by
    rw [he]; simp [Polynomial.derivative_mul, Polynomial.derivative_sub]
  have hd : Polynomial.derivative (c - Polynomial.C s * Polynomial.C s - Polynomial.C s * e)
      = c.derivative - Polynomial.C (s * E.a₁) := by
    rw [Polynomial.derivative_sub, Polynomial.derivative_sub, Polynomial.derivative_mul,
      Polynomial.derivative_mul, hederiv]
    simp [Polynomial.C_mul]
  have hfderiv' : c.derivative.eval x₀ - s * E.a₁ = 0 := by
    have hh := hfderiv
    rw [hd] at hh
    simp only [Polynomial.eval_sub, Polynomial.eval_C] at hh
    exact hh
  have hcderiv : c.derivative.eval x₀ = E.a₁ * s := by
    rw [mul_comm E.a₁ s, ← sub_eq_zero]; exact hfderiv'
  have hcderivval : c.derivative.eval x₀ = 3 * x₀ ^ 2 + 2 * E.a₂ * x₀ + E.a₄ := by
    rw [hcdef]; simp; ring
  have hX : E.a₁ * s = 3 * x₀ ^ 2 + 2 * E.a₂ * x₀ + E.a₄ := hcderiv.symm.trans hcderivval
  have hax' : E.a₁ * x₀ + E.a₃ = 0 := by rw [hax]; ring
  have hY : 2 * s + E.a₁ * x₀ + E.a₃ = 0 := by
    rw [h2, zero_mul, zero_add]; exact hax'
  -- the Weierstrass equation holds at `(x₀, s)`
  have hcval : c.eval x₀ = x₀ ^ 3 + E.a₂ * x₀ ^ 2 + E.a₄ * x₀ + E.a₆ := by
    rw [hcdef]; simp
  have heq : WeierstrassCurve.Affine.Equation E x₀ s := by
    rw [WeierstrassCurve.Affine.equation_iff]
    have hR : x₀ ^ 3 + E.a₂ * x₀ ^ 2 + E.a₄ * x₀ + E.a₆ = s ^ 2 := by rw [← hcval, hceval]
    have hL : s ^ 2 + E.a₁ * x₀ * s + E.a₃ * s = s ^ 2 := by
      linear_combination (norm := first | refl_ring1 | ring1) (s : L) * hax'
    rw [hL, hR]
  -- but `(x₀, s)` is singular
  have hns : ¬ WeierstrassCurve.Affine.Nonsingular E x₀ s := by
    rw [WeierstrassCurve.Affine.nonsingular_iff]
    rintro ⟨-, h | h⟩
    · exact h hX
    · exact h (by linear_combination hY)
  exact hns ((WeierstrassCurve.Affine.equation_iff_nonsingular).mp heq)

end Work.MotC2
