import Mathlib
import Submission.Work.MotK.TGen.ZElim2Defs
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotK.TGen.ZElim2Case14`

The linear form `rX₀ - ηX₁ + τ` with `η⁵ = 1` does not divide the normalised plane model
`g0p r = r⁷X₀⁵ - r³(3+r⁵)X₀²X₁ + (1+2r⁵)X₀X₁³ - r²X₁⁵ + r²` of the residual curve,
provided `r ≠ 0`, `char ≠ 5` and the Klein discriminant `1 - 11r⁵ - r¹⁰` does not vanish.

## The argument

Substituting `X₀ = ηX`, `X₁ = rX + τη⁴` (using `η⁴` in place of `η⁻¹` keeps everything
fraction free; note `η⁴ = η⁻¹` since `η⁵ = 1`) the linear form maps to
`rηX - η(rX + τη⁴) + τ = τ(1 - η⁵) = 0`.  Hence the image of `g0p r` under this substitution
is the zero polynomial.  Comparing the coefficients of `X⁰, X³, X⁴` gives

* `τ⁵ = 1`,
* `1 + 2r⁵ = 5η³r³τ`,
* `3 + r⁵ = 5ηrτ²`.

From these, `(1+2r⁵)⁵ = 3125·(r⁵)³`, `(3+r⁵)⁵ = 3125·r⁵` and `(3+r⁵)³ = 25(1+2r⁵)`.  Writing
`u = 3 + r⁵` these say `u⁵ = 3125(u-3)` and `u³ = 50u - 125`, whence
`125(u² + 5u - 25) = 0`, i.e. `u² + 5u - 25 = 0`.  But then
`1 - 11r⁵ - r¹⁰ = -(u² + 5u - 25) = 0`, contradicting `hdisc`.
-/

set_option maxHeartbeats 1000000

namespace Work.MotK.TGen

open MvPolynomial Polynomial

/-- The substitution `X₀ ↦ ηX`, `X₁ ↦ rX + τη⁴` into a polynomial in one variable `X`.
(With `η⁵ = 1` the element `η⁴` plays the role of `η⁻¹`, and no denominators appear.) -/
noncomputable def psi {L : Type*} [Field L] (r η τ : L) : MvPolynomial (Fin 2) L →ₐ[L] Polynomial L :=
  MvPolynomial.aeval
    ![(Polynomial.C η) * Polynomial.X, (Polynomial.C r) * Polynomial.X + Polynomial.C (τ * η^(4:ℕ))]

/-- The substitution kills the linear form `rX₀ - ηX₁ + τ` when `η⁵ = 1`. -/
lemma psi_lin {L : Type*} [Field L] (r η τ : L) (hη : η ^(5:ℕ) = 1) :
    psi r η τ (MvPolynomial.C r * MvPolynomial.X 0 - MvPolynomial.C η * MvPolynomial.X 1
      + MvPolynomial.C τ) = 0 := by
  rw [psi]
  simp only [map_add, map_sub, map_mul, map_pow, MvPolynomial.aeval_C, MvPolynomial.aeval_X,
    Matrix.cons_val_zero, Matrix.cons_val_one, Polynomial.algebraMap_eq,
    Polynomial.C_mul, Polynomial.C_pow, Polynomial.C_add, Polynomial.C_ofNat, Polynomial.C_1]
  have h1 : (Polynomial.C η : Polynomial L) ^(5:ℕ) = 1 := by
    rw [← Polynomial.C_pow, hη, Polynomial.C_1]
  ring_nf
  rw [h1]
  first | refl_ring1 | ring

/-- Explicit expansion of the substituted normalised model. -/
lemma psi_g0p_expand {L : Type*} [Field L] (r η τ : L) :
    psi r η τ (g0p r)
      = Polynomial.C (η^(5:ℕ)*r^(7:ℕ) - r^(7:ℕ)) * Polynomial.X^(5:ℕ)
        + Polynomial.C (η*r^(3:ℕ) + 2*η*r^(8:ℕ) - 5*η^(4:ℕ)*r^(6:ℕ)*τ) * Polynomial.X^(4:ℕ)
        + Polynomial.C (-10*η^(8:ℕ)*r^(5:ℕ)*τ^(2:ℕ) + 6*η^(5:ℕ)*r^(7:ℕ)*τ + 3*η^(5:ℕ)*r^(2:ℕ)*τ - η^(2:ℕ)*r^(9:ℕ) - 3*η^(2:ℕ)*r^(4:ℕ))
            * Polynomial.X^(3:ℕ)
        + Polynomial.C (-10*η^(12:ℕ)*r^(4:ℕ)*τ^(3:ℕ) + 6*η^(9:ℕ)*r^(6:ℕ)*τ^(2:ℕ) + 3*η^(9:ℕ)*r*τ^(2:ℕ) - η^(6:ℕ)*r^(8:ℕ)*τ
            - 3*η^(6:ℕ)*r^(3:ℕ)*τ) * Polynomial.X^(2:ℕ)
        + Polynomial.C (-5*η^(16:ℕ)*r^(3:ℕ)*τ^(4:ℕ) + 2*η^(13:ℕ)*r^(5:ℕ)*τ^(3:ℕ) + η^(13:ℕ)*τ^(3:ℕ)) * Polynomial.X
        + Polynomial.C (r^(2:ℕ) - η^(20:ℕ)*r^(2:ℕ)*τ^(5:ℕ)) := by
  rw [psi, g0p]
  simp only [map_add, map_sub, map_mul, map_pow, MvPolynomial.aeval_C, MvPolynomial.aeval_X,
    Matrix.cons_val_zero, Matrix.cons_val_one, Polynomial.algebraMap_eq,
    Polynomial.C_mul, Polynomial.C_pow, Polynomial.C_add, Polynomial.C_ofNat, Polynomial.C_1,
    Polynomial.C_neg, Polynomial.C_0, Polynomial.C_sub]
  first | refl_ring1 | ring

/-- The constant coefficient of the substituted model. -/
lemma psi_g0p_coeff0 {L : Type*} [Field L] (r η τ : L) (hη : η ^(5:ℕ) = 1) :
    (psi r η τ (g0p r)).coeff 0 = r^(2:ℕ)*(1 - τ^(5:ℕ)) := by
  rw [psi_g0p_expand]
  have h20 : η ^(20:ℕ) = 1 := by
    rw [show (20 : ℕ) = 5 * 4 by norm_num, pow_mul, hη, one_pow]
  simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
    Polynomial.C_pow, Polynomial.coeff_C, Polynomial.coeff_X]
  rw [h20]
  -- the residue of `Polynomial.coeff_X_pow` is a `if k = n then 1 else 0`, which `norm_num`
  -- evaluates before `ring` normalizes the identity
  norm_num
  first | refl_ring1 | ring

/-- The `X³`-coefficient of the substituted model. -/
lemma psi_g0p_coeff3 {L : Type*} [Field L] (r η τ : L) (hη : η ^(5:ℕ) = 1) :
    (psi r η τ (g0p r)).coeff 3
      = -η^(2:ℕ)*r^(4:ℕ)*(3 + r^(5:ℕ)) + 3*r^(2:ℕ)*τ*(1 + 2*r^(5:ℕ)) - 10*η^(3:ℕ)*r^(5:ℕ)*τ^(2:ℕ) := by
  rw [psi_g0p_expand]
  have h8 : η ^(8:ℕ) = η ^(3:ℕ) := by
    rw [show (8 : ℕ) = 5 + 3 by norm_num, pow_add, hη, one_mul]
  simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
    Polynomial.C_pow, Polynomial.coeff_C, Polynomial.coeff_X]
  rw [h8, hη]
  norm_num
  first | refl_ring1 | ring

/-- The `X⁴`-coefficient of the substituted model. -/
lemma psi_g0p_coeff4 {L : Type*} [Field L] (r η τ : L) :
    (psi r η τ (g0p r)).coeff 4 = η*r^(3:ℕ)*(1 + 2*r^(5:ℕ)) - 5*η^(4:ℕ)*r^(6:ℕ)*τ := by
  rw [psi_g0p_expand]
  simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
    Polynomial.C_pow, Polynomial.coeff_C, Polynomial.coeff_X]
  norm_num
  first | refl_ring1 | ring

theorem ZElim2Case14 (L : Type) [Field L] (h5 : (5 : L) ≠ 0) (r η τ : L) (hr : r ≠ 0)
    (hη : η ^(5:ℕ) = 1) (hdisc : 1 - 11 * r ^(5:ℕ) - r ^(10:ℕ) ≠ 0)
    (q : MvPolynomial (Fin 2) L) :
    (MvPolynomial.C r * MvPolynomial.X 0 - MvPolynomial.C η * MvPolynomial.X 1
        + MvPolynomial.C τ) * q ≠ Work.MotK.TGen.g0p r := by
  intro h
  -- the substituted model vanishes
  have hP : psi r η τ (g0p r) = 0 := by
    have h' := congrArg (psi r η τ) h
    rw [map_mul, psi_lin r η τ hη, zero_mul] at h'
    exact h'.symm
  have hc0 : (psi r η τ (g0p r)).coeff 0 = 0 := by rw [hP]; simp
  have hc3 : (psi r η τ (g0p r)).coeff 3 = 0 := by rw [hP]; simp
  have hc4 : (psi r η τ (g0p r)).coeff 4 = 0 := by rw [hP]; simp
  have h0' : r^(2:ℕ)*(1 - τ^(5:ℕ)) = 0 := by rw [← psi_g0p_coeff0 r η τ hη]; exact hc0
  have h4' : η*r^(3:ℕ)*(1 + 2*r^(5:ℕ)) - 5*η^(4:ℕ)*r^(6:ℕ)*τ = 0 := by
    rw [← psi_g0p_coeff4 r η τ]; exact hc4
  have h3' : -η^(2:ℕ)*r^(4:ℕ)*(3 + r^(5:ℕ)) + 3*r^(2:ℕ)*τ*(1 + 2*r^(5:ℕ)) - 10*η^(3:ℕ)*r^(5:ℕ)*τ^(2:ℕ) = 0 := by
    rw [← psi_g0p_coeff3 r η τ hη]; exact hc3
  have heta : η ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by norm_num : (5 : ℕ) ≠ 0)] at hη
    exact zero_ne_one hη
  -- `τ⁵ = 1`
  have hτ5 : τ ^(5:ℕ) = 1 := by
    have hr2 : r ^(2:ℕ) ≠ 0 := pow_ne_zero 2 hr
    have h1 : 1 - τ ^(5:ℕ) = 0 := by
      rcases mul_eq_zero.mp h0' with h1 | h1
      · exact absurd h1 hr2
      · exact h1
    exact (sub_eq_zero.mp h1).symm
  -- `1 + 2r⁵ = 5η³r³τ`
  have hA : 1 + 2*r^(5:ℕ) = 5*η^(3:ℕ)*r^(3:ℕ)*τ := by
    have hne : η*r^(3:ℕ) ≠ 0 := mul_ne_zero heta (pow_ne_zero 3 hr)
    have hh : η*r^(3:ℕ)*(1 + 2*r^(5:ℕ)) = η*r^(3:ℕ)*(5*η^(3:ℕ)*r^(3:ℕ)*τ) := by linear_combination h4'
    exact mul_left_cancel₀ hne hh
  -- `3 + r⁵ = 5ηrτ²`
  have hB : 3 + r^(5:ℕ) = 5*η*r*τ^(2:ℕ) := by
    have hne : η^(2:ℕ)*r^(4:ℕ) ≠ 0 := mul_ne_zero (pow_ne_zero 2 heta) (pow_ne_zero 4 hr)
    have hh : η^(2:ℕ)*r^(4:ℕ)*(3 + r^(5:ℕ)) = η^(2:ℕ)*r^(4:ℕ)*(5*η*r*τ^(2:ℕ)) := by
      linear_combination (norm := first | refl_ring1 | ring1) -h3' + (3*r^(2:ℕ)*τ)*hA
    exact mul_left_cancel₀ hne hh
  have hA5 : (1 + 2*r^(5:ℕ))^(5:ℕ) = 3125 * (r^(5:ℕ))^(3:ℕ) := by
    have h1 : (1 + 2*r^(5:ℕ))^(5:ℕ) = (5*η^(3:ℕ)*r^(3:ℕ)*τ)^(5:ℕ) := by rw [hA]
    rw [h1]
    have h2 : (5*η^(3:ℕ)*r^(3:ℕ)*τ)^(5:ℕ) = 3125 * (r^(5:ℕ))^(3:ℕ) * (η^(5:ℕ))^(3:ℕ) * τ^(5:ℕ) := by ring
    rw [h2, hη, hτ5]
    first | refl_ring1 | ring
  have hB5 : (3 + r^(5:ℕ))^(5:ℕ) = 3125 * r^(5:ℕ) := by
    have h1 : (3 + r^(5:ℕ))^(5:ℕ) = (5*η*r*τ^(2:ℕ))^(5:ℕ) := by rw [hB]
    rw [h1]
    have h2 : (5*η*r*τ^(2:ℕ))^(5:ℕ) = 3125 * r^(5:ℕ) * η^(5:ℕ) * (τ^(5:ℕ))^(2:ℕ) := by ring
    rw [h2, hη, hτ5]
    first | refl_ring1 | ring
  have hB3 : (3 + r^(5:ℕ))^(3:ℕ) = 25 * (1 + 2*r^(5:ℕ)) := by
    have h1 : (3 + r^(5:ℕ))^(3:ℕ) = (5*η*r*τ^(2:ℕ))^(3:ℕ) := by rw [hB]
    rw [h1]
    have h2 : (5*η*r*τ^(2:ℕ))^(3:ℕ) = 25 * (5*η^(3:ℕ)*r^(3:ℕ)*τ) * τ^(5:ℕ) := by ring
    rw [h2, hτ5, hA]
    first | refl_ring1 | ring
  have hu3 : (3 + r^(5:ℕ))^(3:ℕ) = 50*(3 + r^(5:ℕ)) - 125 := by linear_combination hB3
  have hu5 : (3 + r^(5:ℕ))^(5:ℕ) = 3125*(3 + r^(5:ℕ)) - 9375 := by linear_combination hB5
  -- `(3+r⁵)² + 5(3+r⁵) - 25 = 0`
  have h125 : (125 : L) ≠ 0 := by
    have h : (125 : L) = 5^(3:ℕ) := by norm_num
    rw [h]; exact pow_ne_zero 3 h5
  have hsq : (3 + r^(5:ℕ))^(2:ℕ) + 5*(3 + r^(5:ℕ)) - 25 = 0 := by
    have h1 : (3 + r^(5:ℕ))^(2:ℕ) * (50*(3 + r^(5:ℕ)) - 125) = 3125*(3 + r^(5:ℕ)) - 9375 := by
      calc (3 + r^(5:ℕ))^(2:ℕ) * (50*(3 + r^(5:ℕ)) - 125) = (3 + r^(5:ℕ))^(2:ℕ) * (3 + r^(5:ℕ))^(3:ℕ) := by rw [hu3]
        _ = (3 + r^(5:ℕ))^(5:ℕ) := by ring
        _ = 3125*(3 + r^(5:ℕ)) - 9375 := hu5
    have h2 : 50*(50*(3 + r^(5:ℕ)) - 125) - 125*(3 + r^(5:ℕ))^(2:ℕ) = 3125*(3 + r^(5:ℕ)) - 9375 := by
      calc 50*(50*(3 + r^(5:ℕ)) - 125) - 125*(3 + r^(5:ℕ))^(2:ℕ) = 50*(3 + r^(5:ℕ))^(3:ℕ) - 125*(3 + r^(5:ℕ))^(2:ℕ) := by
            rw [hu3]
        _ = (3 + r^(5:ℕ))^(2:ℕ) * (50*(3 + r^(5:ℕ)) - 125) := by ring
        _ = 3125*(3 + r^(5:ℕ)) - 9375 := h1
    have h3 : (125 : L) * ((3 + r^(5:ℕ))^(2:ℕ) + 5*(3 + r^(5:ℕ)) - 25) = 0 := by
      have key : (125 : L)*((3 + r^(5:ℕ))^(2:ℕ) + 5*(3 + r^(5:ℕ)) - 25)
          = -(50*(50*(3 + r^(5:ℕ)) - 125) - 125*(3 + r^(5:ℕ))^(2:ℕ)
              - (3125*(3 + r^(5:ℕ)) - 9375)) := by ring
      rw [key, sub_eq_zero.mpr h2, neg_zero]
    rcases mul_eq_zero.mp h3 with h | h
    · exact absurd h h125
    · exact h
  have hdisc0 : 1 - 11*r^(5:ℕ) - r^(10:ℕ) = 0 := by
    have h : 1 - 11*r^(5:ℕ) - r^(10:ℕ) = -((3 + r^(5:ℕ))^(2:ℕ) + 5*(3 + r^(5:ℕ)) - 25) := by ring
    rw [h, hsq, neg_zero]
  exact hdisc hdisc0

end Work.MotK.TGen
