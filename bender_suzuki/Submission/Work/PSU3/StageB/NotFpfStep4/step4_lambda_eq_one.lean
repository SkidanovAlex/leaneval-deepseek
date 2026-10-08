import Mathlib
import Submission.Work.PSU3.StageB.NotFpfStep4.step4_algebra

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.PSU3.StageB.NotFpfStep4

/-- **Uniqueness of the quadratic relation `λζ² + wζ + 1 = 0`** (Ch. VII §4, the field
computation behind `step4_algebra`).

In `E = GF(2^{2n})`, with `σ = σE` the Frobenius involution `x ↦ x^{2ⁿ}`, let `ζ ≠ 0` satisfy
`σ ζ = ζ⁻¹` and `ζ ≠ σ ζ` (i.e. `ζ ∉ F_{2ⁿ}`, equivalently `ζ² ≠ 1`).  If `λ, w` are `σ`-fixed
and `λζ² + wζ + 1 = 0`, then `λ = 1` and `w = ζ + ζ⁻¹`.

The argument is the classical one: applying `σ` to the relation and multiplying by `ζ²`
(using `σζ = ζ⁻¹`) produces the conjugate relation `λ + wζ + ζ² = 0`.  Subtracting the two
relations gives `(λ - 1)(ζ² - 1) = 0`, so `λ = 1` because `ζ² ≠ 1` is forced by `ζ ≠ σζ` (if
`ζ² = 1` and `ζ ≠ 0` then `ζ⁻¹ = ζ = σζ`).  Substituting `λ = 1` in the conjugate relation
yields `wζ = -(ζ² + 1) = ζ² + 1` — here characteristic two (`-x = x`, available since
`GaloisField 2 (2n)` is a `ZMod 2`-algebra) converts the sign — and multiplying by `ζ⁻¹`
gives `w = (ζ² + 1)ζ⁻¹ = ζ + ζ⁻¹`. -/
theorem step4_lambda_eq_one {n : ℕ} (hn : 2 ≤ n) {ζ : Work.PSU3.E n} (hζ0 : ζ ≠ 0)
    (hσ : Work.PSU3.σE ζ = ζ⁻¹) (hne : Work.PSU3.σE ζ ≠ ζ)
    {lam w : Work.PSU3.E n} (hlamF : Work.PSU3.σE lam = lam) (hwF : Work.PSU3.σE w = w)
    (h : lam * ζ ^ 2 + w * ζ + 1 = 0) :
    lam = 1 ∧ w = ζ + ζ⁻¹
  := by
  -- `E n = GaloisField 2 (2n)` has characteristic two, so `-x = x`.
  have hchar : CharP (Work.PSU3.E n) 2 := inferInstance
  -- `σ` applied to the relation, using `σζ = ζ⁻¹`, `σλ = λ`, `σw = w`, `σ² = 1`.
  have hs : lam * ζ⁻¹ ^ 2 + w * ζ⁻¹ + 1 = 0 := by
    have hc := congrArg Work.PSU3.σE h
    simpa only [map_add, map_mul, map_one, map_zero, map_pow, hlamF, hwF, hσ] using hc
  -- Multiply the conjugate relation by `ζ²`: `λ + wζ + ζ² = 0`.
  have h2 : lam + w * ζ + ζ ^ 2 = 0 := by
    have hmul : (lam * ζ⁻¹ ^ 2 + w * ζ⁻¹ + 1) * ζ ^ 2 = 0 := by rw [hs, zero_mul]
    have hid : (lam * ζ⁻¹ ^ 2 + w * ζ⁻¹ + 1) * ζ ^ 2 = lam + w * ζ + ζ ^ 2 := by
      have h1 : ζ⁻¹ * ζ = 1 := inv_mul_cancel₀ hζ0
      have hsq : ζ⁻¹ ^ 2 * ζ ^ 2 = 1 := by rw [← mul_pow, h1, one_pow]
      have hlin : ζ⁻¹ * ζ ^ 2 = ζ := by rw [pow_two, ← mul_assoc, h1, one_mul]
      calc (lam * ζ⁻¹ ^ 2 + w * ζ⁻¹ + 1) * ζ ^ 2
        = lam * (ζ⁻¹ ^ 2 * ζ ^ 2) + w * (ζ⁻¹ * ζ ^ 2) + ζ ^ 2 := by ring
        _ = lam * 1 + w * ζ + ζ ^ 2 := by rw [hsq, hlin]
        _ = lam + w * ζ + ζ ^ 2 := by ring
    rwa [hid] at hmul
  -- Subtract the two relations: `(λ - 1)(ζ² - 1) = 0`.
  have hdiff : (lam - 1) * (ζ ^ 2 - 1) = 0 := by linear_combination h - h2
  -- `ζ² ≠ 1`: otherwise `ζ⁻¹ = ζ`, contradicting `σζ = ζ⁻¹ ≠ ζ`.
  have hζ2ne : ζ ^ 2 - 1 ≠ 0 := by
    intro hcontra
    have hsq : ζ ^ 2 = 1 := sub_eq_zero.mp hcontra
    have hζinv : ζ⁻¹ = ζ := by
      rw [pow_two] at hsq
      exact inv_eq_of_mul_eq_one_right hsq
    exact hne (by rw [hσ, hζinv])
  have hlam1 : lam = 1 := by
    rcases mul_eq_zero.mp hdiff with h' | h'
    · exact sub_eq_zero.mp h'
    · exact absurd h' hζ2ne
  -- With `λ = 1`, the conjugate relation reads `wζ = -(ζ² + 1) = ζ² + 1` (characteristic two).
  have hwζ : w * ζ = ζ ^ 2 + 1 := by
    have h' : ζ ^ 2 + w * ζ + 1 = 0 := by rw [hlam1, one_mul] at h; exact h
    have hneg : w * ζ = -(ζ ^ 2 + 1) := by linear_combination h'
    rwa [CharTwo.neg_eq] at hneg
  have hw : w = ζ + ζ⁻¹ := by
    have hkey : w = (w * ζ) * ζ⁻¹ := by simp [mul_assoc, mul_inv_cancel₀ hζ0]
    rw [hkey, hwζ]
    field_simp
  exact ⟨hlam1, hw⟩

end Work.PSU3.StageB.NotFpfStep4
