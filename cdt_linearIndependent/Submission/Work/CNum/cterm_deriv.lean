import Mathlib
import Submission.Work.CNum.Hfun_defs

/-! # CNum: the first two derivatives of the summand `cterm m`

`cterm m φ = 12 log (1 + 2 r^m cos(mφ) + r^{2m})`, `r = 3/4`, is the `m`-th summand
of the shifted `Hfun` sum written in cosine form (`Hfun_defs`).  This file proves
that the formal expressions `ctermDeriv` and `ctermDeriv2` of `Hfun_defs` really are
the first and second derivatives of `cterm m`.

The two computations are done for a general denominator
`1 + 2 u cos(Aφ) + u²` (with `u = r ^ m`, `A = m`), so that no specific value of `u`
is needed, and are then instantiated.  Positivity of `eterm m φ` is proved first:
it is `(1 - u)² + 2u(1 + cos)` and `u = r ^ m < 1` for `m ≥ 1`, while for `m = 0` it
equals `4`. -/

namespace Work.CNum

open Real

/-- The cosine-form denominator `eterm m φ = 1 + 2 r^m cos(mφ) + (r^m)²` is positive. -/
lemma eterm_pos (m : ℕ) (φ : ℝ) : 0 < eterm m φ := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    norm_num [eterm, r34]
  · have hc0 : 0 ≤ r34 ^ m := le_of_lt (r34_pow_pos m)
    have hc1 : r34 ^ m < 1 := r34_pow_lt_one hm
    have hcos : -1 ≤ Real.cos ((m : ℝ) * φ) := Real.neg_one_le_cos _
    have hsq : 0 < (1 - r34 ^ m) ^ 2 := by positivity
    have hnn : 0 ≤ 2 * r34 ^ m * (Real.cos ((m : ℝ) * φ) + 1) :=
      mul_nonneg (by linarith) (by linarith)
    rw [eterm]
    nlinarith [hsq, hnn]

/-- Derivative of `φ ↦ 12 log (1 + 2u cos(Aφ) + u²)`, for any `u`, `A` with a positive
inner expression at `φ`. -/
lemma hasDerivAt_twelve_log (u A φ : ℝ) (h : 0 < 1 + 2 * u * Real.cos (A * φ) + u ^ 2) :
    HasDerivAt (fun ψ : ℝ => 12 * Real.log (1 + 2 * u * Real.cos (A * ψ) + u ^ 2))
      (-24 * A * u * Real.sin (A * φ) / (1 + 2 * u * Real.cos (A * φ) + u ^ 2)) φ := by
  have hinner : HasDerivAt (fun ψ : ℝ => 1 + 2 * u * Real.cos (A * ψ) + u ^ 2)
      (-(2 * u * A * Real.sin (A * φ))) φ := by
    have hid : HasDerivAt (fun ψ : ℝ => A * ψ) A φ := by
      simpa using (hasDerivAt_id φ).const_mul A
    have hc : HasDerivAt (fun ψ : ℝ => Real.cos (A * ψ)) (-Real.sin (A * φ) * A) φ :=
      (Real.hasDerivAt_cos (A * φ)).comp φ hid
    have h2 : HasDerivAt (fun ψ : ℝ => 2 * u * Real.cos (A * ψ))
        (2 * u * (-Real.sin (A * φ) * A)) φ := hc.const_mul (2 * u)
    have h3 : HasDerivAt (fun ψ : ℝ => 1 + 2 * u * Real.cos (A * ψ))
        (2 * u * (-Real.sin (A * φ) * A)) φ := h2.const_add 1
    have h4 : HasDerivAt (fun ψ : ℝ => 1 + 2 * u * Real.cos (A * ψ) + u ^ 2)
        (2 * u * (-Real.sin (A * φ) * A)) φ := h3.add_const (u ^ 2)
    have hder : 2 * u * (-Real.sin (A * φ) * A) = -(2 * u * A * Real.sin (A * φ)) := by ring
    rwa [hder] at h4
  have hlog := (Real.hasDerivAt_log (ne_of_gt h)).comp φ hinner
  have h12 := hlog.const_mul (12 : ℝ)
  have hval : (12 : ℝ) * ((1 + 2 * u * Real.cos (A * φ) + u ^ 2)⁻¹ *
        (-(2 * u * A * Real.sin (A * φ)))) =
      -24 * A * u * Real.sin (A * φ) / (1 + 2 * u * Real.cos (A * φ) + u ^ 2) := by
    rw [div_eq_mul_inv]; ring
  rwa [hval] at h12

/-- Derivative of `φ ↦ -24 A u sin(Aφ) / (1 + 2u cos(Aφ) + u²)`, for any `u`, `A` with a
positive denominator at `φ`. -/
lemma hasDerivAt_sin_div (u A φ : ℝ) (h : 0 < 1 + 2 * u * Real.cos (A * φ) + u ^ 2) :
    HasDerivAt
      (fun ψ : ℝ => -24 * A * u * Real.sin (A * ψ) / (1 + 2 * u * Real.cos (A * ψ) + u ^ 2))
      (-24 * A ^ 2 * u * (Real.cos (A * φ) * (1 + u ^ 2) + 2 * u) /
        (1 + 2 * u * Real.cos (A * φ) + u ^ 2) ^ 2) φ := by
  have hid : HasDerivAt (fun ψ : ℝ => A * ψ) A φ := by
    simpa using (hasDerivAt_id φ).const_mul A
  have hsin : HasDerivAt (fun ψ : ℝ => Real.sin (A * ψ)) (Real.cos (A * φ) * A) φ :=
    (Real.hasDerivAt_sin (A * φ)).comp φ hid
  have hnum : HasDerivAt (fun ψ : ℝ => -24 * A * u * Real.sin (A * ψ))
      (-24 * A * u * (Real.cos (A * φ) * A)) φ := hsin.const_mul (-24 * A * u)
  have hden : HasDerivAt (fun ψ : ℝ => 1 + 2 * u * Real.cos (A * ψ) + u ^ 2)
      (-(2 * u * A * Real.sin (A * φ))) φ := by
    have hc : HasDerivAt (fun ψ : ℝ => Real.cos (A * ψ)) (-Real.sin (A * φ) * A) φ :=
      (Real.hasDerivAt_cos (A * φ)).comp φ hid
    have h2 : HasDerivAt (fun ψ : ℝ => 2 * u * Real.cos (A * ψ))
        (2 * u * (-Real.sin (A * φ) * A)) φ := hc.const_mul (2 * u)
    have h3 : HasDerivAt (fun ψ : ℝ => 1 + 2 * u * Real.cos (A * ψ))
        (2 * u * (-Real.sin (A * φ) * A)) φ := h2.const_add 1
    have h4 : HasDerivAt (fun ψ : ℝ => 1 + 2 * u * Real.cos (A * ψ) + u ^ 2)
        (2 * u * (-Real.sin (A * φ) * A)) φ := h3.add_const (u ^ 2)
    have hder : 2 * u * (-Real.sin (A * φ) * A) = -(2 * u * A * Real.sin (A * φ)) := by ring
    rwa [hder] at h4
  have hdiv := hnum.div hden (ne_of_gt h)
  -- the numerator simplifies using `cos² + sin² = 1`
  have hkey : Real.cos (A * φ) * (1 + 2 * u * Real.cos (A * φ) + u ^ 2)
      + 2 * u * Real.sin (A * φ) ^ 2 = Real.cos (A * φ) * (1 + u ^ 2) + 2 * u := by
    calc Real.cos (A * φ) * (1 + 2 * u * Real.cos (A * φ) + u ^ 2)
          + 2 * u * Real.sin (A * φ) ^ 2
        = Real.cos (A * φ) * (1 + u ^ 2)
            + 2 * u * (Real.cos (A * φ) ^ 2 + Real.sin (A * φ) ^ 2) := by ring
      _ = Real.cos (A * φ) * (1 + u ^ 2) + 2 * u := by rw [Real.cos_sq_add_sin_sq]; ring
  have hval : ((-24 * A * u * (Real.cos (A * φ) * A)) * (1 + 2 * u * Real.cos (A * φ) + u ^ 2)
        - (-24 * A * u * Real.sin (A * φ)) * (-(2 * u * A * Real.sin (A * φ))))
        / (1 + 2 * u * Real.cos (A * φ) + u ^ 2) ^ 2
      = (-24 * A ^ 2 * u * (Real.cos (A * φ) * (1 + u ^ 2) + 2 * u)) /
        (1 + 2 * u * Real.cos (A * φ) + u ^ 2) ^ 2 := by
    rw [← hkey, div_eq_mul_inv, div_eq_mul_inv]
    ring
  rwa [hval] at hdiv

theorem cterm_deriv (m : ℕ) (φ : ℝ) :
    HasDerivAt (cterm m) (ctermDeriv m φ) φ ∧
    HasDerivAt (ctermDeriv m) (ctermDeriv2 m φ) φ := by
  have hpos : 0 < 1 + 2 * r34 ^ m * Real.cos ((m : ℝ) * φ) + (r34 ^ m) ^ 2 := by
    simpa only [eterm] using eterm_pos m φ
  refine ⟨?_, ?_⟩
  · exact hasDerivAt_twelve_log (r34 ^ m) ((m : ℝ)) φ hpos
  · exact hasDerivAt_sin_div (r34 ^ m) ((m : ℝ)) φ hpos

end Work.CNum
