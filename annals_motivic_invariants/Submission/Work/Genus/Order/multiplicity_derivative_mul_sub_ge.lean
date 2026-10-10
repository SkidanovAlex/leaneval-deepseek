import Mathlib
import Submission.Work.Genus.Defs
import Submission.Work.Genus.Order.ord_mul
import Submission.Work.Genus.Order.min_ord_le_ord_add
import Submission.Work.Genus.Order.multiplicity_derivative_ge

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Genus.Order

/-- **The polynomial inequality behind `ord π (deriv f) ≥ ord π f - 1`.**  For an irreducible
`π ∈ F[X]` and non-zero polynomials `a`, `b` with `a.derivative * b - a * b.derivative ≠ 0`,
`multiplicity π a + multiplicity π b - 1 ≤ multiplicity π (a.derivative * b - a * b.derivative)`
(an inequality in `ℤ`).  Route: if both derivatives are non-zero, use the prime-power bound
`multiplicity π a.derivative ≥ multiplicity π a - 1` (and the same for `b`; this follows from
`pow_multiplicity_dvd π a` together with Mathlib's
`Polynomial.pow_sub_one_dvd_derivative_of_pow_dvd` and
`FiniteMultiplicity.le_multiplicity_of_pow_dvd`, and may be proved inline or imported from
`Submission/Work/Genus/Order/multiplicity_derivative_ge.lean` if that module exists),
multiplicativity of `multiplicity` on products of non-zero factors
(`Work.Genus.Order.multiplicity_mul_int`) and the non-archimedean bound
`min (multiplicity π A) (multiplicity π B) ≤ multiplicity π (A - B)`
(`Work.Genus.Order.min_multiplicity_le_multiplicity_add_int` applied to `A` and `-B`, with
`multiplicity_neg`, `sub_eq_add_neg`).  If `a.derivative = 0` the difference is `-(a * b.derivative)`
and then `b.derivative ≠ 0` (else the difference would vanish), so the bound is just the prime-power
bound for `b`; symmetrically for `b.derivative = 0`.  The hypothesis
`a.derivative * b - a * b.derivative ≠ 0` cannot be dropped: over `𝔽_p`, `a = 1`, `b = X ^ p`
makes the difference `0` while the right hand side is `0` and the left hand side is `p - 1 > 0`. -/
lemma multiplicity_derivative_mul_sub_ge {F : Type*} [Field F] {π a b : Polynomial F}
    (hπ : Irreducible π) (ha : a ≠ 0) (hb : b ≠ 0)
    (hP : a.derivative * b - a * b.derivative ≠ 0) :
    (multiplicity π a : ℤ) + (multiplicity π b : ℤ) - 1
      ≤ (multiplicity π (a.derivative * b - a * b.derivative) : ℤ) := by
  have hp : Prime π := hπ.prime
  by_cases hda : a.derivative = 0
  · -- `a.derivative = 0`: the difference is `-(a * b.derivative)`, so only `b` needs bounding.
    have hb' : b.derivative ≠ 0 := by
      intro h
      exact hP (by simp [hda, h])
    have hD : a.derivative * b - a * b.derivative = -(a * b.derivative) := by
      rw [hda, zero_mul, zero_sub]
    rw [hD, multiplicity_neg, multiplicity_mul_int hp ha hb']
    have hge := multiplicity_derivative_ge hπ hb'
    linarith
  · by_cases hdb : b.derivative = 0
    · -- `b.derivative = 0`: symmetrically only `a` needs bounding.
      have ha' : a.derivative ≠ 0 := by
        intro h
        exact hP (by simp [h, hdb])
      have hD : a.derivative * b - a * b.derivative = a.derivative * b := by
        rw [hdb, mul_zero, sub_zero]
      rw [hD, multiplicity_mul_int hp ha' hb]
      have hge := multiplicity_derivative_ge hπ ha'
      linarith
    · -- Both derivatives are non-zero: multiplicativity plus the non-archimedean bound.
      have hAB : a.derivative * b + -(a * b.derivative) ≠ 0 := by
        simpa only [sub_eq_add_neg] using hP
      have hmin := min_multiplicity_le_multiplicity_add_int (π := π) hπ hAB
      rw [multiplicity_neg, ← sub_eq_add_neg] at hmin
      rw [multiplicity_mul_int hp hda hb, multiplicity_mul_int hp ha hdb] at hmin
      have hgea := multiplicity_derivative_ge hπ hda
      have hgeb := multiplicity_derivative_ge hπ hdb
      have hlow : (multiplicity π a : ℤ) + (multiplicity π b : ℤ) - 1
          ≤ min ((multiplicity π a.derivative : ℤ) + (multiplicity π b : ℤ))
                ((multiplicity π a : ℤ) + (multiplicity π b.derivative : ℤ)) := by
        apply le_min <;> linarith
      exact le_trans hlow hmin

end Work.Genus.Order
