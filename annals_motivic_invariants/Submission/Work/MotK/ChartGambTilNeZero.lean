import Mathlib
import Submission.Work.MotK.ChartCompAux
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotK

set_option maxHeartbeats 4000000

/-- **The source equation `F̃(p̃, chartC)` of the T-twisted link is nonzero** (`p̃ = (a·h,0,a·h,b,0)`
is the division-free point `(a·h)·pointC`; `GambC = C((a·h)⁻¹)^6 * GambTil`, so this is equivalent
to `GambC ≠ 0`, the nonvanishing needed by `Work.MotK.ChartCompC`).

Intended route (verified numerically).  Kill `X₀ = X₁ = 0` and keep only `X₂`, i.e. apply the ring
homomorphism `MvPolynomial.eval₂Hom Polynomial.C (fun i : Fin 3 => (![0,0,Polynomial.X] : Fin 3 →
Polynomial K) i)`; the image of `GambTil K a b h` is the explicit univariate polynomial
`C (a^23*b^5*h^15) * X^11 + C (a^23*b^5*h^16) * X^6` (the intermediate expressions are
division-free, so `simp only [GambTil, kleinTwFhom, kleinTwBilin, kleinTwQ, kleinTwP0,
kleinTwStereo, kleinTwS, ptilVec, ptilPt, chartC, Fin.isValue, Matrix.cons_val,
MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_X', map_add, map_mul, map_pow, map_neg, map_sub,
map_one, map_zero, Pi.add_apply]` followed by `ring` should prove that identity).  Then the
coefficient of `X^11` is `a^23*b^5*h^15 ≠ 0`, so the image — and hence `GambTil` — is nonzero.
Concretely: `intro h0; have h1 := congrArg (the eval₂Hom above) h0` … `= 0`, then
`Polynomial.coeff 11` of it is `a^23*b^5*h^15` (use `Polynomial.coeff_C_mul_X_pow`), contradicting
`mul_ne_zero (mul_ne_zero (pow_ne_zero 23 ha) (pow_ne_zero 5 hb)) (pow_ne_zero 15 hh)`. -/
theorem ChartGambTilNeZero (K : Type*) [Field K] (a b h : K) (ha : a ≠ 0) (hb : b ≠ 0) (hh : h ≠ 0) :
    Work.MotK.GambTil K a b h ≠ 0 := by
  intro h0
  -- The substitution `X₀ ↦ 0`, `X₁ ↦ 0`, `X₂ ↦ X` kills everything except the
  -- last chart coordinate; division-free, so it commutes with the link data.
  set φ : MvPolynomial (Fin 3) K →+* Polynomial K :=
    MvPolynomial.eval₂Hom Polynomial.C
      (fun i : Fin 3 => (![0, 0, Polynomial.X] : Fin 3 → Polynomial K) i) with hφ
  have hlav : φ (GambTil K a b h) =
      Polynomial.C (a^23*b^5*h^15) * Polynomial.X^11 +
        Polynomial.C (a^23*b^5*h^16) * Polynomial.X^6 := by
    rw [hφ]
    simp only [GambTil, ptilVec, chartC, kleinTwFhom, kleinTwBilin, kleinTwQ, kleinTwP0,
      kleinTwStereo, kleinTwS,
      map_add, map_mul, map_pow, map_neg, map_sub, map_one, map_zero,
      MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_X',
      Fin.isValue, Matrix.cons_val, Matrix.cons_val_zero, Pi.add_apply,
      ptilPt_apply_zero, ptilPt_apply_one, ptilPt_apply_two, ptilPt_apply_three,
      ptilPt_apply_four]
    first | refl_ring1 | ring
  have h1 : (Polynomial.C (a^23*b^5*h^15) * Polynomial.X^11 +
        Polynomial.C (a^23*b^5*h^16) * Polynomial.X^6).coeff 11 = 0 := by
    rw [← hlav, h0, map_zero, Polynomial.coeff_zero]
  have h2 : (Polynomial.C (a^23*b^5*h^15) * Polynomial.X^11 +
        Polynomial.C (a^23*b^5*h^16) * Polynomial.X^6).coeff 11 = a^23*b^5*h^15 := by
    rw [Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X_pow]
    norm_num
  rw [h2] at h1
  exact (mul_ne_zero (mul_ne_zero (pow_ne_zero 23 ha) (pow_ne_zero 5 hb))
    (pow_ne_zero 15 hh)) h1

end Work.MotK
