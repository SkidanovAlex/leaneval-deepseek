import Mathlib
import Submission.Work.MotAS.aszDpQuad
import Submission.Work.MotAS.ASResidual
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotC5N3.ASZPrimeness.DpQuadNoHab`

The AS residual chart ideal `ZIAS a b g = span (range (zcubAS a b g))` of
`Submission/Work/MotAS/aszDpQuad.lean` contains a monic quadratic in `X₀`, under the *sole*
nondegeneracy hypotheses `a² - ab - b² ≠ 0` and `g ∉ ℘(K)`; no hypothesis `a b ≠ 0` is needed.

The certificate is exactly the one of `Work.MotAS.aszDpQuad`: with

* `α = aszQuAlpha a b`, `β = aszQuBeta a b`

the combination `β · zcubAS a b g 2 + 2α · zcubAS a b g 4` of two generators of `ZIAS a b g` is the
quadratic `β² X₀² + (…) X₀ + (…)` (`Work.MotAS.aszQu_ident`), and `β = 2(a+2b)⁴ ≠ 0` follows from
`a² - ab - b² ≠ 0` alone: `a + 2b = 0` would force `a² - ab - b² = 5b² = 0`.

The hypothesis `hab : a * b ≠ 0` of `aszDpQuad` is never used in that proof, so the same argument
applies to the degenerate cases `a = 0` and `b = 0` (which are reached under `ha`, since then
`b ≠ 0`, resp. `a ≠ 0`).  This file makes that explicit.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.MotC5N3.ASZPrimeness

open MvPolynomial

theorem DpQuadNoHab (K : Type) [Field K] [CharP K 5] (a b g : K)
    (ha : a ^ 2 - a * b - b ^ 2 ≠ 0) (hg : ¬ ∃ c : K, c ^ 5 - c = g) :
    ∃ (l A : MvPolynomial (Fin 2) K),
      (MvPolynomial.X 0 ^ 2
          + MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) l * MvPolynomial.X 0
          + MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) A ∈ Work.MotAS.ZIAS a b g) := by
  have h5 : (5 : K) = 0 := CharP.cast_eq_zero K 5
  -- `a + 2b ≠ 0` from the nondegeneracy hypothesis alone (no `a b ≠ 0`)
  have h2b : a + 2 * b ≠ 0 := by
    intro h
    apply ha
    have hfac : a ^ 2 - a * b - b ^ 2 = (a + 2 * b) * (a - 3 * b) + 5 * b ^ 2 := by ring
    rw [h, zero_mul, zero_add] at hfac
    rw [hfac, h5, zero_mul]
  have h2ne : (2 : K) ≠ 0 := by
    intro h2
    have h32 : (3 : K) * 2 = 1 := by
      have h : (3 : K) * 2 - 1 = (5 : K) * 1 := by ring
      rwa [h5, mul_one, sub_eq_zero] at h
    rw [h2, mul_zero] at h32
    exact one_ne_zero h32.symm
  have hbeta : Work.MotAS.aszQuBeta a b ≠ 0 := by
    rw [Work.MotAS.aszQuBeta_eq a b]
    exact mul_ne_zero h2ne (pow_ne_zero 4 h2b)
  -- the two-generator certificate lies in the ideal
  have hG : C (Work.MotAS.aszQuBeta a b) * Work.MotAS.zcubAS a b g 2
        + C (2 * Work.MotAS.aszQuAlpha a b) * Work.MotAS.zcubAS a b g 4
      ∈ Work.MotAS.ZIAS a b g := by
    have h2 : Work.MotAS.zcubAS a b g 2 ∈ Work.MotAS.ZIAS a b g :=
      Ideal.subset_span (Set.mem_range_self (2 : Fin 5))
    have h4 : Work.MotAS.zcubAS a b g 4 ∈ Work.MotAS.ZIAS a b g :=
      Ideal.subset_span (Set.mem_range_self (4 : Fin 5))
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ h2) (Ideal.mul_mem_left _ _ h4)
  have hident := Work.MotAS.aszQu_ident (K := K) a b g
  -- the scalar `β⁻²`
  have hc : C ((Work.MotAS.aszQuBeta a b) ^ 2)⁻¹ * C ((Work.MotAS.aszQuBeta a b) ^ 2)
      = (1 : MvPolynomial (Fin 3) K) := by
    rw [← map_mul, inv_mul_cancel₀ (pow_ne_zero 2 hbeta), map_one]
  have hr : ∀ p : MvPolynomial (Fin 2) K,
      MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3)
          (C ((Work.MotAS.aszQuBeta a b) ^ 2)⁻¹ * p)
        = C ((Work.MotAS.aszQuBeta a b) ^ 2)⁻¹
            * MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) p := by
    intro p
    rw [map_mul, MvPolynomial.rename_C]
  have key : C ((Work.MotAS.aszQuBeta a b) ^ 2)⁻¹
        * (C ((Work.MotAS.aszQuBeta a b) ^ 2) * (X 0 : MvPolynomial (Fin 3) K) ^ 2
            + MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.aszQuLt a b g) * X 0
            + MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.aszQuAt a b g))
      = (X 0 : MvPolynomial (Fin 3) K) ^ 2
        + (C ((Work.MotAS.aszQuBeta a b) ^ 2)⁻¹
            * MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.aszQuLt a b g)) * X 0
        + C ((Work.MotAS.aszQuBeta a b) ^ 2)⁻¹
            * MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.aszQuAt a b g) := by
    rw [mul_add, mul_add, ← mul_assoc (C ((Work.MotAS.aszQuBeta a b) ^ 2)⁻¹)
      (C ((Work.MotAS.aszQuBeta a b) ^ 2)) ((X 0 : MvPolynomial (Fin 3) K) ^ 2), hc, one_mul]
    first | refl_ring1 | ring
  refine ⟨C ((Work.MotAS.aszQuBeta a b) ^ 2)⁻¹ * Work.MotAS.aszQuLt a b g,
    C ((Work.MotAS.aszQuBeta a b) ^ 2)⁻¹ * Work.MotAS.aszQuAt a b g, ?_⟩
  rw [hr (Work.MotAS.aszQuLt a b g), hr (Work.MotAS.aszQuAt a b g), ← key, ← hident]
  exact Ideal.mul_mem_left _ _ hG

end Work.MotC5N3.ASZPrimeness
