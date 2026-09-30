/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The pole divisor of a polynomial in a rational function

Let `C` be a curve over a field `k`, `t ∈ K(C)` a rational function and `μ ∈ k[X]` a polynomial.
Then the pole divisor of `μ(t)` is `deg μ` times the pole divisor of `t`:

  `(μ(t))_∞ = natDegree μ · (t)_∞`.

The reason is purely local.  At a place `Q`, let `v_Q` be the valuation of `K(C)` at `Q`, so
that `ord_Q x = -log (v_Q x)`.

* If `t` is regular at `Q` (`0 ≤ ord_Q t`, i.e. `v_Q t ≤ 1`), then `μ(t)` is regular at `Q` as
  well: it is a `k`-linear combination of products `t^i`, and the unit ball of `v_Q` is a
  subring containing the constants.
* If `t` has a pole at `Q` (`ord_Q t < 0`, i.e. `1 < v_Q t`), the leading term `a_n t^n` of
  `μ(t)` strictly dominates all the others in valuation, so
  `v_Q (μ(t)) = v_Q t ^ natDegree μ`, whence `ord_Q (μ(t)) = natDegree μ · ord_Q t`.

Both statements are instances of Mathlib's results about valuations that are trivial on the
base field.  Taking `max 0 (·)` of `-ord_Q` then gives the claim place by place.
-/
import Mathlib
import Submission.Work.CurveBasics.All
import Submission.Work.RiemannRoch.Pole

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option linter.style.haveILetI false

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

universe u

namespace Work.RiemannRoch.RR

open Work.CurveBasics

noncomputable section

/-! ## The valuation at a place is trivial on the constants -/

/-- The valuation of the function field at a place `Q` takes the value `1` on the nonzero
constants: constants are units at every place. -/
theorem valuation_algebraMap_eq_one {k : Type u} [Field k] (C : Work.CurveBasics.Curve k)
    (Q : C.Place) {c : k} (hc : c ≠ 0) :
    Q.valuation (algebraMap k C.functionField c) = 1 := by
  have hne : algebraMap k C.functionField c ≠ 0 := by
    simpa using ((algebraMap k C.functionField).injective.ne_iff).mpr hc
  -- `ord = -log v` and the order of a constant is zero
  have h0 : Scheme.ord (algebraMap k C.functionField c) Q.point = 0 :=
    Work.CurveBasics.Order.ordAt_algebraMap_eq_zero C c Q
  have h := Work.CurveBasics.Curve.Place.ord_eq_neg_log_valuation C Q
    (algebraMap k C.functionField c)
  rw [h0] at h
  have hlog : (Q.valuation (algebraMap k C.functionField c)).log = 0 := by linarith
  have hvne : Q.valuation (algebraMap k C.functionField c) ≠ 0 :=
    (Valuation.ne_zero_iff Q.valuation).mpr hne
  calc Q.valuation (algebraMap k C.functionField c)
      = WithZero.exp ((Q.valuation (algebraMap k C.functionField c)).log) :=
        (WithZero.exp_log hvne).symm
    _ = WithZero.exp 0 := by rw [hlog]
    _ = 1 := WithZero.exp_zero

/-- The valuation of the function field at a place is trivial on the base field `k`. -/
theorem valuation_isTrivialOn {k : Type u} [Field k] (C : Work.CurveBasics.Curve k)
    (Q : C.Place) : Valuation.IsTrivialOn k Q.valuation :=
  ⟨fun _ hc => valuation_algebraMap_eq_one C Q hc⟩

/-- At a place of a curve, `t` is regular if and only if `v_Q t ≤ 1`. -/
theorem valuation_le_one_iff {k : Type u} [Field k] (C : Work.CurveBasics.Curve k)
    (Q : C.Place) (x : C.functionField) :
    Q.valuation x ≤ 1 ↔ 0 ≤ C.ordAt x Q := by
  rw [← Valuation.mem_valuationSubring_iff, ← Work.CurveBasics.Curve.Place.valuationSubring_eq,
    Work.CurveBasics.Place.mem_valuationSubring_iff]

/-! ## The two local computations -/

/-- If `t` is regular at `Q` then so is every polynomial in `t`. -/
theorem ordAt_aeval_nonneg {k : Type u} [Field k] (C : Work.CurveBasics.Curve k)
    (Q : C.Place) (t : C.functionField) (μ : Polynomial k) (ht : 0 ≤ C.ordAt t Q) :
    0 ≤ C.ordAt (Polynomial.aeval t μ) Q := by
  haveI htriv : Valuation.IsTrivialOn k Q.valuation := valuation_isTrivialOn C Q
  have hvt : Q.valuation t ≤ 1 := (valuation_le_one_iff C Q t).mpr ht
  have hle : Q.valuation (Polynomial.aeval t μ) ≤ 1 := by
    rw [Polynomial.aeval_eq_sum_range]
    apply Valuation.map_sum_le
    intro i _
    rw [Algebra.smul_def, Valuation.map_mul, Valuation.map_pow]
    calc Q.valuation (algebraMap k C.functionField (μ.coeff i)) * Q.valuation t ^ i
        ≤ 1 * 1 :=
          mul_le_mul' (Valuation.IsTrivialOn.valuation_algebraMap_le_one Q.valuation _)
            (pow_le_one' hvt i)
      _ = 1 := one_mul 1
  rw [← valuation_le_one_iff C Q (Polynomial.aeval t μ)]
  exact hle

/-- If `t` has a pole at `Q` then `ord_Q (μ(t)) = natDegree μ · ord_Q t`. -/
theorem ordAt_aeval_eq_of_neg {k : Type u} [Field k] (C : Work.CurveBasics.Curve k)
    (Q : C.Place) (t : C.functionField) (μ : Polynomial k) (hμ : μ ≠ 0)
    (ht : C.ordAt t Q < 0) :
    C.ordAt (Polynomial.aeval t μ) Q = (μ.natDegree : ℤ) * C.ordAt t Q := by
  haveI htriv : Valuation.IsTrivialOn k Q.valuation := valuation_isTrivialOn C Q
  have hpos : 1 < Q.valuation t := by
    have hle : ¬ (Q.valuation t ≤ 1) := by
      intro hlt
      exact absurd ((valuation_le_one_iff C Q t).mp hlt) (not_le.mpr ht)
    exact not_le.mp hle
  have hval : Q.valuation (Polynomial.aeval t μ) = Q.valuation t ^ μ.natDegree :=
    Polynomial.valuation_aeval_eq_valuation_X_pow_natDegree_of_one_lt_valuation_X t hpos hμ
  have h1 := Work.CurveBasics.Curve.Place.ord_eq_neg_log_valuation C Q (Polynomial.aeval t μ)
  have h2 := Work.CurveBasics.Curve.Place.ord_eq_neg_log_valuation C Q t
  show Scheme.ord (Polynomial.aeval t μ) Q.point = (μ.natDegree : ℤ) * Scheme.ord t Q.point
  rw [h1, h2, hval, WithZero.log_pow, nsmul_eq_mul]
  ring

/-! ## The pole divisor identity -/

theorem riemann_poleDivisor_aeval {k : Type u} [Field k]
    (C : Work.CurveBasics.Curve k) (t : C.functionField) (μ : Polynomial k) :
    Work.RiemannRoch.Curve.poleDivisor C (Polynomial.aeval t μ)
      = μ.natDegree • Work.RiemannRoch.Curve.poleDivisor C t := by
  ext Q
  rcases eq_or_ne μ 0 with rfl | hμ
  · have hz : C.ordAt (0 : C.functionField) Q = 0 := Work.RiemannRoch.Curve.ordAt_zero C Q
    simp [Polynomial.aeval_zero, Work.RiemannRoch.Curve.poleDivisor_apply, hz,
      Finsupp.smul_apply]
  · simp only [Work.RiemannRoch.Curve.poleDivisor_apply, Finsupp.smul_apply, nsmul_eq_mul]
    by_cases ht : 0 ≤ C.ordAt t Q
    · have h2 : 0 ≤ C.ordAt (Polynomial.aeval t μ) Q := ordAt_aeval_nonneg C Q t μ ht
      rw [max_eq_left (show -(C.ordAt (Polynomial.aeval t μ) Q) ≤ 0 by linarith),
        max_eq_left (show -(C.ordAt t Q) ≤ 0 by linarith), mul_zero]
    · have ht' : C.ordAt t Q < 0 := not_le.mp ht
      have h2 : C.ordAt (Polynomial.aeval t μ) Q = (μ.natDegree : ℤ) * C.ordAt t Q :=
        ordAt_aeval_eq_of_neg C Q t μ hμ ht'
      rw [h2, max_eq_right (show (0 : ℤ) ≤ -(C.ordAt t Q) by linarith),
        max_eq_right (show (0 : ℤ) ≤ -((μ.natDegree : ℤ) * C.ordAt t Q) by
          have : (0 : ℤ) ≤ (μ.natDegree : ℤ) := Int.natCast_nonneg _
          nlinarith)]
      ring

end

end Work.RiemannRoch.RR
