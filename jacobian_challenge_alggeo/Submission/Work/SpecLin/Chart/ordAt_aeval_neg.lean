import Mathlib
import Submission.Work.CurveBasics.All

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


namespace Work.SpecLin.Chart

open CategoryTheory AlgebraicGeometry

open scoped WithZero

namespace ordAt_aeval_neg_aux

variable {K : Type*} [Field K]

/-- The adic valuation of a place, which takes values `≤ 1` exactly on the functions regular at
the place, is `> 1` on a function of negative order of vanishing. -/
private lemma one_lt_valuation_iff (C : Work.CurveBasics.Curve K) (Q : C.Place)
    {x : C.functionField} (hx : x ≠ 0) :
    (1 : WithZero (Multiplicative ℤ)) < Q.valuation x ↔ C.ordAt x Q < 0 := by
  change 1 < Q.valuation x ↔ Scheme.ord x Q.point < 0
  rw [Work.CurveBasics.Curve.Place.ord_eq_neg_log_valuation]
  have hv : Q.valuation x ≠ 0 := fun h => hx ((Valuation.zero_iff Q.valuation).mp h)
  rw [neg_lt_zero, ← WithZero.exp_zero (M := ℤ), WithZero.lt_log_iff_exp_lt hv]

/-- The constant functions of a curve lie in the valuation ring at every place, i.e. the adic
valuation of a constant is at most `1`. -/
private lemma valuation_algebraMap_le_one (C : Work.CurveBasics.Curve K) (Q : C.Place) (c : K) :
    Q.valuation (algebraMap K C.functionField c) ≤ 1 := by
  rw [← Valuation.mem_valuationSubring_iff]
  rw [← Work.CurveBasics.Curve.Place.valuationSubring_eq]
  rw [Work.CurveBasics.Place.mem_valuationSubring_iff]
  change 0 ≤ C.ordAt (algebraMap K C.functionField c) Q
  rw [Work.CurveBasics.Order.ordAt_algebraMap_eq_zero]

/-- A nonzero constant function of a curve is a unit of the valuation ring at every place, i.e.
its adic valuation is `1`. -/
private lemma valuation_algebraMap_eq_one (C : Work.CurveBasics.Curve K) (Q : C.Place)
    {c : K} (hc : c ≠ 0) :
    Q.valuation (algebraMap K C.functionField c) = 1 := by
  have hmul : Q.valuation (algebraMap K C.functionField c) *
      Q.valuation (algebraMap K C.functionField c⁻¹) = 1 := by
    rw [← Valuation.map_mul, ← map_mul, mul_inv_cancel₀ hc, map_one]
    exact Valuation.map_one Q.valuation
  have hge : 1 ≤ Q.valuation (algebraMap K C.functionField c) := by
    calc (1 : WithZero (Multiplicative ℤ)) = Q.valuation (algebraMap K C.functionField c) *
            Q.valuation (algebraMap K C.functionField c⁻¹) := hmul.symm
      _ ≤ Q.valuation (algebraMap K C.functionField c) * 1 :=
            mul_le_mul_right (valuation_algebraMap_le_one C Q c⁻¹) _
      _ = Q.valuation (algebraMap K C.functionField c) := mul_one _
  exact le_antisymm (valuation_algebraMap_le_one C Q c) hge

/-- If `x` has a pole at `Q` (equivalently: has adic valuation `> 1` there), then the evaluation
`g(x)` of any nonzero polynomial `g` at `x` has adic valuation `(vQ x) ^ (natDegree g)`: the
leading term of `g` strictly dominates all the others. -/
private lemma valuation_aeval_eq (C : Work.CurveBasics.Curve K) (Q : C.Place) {x : C.functionField}
    (hx : 1 < Q.valuation x) {g : Polynomial K} (hg : g ≠ 0) :
    Q.valuation (Polynomial.aeval x g) = (Q.valuation x) ^ g.natDegree := by
  have ha : g.coeff g.natDegree ≠ 0 := by
    rw [Polynomial.coeff_natDegree]
    exact fun h => hg (Polynomial.leadingCoeff_eq_zero.mp h)
  have hterm : ∀ i : ℕ, i < g.natDegree →
      Q.valuation (algebraMap K C.functionField (g.coeff i) * x ^ i)
        < Q.valuation (algebraMap K C.functionField (g.coeff g.natDegree) * x ^ g.natDegree) := by
    intro i hi
    have hle : Q.valuation (algebraMap K C.functionField (g.coeff i) * x ^ i)
        ≤ 1 * (Q.valuation x) ^ i := by
      rw [Valuation.map_mul, Valuation.map_pow]
      exact mul_le_mul_left (valuation_algebraMap_le_one C Q (g.coeff i)) _
    have hlt : (1 : WithZero (Multiplicative ℤ)) * (Q.valuation x) ^ i
        < 1 * (Q.valuation x) ^ g.natDegree := by
      rw [one_mul, one_mul]
      exact pow_lt_pow_right₀ hx hi
    have hFN : Q.valuation (algebraMap K C.functionField (g.coeff g.natDegree) * x ^ g.natDegree)
        = 1 * (Q.valuation x) ^ g.natDegree := by
      rw [Valuation.map_mul, Valuation.map_pow, valuation_algebraMap_eq_one C Q ha, one_mul]
    rw [hFN]
    exact lt_of_le_of_lt hle hlt
  have hsum := Valuation.map_sum_eq_of_lt (v := Q.valuation)
      (s := Finset.range (g.natDegree + 1))
      (f := fun i => algebraMap K C.functionField (g.coeff i) * x ^ i)
      (j := g.natDegree) (Finset.mem_range.mpr (Nat.lt_succ_self _)) (by
        intro i hi
        rw [Finset.mem_sdiff, Finset.mem_range, Finset.mem_singleton] at hi
        exact hterm i (by omega))
  rw [Polynomial.aeval_def, Polynomial.eval₂_eq_sum_range, hsum, Valuation.map_mul, Valuation.map_pow,
    valuation_algebraMap_eq_one C Q ha, one_mul]

end ordAt_aeval_neg_aux

/-- If a rational function `x₀` has a pole at a place `Q`, then for any nonconstant polynomial
`g` the rational function `g(x₀)` again has a pole at `Q`. -/
theorem ordAt_aeval_neg {K : Type*} [Field K] (C : Work.CurveBasics.Curve K) (Q : C.Place)
    {x₀ : C.functionField} (hx : C.ordAt x₀ Q < 0) {g : Polynomial K} (hg : g ≠ 0)
    (hgd : g.natDegree ≠ 0) : C.ordAt (Polynomial.aeval x₀ g) Q < 0 := by
  have hx0 : x₀ ≠ 0 := by
    rintro rfl
    have : C.ordAt (0 : C.functionField) Q = 0 := by
      change Scheme.ord (0 : C.functionField) Q.point = 0
      simp
    omega
  have h1 : (1 : WithZero (Multiplicative ℤ)) < Q.valuation x₀ :=
    (ordAt_aeval_neg_aux.one_lt_valuation_iff C Q hx0).mpr hx
  have hval := ordAt_aeval_neg_aux.valuation_aeval_eq C Q h1 hg
  have hgt : (1 : WithZero (Multiplicative ℤ)) < Q.valuation (Polynomial.aeval x₀ g) := by
    rw [hval]
    exact one_lt_pow₀ h1 hgd
  have hne : Q.valuation (Polynomial.aeval x₀ g) ≠ 0 := ne_of_gt (zero_lt_one.trans hgt)
  have hne' : Polynomial.aeval x₀ g ≠ 0 := fun h => hne ((Valuation.zero_iff Q.valuation).mpr h)
  exact (ordAt_aeval_neg_aux.one_lt_valuation_iff C Q hne').mp hgt

end Work.SpecLin.Chart
