/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Submission.NK.GlobalCFT.IdeleClassGroup.CompactDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The archimedean sum of a bounded norm-one idèle

Let `K` be a number field, `S` a finite set of nonarchimedean places and `C₀ ≥ 1`.  For an idèle
`y` of content one which is bounded-integral for `(S, C₀)` (i.e. a local unit outside `S`, integral
at every finite place and bounded below by `C₀⁻¹` at the places of `S`), this file computes the
*logarithmic archimedean sum*

`L(y) = ∑_{w | ∞} mult w * log ‖y_w‖`.

Logarithmising the content formula
(`NK.GlobalCFT.IdeleClassGroup.abs_val_eq_prod_of_norm_eq_one`) gives the three facts
formalised here:

* `L(y) = - ∑_{q ∈ S} log ‖y_q‖` — the archimedean contribution is the negative of the
  nonarchimedean one;
* `L(y) ≥ 0` — it is nonnegative;
* `L(y) ≤ |S| * log C₀` — it is bounded by the size of `S` and the constant `C₀`.

These are the estimates used to see that the archimedean part of the norm-one idèles stays in a
compact annulus once the finite part is bounded.

## Main results

* `NK.GlobalCFT.IdeleClassGroup.globalCFT_normOne_archimedean_sum`
-/

set_option autoImplicit false

open scoped NumberField RestrictedProduct
open NumberField IsDedekindDomain

noncomputable section

namespace NK.GlobalCFT.IdeleClassGroup

variable {K : Type*} [Field K] [NumberField K]

theorem globalCFT_normOne_archimedean_sum {K : Type*} [Field K] [NumberField K]
    (S : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) {C₀ : ℝ}
    (hC₀ : 1 ≤ C₀) {y : NK.GlobalCFT.Idele K}
    (hy : y ∈ NK.GlobalCFT.Idele.normOne K)
    (hbd : NK.GlobalCFT.IdeleClassGroup.IsBoundedIntegral K S C₀ y) :
    (∑ w : NumberField.InfinitePlace K,
        (w.mult : ℝ) * Real.log ‖(y (NK.GlobalCFT.Place.ofInfinite w) : w.Completion)‖)
      = - ∑ q ∈ S, Real.log ‖(y (NK.GlobalCFT.Place.ofFinite q) : q.adicCompletion K)‖ ∧
    0 ≤ ∑ w : NumberField.InfinitePlace K,
        (w.mult : ℝ) * Real.log ‖(y (NK.GlobalCFT.Place.ofInfinite w) : w.Completion)‖ ∧
    (∑ w : NumberField.InfinitePlace K,
        (w.mult : ℝ) * Real.log ‖(y (NK.GlobalCFT.Place.ofInfinite w) : w.Completion)‖)
      ≤ (S.card : ℝ) * Real.log C₀ := by
  classical
  -- Positivity of the two products occurring in the content formula.
  have hApos : 0 < ∏ q ∈ S, ‖(y (NK.GlobalCFT.Place.ofFinite q) : q.adicCompletion K)‖ :=
    Finset.prod_pos fun q _ =>
      norm_pos_iff.mpr (Units.ne_zero (y (NK.GlobalCFT.Place.ofFinite q)))
  have hBpos : 0 < ∏ w : NumberField.InfinitePlace K,
      ‖(y (NK.GlobalCFT.Place.ofInfinite w) : w.Completion)‖ ^ w.mult :=
    Finset.prod_pos fun w _ =>
      pow_pos (norm_pos_iff.mpr (Units.ne_zero (y (NK.GlobalCFT.Place.ofInfinite w)))) _
  -- The content formula, together with `abs y = 1` from `y ∈ 𝕀¹ K`.
  have hprod := NK.GlobalCFT.IdeleClassGroup.abs_val_eq_prod_of_norm_eq_one
    (K := K) (S := S) (x := y) hbd.1
  have habs : ((NK.GlobalCFT.Idele.abs K y : ℝˣ) : ℝ) = 1 := by
    rw [NK.GlobalCFT.Idele.mem_normOne.mp hy]; simp
  rw [habs] at hprod
  -- Logarithm of a product over `S`, resp. over the archimedean places.
  have hlogA : Real.log (∏ q ∈ S, ‖(y (NK.GlobalCFT.Place.ofFinite q) : q.adicCompletion K)‖)
      = ∑ q ∈ S, Real.log ‖(y (NK.GlobalCFT.Place.ofFinite q) : q.adicCompletion K)‖ :=
    Real.log_prod fun q _ => ne_of_gt (norm_pos_iff.mpr (Units.ne_zero _))
  have hlogB : Real.log (∏ w : NumberField.InfinitePlace K,
        ‖(y (NK.GlobalCFT.Place.ofInfinite w) : w.Completion)‖ ^ w.mult)
      = ∑ w : NumberField.InfinitePlace K,
          (w.mult : ℝ) * Real.log ‖(y (NK.GlobalCFT.Place.ofInfinite w) : w.Completion)‖ := by
    rw [Real.log_prod (s := Finset.univ)
      (f := fun w : NumberField.InfinitePlace K =>
        ‖(y (NK.GlobalCFT.Place.ofInfinite w) : w.Completion)‖ ^ w.mult)
      (fun w _ => ne_of_gt (pow_pos (norm_pos_iff.mpr (Units.ne_zero _)) _))]
    exact Finset.sum_congr rfl fun w _ => Real.log_pow _ _
  have hlog : Real.log ((∏ q ∈ S, ‖(y (NK.GlobalCFT.Place.ofFinite q) : q.adicCompletion K)‖) *
      (∏ w : NumberField.InfinitePlace K,
        ‖(y (NK.GlobalCFT.Place.ofInfinite w) : w.Completion)‖ ^ w.mult)) = 0 := by
    rw [← hprod, Real.log_one]
  rw [Real.log_mul (ne_of_gt hApos) (ne_of_gt hBpos), hlogA, hlogB] at hlog
  -- The archimedean sum is the negative of the nonarchimedean one.
  have hkey : (∑ w : NumberField.InfinitePlace K,
        (w.mult : ℝ) * Real.log ‖(y (NK.GlobalCFT.Place.ofInfinite w) : w.Completion)‖)
      = - ∑ q ∈ S, Real.log ‖(y (NK.GlobalCFT.Place.ofFinite q) : q.adicCompletion K)‖ := by
    linarith
  refine ⟨hkey, ?_, ?_⟩
  · -- Nonnegativity: every `q ∈ S` contributes `log ‖y_q‖ ≤ 0`.
    rw [hkey]
    exact neg_nonneg.mpr (Finset.sum_nonpos fun q hq =>
      Real.log_nonpos (norm_nonneg _) (hbd.2 q hq).2)
  · -- The upper bound: every `q ∈ S` contributes `-log ‖y_q‖ ≤ log C₀`.
    rw [hkey, ← Finset.sum_neg_distrib]
    have hC₀pos : 0 < C₀ := lt_of_lt_of_le one_pos hC₀
    calc ∑ q ∈ S, -Real.log ‖(y (NK.GlobalCFT.Place.ofFinite q) : q.adicCompletion K)‖
        ≤ ∑ q ∈ S, Real.log C₀ := Finset.sum_le_sum fun q hq => by
          have h := Real.log_le_log (inv_pos.mpr hC₀pos) (hbd.2 q hq).1
          rw [Real.log_inv] at h
          linarith
      _ = (S.card : ℝ) * Real.log C₀ := by rw [Finset.sum_const, nsmul_eq_mul]

end NK.GlobalCFT.IdeleClassGroup
