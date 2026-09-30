/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Base change of divisors: `toDiv ∘ SumDiv.baseChange = divMap ∘ toDiv`

The base change of divisors along a field extension `L/k` is `Curve.divMap C L : Div C →+ Div C_L`,
whose coefficient at a place `Q'` of `C_L` over a place `Q` of `C` is `e(Q'/Q) · D(Q)` (with
`e(Q'/Q) = 0` if the image of `Q'` is not a closed point).  On the other hand a multiset `s` of
`k`-points of `C` can be base changed to a multiset `SumDiv.baseChange C L s` of `L`-points of
`C_L`, and both constructions give rise to effective divisors.  This file proves that the two
constructions agree:

`SumDiv.toDiv C_L (SumDiv.baseChange C L s) = divMap C L (SumDiv.toDiv C s)`.

This is the divisor-level bridge between the multisets of points (`Σ f`) and the divisor theory
(`Curve.Div`), used to turn a divisor over `k` into a multiset over a splitting field.

The proof is a coefficient computation at a place `Q'` of `C_L`, and uses exactly the three
"fibre over a `k`-rational point" facts, taken here as hypotheses:

* `hproj` (`Work.KeyLemma.BaseChange.proj_placeOfPoint_baseChange`): the base-changed place of
  `Pt.baseChange L p` projects to the place of `p`;
* `huniq`: the place of `C_L` over a place of the form `placeOfPoint C p` is unique;
* `hramIdx`: the ramification index of such a place is `1`.

## Main results

* `Work.KeyLemma.BaseChange.coeffAt_baseChange`
* `Work.KeyLemma.BaseChange.toDiv_baseChange`
-/
import Mathlib
import Submission.Work.KeyLemma.BaseChange

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


namespace Work.KeyLemma.BaseChange

universe u

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

/-- **Coefficient of the base change of a multiset of points.**  The coefficient at a place `Q'` of
`C_L` of the divisor `SumDiv.toDiv C_L (SumDiv.baseChange C L s)` attached to the base change of a
multiset `s` of `k`-points of `C` is the sum of the multiplicities of those points `p` of `s`
whose base-changed place is `Q'`. -/
theorem coeffAt_baseChange {k : Type u} [Field k] (C : Work.CurveBasics.Curve k)
    (L : Type u) [Field L] [Algebra k L] (s : Work.KeyLemma.Curve.SumDiv C)
    (Q' : (Work.CurveBasics.Curve.baseChange C L).Place) :
    (Work.KeyLemma.Curve.SumDiv.baseChange C L s).coeffAt Q' =
      s.sum (fun p m => if Work.KeyLemma.Curve.placeOfPoint
            (Work.CurveBasics.Curve.baseChange C L)
            (Work.KeyLemma.Curve.Pt.baseChange L p) = Q' then (m : ℤ) else 0) := by
  classical
  have h1 : (Work.KeyLemma.Curve.SumDiv.baseChange C L s).coeffAt Q' =
      (Finsupp.mapDomain (Work.KeyLemma.Curve.Pt.baseChange L) s).sum
        (fun q m => if Work.KeyLemma.Curve.placeOfPoint
            (Work.CurveBasics.Curve.baseChange C L) q = Q' then (m : ℤ) else 0) := rfl
  rw [h1]
  exact Finsupp.sum_mapDomain_index (fun b => by split <;> simp)
    (fun b m1 m2 => by split <;> simp [Nat.cast_add])

theorem toDiv_baseChange {k : Type u} [Field k] (C : Work.CurveBasics.Curve k)
    (L : Type u) [Field L] [Algebra k L] (s : Work.KeyLemma.Curve.SumDiv C)
    (hproj : ∀ p : Work.KeyLemma.Curve.Point C,
      Work.CurveBasics.Curve.baseChangeFst C L
        ((Work.KeyLemma.Curve.placeOfPoint (Work.CurveBasics.Curve.baseChange C L)
          (Work.KeyLemma.Curve.Pt.baseChange L p)).point) =
      (Work.KeyLemma.Curve.placeOfPoint C p).point)
    (huniq : ∀ (p : Work.KeyLemma.Curve.Point C)
      (Q' : (Work.CurveBasics.Curve.baseChange C L).Place),
      Work.CurveBasics.Curve.baseChangeFst C L Q'.point =
        (Work.KeyLemma.Curve.placeOfPoint C p).point →
      Q' = Work.KeyLemma.Curve.placeOfPoint (Work.CurveBasics.Curve.baseChange C L)
        (Work.KeyLemma.Curve.Pt.baseChange L p))
    (hramIdx : ∀ p : Work.KeyLemma.Curve.Point C,
      Work.CurveBasics.Curve.ramIdx C L
        (Work.KeyLemma.Curve.placeOfPoint (Work.CurveBasics.Curve.baseChange C L)
          (Work.KeyLemma.Curve.Pt.baseChange L p)) = 1) :
    Work.KeyLemma.Curve.SumDiv.toDiv (Work.CurveBasics.Curve.baseChange C L)
        (Work.KeyLemma.Curve.SumDiv.baseChange C L s) =
      Work.CurveBasics.Curve.divMap C L (Work.KeyLemma.Curve.SumDiv.toDiv C s) := by
  classical
  apply Finsupp.ext
  intro Q'
  rw [Work.KeyLemma.Curve.SumDiv.toDiv_apply, Work.CurveBasics.Curve.divMap_apply]
  by_cases hcl : IsClosed ({(C.baseChangeFst L) Q'.point} : Set C.left)
  · -- the place `Q'` of `C_L` lies over a closed point of `C`: compare coefficients at the
    -- place `C.under L Q' hcl` of `C`.
    have hcoe : Work.CurveBasics.Curve.divMapCoeff C L (Work.KeyLemma.Curve.SumDiv.toDiv C s) Q'
        = (Work.KeyLemma.Curve.SumDiv.toDiv C s) (C.under L Q' hcl) * C.ramIdx L Q' := by
      rw [Work.CurveBasics.Curve.divMapCoeff, dite_eq_left hcl]
    rw [hcoe, Work.KeyLemma.Curve.SumDiv.toDiv_apply]
    rw [coeffAt_baseChange C L s Q']
    rw [Work.KeyLemma.Curve.SumDiv.coeffAt]
    -- Both sides are sums over the points of `s`; the conditions "the base-changed place is `Q'`"
    -- and "the place is `C.under L Q' hcl`" are equivalent.
    have hS : s.sum (fun p m => if Work.KeyLemma.Curve.placeOfPoint
          (Work.CurveBasics.Curve.baseChange C L) (Work.KeyLemma.Curve.Pt.baseChange L p) = Q'
          then (m : ℤ) else 0) =
        s.sum (fun p m => if Work.KeyLemma.Curve.placeOfPoint C p = C.under L Q' hcl
          then (m : ℤ) else 0) := by
      refine Finsupp.sum_congr fun p hp => ?_
      by_cases hc : Work.KeyLemma.Curve.placeOfPoint (Work.CurveBasics.Curve.baseChange C L)
          (Work.KeyLemma.Curve.Pt.baseChange L p) = Q'
      · have hc2 : Work.KeyLemma.Curve.placeOfPoint C p = C.under L Q' hcl := by
          apply Subtype.ext
          calc (Work.KeyLemma.Curve.placeOfPoint C p).point
              = (C.baseChangeFst L) ((Work.KeyLemma.Curve.placeOfPoint
                    (Work.CurveBasics.Curve.baseChange C L)
                    (Work.KeyLemma.Curve.Pt.baseChange L p)).point) := (hproj p).symm
            _ = (C.baseChangeFst L) Q'.point := by rw [hc]
            _ = (C.under L Q' hcl).point := rfl
        rw [ite_eq_left hc, ite_eq_left hc2]
      · have hc2 : ¬ (Work.KeyLemma.Curve.placeOfPoint C p = C.under L Q' hcl) := by
          intro hcon
          exact hc (huniq p Q' (by
            have h3 : (Work.KeyLemma.Curve.placeOfPoint C p).point
                = (C.under L Q' hcl).point := congrArg (fun Q => Q.point) hcon
            rw [h3]
            rfl)).symm
        rw [ite_eq_right hc, ite_eq_right hc2]
    rw [hS]
    -- The ramification index is `1` where the sum does not vanish.
    by_cases hS0 : s.sum (fun p m => if Work.KeyLemma.Curve.placeOfPoint C p = C.under L Q' hcl
        then (m : ℤ) else 0) = 0
    · rw [hS0, zero_mul]
    · have hform : s.sum (fun p m => if Work.KeyLemma.Curve.placeOfPoint C p = C.under L Q' hcl
          then (m : ℤ) else 0)
          = ∑ p ∈ s.support, (if Work.KeyLemma.Curve.placeOfPoint C p = C.under L Q' hcl
            then (s p : ℤ) else 0) := rfl
      obtain ⟨p, hp_mem, hp_ne⟩ :=
        Finset.exists_ne_zero_of_sum_ne_zero (by rw [← hform]; exact hS0)
      have hcond : Work.KeyLemma.Curve.placeOfPoint C p = C.under L Q' hcl := by
        by_contra hc
        exact hp_ne (by rw [ite_eq_right hc])
      have hram : C.ramIdx L Q' = 1 := by
        have hq : Q' = Work.KeyLemma.Curve.placeOfPoint
            (Work.CurveBasics.Curve.baseChange C L)
            (Work.KeyLemma.Curve.Pt.baseChange L p) := by
          apply huniq p Q'
          have h3 : (Work.KeyLemma.Curve.placeOfPoint C p).point = (C.under L Q' hcl).point :=
            congrArg (fun Q => Q.point) hcond
          rw [h3]
          rfl
        rw [hq, hramIdx p]
      rw [hram, mul_one]
  · -- the place `Q'` of `C_L` does not lie over a closed point of `C`: both coefficients vanish.
    have hcoe : Work.CurveBasics.Curve.divMapCoeff C L
        (Work.KeyLemma.Curve.SumDiv.toDiv C s) Q' = 0 := by
      rw [Work.CurveBasics.Curve.divMapCoeff, dite_eq_right hcl]
    rw [hcoe]
    rw [coeffAt_baseChange C L s Q']
    rw [show s.sum (fun p m => if Work.KeyLemma.Curve.placeOfPoint
          (Work.CurveBasics.Curve.baseChange C L) (Work.KeyLemma.Curve.Pt.baseChange L p) = Q'
          then (m : ℤ) else 0) = s.sum (fun p m => (0 : ℤ)) from
      Finsupp.sum_congr fun p hp => by
        by_cases hc : Work.KeyLemma.Curve.placeOfPoint (Work.CurveBasics.Curve.baseChange C L)
            (Work.KeyLemma.Curve.Pt.baseChange L p) = Q'
        · -- the base-changed place would project to a closed point of `C`, contradiction
          exfalso
          apply hcl
          have h2' : Q'.point = (Work.KeyLemma.Curve.placeOfPoint
              (Work.CurveBasics.Curve.baseChange C L)
              (Work.KeyLemma.Curve.Pt.baseChange L p)).point := by rw [hc]
          have hset : ({(C.baseChangeFst L) Q'.point} : Set C.left)
              = {(Work.KeyLemma.Curve.placeOfPoint C p).point} := by rw [h2', hproj p]
          rw [hset]
          exact (Work.KeyLemma.Curve.placeOfPoint C p).isClosed
        · rw [ite_eq_right hc]]
    simp

end Work.KeyLemma.BaseChange
