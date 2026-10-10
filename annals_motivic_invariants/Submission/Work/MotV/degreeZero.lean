/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.MotV

# Degree zero: the sum of the orders of vanishing of a function is zero

This file proves `Work.MotV.degreeZero`: for `f ≠ 0` in the function field `N(E)` of an elliptic
curve `E` over an algebraically closed field `N` and any finite set `S` of rational places
containing the support of `f`, the sum `ordSum E S f` of the orders of vanishing of `f` over `S`
is zero.  (This is the statement that the divisor of `f` has degree zero, in the form needed by
the Hurwitz count of route V.)

The proof reduces `f = a / b` with `a b` in the affine coordinate ring, uses the additivity of
`ordP` (`H.ord_mul`, `H.ord_inv`) and the hypothesis `hSumA` (the degree-zero statement for
elements of the coordinate ring, whose support is `ptsOf E (norm a)`), together with the support
inclusion `Work.MotV.support_subset` proved here: the support of a coordinate-ring element `a` is
contained in `ptsOf E H.infRat (Algebra.norm (Polynomial N) a)` — the point at infinity together
with the places above the roots of the norm of `a`.
-/

import Mathlib
import Submission.Work.MotV.H1Data
import Submission.Work.MotV.Machinery
import Submission.Work.MotC2.AffPlace
import Submission.Work.MotC2.Classification
import Submission.Work.MotV.normEvalOfAlgHom
import Submission.Work.MotV.algHomOfOrdNeZero
import Submission.Work.MotV.memPtsOfAffPlace
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open Polynomial WeierstrassCurve WeierstrassCurve.Affine

namespace Work.MotV

noncomputable section

/-- The support of an element of the affine coordinate ring is contained in `ptsOf`: if the order
of vanishing of `algebraMap a` at a rational place `Q` is nonzero, then either `Q` is the point at
infinity, or `Q` is the local ring of a nonsingular affine point `(c,d)` whose `x`-coordinate `c`
is a root of the norm of `a`. -/
theorem support_subset {N : Type*} [Field N] (E : WeierstrassCurve N) [E.IsElliptic]
    (H : Work.MotV.H1Data N E) (a : WeierstrassCurve.Affine.CoordinateRing E) (ha : a ≠ 0) :
    ∀ Q : Work.MotV.Place N E,
      Work.MotV.ordP E Q
        (algebraMap (WeierstrassCurve.Affine.CoordinateRing E) (Work.MotC2.Func E) a) ≠ 0 →
      Q ∈ Work.MotV.ptsOf E H.infRat (Algebra.norm (Polynomial N) a) := by
  intro Q hQ
  rcases Work.MotC2.Classification N E Q.1 Q.2 with h | ⟨c, d, hns, hQ1⟩
  · -- the point at infinity
    have hQ' : Q = ⟨Work.MotC2.infPlace E, H.infRat⟩ := Subtype.ext h
    rw [hQ']
    simp [Work.MotV.ptsOf]
  · -- an affine place
    have hplace : Work.MotC2.IsRatPlace E (Work.MotC2.affPlaceAt E c d) := hQ1 ▸ Q.2
    have hQ' : Q = ⟨Work.MotC2.affPlaceAt E c d, hplace⟩ := Subtype.ext hQ1
    have hord : Work.MotV.ordOfPlace E (Work.MotC2.affPlaceAt E c d) hplace
        (algebraMap (WeierstrassCurve.Affine.CoordinateRing E) (Work.MotC2.Func E) a) ≠ 0 := by
      have h2 := hQ
      rw [hQ'] at h2
      simpa only [Work.MotV.ordP] using h2
    obtain ⟨φ, hx, hy, hφa⟩ := Work.MotV.algHomOfOrdNeZero E H a ha c d hns hplace hord
    have heq : WeierstrassCurve.Affine.Equation E c d :=
      (WeierstrassCurve.Affine.equation_iff_nonsingular).mpr hns
    have hroot : (Algebra.norm (Polynomial N) a).IsRoot c :=
      Work.MotV.normEvalOfAlgHom E a c d φ hx hy hφa heq
    rw [hQ']
    exact Work.MotV.memPtsOfAffPlace E a ha H.infRat c d hns hplace hroot

theorem degreeZero {N : Type*} [Field N] [IsAlgClosed N] (E : WeierstrassCurve N) [E.IsElliptic]
    (H : Work.MotV.H1Data N E)
    (hSumA : ∀ (a : WeierstrassCurve.Affine.CoordinateRing E), a ≠ 0 →
      Work.MotV.ordSum E (Work.MotV.ptsOf E H.infRat (Algebra.norm (Polynomial N) a))
        (algebraMap (WeierstrassCurve.Affine.CoordinateRing E) (Work.MotC2.Func E) a) = 0)
    (f : Work.MotC2.Func E) (hf : f ≠ 0) (S : Finset (Work.MotV.Place N E))
    (hsup : ∀ Q : Work.MotV.Place N E, Work.MotV.ordP E Q f ≠ 0 → Q ∈ S) :
    Work.MotV.ordSum E S f = 0 := by
  classical
  -- write `f = a / b` with `a`, `b` in the coordinate ring
  obtain ⟨a, b, hb_mem, hdiv⟩ :=
    IsFractionRing.div_surjective (WeierstrassCurve.Affine.CoordinateRing E) f
  have hb : b ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hb_mem
  have hfb : algebraMap (WeierstrassCurve.Affine.CoordinateRing E) (Work.MotC2.Func E) b ≠ 0 := by
    intro h0
    exact hb (IsFractionRing.injective (WeierstrassCurve.Affine.CoordinateRing E)
      (Work.MotC2.Func E) (by simpa using h0))
  have hfa : algebraMap (WeierstrassCurve.Affine.CoordinateRing E) (Work.MotC2.Func E) a ≠ 0 := by
    intro h0
    exact hf (by rw [← hdiv, h0, zero_div])
  have ha : a ≠ 0 := fun h0 => hfa (by rw [h0, map_zero])
  -- additivity of the order of vanishing
  have hpoint : ∀ Q : Work.MotV.Place N E,
      Work.MotV.ordP E Q f =
        Work.MotV.ordP E Q (algebraMap (WeierstrassCurve.Affine.CoordinateRing E)
            (Work.MotC2.Func E) a) -
          Work.MotV.ordP E Q (algebraMap (WeierstrassCurve.Affine.CoordinateRing E)
            (Work.MotC2.Func E) b) := by
    intro Q
    simp only [Work.MotV.ordP]
    rw [← hdiv, div_eq_mul_inv]
    rw [H.ord_mul Q.1 Q.2 _ _ hfa (inv_ne_zero hfb), H.ord_inv Q.1 Q.2 _ hfb]
    first | refl_ring1 | ring
  -- the supports of `a` and of `b`
  let Ta : Finset (Work.MotV.Place N E) :=
    Work.MotV.ptsOf E H.infRat (Algebra.norm (Polynomial N) a)
  let Tb : Finset (Work.MotV.Place N E) :=
    Work.MotV.ptsOf E H.infRat (Algebra.norm (Polynomial N) b)
  let T : Finset (Work.MotV.Place N E) := (Ta ∪ Tb) ∪ S
  have hsupp_a : ∀ Q : Work.MotV.Place N E,
      Work.MotV.ordP E Q
        (algebraMap (WeierstrassCurve.Affine.CoordinateRing E) (Work.MotC2.Func E) a) ≠ 0 →
      Q ∈ Ta :=
    support_subset E H a ha
  have hsupp_b : ∀ Q : Work.MotV.Place N E,
      Work.MotV.ordP E Q
        (algebraMap (WeierstrassCurve.Affine.CoordinateRing E) (Work.MotC2.Func E) b) ≠ 0 →
      Q ∈ Tb :=
    support_subset E H b hb
  -- enlarge `S` to `T`
  have hsum1 : Work.MotV.ordSum E S f = ∑ Q ∈ T, Work.MotV.ordP E Q f := by
    show (∑ Q ∈ S, Work.MotV.ordP E Q f) = ∑ Q ∈ T, Work.MotV.ordP E Q f
    refine Finset.sum_subset ?_ ?_
    · intro x hx
      exact Finset.mem_union.mpr (Or.inr hx)
    · intro x _ hxS
      by_contra hne
      exact hxS (hsup x hne)
  -- linearity of the sum
  have hsum2 : ∑ Q ∈ T, Work.MotV.ordP E Q f =
      (∑ Q ∈ T, Work.MotV.ordP E Q (algebraMap (WeierstrassCurve.Affine.CoordinateRing E)
          (Work.MotC2.Func E) a)) -
        ∑ Q ∈ T, Work.MotV.ordP E Q (algebraMap (WeierstrassCurve.Affine.CoordinateRing E)
          (Work.MotC2.Func E) b) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun Q _ => hpoint Q)
  -- the sums of the orders of `a` and of `b` vanish (`hSumA` and the support inclusion)
  have hTa_sum : ∑ Q ∈ T, Work.MotV.ordP E Q (algebraMap
      (WeierstrassCurve.Affine.CoordinateRing E) (Work.MotC2.Func E) a) = 0 := by
    have hle : Ta ⊆ T :=
      fun x hx => Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl hx)))
    have hzero : ∀ x ∈ T, x ∉ Ta → Work.MotV.ordP E x (algebraMap
        (WeierstrassCurve.Affine.CoordinateRing E) (Work.MotC2.Func E) a) = 0 := by
      intro x _ hx
      by_contra hne
      exact hx (hsupp_a x hne)
    rw [← Finset.sum_subset hle hzero]
    show Work.MotV.ordSum E Ta (algebraMap (WeierstrassCurve.Affine.CoordinateRing E)
      (Work.MotC2.Func E) a) = 0
    exact hSumA a ha
  have hTb_sum : ∑ Q ∈ T, Work.MotV.ordP E Q (algebraMap
      (WeierstrassCurve.Affine.CoordinateRing E) (Work.MotC2.Func E) b) = 0 := by
    have hle : Tb ⊆ T :=
      fun x hx => Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr hx)))
    have hzero : ∀ x ∈ T, x ∉ Tb → Work.MotV.ordP E x (algebraMap
        (WeierstrassCurve.Affine.CoordinateRing E) (Work.MotC2.Func E) b) = 0 := by
      intro x _ hx
      by_contra hne
      exact hx (hsupp_b x hne)
    rw [← Finset.sum_subset hle hzero]
    show Work.MotV.ordSum E Tb (algebraMap (WeierstrassCurve.Affine.CoordinateRing E)
      (Work.MotC2.Func E) b) = 0
    exact hSumA b hb
  rw [hsum1, hsum2, hTa_sum, hTb_sum, sub_zero]

end

end Work.MotV
