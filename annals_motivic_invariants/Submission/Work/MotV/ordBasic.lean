/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.MotV

# Elementary consequences of the order axioms at a rational place

`Work.MotV.ordOfPlace E S hS f` is the order of vanishing of `f ∈ N(E)` at the rational place `S`
(positive = zero of `f`, negative = pole).  The file `Submission/Work/MotV/H1Data.lean` collects the
basic laws of `ordOfPlace` (multiplicativity, inverse, sign criterion, ultrametric inequality, the
local structure at the point at infinity) as the fields of the structure `Work.MotV.H1Data`.

Here we derive from those axioms the elementary corollaries that the computation of the pole order
at infinity needs:

* `ordOfPlace_one`, `ordOfPlace_neg_one`, `ordOfPlace_neg`: the order of `1`, `-1`, `-f`;
* `ordOfPlace_const`: the order of a non-zero constant is `0`;
* `ordOfPlace_pow`: `v(fⁿ) = n·v(f)`;
* `ordOfPlace_add_eq_of_lt`, `ordOfPlace_add_eq_min`: **no cancellation** between summands of
  different order, `v(f+g) = min (v f) (v g)`.

We also record two geometric facts about the chart at infinity that are useful for consumers:
`genY_ne_zero` and the membership of `aeval (infU E) P` in the local ring of the point at infinity.
-/

import Mathlib
import Submission.Work.MotV.H1Data
import Submission.Work.MotV.PlaceDefs
import Submission.Work.MotC2.PoleOrder
import Submission.Work.MotC2.PoleTgen
import Submission.Work.MotC2.aeval_infU_mul_pow_eq_aeval_reverse
import Submission.Work.MotC2.algebraMap_smul_eq_aeval
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open WeierstrassCurve WeierstrassCurve.Affine
open scoped WithZero

namespace Work.MotV

noncomputable section

variable {N : Type*} [Field N]

/-! ## The order axioms -/

section OrdAxioms

variable (E : WeierstrassCurve N) [E.IsElliptic] (H : H1Data N E)
variable (S : Subalgebra N (MotC2.Func E)) (hS : MotC2.IsRatPlace E S)
include H

/-- The order of `1` is `0`: `1` and `1⁻¹ = 1` are both regular at `S`. -/
lemma ordOfPlace_one : ordOfPlace E S hS (1 : MotC2.Func E) = 0 := by
  have hle : (0 : ℤ) ≤ ordOfPlace E S hS (1 : MotC2.Func E) :=
    (H.ord_nonneg S hS 1).mpr S.one_mem
  have hinv : ordOfPlace E S hS ((1 : MotC2.Func E))⁻¹ =
      -ordOfPlace E S hS (1 : MotC2.Func E) := H.ord_inv S hS 1 one_ne_zero
  rw [inv_one] at hinv
  linarith

/-- The order of `-1` is `0`. -/
lemma ordOfPlace_neg_one : ordOfPlace E S hS (-1 : MotC2.Func E) = 0 := by
  have hle : (0 : ℤ) ≤ ordOfPlace E S hS (-1 : MotC2.Func E) :=
    (H.ord_nonneg S hS (-1)).mpr (S.neg_mem S.one_mem)
  have hne : (-1 : MotC2.Func E) ≠ 0 := neg_ne_zero.mpr one_ne_zero
  have hinv : ordOfPlace E S hS ((-1 : MotC2.Func E))⁻¹ =
      -ordOfPlace E S hS (-1 : MotC2.Func E) := H.ord_inv S hS (-1) hne
  rw [inv_neg, inv_one] at hinv
  linarith

/-- `v(-f) = v(f)` for `f ≠ 0`. -/
lemma ordOfPlace_neg (f : MotC2.Func E) (hf : f ≠ 0) :
    ordOfPlace E S hS (-f) = ordOfPlace E S hS f := by
  have hmul := H.ord_mul S hS (-1) f (neg_ne_zero.mpr one_ne_zero) hf
  rw [ordOfPlace_neg_one E H S hS, zero_add, neg_one_mul] at hmul
  exact hmul

/-- The order of a non-zero constant is `0`. -/
lemma ordOfPlace_const (c : N) (hc : c ≠ 0) :
    ordOfPlace E S hS (algebraMap N (MotC2.Func E) c) = 0 := by
  have hc' : algebraMap N (MotC2.Func E) c ≠ 0 := by
    simpa using (FaithfulSMul.algebraMap_injective N (MotC2.Func E)).ne hc
  have h1 : (0 : ℤ) ≤ ordOfPlace E S hS (algebraMap N (MotC2.Func E) c) :=
    (H.ord_nonneg S hS _).mpr (S.algebraMap_mem c)
  have hmem : (algebraMap N (MotC2.Func E) c)⁻¹ ∈ S := by
    rw [← map_inv₀]
    exact S.algebraMap_mem c⁻¹
  have h2 : (0 : ℤ) ≤ ordOfPlace E S hS (algebraMap N (MotC2.Func E) c)⁻¹ :=
    (H.ord_nonneg S hS _).mpr hmem
  have h3 : ordOfPlace E S hS (algebraMap N (MotC2.Func E) c)⁻¹ =
      -ordOfPlace E S hS (algebraMap N (MotC2.Func E) c) := H.ord_inv S hS _ hc'
  linarith

/-- `v(fⁿ) = n·v(f)`. -/
lemma ordOfPlace_pow (f : MotC2.Func E) (hf : f ≠ 0) (n : ℕ) :
    ordOfPlace E S hS (f ^ n) = n * ordOfPlace E S hS f := by
  induction n with
  | zero => simp [ordOfPlace_one E H S hS]
  | succ n ih =>
      rw [pow_succ]
      rw [H.ord_mul S hS (f ^ n) f (pow_ne_zero n hf) hf, ih]
      push_cast
      first | refl_ring1 | ring

/-- **No cancellation**: if `v(f) < v(g)` then `v(f+g) = v(f)`. -/
lemma ordOfPlace_add_eq_of_lt (f g : MotC2.Func E) (hf : f ≠ 0) (hg : g ≠ 0)
    (hfg : f + g ≠ 0) (h : ordOfPlace E S hS f < ordOfPlace E S hS g) :
    ordOfPlace E S hS (f + g) = ordOfPlace E S hS f := by
  have hsum := H.ord_add S hS (f + g) (-g) (by rw [add_neg_cancel_right]; exact hf)
  rw [add_neg_cancel_right] at hsum
  rw [ordOfPlace_neg E H S hS g hg] at hsum
  have hle : ordOfPlace E S hS (f + g) ≤ ordOfPlace E S hS f := by
    by_contra hcon
    rw [not_le] at hcon
    have hlt : ordOfPlace E S hS f < min (ordOfPlace E S hS (f + g)) (ordOfPlace E S hS g) :=
      lt_min hcon h
    exact absurd (lt_of_le_of_lt hsum hlt) (lt_irrefl _)
  have hge : ordOfPlace E S hS f ≤ ordOfPlace E S hS (f + g) := by
    have := H.ord_add S hS f g hfg
    rwa [min_eq_left (le_of_lt h)] at this
  linarith

/-- **No cancellation**: if `v(f) ≠ v(g)` then `v(f+g) = min (v f) (v g)`. -/
lemma ordOfPlace_add_eq_min (f g : MotC2.Func E) (hf : f ≠ 0) (hg : g ≠ 0)
    (hfg : f + g ≠ 0) (hne : ordOfPlace E S hS f ≠ ordOfPlace E S hS g) :
    ordOfPlace E S hS (f + g) = min (ordOfPlace E S hS f) (ordOfPlace E S hS g) := by
  rcases lt_or_gt_of_ne hne with h | h
  · rw [ordOfPlace_add_eq_of_lt E H S hS f g hf hg hfg h, min_eq_left (le_of_lt h)]
  · have h' := ordOfPlace_add_eq_of_lt E H S hS g f hg hf (by rwa [add_comm]) h
    rw [add_comm, min_comm, h', min_eq_left (le_of_lt h)]

end OrdAxioms

/-! ## The chart at infinity -/

section Chart

/-- `y = genY E` is non-zero in the function field. -/
lemma genY_ne_zero (E : WeierstrassCurve N) : genY E ≠ 0 := by
  have hone : WeierstrassCurve.Affine.CoordinateRing.YClass E (0 : Polynomial N) ≠ 0 :=
    WeierstrassCurve.Affine.CoordinateRing.YClass_ne_zero (W' := E) 0
  have hcoord : MotC2.coordY E ≠ 0 := by
    simpa [WeierstrassCurve.Affine.CoordinateRing.YClass, MotC2.coordY_eq_mk] using hone
  intro h
  have h' : (algebraMap (CoordinateRing E) (MotC2.Func E)) (MotC2.coordY E) =
      (algebraMap (CoordinateRing E) (MotC2.Func E)) 0 := by
    rw [map_zero]
    exact h
  exact hcoord (IsFractionRing.injective (CoordinateRing E) (MotC2.Func E) h')

/-- A polynomial in `u = 1/x` lies in the local ring of the point at infinity. -/
lemma aeval_infU_mem_infPlace (E : WeierstrassCurve N) (P : Polynomial N) :
    Polynomial.aeval (MotC2.infU E) P ∈ MotC2.infPlace E :=
  MotC2.infCoordRing_le_infPlace E (MotC2.aeval_infU_mem_infCoordRing E P)

/-- A polynomial in `u = 1/x` is regular at the point at infinity. -/
lemma ordOfPlace_aeval_infU_nonneg (E : WeierstrassCurve N) [E.IsElliptic] (H : H1Data N E)
    (P : Polynomial N) :
    0 ≤ ordOfPlace E (MotC2.infPlace E) H.infRat (Polynomial.aeval (MotC2.infU E) P) :=
  (H.ord_nonneg (MotC2.infPlace E) H.infRat _).mpr (aeval_infU_mem_infPlace E P)

end Chart

end

end Work.MotV
