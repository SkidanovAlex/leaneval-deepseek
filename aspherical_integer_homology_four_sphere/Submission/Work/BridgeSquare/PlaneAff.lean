/-
# `BridgeSquare/PlaneAff.lean` — finite affine chains in the cusp coordinate space `E3 = ℝ³`

This module is the combinatorial backbone of the slab/plane comparison used by
`Work.BridgeSquare.planeIdentT`.

A *finite affine `k`-chain* is a finitely supported `ℤ`-combination of vertex families
`Fin (k+1) → CuspE3`; the chain *is* the formal sum (`AffC k := (Fin (k+1) → CuspE3) →₀ ℤ`).
Pushing a vertex family forward along a continuous map `G : E3 → X` by the affine simplex `esimp`
(the map `w ↦ ∑ᵢ wᵢ • pᵢ`) gives the singular chain `toSing G p = singGen (G ∘ esimp p)`, and
`toSing` is `ℤ`-linear.  The main results are

* `dLC` — the *combinatorial* boundary (alternating sum of the face families) and
  `toSing_d` — `∂ (toSing G c) = toSing G (dLC c)`: the core identity that turns every chain
  identity of the domain into a chain identity of `M̄` **without any affineness assumption**;
* `coneLC` / `dLC_coneLC` — the cone over a point and the sign-free cone formula
  `∂ (b * c) = c - b * (∂ c)`.

Because no affineness is assumed, the geometric input of the slab (that `mbarPt v` is affine on a
cube, that a chart matches a polytope face, …) enters **only** where two specific chains are
identified, never in the bookkeeping.
-/
import Mathlib
import Submission.Work.BridgeSquare.affineChain
import Submission.Work.BridgeSquare.ChartAlgA

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped Topology Simplicial
open Convexity

-- The `ℤ`-module structure on the carrier of a `ModuleCat` is reached through `ZSMul.toSMul`;
-- making that instance the preferred one makes `map_smul`/`one_smul`/`map_sum` fire (the same
-- device as in `PsiM_truncCell_mem_range.lean` / `Endgame.lean`).
attribute [local instance 100] ZSMul.toSMul
attribute [local instance 100] instMulActionIntOfSubtractionMonoid

namespace Work.BridgeSquare

noncomputable section

/-! ## §1  Faces and cones of vertex families -/

/-- The `i`-th face of a vertex family: the family with the `i`-th vertex omitted. -/
def vface {k : ℕ} (i : Fin (k + 2)) (p : Fin (k + 2) → CuspE3) : Fin (k + 1) → CuspE3 :=
  fun j => p (Fin.succAbove i j)

/-- The cone of a vertex family over a point `b`: prepend `b`. -/
def vcone {k : ℕ} (b : CuspE3) (p : Fin (k + 1) → CuspE3) : Fin (k + 2) → CuspE3 :=
  Fin.cons b p

@[simp] theorem vcone_apply_zero {k : ℕ} (b : CuspE3) (p : Fin (k + 1) → CuspE3) :
    vcone b p 0 = b := rfl

@[simp] theorem vcone_apply_succ {k : ℕ} (b : CuspE3) (p : Fin (k + 1) → CuspE3)
    (j : Fin (k + 1)) : vcone b p j.succ = p j := rfl

/-! ## §2  Affine chains, their boundary and the cone -/

/-- **Finite affine chains of the cusp coordinate space.** -/
abbrev AffC (k : ℕ) := (Fin (k + 1) → CuspE3) →₀ ℤ

/-- **The combinatorial boundary** of affine chains: the alternating sum of the face families. -/
def dLC (k : ℕ) : AffC (k + 1) →ₗ[ℤ] AffC k :=
  ∑ i : Fin (k + 2), ((-1 : ℤ) ^ (i : ℕ)) • Finsupp.lmapDomain ℤ ℤ (vface (k := k) i)

/-- **The cone** of an affine chain over the point `b`. -/
def coneLC (k : ℕ) (b : CuspE3) : AffC k →ₗ[ℤ] AffC (k + 1) :=
  Finsupp.lmapDomain ℤ ℤ (vcone (k := k) b)

theorem dLC_single (k : ℕ) (p : Fin (k + 2) → CuspE3) (a : ℤ) :
    dLC k (Finsupp.single p a)
      = ∑ i : Fin (k + 2), ((-1 : ℤ) ^ (i : ℕ)) • Finsupp.single (vface i p) a := by
  simp only [dLC, LinearMap.sum_apply, LinearMap.smul_apply, Finsupp.lmapDomain_apply,
    Finsupp.mapDomain_single]

theorem coneLC_single (k : ℕ) (b : CuspE3) (p : Fin (k + 1) → CuspE3) (a : ℤ) :
    coneLC k b (Finsupp.single p a) = Finsupp.single (vcone b p) a := by
  rw [coneLC, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]

/-! ### The `Fin`-combinatorics of the cone formula -/

lemma succAbove_succ_succ {n : ℕ} (i : Fin (n + 1)) (j : Fin n) :
    (i.succ).succAbove (j.succ) = (i.succAbove j).succ := by
  rcases lt_or_ge i j.succ with h | h
  · rw [Fin.succAbove_of_lt_succ _ _ (Fin.succ_lt_succ_iff.mpr h),
        Fin.succAbove_of_lt_succ _ _ h]
  · rw [Fin.succAbove_of_succ_le _ _ (Fin.succ_le_succ_iff.mpr h),
        Fin.succAbove_of_succ_le _ _ h, Fin.castSucc_succ]

lemma vface_zero_vcone {k : ℕ} (b : CuspE3) (p : Fin (k + 2) → CuspE3) :
    vface (k := k + 1) (0 : Fin (k + 3)) (vcone b p) = p := by
  funext j; rfl

lemma vface_succ_vcone {k : ℕ} (i : Fin (k + 2)) (b : CuspE3) (p : Fin (k + 2) → CuspE3) :
    vface (k := k + 1) i.succ (vcone b p) = vcone b (vface (k := k) i p) := by
  funext j
  induction j using Fin.cases with
  | zero => rfl
  | succ j' => simp only [vface, vcone, Fin.cons_succ, succAbove_succ_succ]

lemma neg_one_pow_fin_succ {k : ℕ} (i : Fin (k + 2)) :
    ((-1 : ℤ) ^ (i.succ : ℕ)) = -((-1 : ℤ) ^ (i : ℕ)) := by
  rw [Fin.val_succ, pow_succ]; ring

/-- The cone formula on a single generator. -/
theorem dLC_coneLC_single (k : ℕ) (b : CuspE3) (p : Fin (k + 2) → CuspE3) (a : ℤ) :
    dLC (k + 1) (coneLC (k + 1) b (Finsupp.single p a))
      = Finsupp.single p a - coneLC k b (dLC k (Finsupp.single p a)) := by
  have hL : dLC (k + 1) (coneLC (k + 1) b (Finsupp.single p a))
      = ∑ i : Fin (k + 3), ((-1 : ℤ) ^ (i : ℕ)) • Finsupp.single (vface i (vcone b p)) a := by
    rw [coneLC_single, dLC_single]
  have hR : coneLC k b (dLC k (Finsupp.single p a))
      = ∑ i : Fin (k + 2), ((-1 : ℤ) ^ (i : ℕ)) • Finsupp.single (vcone b (vface i p)) a := by
    rw [dLC_single, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, coneLC_single]
  rw [hL, hR, Fin.sum_univ_succ, vface_zero_vcone]
  simp only [Fin.val_zero, pow_zero, one_smul]
  rw [Finset.sum_congr rfl (fun i _ => by
        rw [neg_one_pow_fin_succ, vface_succ_vcone, neg_smul]), Finset.sum_neg_distrib]
  abel

/-- **The sign-free cone formula**: `∂ (b * c) = c - b * (∂ c)`. -/
theorem dLC_coneLC (k : ℕ) (b : CuspE3) (c : AffC (k + 1)) :
    dLC (k + 1) (coneLC (k + 1) b c) = c - coneLC k b (dLC k c) := by
  refine Finsupp.induction c ?h0 ?hstep
  · simp
  · intro a b' f ha hb hf
    simp only [map_add]
    rw [hf, dLC_coneLC_single]
    abel

/-- A coned cycle is *bounded* by the original cycle. -/
theorem dLC_coneLC_of_dLC_eq_zero (k : ℕ) (b : CuspE3) (c : AffC (k + 1))
    (hc : dLC k c = 0) : dLC (k + 1) (coneLC (k + 1) b c) = c := by
  rw [dLC_coneLC, hc, map_zero, sub_zero]

/-! ## §3  Pushing affine chains into a space (see `PlanePush.lean`)

The pushforward `toSing` of an affine chain along a continuous map `G : E3 → X`, together with the
chain-map identity `∂ (toSing G c) = toSing G (dLC c)`, lives in `Submission/Work/BridgeSquare/
PlanePush.lean`: it needs the scalar-action bookkeeping of the `ModuleCat` carriers (the
`ZSMul.toSMul` instance and `zsmul_eq_smul_cast`), which is kept out of this file so that the
purely combinatorial part above stays free of it.
-/

end

end Work.BridgeSquare
