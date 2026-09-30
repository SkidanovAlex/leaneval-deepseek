/-
# `BridgeSquare/planeToSingD.lean` — the chain-map identity `∂ ∘ toSing = toSing ∘ dLC`

The pushforward `toSing G k : AffC k →ₗ[ℤ] C_k(X)` of finite affine chains of the cusp coordinate
space `E3 = ℝ³` along a continuous map `G : E3 → X` (`PlanePush.lean`) satisfies

  `∂ (toSing G (k+1) c) = toSing G k (dLC k c)`,

i.e. it is a chain map from the *combinatorial* chain complex `(AffC, dLC)` of `PlaneAff.lean` to
the singular chain complex of `X`.  **No affineness assumption is needed**: the statement is the
formal consequence of the boundary formula for a single singular generator, applied to the
description of `toSing` as a `ℤ`-linear combination.

## Proof

Every chain `c = ∑ₚ aₚ • p` is a `ℤ`-linear combination of the generators `p` (a `Fin (k+2) → E3`
vertex family), and both sides of the identity are `ℤ`-linear in `c` (`dLC` and `toSing` are linear,
`∂` is additive and `ℤ`-homogeneous).  So it suffices to prove the identity for `Finsupp.single p a`,
and since `single p a = a • single p 1` it suffices, by homogeneity, to prove it for `single p 1`.
For that one computes

* `toSing G (k+1) (single p 1) = singGen (G ∘ esimp p)` (`toSing_single_one`), and
* the boundary of the pushed generator is the alternating sum of the pushed generators of the face
  families, `∂ (singGen (G ∘ esimp p)) = ∑ᵢ (-1)ⁱ • singGen (G ∘ esimp (vface i p))`
  (`toSing_esimp_d`, from `singGen_d` of `ChartAlgA.lean` and the face compatibility
  `esimp_comp_cFace`), which is exactly `toSing G k (dLC k (single p 1))` by `dLC_single`.

*Remark on the scalar action.*  The carrier of a `ModuleCat ℤ` is a `ℤ`-module in several ways
(`ZSMul.toSMul`, the action induced by `Module.toDistribMulAction`, …) and the several occurrences
of `•` in the statements below are resolved by different type class instances.  The option
`backward.isDefEq.respectTransparency false` makes unification see through the instance
definitions, which is what lets `simp`/`map_zsmul` handle the bookkeeping; the statement itself
never mentions `•`, so this is purely a matter of the proof.
-/
import Mathlib
import Submission.Work.BridgeSquare.PlanePush
import Submission.Work.BridgeSquare.PlaneAff
import Submission.Work.BridgeSquare.ChartAlgA

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped Topology Simplicial
open Convexity

namespace Work.BridgeSquare

noncomputable section

/-! ## §1  The face of an affine simplex -/

/-- **The `i`-th face of the affine simplex `esimp p` is the affine simplex of the face family**
`vface i p = p ∘ Fin.succAbove i`. -/
theorem esimp_comp_cFace {k : ℕ} (p : Fin (k + 2) → CuspE3) (i : Fin (k + 2)) :
    (esimp p).comp (cFace i) = esimp (vface i p) := by
  apply ContinuousMap.ext
  intro z
  exact esimp_map p i.succAbove z

/-! ## §2  The boundary of a pushed affine generator -/

/-- **The boundary of a pushed affine generator**: the alternating sum of the pushed generators of
the face families.  This is `singGen_d` (`ChartAlgA.lean`) combined with the face compatibility
`esimp_comp_cFace`. -/
theorem toSing_esimp_d {X : TopCat} (G : C(CuspE3, X)) (k : ℕ) (p : Fin (k + 2) → CuspE3) :
    (singCxFun.obj X).d (k + 1) k (singGen (G.comp (esimp p)))
      = ∑ i : Fin (k + 2), ((-1 : ℤ) ^ (i : ℕ)) •
          singGen (G.comp (esimp (vface i p))) := by
  rw [singGen_d]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ContinuousMap.comp_assoc, esimp_comp_cFace]

/-- **`toSing` on the unit generator**: the pushforward of the vertex family `p` with coefficient
one is the singular generator of the affine simplex `G ∘ esimp p`. -/
theorem toSing_single_one {X : TopCat} (G : C(CuspE3, X)) (k : ℕ)
    (p : Fin (k + 1) → CuspE3) :
    toSing G k (Finsupp.single p (1 : ℤ)) = singGen (G.comp (esimp p)) := by
  rw [toSing, Finsupp.linearCombination_single]
  simp

/-- The differential of the singular chain complex of `X` commutes with the `ℤ`-action on chains. -/
theorem singCx_d_zsmul {X : TopCat} (m n : ℕ) (a : ℤ) (x : (singCxFun.obj X).X m) :
    (singCxFun.obj X).d m n (a • x) = a • ((singCxFun.obj X).d m n x) :=
  map_zsmul (ConcreteCategory.hom ((singCxFun.obj X).d m n)) a x

/-! ## §3  The generator case of the chain-map identity -/

/-- **The chain-map identity on the unit generator** `single p 1`: the boundary of
`toSing G (k+1) (single p 1)` is `toSing G k (dLC k (single p 1))`. -/
theorem planeToSingD_gen_one {X : TopCat} (G : C(CuspE3, X)) (k : ℕ)
    (p : Fin (k + 2) → CuspE3) :
    (singCxFun.obj X).d (k + 1) k (toSing G (k + 1) (Finsupp.single p 1))
      = toSing G k (dLC k (Finsupp.single p 1)) := by
  have hR : toSing G k (dLC k (Finsupp.single p 1))
      = ∑ i : Fin (k + 2), ((-1 : ℤ) ^ (i : ℕ)) •
          singGen (G.comp (esimp (vface i p))) := by
    rw [dLC_single, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_zsmul, toSing_single_one]
  rw [toSing_single_one, toSing_esimp_d, hR]

/-- **The chain-map identity on a generator** `single p a` with an arbitrary coefficient `a`. -/
theorem planeToSingD_gen {X : TopCat} (G : C(CuspE3, X)) (k : ℕ)
    (p : Fin (k + 2) → CuspE3) (a : ℤ) :
    (singCxFun.obj X).d (k + 1) k (toSing G (k + 1) (Finsupp.single p a))
      = toSing G k (dLC k (Finsupp.single p a)) := by
  have hs : (Finsupp.single p a : AffC (k + 1)) = a • Finsupp.single p (1 : ℤ) := by
    rw [Finsupp.smul_single_one]
  rw [hs, map_zsmul, singCx_d_zsmul, planeToSingD_gen_one, ← map_zsmul, ← map_zsmul, ← hs]

/-! ## §4  The chain-map identity -/

/-- **The pushforward of affine chains is a chain map**: `∂ (toSing G c) = toSing G (dLC c)`.

Both sides are `ℤ`-linear in `c`, so it suffices to prove the identity on the generators
`Finsupp.single p a` (`planeToSingD_gen`); the induction is `Finsupp.induction`. -/
theorem planeToSingD {X : TopCat} (G : C(CuspE3, X)) (k : ℕ) (c : AffC (k + 1)) :
    (singCxFun.obj X).d (k + 1) k (toSing G (k + 1) c) = toSing G k (dLC k c) := by
  refine Finsupp.induction c ?_ ?_
  · simp
  · intro p a f hp ha hf
    simp only [map_add]
    rw [hf, planeToSingD_gen]

end

end Work.BridgeSquare
