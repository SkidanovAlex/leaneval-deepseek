/-
# Pushing chains of the subdivision of `Q̄` into the chains of `mbarSd`

**Work package W7** of `Submission/Work/NOTES_LEAD_eA.md` (the boundary compatibility of the atlas).

A `k`-simplex of `mbarSd` is an orbit of pairs `(c, s)` — a copy bit and a flag of `Q̄`.  This file
introduces

* `nodeSimplex c s` — the `k`-simplex of `mbarSd` represented by `(c,s)`, and its carrier/lift
  (`carCx_nodeSimplex`, `liftCx_nodeSimplex`) as well as its face maps (`nodeSimplex_face`);
* `pushNode c k` — the linear map sending a chain `∑ a_s • s` of the order complex of `Q̄` to
  `∑ a_s • [nodeSimplex c s]` in the chains of `mbarSd`;
* the support fact `subdivCell_apply_last`: every simplex of the subdivision chain of a cell `e`
  ends at `e`.

The chain-map property `pushNode c k (D z) = kδCpt mbarSd k (pushNode c (k+1) z)` is in
`Submission/Work/MbarHomology/Mbar/pushNode_kδCpt.lean`.
-/
import Mathlib
import Submission.Work.MbarHomology.Mbar.AtlasCx
import Submission.Work.MbarHomology.CellAtlas.Core

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option autoImplicit false

namespace Work.MbarHomology.Mbar

open Work.Subdivision Work.ConvexCells
open scoped BigOperators

noncomputable section

-- Pin the `ℤ`-module structures on free modules so that they agree with the ones used by the
-- `ModuleCat` objects of `CellAtlas.Core`.
attribute [local instance 2000] Pi.Function.module Finsupp.module
attribute [local instance 100] ZSMul.toSMul
attribute [local instance 100] instMulActionIntOfSubtractionMonoid

/-! ## 1. The simplex represented by a node -/

/-- The `k`-simplex of `mbarSd` represented by the pair `(c, s)`: a copy bit and a flag of `Q̄`. -/
def nodeSimplex (c : ZMod 2) {k : ℕ} (s : Simplex QbarCW.Cell k) : Fin (mbarSd.card k) :=
  (mbarEquiv k).symm (Quotient.mk (flagSetoid k) (c, s))

theorem carCx_nodeSimplex (c : ZMod 2) {k : ℕ} (s : Simplex QbarCW.Cell k) :
    carCx (nodeSimplex c s) = carQ (c, s) := by
  show carQq ((mbarEquiv k) ((mbarEquiv k).symm (Quotient.mk (flagSetoid k) (c, s)))) = carQ (c, s)
  rw [Equiv.apply_symm_apply]
  rfl

theorem liftCx_nodeSimplex (c : ZMod 2) {k : ℕ} (s : Simplex QbarCW.Cell k) :
    liftCx (nodeSimplex c s) = liftQ (c, s) := by
  show liftQq ((mbarEquiv k) ((mbarEquiv k).symm (Quotient.mk (flagSetoid k) (c, s)))) = liftQ (c, s)
  rw [Equiv.apply_symm_apply]
  rfl

/-- The face maps of `mbarSd` on the simplices represented by nodes. -/
theorem nodeSimplex_face (c : ZMod 2) {k : ℕ} (s : Simplex QbarCW.Cell (k + 1)) (i : Fin (k + 2)) :
    mbarSd.face (nodeSimplex c s) i = nodeSimplex c (Simplex.face i s) := by
  show (mbarEquiv k).symm (mbarFaceQ flagRel_face i (mbarEquiv (k + 1) (nodeSimplex c s)))
      = (mbarEquiv k).symm (Quotient.mk (flagSetoid k) (c, Simplex.face i s))
  rw [show mbarEquiv (k + 1) (nodeSimplex c s) = Quotient.mk (flagSetoid (k + 1)) (c, s) from
    Equiv.apply_symm_apply _ _]
  rfl

/-! ## 2. The push -/

/-- The linear push of a chain of the order complex of `Q̄` to the chains of `mbarSd` along the
node `(c, ·)`. -/
noncomputable def pushNode (c : ZMod 2) (k : ℕ) :
    chainMod QbarCW.Cell k →ₗ[ℤ] (Fin (mbarSd.card k) →₀ ℤ) :=
  Finsupp.linearCombination ℤ fun s => Finsupp.single (nodeSimplex c s) 1

theorem pushNode_single (c : ZMod 2) (k : ℕ) (s : Simplex QbarCW.Cell k) :
    pushNode c k (Finsupp.single s 1) = Finsupp.single (nodeSimplex c s) 1 := by
  simp only [pushNode, Finsupp.linearCombination_single, one_smul]

theorem pushNode_apply (c : ZMod 2) (k : ℕ) (z : chainMod QbarCW.Cell k) :
    pushNode c k z = ∑ s ∈ z.support, z s • Finsupp.single (nodeSimplex c s) 1 := by
  rw [pushNode, Finsupp.linearCombination_apply]
  rfl

/-! ## 3. The support of the subdivision chain of a cell -/

/-- **Every simplex of the subdivision chain of a cell ends at that cell.** -/
theorem subdivCell_apply_last (P : PolyCW) (n : ℕ) (e : {e : P.Cell // P.dim e = n}) :
    ∀ σ ∈ (PolyCW.subdivCell P n e).support, σ (Fin.last n) = e.1 := by
  induction n with
  | zero =>
      intro σ hσ
      rw [PolyCW.subdivCell_zero] at hσ
      have h : σ = Simplex.vertex e.1 := by
        rw [Finsupp.support_single _ (one_ne_zero : (1 : ℤ) ≠ 0)] at hσ
        exact Finset.mem_singleton.mp hσ
      rw [h, Simplex.vertex_apply]
  | succ n ih =>
      intro σ hσ
      rw [PolyCW.subdivCell_succ_eq] at hσ
      have hσ₁ := Finsupp.support_smul hσ
      obtain ⟨τ, _hτ, hτe, hσeq⟩ := PolyCW.coneLM_mem_support hσ₁
      rw [hσeq, Simplex.snoc_apply_last]

/-- The support of the subdivision chain of a cell is contained in the simplices ending at it. -/
theorem subdivCell_support_subset (P : PolyCW) (n : ℕ) (e : {e : P.Cell // P.dim e = n}) :
    (PolyCW.subdivCell P n e).support ⊆
      (Finset.univ.filter (fun σ : Simplex P.Cell n => σ (Fin.last n) = e.1)) := by
  intro σ hσ
  rw [Finset.mem_filter]
  exact ⟨Finset.mem_univ _, subdivCell_apply_last P n e σ hσ⟩

end

end Work.MbarHomology.Mbar
