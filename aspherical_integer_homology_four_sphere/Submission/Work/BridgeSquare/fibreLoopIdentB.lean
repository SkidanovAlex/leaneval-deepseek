/-
# `fibreLoopIdentB`: the `κ_{v,3}` fibre identity

Target: for every cusp `v`, the *singular* `1`-chain of the `κ_{v,3}`-longitude of the `v`-th
subtorus (`singB v`, the image of the `b`-loop of the `T²` `Δ`-model under the section `Fn v`) differs
from `±` the *cellular* fibre loop `PsiM (fibreLoopVec v 1)` by a boundary of a `2`-chain of `M̄`.

## The proof

* `singB v` is, up to a boundary, the sum of the `fibreLen v 1` unit cube edges of the corner line
  of the longitude (`singB_eq_pieces`, in `BridgeSquare/fibreSteps.lean`).
* Each unit cube edge of the corner line agrees, up to a boundary, with `± edgeSign · Ψ_M` of the
  matching cellular `1`-cell (`piece_eq_psi`, in `BridgeSquare/piece_eq_psi.lean`), the matching
  being the reversal of the edge indices and the global sign being `±1`.
* The cellular `Ψ_M`-image of the fibre loop expands in the basis of those unit cells with the
  coefficients `edgeSign` (`fibreLoop_expandB` below).

Summing the second identity over the edges and reindexing by the reversal identifies the sum of the
chart edges with `s • Ψ_M (fibreLoopVec v 1)` up to a boundary, and combining with the first
gives the theorem.
-/
import Mathlib
import Submission.Work.BridgeSquare.FibreData
import Submission.Work.BridgeSquare.subtorusBoundaries_of_fibreIdent
import Submission.Work.BridgeSquare.PsiM_truncCell_mem_range
import Submission.Work.BridgeSquare.kleinPt_corner
import Submission.Work.BridgeSquare.Fn_apply
import Submission.Work.BridgeSquare.affineChain
import Submission.Work.BridgeSquare.ChartAlgA
import Submission.Work.BridgeSquare.prism_c1
import Submission.Work.BridgeSquare.fibreSteps
import Submission.Work.BridgeSquare.piece_eq_psi

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped Topology Simplicial
open Convexity

namespace Work.BridgeSquare

noncomputable section

open Work.HomologyIso.Gen (mbarDim)

/-! ## §1  The expansion of the cellular fibre loop in the unit-edge basis -/

/-- The basis vector of the `k`-th unit edge cell of the `κ_{v,3}`-fibre loop, as an element of the
cellular chain group `C_1 = ↑(Gen.mbarCx.toChainComplex.X 1)`.

Written through an explicit `def` (as `evecA` in the `A`-case) so that the `mbarDim`-indexed type
of the chain complex, which is only definitionally equal to `Fin 168 → ℤ`, does not have to be seen
through by type class inference. -/
def evecB (v : Fin 5) (k : Fin (fibreLen v 1)) :
    ↥((Work.HomologyIso.Gen.mbarCx.toChainComplex).X 1) :=
  Pi.single (edgeCell v 1 (eIdx v k)) (1 : ℤ)

/-- **The expansion of the cellular fibre loop** in the basis of the unit cells. -/
theorem fibreLoop_expandB_point (v : Fin 5) (i : Fin 168) :
    fibreLoopVec v 1 i
      = (∑ k : Fin (fibreLen v 1), edgeSign v 1 (eIdx v k) •
          (Pi.single (edgeCell v 1 (eIdx v k)) (1 : ℤ) : Fin (mbarDim 1) → ℤ)) i := by
  fin_cases v <;> fin_cases i <;> decide

theorem fibreLoop_expandB (v : Fin 5) :
    fibreLoopVec v 1 = ∑ k : Fin (fibreLen v 1), edgeSign v 1 (eIdx v k) • evecB v k := by
  funext i
  exact fibreLoop_expandB_point v i

/-- **Linearity**: the `Ψ_M`-image of the cellular fibre loop expands in the basis of the images of
the unit cells with the same coefficients. -/
theorem PsiM_f_fibreLoopB (v : Fin 5) :
    (PsiM.f 1) (fibreLoopVec v 1)
      = ∑ k : Fin (fibreLen v 1), edgeSign v 1 (eIdx v k) • (PsiM.f 1) (evecB v k) := by
  calc (PsiM.f 1) (fibreLoopVec v 1)
      = (PsiM.f 1) (∑ k : Fin (fibreLen v 1), edgeSign v 1 (eIdx v k) • evecB v k) :=
        congrArg (PsiM.f 1) (fibreLoop_expandB v)
    _ = ∑ k : Fin (fibreLen v 1), (PsiM.f 1) (edgeSign v 1 (eIdx v k) • evecB v k) :=
        map_sum _ _ _
    _ = ∑ k : Fin (fibreLen v 1), edgeSign v 1 (eIdx v k) • (PsiM.f 1) (evecB v k) :=
        Finset.sum_congr rfl fun k _ => map_zsmul _ _ _

/-! ## §2  Summing the per-edge identities over the corner line -/

/-- **The sum of the unit cube edges of the corner line is `± Ψ_M` of the fibre loop, up to a
boundary.**  This is `piece_eq_psi` summed over the edges and reindexed by the reversal `τ`. -/
theorem pieces_eq_smul_psi (v : Fin 5) :
    ∃ (s : ℤ) (W : ↥((singCxFun.obj cMtop).X 2)),
      (s = 1 ∨ s = -1) ∧
      (∑ i : Fin (fibreLen v 1), c1 v (Xv v (i : ℕ)) (Xv v ((i : ℕ) + 1)))
        = s • (PsiM.f 1) (fibreLoopVec v 1) + (singCxFun.obj cMtop).d 2 1 W := by
  obtain ⟨τ, s, hs, hpiece⟩ := piece_eq_psi v
  choose Z hZ using hpiece
  refine ⟨s, ∑ i : Fin (fibreLen v 1), Z i, hs, ?_⟩
  have hterm : ∀ i : Fin (fibreLen v 1),
      c1 v (Xv v (i : ℕ)) (Xv v ((i : ℕ) + 1))
        = s • (edgeSign v 1 (eIdx v (τ i)) • (PsiM.f 1) (evecB v (τ i)))
          + (singCxFun.obj cMtop).d 2 1 (Z i) := by
    intro i
    simpa only [evecB] using hZ i
  calc (∑ i : Fin (fibreLen v 1), c1 v (Xv v (i : ℕ)) (Xv v ((i : ℕ) + 1)))
      = ∑ i : Fin (fibreLen v 1),
          (s • (edgeSign v 1 (eIdx v (τ i)) • (PsiM.f 1) (evecB v (τ i)))
            + (singCxFun.obj cMtop).d 2 1 (Z i)) :=
        Finset.sum_congr rfl fun i _ => hterm i
    _ = (∑ i : Fin (fibreLen v 1),
            s • (edgeSign v 1 (eIdx v (τ i)) • (PsiM.f 1) (evecB v (τ i))))
          + (singCxFun.obj cMtop).d 2 1 (∑ i : Fin (fibreLen v 1), Z i) := by
        rw [Finset.sum_add_distrib, map_sum]
    _ = s • (∑ i : Fin (fibreLen v 1),
            edgeSign v 1 (eIdx v (τ i)) • (PsiM.f 1) (evecB v (τ i)))
          + (singCxFun.obj cMtop).d 2 1 (∑ i : Fin (fibreLen v 1), Z i) := by
        rw [Finset.sum_zsmul]
    _ = s • (∑ k : Fin (fibreLen v 1),
            edgeSign v 1 (eIdx v k) • (PsiM.f 1) (evecB v k))
          + (singCxFun.obj cMtop).d 2 1 (∑ i : Fin (fibreLen v 1), Z i) := by
        rw [Equiv.sum_comp τ (fun k : Fin (fibreLen v 1) =>
          edgeSign v 1 (eIdx v k) • (PsiM.f 1) (evecB v k))]
    _ = s • (PsiM.f 1) (fibreLoopVec v 1)
          + (singCxFun.obj cMtop).d 2 1 (∑ i : Fin (fibreLen v 1), Z i) := by
        rw [PsiM_f_fibreLoopB v]

/-! ## §3  The fibre identity -/

theorem fibreLoopIdentB (v : Fin 5) :
    ∃ (s : ℤ) (y : ↑((Work.BridgeSquare.singCxFun.obj
        (TopCat.of Work.FoldInst.Mbar)).X 2)),
      (s = 1 ∨ s = -1) ∧
      ((Work.BridgeSquare.singCxFun.obj (TopCat.of Work.FoldInst.Mbar)).d 2 1) y
        = Work.BridgeSquare.singB v
          - s • (Work.BridgeSquare.PsiM.f 1) (Work.BridgeSquare.fibreLoopVec v 1) := by
  obtain ⟨s, W, hs, hW⟩ := pieces_eq_smul_psi v
  obtain ⟨Z, hZ⟩ := singB_eq_pieces v
  refine ⟨s, Z + W, hs, ?_⟩
  have hrange : (∑ i ∈ Finset.range (fibreLen v 1), c1 v (Xv v i) (Xv v (i + 1)))
      = ∑ i : Fin (fibreLen v 1), c1 v (Xv v (i : ℕ)) (Xv v ((i : ℕ) + 1)) :=
    (Fin.sum_univ_eq_sum_range (fun i => c1 v (Xv v i) (Xv v (i + 1)))
      (fibreLen v 1)).symm
  rw [map_add, hZ, hrange, hW]
  abel

end

end Work.BridgeSquare
