import Mathlib
import Submission.Work.ANALYTIC.qElemSetup

/-!
# `cBounded (qElem S x) = coordTimesDeltaAt ((ℕ∪∞) ⊗ S) (pullbackX S x) (fstNS S)`

`Work.ANALYTIC.qElem S x ∈ P((ℕ∪∞) ⊗ S)` is the finite ℤ-linear combination
`Σ_{j ∈ Icc (-N) N} j·[gAt ((ℕ∪∞)⊗S) (pullbackX S x) (fstNS S) j]` of `P_proj`-images of the
generators `[gAt … j]`, where `N = qBound S x` is the (canonically chosen) uniform bound of the
bounded family `x`.

This file proves that `cBounded` sends it to `coordTimesDeltaAt ((ℕ∪∞) ⊗ S) (pullbackX S x)
(fstNS S)`, i.e. `Work.ANALYTIC.QElemCBounded`, by *reproving* the key computation of
`Submission/Work/ANALYTIC/coordTimesDeltaAt_mem_range.lean` with the sum taken over the *fixed*
index range `Icc (-(qBound S x)) (qBound S x)` rather than over the range of a chosen bound
`N` (that file's witness is literally `qElem S x`, but its statement is only the existential
form, so the explicit-witness form is proved here as `cBounded_qSum`).

The proof is the same computation: `cBounded` corresponds under `freeHomEquiv` to `deltaElem ∈
∏^bnd ℤ(ℕ∪{∞})`, so `P_proj ≫ cBounded` sends the generator `[g]` to the element `E_g` whose
`m`-th component is `s ↦ [g s = m]`; hence the sum `Σ_j j·E_{gAt S x f j}` has `m`-th component
`Σ_j j·[gAt S x f j s = m]`, which is `x_m(s)·[f s = m]` because `gAt S x f j s = m` holds
exactly for `j = x_m(s)` when `f s = m` (and for no `j` otherwise), and `x_m(s) ∈ Icc (-N) N`.
-/

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed OnePoint
open _root_.LightCondensed _root_.LightCondensed.Solid
open Opposite

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Work.ANALYTIC

attribute [local instance] Classical.propDecidable

/-- **The explicit preimage of `coordTimesDeltaAt S x f` under `cBounded`.**  For any uniform
bound `N` of a bounded family `x ∈ ∏^bnd ℤ(S)` and any continuous `f : S ⟶ ℕ∪{∞}`, the element
`Σ_{j ∈ Icc (-N) N} j • (zmap (gAt S x f j) ≫ P_proj)` of `P(S)` is mapped by `cBounded` to
`coordTimesDeltaAt S x f` (whose `m`-th component is `s ↦ x_m(s)·[f s = m]`).

This is the general form of `Work.ANALYTIC.coordTimesDeltaAt_mem_range` with an *explicit*,
bound-independent witness: it is the statement that `qElem` (which uses `N := qBound S x`) is a
preimage of the shift data. -/
lemma cBounded_qSum (S : LightProfinite.{0})
    (x : ↥(boundedSeq.obj.obj (Opposite.op S))) (f : S ⟶ (ℕ∪{∞})) (N : ℤ)
    (hN : ∀ n s, |x.1 n s| ≤ N) :
    cBounded.hom.app (Opposite.op S)
        (freeHomEquiv S LightCondensed.P
          (∑ j ∈ Finset.Icc (-N) N,
            j • (Work.ATOM.zmap (gAt S x f j) ≫ LightCondensed.P_proj)))
      = coordTimesDeltaAt S x f := by
  have hnat := freeHomEquiv_naturality_target S (cBounded : LightCondensed.P ⟶ boundedSeq)
    (∑ j ∈ Finset.Icc (-N) N,
      j • (Work.ATOM.zmap (gAt S x f j) ≫ LightCondensed.P_proj))
  rw [← hnat]
  have hcomp : (∑ j ∈ Finset.Icc (-N) N,
        j • (Work.ATOM.zmap (gAt S x f j) ≫ LightCondensed.P_proj)) ≫ cBounded
      = ∑ j ∈ Finset.Icc (-N) N, j • (Work.ATOM.zmap (gAt S x f j) ≫
          (freeHomEquiv (ℕ∪{∞}) boundedSeq).symm deltaElem) := by
    rw [Preadditive.sum_comp]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    rw [Linear.smul_comp, Category.assoc, P_proj_cBounded]
  rw [hcomp, freeHomEquiv_mapSum]
  have hsum : (∑ j ∈ Finset.Icc (-N) N, freeHomEquiv S boundedSeq
        (j • (Work.ATOM.zmap (gAt S x f j) ≫
          (freeHomEquiv (ℕ∪{∞}) boundedSeq).symm deltaElem)))
      = (∑ j ∈ Finset.Icc (-N) N, j • gAtElem S x f j) := by
    refine Finset.sum_congr rfl (fun j hj => ?_)
    rw [freeHomEquiv_mapZsmul, freeHomEquiv_zmap_gAt]
  rw [hsum]
  exact sum_gAt_eq S x f N hN

/-- **`cBounded` sends `qElem S x` to the shift data of the tower**: instantiating
`cBounded_qSum` at the test object `(ℕ∪∞) ⊗ S`, the family `pullbackX S x` and the projection
`fstNS S`, with the canonical bound `qBound S x` (whose defining property is `qBound_spec`).
The witness of `cBounded_qSum` is by construction (`rfl`) the element `qElem S x`. -/
theorem qElem_cBounded : Work.ANALYTIC.QElemCBounded := by
  intro S x
  exact cBounded_qSum ((ℕ∪{∞}) ⊗ S) (pullbackX S x) (fstNS S) (qBound S x)
    (fun n t => qBound_spec S x n t)

end Work.ANALYTIC

end
