/-
# `Final/`: the Mayer–Vietoris cover of `M̂` and its long exact sequence

The open cover `M̂ = A ∪ B` of `Work.Space.Assembly` (`Aset_sup_Bset`), together with the
Mayer–Vietoris long exact sequence `Work.Final.coverMVLES` of that cover, in the indexing of
`Work.HomologyMV.MVLES`.  Its terms are, by definition,

* `(k,0) = H_k(A ∩ B)`, `(k,1) = H_k(A) ⊞ H_k(B)`, `(k,2) = H_k(C^{A,B})` for `k ≥ 0`
  (`Work.Final.mhatMVLES_H_zero/one/two`, `Work.Final.mhatMVLES_hX`), and the zero module for
  `k < 0`;
* the maps are the library Mayer–Vietoris maps `Work.Final.mvF`, `mvG` and the connecting map
  `mvD` transported along the canonical isomorphisms of the terms (the value lemmas
  `Work.Final.coverD_zero/one/two` and `coverD_zero_neg/one_neg/two_neg` in `Final/Cover.lean`
  state them explicitly, for an arbitrary open cover).

The only input is `Work.Final.MVExactDegreeZero`, the degree-`0` exactness, which is
`Work.Final.mvRightX_zero_surjective` (`Submission/Work/Final/mvRightX_zero_surjective.lean`) via
`Work.Final.mvExactDegreeZero_of_mvRightX`.
-/
import Submission.Work.Final.Cover

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 400000

open CategoryTheory AlgebraicTopology
open scoped Topology

namespace Work.Final

noncomputable section

variable [rt : Work.Space.RTData]

/-- The first open set `A` of the cover of `M̂`, as a set. -/
abbrev mhatAset : Set rt.Mhat := (rt.core.Aset : Set rt.Mhat)

/-- The second open set `B` of the cover of `M̂`, as a set. -/
abbrev mhatBset : Set rt.Mhat := (rt.core.Bset : Set rt.Mhat)

theorem mhatAset_isOpen : IsOpen (mhatAset (rt := rt)) := rt.core.Aset.isOpen

theorem mhatBset_isOpen : IsOpen (mhatBset (rt := rt)) := rt.core.Bset.isOpen

/-- **`M̂ = A ∪ B`** — the two open sets cover `M̂` (`Work.Space.Assembly.Aset_sup_Bset`). -/
theorem mhatAset_union_mhatBset : mhatAset (rt := rt) ∪ mhatBset (rt := rt) = Set.univ := by
  have h := Work.Space.Assembly.Aset_sup_Bset rt.core
  simpa [mhatAset, mhatBset] using
    congrArg (fun (x : TopologicalSpace.Opens rt.Mhat) => (x : Set rt.Mhat)) h

/-- **The Mayer–Vietoris long exact sequence of the cover `M̂ = A ∪ B`.** -/
def mhatMVLES (hmv0 : MVExactDegreeZero (X := TopCat.of rt.Mhat) (mhatAset (rt := rt))
    (mhatBset (rt := rt))) : Work.HomologyMV.MVLES :=
  coverMVLES (X := TopCat.of rt.Mhat) (mhatAset (rt := rt)) (mhatBset (rt := rt))
    (mhatAset_isOpen (rt := rt)) (mhatBset_isOpen (rt := rt)) (mhatAset_union_mhatBset (rt := rt))
    hmv0

@[simp] theorem mhatMVLES_H_zero
    (hmv0 : MVExactDegreeZero (X := TopCat.of rt.Mhat) (mhatAset (rt := rt))
      (mhatBset (rt := rt))) (k : ℕ) :
    (mhatMVLES hmv0).H ((k : ℤ), 0) =
      Work.Cohomology.HInter (X := TopCat.of rt.Mhat) mhatAset mhatBset k := by
  rw [mhatMVLES]
  exact coverMVLES_H_zero (X := TopCat.of rt.Mhat) mhatAset mhatBset mhatAset_isOpen
    mhatBset_isOpen mhatAset_union_mhatBset hmv0 k

@[simp] theorem mhatMVLES_H_one
    (hmv0 : MVExactDegreeZero (X := TopCat.of rt.Mhat) (mhatAset (rt := rt))
      (mhatBset (rt := rt))) (k : ℕ) :
    (mhatMVLES hmv0).H ((k : ℤ), 1) =
      Work.Cohomology.HBiprod (X := TopCat.of rt.Mhat) mhatAset mhatBset k := by
  rw [mhatMVLES]
  exact coverMVLES_H_one (X := TopCat.of rt.Mhat) mhatAset mhatBset mhatAset_isOpen
    mhatBset_isOpen mhatAset_union_mhatBset hmv0 k

@[simp] theorem mhatMVLES_H_two
    (hmv0 : MVExactDegreeZero (X := TopCat.of rt.Mhat) (mhatAset (rt := rt))
      (mhatBset (rt := rt))) (k : ℕ) :
    (mhatMVLES hmv0).H ((k : ℤ), 2) =
      Work.Cohomology.HSmall (X := TopCat.of rt.Mhat) mhatAset mhatBset k := by
  rw [mhatMVLES]
  exact coverMVLES_H_two (X := TopCat.of rt.Mhat) mhatAset mhatBset mhatAset_isOpen
    mhatBset_isOpen mhatAset_union_mhatBset hmv0 k

/-- **The `(k,2)`-slot is the singular homology of `M̂`** — this is the field `hX` of
`Work.Final.FinalInputs`, with `L := mhatMVLES hmv0`. -/
def mhatMVLES_hX
    (hmv0 : MVExactDegreeZero (X := TopCat.of rt.Mhat) (mhatAset (rt := rt))
      (mhatBset (rt := rt))) (k : ℕ) :
    (mhatMVLES hmv0).H ((k : ℤ), 2) ≅ LeanEval.Topology.intHomology k (TopCat.of rt.Mhat) :=
  coverMVLES_hX (X := TopCat.of rt.Mhat) mhatAset mhatBset mhatAset_isOpen mhatBset_isOpen
    mhatAset_union_mhatBset hmv0 k

end

end Work.Final
