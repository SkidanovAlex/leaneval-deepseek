import Submission.Work.ThreeConnected.Sphere

set_option synthInstance.maxHeartbeats 400000

/-!
# The point-set surgery `M' = (M ∖ S^k × D̊^{n-k}) ∪ (D^{k+1} × S^{n-k-1})`

This module contains the **point-set construction of the surgered space** of item 1 of the brief: the
space obtained from a space `M` by deleting the interior of an embedded tube `S^k × D^{l+1}`
(`l + 1 = n - k`) and gluing in the surgery region `D^{k+1} × S^l` along the common boundary
`S^k × S^l`.

## The construction

The construction is the quotient of the disjoint union of the two pieces

* the complement `M ∖ φ(S^k × D̊^{l+1})` of the open tube, and
* the surgery region `D^{k+1} × S^l`,

by the identification of the boundary `S^k × S^l` of the two.  As in
`Submission/Work/Surgery/Handle.lean`, the quotient is presented as the kernel of a *normal-form map*

`Sum ↥(TubeComplement φ) (D^{k+1} × S^l) → Sum (Sum A B) (S^k × S^l)`

whose three target pieces are the complement of the closed tube, the complement of the attaching
sphere in the surgery region, and the common boundary `S^k × S^l`.

## What is here, and what is not

* `Work.ThreeConnected.TubeComplement`, `Work.ThreeConnected.TubeBoundary`,
  `Work.ThreeConnected.surgeryNF`, `Work.ThreeConnected.SurgerySpace` — the construction;
* `Submission/Work/ThreeConnected/SurgerySpace/surgery_identified.lean` —
  **the identification**: a point of the complement is identified with a point of the surgery region
  exactly when they are matched by the attaching homeomorphism of the tube boundary;
* `Submission/Work/ThreeConnected/SurgerySpace/surgerySpace_compactSpace.lean` — **the surgered space
  is compact** when `M` is compact and the open tube has open image in `M` (the
  tubular-neighbourhood condition, which is part of the data of a trivialised normal bundle);

What is *not* here: the smooth structure on `SurgerySpace` (that is the handle-attachment theorem
`Work.Surgery.SmoothAttach` of `Submission/Work/Surgery/Handle.lean`), the identification of
`SurgerySpace` with `Work.Surgery.AttachData.Handlebody` of the complement, and the computation of
its homology.  See `README.md`.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open scoped Manifold Topology ContDiff
open Function
open Classical

namespace Work.ThreeConnected

open Work.Bordism Work.Surgery Work.SignatureBordism Work.Cohomology

noncomputable section

variable {k l : ℕ} {M : Type*} [TopologicalSpace M]

/-- The open unit disk `D̊^{l+1} ⊆ D^{l+1}`. -/
def openDisk (l : ℕ) : Set (Work.Surgery.Disk l) :=
  {y | ‖((y : Work.Surgery.Disk l) : EuclideanSpace ℝ (Fin (l + 1)))‖ < 1}

/-- **The complement of the open tube** `φ(S^k × D̊^{l+1})` in `M`: the piece which survives the
surgery. -/
def TubeComplement (φ : Work.Surgery.Sph k × Work.Surgery.Disk l → M) : Set M :=
  {x | ∀ (p : Work.Surgery.Sph k) (y : Work.Surgery.Disk l), y ∈ openDisk l → φ (p, y) ≠ x}

/-- **The boundary tube** `φ(S^k × S^l) ⊆ M`: the common boundary of the two pieces of the surgery,
along which they are glued. -/
def TubeBoundary (φ : Work.Surgery.Sph k × Work.Surgery.Disk l → M) : Set M :=
  {x | ∃ (p : Work.Surgery.Sph k) (q : Work.Surgery.Sph l),
    φ (p, Work.Surgery.sphToDisk l q) = x}

/-- The three pieces of the surgered space: the complement of the closed tube, the complement of the
attaching sphere in the surgery region, and the common boundary `S^k × S^l`. -/
abbrev SurgeryPieces (φ : Work.Surgery.Sph k × Work.Surgery.Disk l → M) : Type _ :=
  Sum (Sum {x : M // x ∈ TubeComplement φ ∧ x ∉ TubeBoundary φ}
           {u : Work.Surgery.Disk k × Work.Surgery.Sph l // u.1 ∉ Work.Surgery.diskSphere k})
      (Work.Surgery.Sph k × Work.Surgery.Sph l)

/-- The normal-form map of the surgery: a point of the complement and a point of the surgery region
are mapped to the *same* piece exactly when they match, so that the kernel of this map is the
relation of the surgery. -/
def surgeryNF (φ : Work.Surgery.Sph k × Work.Surgery.Disk l → M) (hφ : Function.Injective φ) :
    (↥(TubeComplement φ) ⊕ (Work.Surgery.Disk k × Work.Surgery.Sph l)) → SurgeryPieces φ
  | Sum.inl x => if hx : (x : M) ∈ TubeBoundary φ then
      Sum.inr (Classical.choose hx, Classical.choose (Classical.choose_spec hx))
    else Sum.inl (Sum.inl ⟨x.1, x.2, hx⟩)
  | Sum.inr u => if hu : u.1 ∈ Work.Surgery.diskSphere k then
      Sum.inr ((Work.Surgery.sphHomeoDiskSphere k).symm ⟨u.1, hu⟩, u.2)
    else Sum.inl (Sum.inr ⟨u, hu⟩)

/-- **The surgered space** `M' = (M ∖ S^k × D̊^{l+1}) ∪ (D^{k+1} × S^l)`: the quotient of the
complement of the open tube and of the surgery region by the identification of their common boundary
`S^k × S^l`. -/
abbrev SurgerySpace (φ : Work.Surgery.Sph k × Work.Surgery.Disk l → M)
    (hφ : Function.Injective φ) : Type _ :=
  Quotient (Setoid.ker (surgeryNF φ hφ))

/-- The quotient map of the surgery. -/
def surgeryQ (φ : Work.Surgery.Sph k × Work.Surgery.Disk l → M) (hφ : Function.Injective φ) :
    (↥(TubeComplement φ) ⊕ (Work.Surgery.Disk k × Work.Surgery.Sph l)) → SurgerySpace φ hφ :=
  Quotient.mk''

theorem continuous_surgeryQ (φ : Work.Surgery.Sph k × Work.Surgery.Disk l → M)
    (hφ : Function.Injective φ) : Continuous (surgeryQ φ hφ) := by
  change Continuous (Quotient.mk'' (s₁ := Setoid.ker (surgeryNF φ hφ)))
  exact continuous_quotient_mk'

/-- The inclusion of the complement of the open tube into the surgered space. -/
def surgeryι (φ : Work.Surgery.Sph k × Work.Surgery.Disk l → M) (hφ : Function.Injective φ) :
    ↥(TubeComplement φ) → SurgerySpace φ hφ :=
  fun x => surgeryQ φ hφ (Sum.inl x)

/-- The inclusion of the surgery region `D^{k+1} × S^l` into the surgered space. -/
def surgeryj (φ : Work.Surgery.Sph k × Work.Surgery.Disk l → M) (hφ : Function.Injective φ) :
    Work.Surgery.Disk k × Work.Surgery.Sph l → SurgerySpace φ hφ :=
  fun u => surgeryQ φ hφ (Sum.inr u)

theorem continuous_surgeryι (φ : Work.Surgery.Sph k × Work.Surgery.Disk l → M)
    (hφ : Function.Injective φ) : Continuous (surgeryι φ hφ) :=
  (continuous_surgeryQ φ hφ).comp continuous_inl

theorem continuous_surgeryj (φ : Work.Surgery.Sph k × Work.Surgery.Disk l → M)
    (hφ : Function.Injective φ) : Continuous (surgeryj φ hφ) :=
  (continuous_surgeryQ φ hφ).comp continuous_inr

end

end Work.ThreeConnected
