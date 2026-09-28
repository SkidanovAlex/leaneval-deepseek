import Submission.Work.ThreeConnected.SurgerySpace

/-!
# The trace of a surgery: `W = M × ℝ ∪_φ (D^{k+1} × D^{l+1})`

This module builds the **trace** of a surgery on an embedded framed sphere, as a concrete quotient
space.  With `l + 1 = n - k`, the tube `S^k × D^{l+1} ⊆ M` and the attaching region of the
`(k+1)`-handle, the trace is the quotient

`W = (M × ℝ) ⊔ (D^{k+1} × D^{l+1}) / (φ (p, y), 1) ∼ (sphToDisk p, y)`   for `p ∈ S^k`, `y ∈ D^{l+1}`,

i.e. the cylinder on `M` with a `(k+1)`-handle glued to the top end along the tube (the
parametrisation of the tube being the trivialisation of the normal bundle).  Its boundary is
`M × {0}` on one side and, on the other,

`∂W ∖ (M × {0}) = (M ∖ S^k × D̊^{l+1}) ∪_{S^k × S^l} (D^{k+1} × S^l)`,

which is exactly the surgered space `Work.ThreeConnected.SurgerySpace` of
`Submission/Work/ThreeConnected/SurgerySpace.lean`.  Thus `W` is a bordism from `M` to the surgered
manifold `N`, and the two ends sit in `W` as *subspaces*

* `Work.ThreeConnected.traceιM : M → Trace φ hφ` (the level `0` of the cylinder),
* `Work.ThreeConnected.traceιN : SurgerySpace φ hφ → Trace φ hφ` (the surgered end),

which is what makes the two long exact sequences of the pairs `(W, M)` and `(W, N)` — and with them
the effect of the surgery on homology — statable: see
`Submission/Work/ThreeConnected/SurgeryHomology.lean`.

## Main definitions

* `Work.ThreeConnected.TracePieces`, `Work.ThreeConnected.traceNF`, `Work.ThreeConnected.Trace` — the
  trace and its normal-form presentation as the kernel of an explicit map (as for `SurgerySpace`);
* `Work.ThreeConnected.traceQ`, `Work.ThreeConnected.traceιM` — the quotient map and the `M`-end;
* `Work.ThreeConnected.traceOfSurgeryPiece` — the auxiliary map on the pieces of the surgered space.

The point-set properties of the trace (injectivity of the two ends, the identification of the two
pieces, compactness when `M` is compact and the cylinder is taken over `[0,1]`) are in the modules
`Submission/Work/ThreeConnected/Trace/`.
-/

set_option backward.isDefEq.respectTransparency false

open scoped Manifold Topology ContDiff
open Function
open Classical

namespace Work.ThreeConnected

open Work.Bordism Work.Surgery Work.SignatureBordism Work.Cohomology

noncomputable section

variable {k l : ℕ} {M : Type*} [TopologicalSpace M]

/-- The three pieces of the trace: the complement of the gluing set in the cylinder, the complement
of the attaching sphere in the handle, and the common attaching region `S^k × D^{l+1}`. -/
abbrev TracePieces (φ : Work.Surgery.Sph k × Work.Surgery.Disk l → M) : Type _ :=
  Sum (Sum {w : M × ℝ // w.2 ≠ 1 ∨ w.1 ∉ Set.range φ}
           {u : Work.Surgery.Disk k × Work.Surgery.Disk l //
             u.1 ∉ Work.Surgery.diskSphere k})
      (Work.Surgery.Sph k × Work.Surgery.Disk l)

/-- The normal-form map of the trace: a point of the cylinder at level `1` whose base point lies in
the tube is sent to the corresponding point of the attaching region of the handle, and a point of the
attaching region of the handle to the corresponding point of the tube; everything else is kept. -/
def traceNF (φ : Work.Surgery.Sph k × Work.Surgery.Disk l → M) (hφ : Function.Injective φ) :
    ((M × ℝ) ⊕ (Work.Surgery.Disk k × Work.Surgery.Disk l)) → TracePieces φ
  | Sum.inl w => if h : w.2 = 1 ∧ w.1 ∈ Set.range φ then
      Sum.inr (Classical.choose h.2)
    else Sum.inl (Sum.inl ⟨w, by tauto⟩)
  | Sum.inr u => if hu : u.1 ∈ Work.Surgery.diskSphere k then
      Sum.inr ((Work.Surgery.sphHomeoDiskSphere k).symm ⟨u.1, hu⟩, u.2)
    else Sum.inl (Sum.inr ⟨u, hu⟩)

/-- **The trace** `W = M × ℝ ∪_φ (D^{k+1} × D^{l+1})` of the surgery along a framed sphere: the
quotient of the cylinder on `M` and of the `(k+1)`-handle by the identification of the tube with the
attaching region. -/
abbrev Trace (φ : Work.Surgery.Sph k × Work.Surgery.Disk l → M) (hφ : Function.Injective φ) :
    Type _ :=
  Quotient (Setoid.ker (traceNF φ hφ))

/-- The quotient map of the trace. -/
def traceQ (φ : Work.Surgery.Sph k × Work.Surgery.Disk l → M) (hφ : Function.Injective φ) :
    ((M × ℝ) ⊕ (Work.Surgery.Disk k × Work.Surgery.Disk l)) → Trace φ hφ :=
  Quotient.mk''

/-- **The `M`-end of the trace**: the level `0` of the cylinder. -/
def traceιM (φ : Work.Surgery.Sph k × Work.Surgery.Disk l → M) (hφ : Function.Injective φ) :
    M → Trace φ hφ :=
  fun x => traceQ φ hφ (Sum.inl (x, 0))

/-- The map on the pieces of the surgered space which is to descend to the inclusion of the surgered
end: a point of the complement of the open tube goes to level `1` of the cylinder, a point of the
surgery region `D^{k+1} × S^l` to the corresponding point of the boundary of the handle. -/
def traceOfSurgeryPiece (φ : Work.Surgery.Sph k × Work.Surgery.Disk l → M)
    (hφ : Function.Injective φ) :
    (↥(TubeComplement φ) ⊕ (Work.Surgery.Disk k × Work.Surgery.Sph l)) → Trace φ hφ
  | Sum.inl x => traceQ φ hφ (Sum.inl (x.1, 1))
  | Sum.inr u => traceQ φ hφ (Sum.inr (u.1, Work.Surgery.sphToDisk l u.2))

end

end Work.ThreeConnected
