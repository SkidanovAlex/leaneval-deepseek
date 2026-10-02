import Mathlib
import Submission.Work.Thom.Basic
import Submission.Work.Tubular.BundleDisc

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option linter.unusedVariables false

/-!
# Pieces of the sphere bundle of a Euclidean real bundle

This is the definition layer of the argument that the sphere bundle `S(Z)` of a Euclidean real
bundle `Z` over a compact charted base of dimension `8` has no homology above degree `dim + rank`.

* `Work.SphHomology.ModelSph F` — the unit sphere of the model fibre, as a type;
* `Work.SphHomology.sphOver Z v` — the part of the sphere bundle of `Z` lying over `v ⊆ B`;
* `Work.SphHomology.SphPiece Z i` — the part of the sphere bundle lying over a trivialising set
  `Z.baseSet i`, on which the bundle is trivial.
-/

open scoped Topology
open Work.TangentClasses

namespace Work.SphHomology

noncomputable section

variable {B : Type*} [TopologicalSpace B] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {ι : Type*}

/-- The unit sphere of the model fibre `F`, as a type. -/
abbrev ModelSph (F : Type*) [NormedAddCommGroup F] : Type _ := ↥(Metric.sphere (0 : F) 1)

/-- The part of the sphere bundle of `Z` lying over a set `v ⊆ B`. -/
def sphOver (Z : RealBundle B F ι) (v : Set B) : Set (Work.Thom.SphSub Z) :=
  {p | Z.proj (p : Z.TotalSpace) ∈ v}

@[simp] theorem mem_sphOver {Z : RealBundle B F ι} {v : Set B} {p : Work.Thom.SphSub Z} :
    p ∈ sphOver Z v ↔ Z.proj (p : Z.TotalSpace) ∈ v := Iff.rfl

/-- The part of the sphere bundle of `Z` lying over a trivialising set `Z.baseSet i`. -/
abbrev SphPiece (Z : RealBundle B F ι) (i : ι) : Type _ :=
  ↥(sphOver Z (Z.baseSet i))

/-- The projection of the sphere bundle to the base is continuous. -/
theorem continuous_sphProj (Z : RealBundle B F ι) :
    Continuous (fun p : Work.Thom.SphSub Z => Z.proj (p : Z.TotalSpace)) :=
  Z.continuous_proj.comp continuous_subtype_val

/-- The part of the sphere bundle over an open set is open. -/
theorem isOpen_sphOver (Z : RealBundle B F ι) {v : Set B} (hv : IsOpen v) :
    IsOpen (sphOver Z v) :=
  hv.preimage (continuous_sphProj Z)

/-- The part of the sphere bundle over a closed set is closed. -/
theorem isClosed_sphOver (Z : RealBundle B F ι) {v : Set B} (hv : IsClosed v) :
    IsClosed (sphOver Z v) :=
  hv.preimage (continuous_sphProj Z)

/-- The part of the sphere bundle over a larger set is larger. -/
theorem sphOver_mono (Z : RealBundle B F ι) {v w : Set B} (h : v ⊆ w) :
    sphOver Z v ⊆ sphOver Z w :=
  fun _ hp => h hp

/-- The part of the sphere bundle over a trivialising set is open. -/
theorem isOpen_sphPiece (Z : RealBundle B F ι) (i : ι) : IsOpen (sphOver Z (Z.baseSet i)) :=
  isOpen_sphOver Z (Z.isOpen_baseSet i)

/-- Membership in the complement of the zero section, in terms of the fibrewise norm. -/
theorem mem_zeroComplement_iff_fibreNorm_ne_zero (Z : RealBundle B F ι) (p : Z.TotalSpace) :
    p ∈ Work.Thom.zeroComplement Z ↔ Work.Thom.fibreNorm Z p ≠ 0 := by
  rw [Work.Thom.mem_zeroComplement, Work.Thom.fibreNorm]
  exact norm_ne_zero_iff.symm

end

end Work.SphHomology
