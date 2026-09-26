import Mathlib
import Submission.Work.Box.Shrink
import Submission.Work.SurgeryInvariance.All
import Submission.Work.Topology.SphereSlicing.All
import Submission.Work.BoxBubble.mustbeinessentialBox

/-!
# The double bubble of Pardon's shrinking step: vocabulary

This file sets up the geometric vocabulary of the *double bubble* which Pardon's shrinking step of
`Submission/Work/BoxShrink` applies to, and in which the reduction of the crux
(`Work.BoxShrink.CruxStatement`) to its local models is stated.  See
`Submission/Work/BoxShrink/Core/README.md` for the mathematical account.

The setting is fixed by the crux statement: a box `PBox s c σ` (`Submission.PBox`, an *open* box
with the self-similar side lengths `1, 2^{1/3}, 2^{2/3}` permuted by `σ`), cut by the plane
`{y | y (σ 2) = c (σ 2) + u}` perpendicular to the `σ 2`-direction.  Writing `u' = c (σ 2) + u`,

* `upperHalf c σ u`, `lowerHalf c σ u` are the two open half-spaces `{y (σ 2) > u'}` and
  `{y (σ 2) < u'}`; `cutPlane c σ u` is the plane `{y (σ 2) = u'}`;
* `sphereSet c σ s = {y | boxNorm c σ y = s}` is the boundary sphere `∂PBox s c σ` (the same set as
  `Work.Topology.SphereSlicing.BoxSphere`, whose `IsEmbeddedSphere` instance is available there);
* `cutDisc s c σ u = PBox s c σ ∩ cutPlane c σ u` is the flat disc of the plane inside the box,
  whose boundary circle lies on `∂PBox s c σ` — the disc `D` glued to the sphere `S = ∂PBox s c σ`
  to form Pardon's double bubble;
* `boxRegion P s c σ = P.carrier ∩ PBox s c σ` is the region of the torus surface inside the sphere
  (`= F ∩ int(S)`), `upperRegion`/`lowerRegion` are its intersections with the two open half-spaces,
  `sliceRegion` its intersection with the plane.

The key structural facts (all proved in `Submission.Work.BoxShrink.Core.Basic`): `boxRegion`,
`upperRegion`, `lowerRegion` are *open* in the surface (the box is open), `upperRegion` and
`lowerRegion` are disjoint, and `boxRegion` is the union of the two half-regions with the closed
slice `sliceRegion`.  In the double bubble the two half-regions are the traces `F ∩ int(Hᵢ)` of the
interiors of the two halves `Hᵢ` of the bubble, and `sliceRegion ⊆ F ∩ D` is the trace of the
slicing disc.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.BoxShrink.Core

noncomputable section

/-! ## The two half-spaces of the cutting plane -/

/-- The **upper half** of `ℝ³` bounded by the cutting plane
`{y | y (σ 2) = c (σ 2) + u}`. -/
def upperHalf (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ) : Set R3 :=
  {y : R3 | c (σ 2) + u < y (σ 2)}

/-- The **lower half** of `ℝ³` bounded by the cutting plane. -/
def lowerHalf (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ) : Set R3 :=
  {y : R3 | y (σ 2) < c (σ 2) + u}

/-- The **cutting plane** itself. -/
def cutPlane (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ) : Set R3 :=
  {y : R3 | y (σ 2) = c (σ 2) + u}

@[simp] theorem mem_upperHalf {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ} {y : R3} :
    y ∈ upperHalf c σ u ↔ c (σ 2) + u < y (σ 2) := Iff.rfl

@[simp] theorem mem_lowerHalf {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ} {y : R3} :
    y ∈ lowerHalf c σ u ↔ y (σ 2) < c (σ 2) + u := Iff.rfl

@[simp] theorem mem_cutPlane {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ} {y : R3} :
    y ∈ cutPlane c σ u ↔ y (σ 2) = c (σ 2) + u := Iff.rfl

theorem upperHalf_eq_lt {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ} :
    upperHalf c σ u = {y : R3 | c (σ 2) + u < y (σ 2)} := rfl

/-- The plane is the complement of the two open half-spaces. -/
theorem cutPlane_eq_compl_union (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ) :
    cutPlane c σ u = (upperHalf c σ u ∪ lowerHalf c σ u)ᶜ := by
  ext y
  simp only [mem_cutPlane, Set.mem_compl_iff, Set.mem_union, mem_upperHalf, mem_lowerHalf,
    not_or]
  constructor
  · intro h; exact ⟨by linarith, by linarith⟩
  · rintro ⟨h1, h2⟩; exact le_antisymm (le_of_not_gt h1) (le_of_not_gt h2)

/-! ## Pardon's box, its boundary sphere, and the slicing disc -/

/-- The **boundary sphere** of Pardon's box: the level set `{y | boxNorm c σ y = s}` of the box
norm.  This is `Work.Topology.SphereSlicing.BoxSphere`, recorded here under the naming convention of
this directory. -/
def sphereSet (c : R3) (σ : Equiv.Perm (Fin 3)) (s : ℝ) : Set R3 :=
  {y : R3 | Submission.boxNorm c σ y = s}

@[simp] theorem mem_sphereSet {c : R3} {σ : Equiv.Perm (Fin 3)} {s : ℝ} {y : R3} :
    y ∈ sphereSet c σ s ↔ Submission.boxNorm c σ y = s := Iff.rfl

theorem sphereSet_eq_BoxSphere (c : R3) (σ : Equiv.Perm (Fin 3)) (s : ℝ) :
    sphereSet c σ s = Work.Topology.SphereSlicing.BoxSphere s c σ := rfl

/-- The **slicing disc**: the flat disc cut out of the box by the plane.  Its boundary circle is
`∂(PBox s c σ) ∩ cutPlane = ∂D`, the curve along which the disc is glued to the sphere in Pardon's
double bubble. -/
def cutDisc (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ) : Set R3 :=
  Submission.PBox s c σ ∩ cutPlane c σ u

@[simp] theorem mem_cutDisc {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ} {y : R3} :
    y ∈ cutDisc s c σ u ↔ y ∈ Submission.PBox s c σ ∧ y (σ 2) = c (σ 2) + u := Iff.rfl

/-! ## The regions of the torus surface -/

/-- The **region of the surface inside the sphere** `∂PBox s c σ`, i.e. `F ∩ int(S)`.  (`PBox` is
an open box, so this is `P.carrier ∩ PBox s c σ`; it is open in `F`.) -/
def boxRegion (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) : Set R3 :=
  P.carrier ∩ Submission.PBox s c σ

/-- The **upper half-region**: the trace of the inside of the upper half of the double bubble. -/
def upperRegion (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u : ℝ) : Set R3 :=
  P.carrier ∩ Submission.PBox s c σ ∩ upperHalf c σ u

/-- The **lower half-region**. -/
def lowerRegion (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u : ℝ) : Set R3 :=
  P.carrier ∩ Submission.PBox s c σ ∩ lowerHalf c σ u

/-- The **slice**: the trace of the cutting plane inside the box, a closed subset of the region. -/
def sliceRegion (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u : ℝ) : Set R3 :=
  P.carrier ∩ Submission.PBox s c σ ∩ cutPlane c σ u

@[simp] theorem mem_boxRegion {P : Work.CoreTopology.ParamTorus} {s : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {y : R3} :
    y ∈ boxRegion P s c σ ↔ y ∈ P.carrier ∧ y ∈ Submission.PBox s c σ := Iff.rfl

@[simp] theorem mem_upperRegion {P : Work.CoreTopology.ParamTorus} {s : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {u : ℝ} {y : R3} :
    y ∈ upperRegion P s c σ u ↔
      y ∈ P.carrier ∧ y ∈ Submission.PBox s c σ ∧ c (σ 2) + u < y (σ 2) :=
  ⟨fun h => ⟨h.1.1, h.1.2, h.2⟩, fun h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩⟩

@[simp] theorem mem_lowerRegion {P : Work.CoreTopology.ParamTorus} {s : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {u : ℝ} {y : R3} :
    y ∈ lowerRegion P s c σ u ↔
      y ∈ P.carrier ∧ y ∈ Submission.PBox s c σ ∧ y (σ 2) < c (σ 2) + u :=
  ⟨fun h => ⟨h.1.1, h.1.2, h.2⟩, fun h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩⟩

@[simp] theorem mem_sliceRegion {P : Work.CoreTopology.ParamTorus} {s : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {u : ℝ} {y : R3} :
    y ∈ sliceRegion P s c σ u ↔
      y ∈ P.carrier ∧ y ∈ Submission.PBox s c σ ∧ y (σ 2) = c (σ 2) + u :=
  ⟨fun h => ⟨h.1.1, h.1.2, h.2⟩, fun h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩⟩

/-- The region inside the sphere is the union of the two half-regions and the slice. -/
theorem boxRegion_eq_union (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u : ℝ) :
    boxRegion P s c σ =
      (upperRegion P s c σ u ∪ lowerRegion P s c σ u) ∪ sliceRegion P s c σ u := by
  ext y
  simp only [mem_boxRegion, mem_upperRegion, mem_lowerRegion, mem_sliceRegion,
    Set.mem_union]
  constructor
  · rintro ⟨hyc, hyb⟩
    rcases lt_trichotomy (y (σ 2)) (c (σ 2) + u) with h | h | h
    · exact Or.inl (Or.inr ⟨hyc, hyb, h⟩)
    · exact Or.inr ⟨hyc, hyb, h⟩
    · exact Or.inl (Or.inl ⟨hyc, hyb, h⟩)
  · rintro (⟨⟨hyc, hyb, -⟩ | ⟨hyc, hyb, -⟩⟩ | ⟨hyc, hyb, -⟩) <;> exact ⟨hyc, hyb⟩

/-- The half-regions lie in the region. -/
theorem upperRegion_subset (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u : ℝ) : upperRegion P s c σ u ⊆ boxRegion P s c σ :=
  fun _ h => ⟨h.1.1, h.1.2⟩

theorem lowerRegion_subset (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u : ℝ) : lowerRegion P s c σ u ⊆ boxRegion P s c σ :=
  fun _ h => ⟨h.1.1, h.1.2⟩

theorem sliceRegion_subset (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u : ℝ) : sliceRegion P s c σ u ⊆ boxRegion P s c σ :=
  fun _ h => ⟨h.1.1, h.1.2⟩

/-- The slice is the trace of the flat disc on the surface. -/
theorem sliceRegion_eq_carrier_inter_cutDisc (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u : ℝ) :
    sliceRegion P s c σ u = P.carrier ∩ cutDisc s c σ u := by
  ext y
  simp only [mem_sliceRegion, mem_cutDisc, Set.mem_inter_iff]

/-- The region inside the sphere is contained in the *closed* box... it *is* the trace of the open
box, so every point of it is at box norm `< s`. -/
theorem boxNorm_lt_of_mem_boxRegion {P : Work.CoreTopology.ParamTorus} {s : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {y : R3} (hy : y ∈ boxRegion P s c σ) :
    Submission.boxNorm c σ y < s :=
  (Submission.mem_PBox_iff s c σ y).mp hy.2

end

end Work.BoxShrink.Core
