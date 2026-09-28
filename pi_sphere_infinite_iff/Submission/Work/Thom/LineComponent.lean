import Mathlib
import Submission.Work.Thom.LineSection
import Submission.Work.Thom.Indicator
import Submission.Work.Cohomology.Sd_comm

set_option synthInstance.maxHeartbeats 400000


local instance instInhabitedDeltaZeroLC : Inhabited ↑(Work.Cohomology.Delta 0) :=
  ⟨⟨Pi.single (0 : Fin (0 + 1)) 1, single_mem_stdSimplex ℝ (0 : Fin (0 + 1))⟩⟩


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

/-!
# The connected components of the zero complement of the trivial line bundle

For the trivial real line bundle `E = B × ℝ → B` with total space `X` and zero complement
`A = E∖0`, the two halves `A₊ = linePos` and `A₋ = lineNeg` are open, disjoint and cover `A`
(`Work.Thom.zeroComplement_eq_union`), so **every connected component of `A` is contained in one
of them**: a singular `1`-simplex of `A` has preconnected image, hence lies in `A₊` or in `A₋`.

This is the geometric input that makes the "difference of the two ends" class
`Work.Thom.indicatorClass` of `A` have the values `0` and `1` on the two constant sections
`σ₊`, `σ₋` of the trivial line bundle.

## Main results

* `Work.Thom.Apos`, `Work.Thom.Aneg` — the two halves of `A`, with `Work.Thom.isOpen_Apos`,
  `Work.Thom.isOpen_Aneg`, `Work.Thom.disjoint_Apos_Aneg`, `Work.Thom.Apos_union_Aneg`;
* `Work.Thom.range_sdMap_one_subset_or` — the image of a `1`-simplex lies on one side;
* `Work.Thom.pi0Rel_piece_iff` — an edge does not change the side;
* `Work.Thom.mem_lineNeg_of_pi0_mk_eq` and `Work.Thom.not_mem_lineNeg_of_pi0_mk_eq` — a point of
  the same connected component as a point of `A₊` is not in `A₋`;
* `Work.Thom.pi0_mk_eq_of_mem_both` — consequently a point of `A₋` cannot be in the component of a
  point of `A₊`.
-/

open CategoryTheory AlgebraicTopology Limits Simplicial

open scoped Topology Simplicial

open Classical

open Work.TangentClasses

namespace Work.Thom

noncomputable section

variable {B : Type} [TopologicalSpace B] {ι₀ : Type} [Inhabited ι₀]

/-- The two halves of the zero complement of the trivial line bundle, as subsets of the space
`E∖0`. -/
def Apos : Set ↥(zeroComplement (RealBundle.trivial B ℝ ι₀)) :=
  {a | ((a : ↥(zeroComplement (RealBundle.trivial B ℝ ι₀))) :
    (RealBundle.trivial B ℝ ι₀).TotalSpace) ∈ linePos}

/-- The negative half, as a subset of the space `E∖0`. -/
def Aneg : Set ↥(zeroComplement (RealBundle.trivial B ℝ ι₀)) :=
  {a | ((a : ↥(zeroComplement (RealBundle.trivial B ℝ ι₀))) :
    (RealBundle.trivial B ℝ ι₀).TotalSpace) ∈ lineNeg}

theorem isOpen_Apos : IsOpen (Apos (B := B) (ι₀ := ι₀)) :=
  isOpen_linePos.preimage continuous_subtype_val

theorem isOpen_Aneg : IsOpen (Aneg (B := B) (ι₀ := ι₀)) :=
  isOpen_lineNeg.preimage continuous_subtype_val

theorem disjoint_Apos_Aneg : Disjoint (Apos (B := B) (ι₀ := ι₀)) (Aneg (B := B) (ι₀ := ι₀)) := by
  refine Set.disjoint_left.mpr ?_
  intro a ha hb
  have ha' : ((a : ↥(zeroComplement (RealBundle.trivial B ℝ ι₀))) :
      (RealBundle.trivial B ℝ ι₀).TotalSpace) ∈ linePos := ha
  have hb' : ((a : ↥(zeroComplement (RealBundle.trivial B ℝ ι₀))) :
      (RealBundle.trivial B ℝ ι₀).TotalSpace) ∈ lineNeg := hb
  exact Set.disjoint_left.mp (disjoint_linePos_lineNeg (B := B) (ι₀ := ι₀)) ha' hb'

theorem Apos_union_Aneg :
    Apos (B := B) (ι₀ := ι₀) ∪ Aneg (B := B) (ι₀ := ι₀) = Set.univ := by
  ext a
  constructor
  · intro _
    exact Set.mem_univ a
  · intro _
    have ha : ((a : ↥(zeroComplement (RealBundle.trivial B ℝ ι₀))) :
        (RealBundle.trivial B ℝ ι₀).TotalSpace) ∈
          linePos ∪ lineNeg := by
      rw [← zeroComplement_eq_union]
      exact a.property
    rcases ha with h | h
    · exact Or.inl h
    · exact Or.inr h

/-- **The image of a singular `1`-simplex of `E∖0` lies on one side.** -/
theorem range_sdMap_one_subset_or (σ : Work.Cohomology.Simplex (TopCat.of ↥(zeroComplement (RealBundle.trivial B ℝ ι₀))) 1) :
    (∀ z, ((Work.Cohomology.sdMap 1 σ z : ↥(zeroComplement (RealBundle.trivial B ℝ ι₀))) :
        (RealBundle.trivial B ℝ ι₀).TotalSpace) ∈ linePos) ∨
      (∀ z, ((Work.Cohomology.sdMap 1 σ z : ↥(zeroComplement (RealBundle.trivial B ℝ ι₀))) :
        (RealBundle.trivial B ℝ ι₀).TotalSpace) ∈ lineNeg) := by
  haveI : PreconnectedSpace ↥(stdSimplex ℝ (Fin 2)) :=
    Subtype.preconnectedSpace (Convex.isPreconnected (convex_stdSimplex ℝ (Fin 2)))
  have hcont : Continuous (fun z : Work.Cohomology.Delta 1 => (Work.Cohomology.sdMap 1 σ) z) :=
    (TopCat.Hom.equivContinuousMap _ _ (Work.Cohomology.sdMap 1 σ)).continuous
  have hpre : IsPreconnected (Set.range (Work.Cohomology.sdMap 1 σ)) :=
    isPreconnected_range hcont
  have hcov : Set.range (Work.Cohomology.sdMap 1 σ) ⊆ Apos (B := B) (ι₀ := ι₀) ∪ Aneg (B := B) (ι₀ := ι₀) := by
    rw [Apos_union_Aneg]
    exact Set.subset_univ _
  rcases hpre.subset_or_subset isOpen_Apos isOpen_Aneg disjoint_Apos_Aneg hcov with h | h
  · left
    intro z
    exact h ⟨z, rfl⟩
  · right
    intro z
    exact h ⟨z, rfl⟩

/-- The `0`-simplex associated with a point. -/
theorem toSSetObj₀Equiv_eq_sdMap (σ : (TopCat.toSSet.obj (TopCat.of ↥(zeroComplement (RealBundle.trivial B ℝ ι₀)))) _⦋0⦌) :
    TopCat.toSSetObj₀Equiv σ = (Work.Cohomology.sdMap 0 σ) default := by
  first
    | (rw [TopCat.toSSetObj₀Equiv_apply]; rfl)
    | (rw [TopCat.toSSetObj₀Equiv_eq_T _ default]; rfl)

/-- **The sides of the faces of a `1`-simplex**: the point of a face of a singular `1`-simplex of
`E∖0` lies in the half in which the image of the simplex lies. -/
theorem face_piece_iff (σ : Work.Cohomology.Simplex (TopCat.of ↥(zeroComplement (RealBundle.trivial B ℝ ι₀))) 1)
    (i j : Fin 2) :
    (((TopCat.toSSetObj₀Equiv ((TopCat.toSSet.obj
        (TopCat.of ↥(zeroComplement (RealBundle.trivial B ℝ ι₀)))).δ i σ) :
      ↥(zeroComplement (RealBundle.trivial B ℝ ι₀))) :
        (RealBundle.trivial B ℝ ι₀).TotalSpace) ∈ lineNeg ↔
      ((TopCat.toSSetObj₀Equiv ((TopCat.toSSet.obj
        (TopCat.of ↥(zeroComplement (RealBundle.trivial B ℝ ι₀)))).δ j σ) :
      ↥(zeroComplement (RealBundle.trivial B ℝ ι₀))) :
        (RealBundle.trivial B ℝ ι₀).TotalSpace) ∈ lineNeg) := by
  rcases range_sdMap_one_subset_or (B := B) (ι₀ := ι₀) σ with hpos | hneg
  · have hmem : ∀ k : Fin 2,
        ((TopCat.toSSetObj₀Equiv ((TopCat.toSSet.obj
          (TopCat.of ↥(zeroComplement (RealBundle.trivial B ℝ ι₀)))).δ k σ) :
        ↥(zeroComplement (RealBundle.trivial B ℝ ι₀))) :
          (RealBundle.trivial B ℝ ι₀).TotalSpace) ∈ linePos := by
      intro k
      rw [toSSetObj₀Equiv_eq_sdMap,
        ← Work.Cohomology.faceMap_comp_sdMap
          (TopCat.of ↥(zeroComplement (RealBundle.trivial B ℝ ι₀))) 0 σ k]
      exact hpos _
    constructor <;> intro hcon
    · exact absurd (hmem i) (fun hp => Set.disjoint_left.mp
        (disjoint_linePos_lineNeg (B := B) (ι₀ := ι₀)) hp hcon)
    · exact absurd (hmem j) (fun hp => Set.disjoint_left.mp
        (disjoint_linePos_lineNeg (B := B) (ι₀ := ι₀)) hp hcon)
  · have hmem : ∀ k : Fin 2,
        ((TopCat.toSSetObj₀Equiv ((TopCat.toSSet.obj
          (TopCat.of ↥(zeroComplement (RealBundle.trivial B ℝ ι₀)))).δ k σ) :
        ↥(zeroComplement (RealBundle.trivial B ℝ ι₀))) :
          (RealBundle.trivial B ℝ ι₀).TotalSpace) ∈ lineNeg := by
      intro k
      rw [toSSetObj₀Equiv_eq_sdMap,
        ← Work.Cohomology.faceMap_comp_sdMap
          (TopCat.of ↥(zeroComplement (RealBundle.trivial B ℝ ι₀))) 0 σ k]
      exact hneg _
    exact ⟨fun _ => hmem j, fun _ => hmem i⟩

/-- **An edge does not change the side**: the endpoints of a singular `1`-simplex of `E∖0` are
both in `A₊` or both in `A₋` (as points of `E∖0`). -/
theorem pi0Rel_piece_iff
    (x y : (TopCat.toSSet.obj (TopCat.of ↥(zeroComplement (RealBundle.trivial B ℝ ι₀)))) _⦋0⦌)
    (h : SSet.π₀Rel x y) :
    (((TopCat.toSSetObj₀Equiv x : ↥(zeroComplement (RealBundle.trivial B ℝ ι₀))) :
        (RealBundle.trivial B ℝ ι₀).TotalSpace) ∈ lineNeg ↔
      ((TopCat.toSSetObj₀Equiv y : ↥(zeroComplement (RealBundle.trivial B ℝ ι₀))) :
        (RealBundle.trivial B ℝ ι₀).TotalSpace) ∈ lineNeg) := by
  obtain ⟨e⟩ := h
  have hx : (TopCat.toSSet.obj (TopCat.of ↥(zeroComplement (RealBundle.trivial B ℝ ι₀)))).δ 1 e.edge = x :=
    e.src_eq
  have hy : (TopCat.toSSet.obj (TopCat.of ↥(zeroComplement (RealBundle.trivial B ℝ ι₀)))).δ 0 e.edge = y :=
    e.tgt_eq
  have h1 := face_piece_iff (B := B) (ι₀ := ι₀) e.edge 1 0
  rw [hx, hy] at h1
  exact h1

/-- The predicate "the point lies in `A₋`" is constant on the connected components of `E∖0`. -/
theorem iff_of_eqvGen
    {x y : (TopCat.toSSet.obj (TopCat.of ↥(zeroComplement (RealBundle.trivial B ℝ ι₀)))) _⦋0⦌}
    (h : Relation.EqvGen SSet.π₀Rel x y) :
    (((TopCat.toSSetObj₀Equiv x : ↥(zeroComplement (RealBundle.trivial B ℝ ι₀))) :
        (RealBundle.trivial B ℝ ι₀).TotalSpace) ∈ lineNeg ↔
      ((TopCat.toSSetObj₀Equiv y : ↥(zeroComplement (RealBundle.trivial B ℝ ι₀))) :
        (RealBundle.trivial B ℝ ι₀).TotalSpace) ∈ lineNeg) := by
  induction h with
  | rel a b hab => exact pi0Rel_piece_iff (B := B) (ι₀ := ι₀) a b hab
  | refl a => exact Iff.rfl
  | symm a b hab ih => exact ih.symm
  | trans a b c hab hbc ih₁ ih₂ => exact ih₁.trans ih₂

/-- **A point of the same connected component of `E∖0` as a point of `A₋` lies in `A₋`.** -/
theorem mem_lineNeg_of_pi0_mk_eq
    {x y : (TopCat.toSSet.obj (TopCat.of ↥(zeroComplement (RealBundle.trivial B ℝ ι₀)))) _⦋0⦌}
    (h : SSet.π₀.mk x = SSet.π₀.mk y)
    (hy : ((TopCat.toSSetObj₀Equiv y : ↥(zeroComplement (RealBundle.trivial B ℝ ι₀))) :
        (RealBundle.trivial B ℝ ι₀).TotalSpace) ∈ lineNeg) :
    ((TopCat.toSSetObj₀Equiv x : ↥(zeroComplement (RealBundle.trivial B ℝ ι₀))) :
        (RealBundle.trivial B ℝ ι₀).TotalSpace) ∈ lineNeg :=
  (iff_of_eqvGen (B := B) (ι₀ := ι₀) ((SSet.π₀.mk_eq_mk_iff x y).mp h)).mpr hy

/-- **A point of the same connected component of `E∖0` as a point of `A₊` is not in `A₋`.** -/
theorem not_mem_lineNeg_of_pi0_mk_eq_of_mem_linePos
    {x y : (TopCat.toSSet.obj (TopCat.of ↥(zeroComplement (RealBundle.trivial B ℝ ι₀)))) _⦋0⦌}
    (h : SSet.π₀.mk x = SSet.π₀.mk y)
    (hy : ((TopCat.toSSetObj₀Equiv y : ↥(zeroComplement (RealBundle.trivial B ℝ ι₀))) :
        (RealBundle.trivial B ℝ ι₀).TotalSpace) ∈ linePos) :
    ((TopCat.toSSetObj₀Equiv x : ↥(zeroComplement (RealBundle.trivial B ℝ ι₀))) :
        (RealBundle.trivial B ℝ ι₀).TotalSpace) ∉ lineNeg := by
  intro hx
  have h2 := (iff_of_eqvGen (B := B) (ι₀ := ι₀) ((SSet.π₀.mk_eq_mk_iff x y).mp h)).mp hx
  exact Set.disjoint_left.mp (disjoint_linePos_lineNeg (B := B) (ι₀ := ι₀)) hy h2

end

end Work.Thom
