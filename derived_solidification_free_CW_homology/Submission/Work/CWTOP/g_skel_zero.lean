import Mathlib
import Submission.Work.CWTOP.Closed
import Submission.Work.CWTOP.Pieces
import Submission.Work.CWTOP.isClosed_centres
import Submission.Work.CWTOP.isClosed_of_finite_inter_closedCell

/-!
# The `0`-skeleton of a Hausdorff CW complex lies in every `CWClosed` class

For a CW complex `C` in a Hausdorff space `X`, the `0`-skeleton `skel C 0` is the set of the
centres of the `0`-cells.  We show that it is a *closed discrete* subset of `X`: every subset of
`skel C 0` is closed in `X`.  Consequently `skel C 0` is a discrete space, and since it is the
disjoint union of the `0`-cells (each of which is a single point), it is homeomorphic to the
`σ`-type `Σ j : cell C 0, PUnit`.

The closure axioms `CWClosed` contain the empty space and a point, and are stable under `σ`-types
and homotopy equivalences, so `G (skel C 0)` follows for every `CWClosed` class `G`.

The mathematical input is that the boundary of a higher dimensional cell meets the `0`-skeleton in
finitely many points (closure finiteness); this is the only place where the CW structure is used,
via `CWComplex.cellFrontier_subset_finite_openCell` and
`RelCWComplex.skeleton_inter_closedCell_eq_skeleton_inter_cellFrontier`.
-/

open Set Topology

namespace Work.CWTOP

set_option linter.unusedSectionVars false

variable {X : Type} [TopologicalSpace X] [T2Space X] {C : Set X} [Topology.CWComplex C]

/-! ## §1 The `0`-skeleton is a closed discrete set of points -/

/-- The centre of a `0`-cell, written in the standard normal form of the model disk `𝔻 0`. -/
lemma cellCentre_zero_eq_map (j : RelCWComplex.cell C 0) :
    cellCentre C 0 j = RelCWComplex.map 0 j ![] := by
  have h := RelCWComplex.map_zero_mem_openCell (C := C) 0 j
  rw [RelCWComplex.openCell_zero_eq_singleton] at h
  exact h

/-- The open cell containing a point of the `0`-skeleton has dimension `0`. -/
lemma eq_zero_of_mem_skel_zero_of_mem_openCell {x : X} (hx : x ∈ skel C 0)
    {m : ℕ} {j : RelCWComplex.cell C m} (hxm : x ∈ RelCWComplex.openCell m j) : m = 0 := by
  rw [skel, SetLike.mem_coe, CWComplex.mem_skeleton_iff] at hx
  obtain ⟨m0, hm0, j0, hj0⟩ := hx
  have hm0' : m0 ≤ 0 := ENat.natCast_le_natCast.mp hm0
  have hm0'' : m0 = 0 := Nat.eq_zero_of_le_zero hm0'
  subst hm0''
  have hsig : (⟨m, j⟩ : Σ l, RelCWComplex.cell C l) = ⟨0, j0⟩ :=
    RelCWComplex.eq_of_not_disjoint_openCell (not_disjoint_iff.mpr ⟨x, hxm, hj0⟩)
  exact (Sigma.mk.inj hsig).1

/-- The trace of the `0`-skeleton on the boundary of a cell is contained in the union of the
finitely many `0`-cells listed by the closure finiteness of that cell. -/
lemma skel_zero_inter_cellFrontier_subset (n : ℕ) (j : RelCWComplex.cell C n)
    (I : Π m, Finset (RelCWComplex.cell C m))
    (hI : RelCWComplex.cellFrontier n j ⊆ ⋃ m, ⋃ (_ : m < n), ⋃ j' ∈ I m, RelCWComplex.openCell m j') :
    skel C 0 ∩ RelCWComplex.cellFrontier n j ⊆ ⋃ j' ∈ I 0, RelCWComplex.openCell 0 j' := by
  intro x hx
  obtain ⟨hx0, hxf⟩ := hx
  have hxf' := hI hxf
  simp only [mem_iUnion] at hxf'
  obtain ⟨m, _hm, j', hj', hxj'⟩ := hxf'
  have hm0 : m = 0 := eq_zero_of_mem_skel_zero_of_mem_openCell hx0 hxj'
  subst hm0
  exact mem_iUnion₂.mpr ⟨j', hj', hxj'⟩

/-- The `0`-skeleton meets every closed cell in a finite set.  This is closure finiteness: for a
cell of positive dimension the `0`-skeleton meets its boundary in finitely many points, and on a
`0`-cell the intersection is a single point. -/
theorem finite_skel_zero_inter_closedCell (n : ℕ) (j : RelCWComplex.cell C n) :
    (skel C 0 ∩ RelCWComplex.closedCell n j).Finite := by
  rcases n with _ | n
  · rw [RelCWComplex.closedCell_zero_eq_singleton]
    exact (finite_singleton _).subset inter_subset_right
  · rw [RelCWComplex.skeleton_inter_closedCell_eq_skeleton_inter_cellFrontier (C := C) (by norm_num)]
    obtain ⟨I, hI⟩ := CWComplex.cellFrontier_subset_finite_openCell (n + 1) j
    refine (Finite.biUnion ((I 0).finite_toSet) ?_).subset
      (skel_zero_inter_cellFrontier_subset (n + 1) j I hI)
    intro j' _
    rw [RelCWComplex.openCell_zero_eq_singleton]
    exact finite_singleton _

/-- Every subset of the `0`-skeleton of a Hausdorff CW complex is closed in the ambient space. -/
theorem isClosed_of_subset_skel_zero {S : Set X} (hS : S ⊆ skel C 0) : IsClosed S := by
  refine isClosed_of_finite_inter_closedCell (C := C) (S := S) (hSC := hS.trans ?_) (hfin := ?_)
  · exact RelCWComplex.Subcomplex.subset_complex (RelCWComplex.skeleton C (0 : ℕ))
  · intro n j
    exact (finite_skel_zero_inter_closedCell n j).subset (Set.inter_subset_inter hS subset_rfl)

/-- Every subset of the `0`-skeleton is open in the subspace topology. -/
lemma isOpen_skel_zero_subset (V : Set (skel C 0)) : IsOpen V := by
  have hVc : IsClosed (Subtype.val '' Vᶜ : Set X) :=
    isClosed_of_subset_skel_zero (by rintro x ⟨y, _, rfl⟩; exact y.2)
  refine isOpen_induced_iff.mpr ⟨(Subtype.val '' Vᶜ : Set X)ᶜ, hVc.isOpen_compl, ?_⟩
  ext y
  simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_image]
  constructor
  · intro h
    by_contra hyV
    exact h ⟨y, hyV, rfl⟩
  · rintro hV ⟨z, hz, hzy⟩
    exact hz (by rwa [Subtype.ext hzy])

/-- The `0`-skeleton of a Hausdorff CW complex is a discrete topological space. -/
instance instDiscreteTopologySkelZero : DiscreteTopology (skel C 0) :=
  discreteTopology_iff_forall_isOpen.mpr isOpen_skel_zero_subset

/-! ## §2 The `0`-skeleton as a disjoint union of points -/

/-- The centre of a `0`-cell lies in the `0`-skeleton. -/
lemma cellCentre_mem_skel_zero (j : RelCWComplex.cell C 0) : cellCentre C 0 j ∈ skel C 0 :=
  RelCWComplex.openCell_subset_skeleton 0 j (cellCentre_mem_openCell 0 j)

/-- Distinct `0`-cells have distinct centres. -/
lemma cellCentre_zero_injective : Function.Injective (cellCentre (C := C) 0) := by
  intro i j h
  have h' : RelCWComplex.map 0 i ![] = RelCWComplex.map 0 j ![] := by
    rw [← cellCentre_zero_eq_map i, ← cellCentre_zero_eq_map j]
    exact h
  exact RelCWComplex.injective_map_zero C h'

/-- Every point of the `0`-skeleton is the centre of a (unique) `0`-cell. -/
lemma exists_cellCentre_eq_of_mem_skel_zero {x : X} (hx : x ∈ skel C 0) :
    ∃ j : RelCWComplex.cell C 0, cellCentre C 0 j = x := by
  have hx' := hx
  rw [skel, SetLike.mem_coe, CWComplex.mem_skeleton_iff] at hx
  obtain ⟨m, _hm, j, hj⟩ := hx
  have hm0 : m = 0 := eq_zero_of_mem_skel_zero_of_mem_openCell hx' hj
  subst hm0
  refine ⟨j, ?_⟩
  rw [RelCWComplex.openCell_zero_eq_singleton] at hj
  rw [cellCentre_zero_eq_map]
  exact hj.symm

/-- The `0`-cell of a point of the `0`-skeleton. -/
noncomputable def skelZeroCell (y : skel C 0) : RelCWComplex.cell C 0 :=
  Classical.choose (exists_cellCentre_eq_of_mem_skel_zero y.2)

lemma skelZeroCell_spec (y : skel C 0) : cellCentre C 0 (skelZeroCell y) = y.1 :=
  Classical.choose_spec (exists_cellCentre_eq_of_mem_skel_zero y.2)

/-- The `0`-skeleton is the disjoint union of its `0`-cells, i.e. of a family of points. -/
noncomputable def skelZeroEquiv : (Σ _ : RelCWComplex.cell C 0, PUnit) ≃ skel C 0 where
  toFun := fun s => ⟨cellCentre C 0 s.1, cellCentre_mem_skel_zero s.1⟩
  invFun := fun y => ⟨skelZeroCell y, PUnit.unit⟩
  left_inv := by
    rintro ⟨j, u⟩
    obtain rfl : u = PUnit.unit := Subsingleton.elim u PUnit.unit
    refine Sigma.ext (cellCentre_zero_injective ?_) HEq.rfl
    rw [skelZeroCell_spec]
  right_inv := fun y => Subtype.ext (skelZeroCell_spec y)

/-- The `0`-skeleton of a Hausdorff CW complex is homeomorphic to a disjoint union of points. -/
noncomputable def skelZeroHomeo : (Σ _ : RelCWComplex.cell C 0, PUnit) ≃ₜ skel C 0 :=
  { skelZeroEquiv with
    continuous_toFun := continuous_of_discreteTopology
    continuous_invFun := continuous_of_discreteTopology }

/-! ## §3 The main theorem -/

/-- **The `0`-skeleton.** The `0`-skeleton of a Hausdorff CW complex lies in every class of
spaces satisfying the closure axioms `CWClosed`. -/
theorem g_skel_zero {X : Type} [TopologicalSpace X] [T2Space X] {C : Set X}
    [Topology.CWComplex C] (G : TopCat.{0} → Prop) (hG : Submission.Blueprint.CWClosed G) :
    G (TopCat.of (Work.CWTOP.skel C 0)) := by
  have hsigma : G (TopCat.of (Σ _ : RelCWComplex.cell C 0, PUnit)) :=
    hG.sigma (RelCWComplex.cell C 0) (fun _ => TopCat.of PUnit) (fun _ => hG.point)
  exact hG.of_homotopyEquiv (TopCat.of (skel C 0))
    (TopCat.of (Σ _ : RelCWComplex.cell C 0, PUnit)) (skelZeroHomeo.symm.toHomotopyEquiv) hsigma

end Work.CWTOP
