/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib
import Submission.Work.CWTOP.Basic
import Submission.Work.CWTOP.isClosed_skel_diff_openCell
import Submission.Work.CWTOP.contractibleSpace_openCell
import Submission.Work.CWTOP.homotopyEquiv_sigma

/-!
# The union of the open top cells is homotopy equivalent to the set of top cells

This file proves `Work.CWTOP.homotopyEquiv_stepV`: for a Hausdorff CW complex `C` in `X` and
`n : ℕ`, the union `stepV C n` of the open `(n+1)`-cells is homotopy equivalent to the discrete
space `Σ j : cell C (n+1), PUnit` of `(n+1)`-cells.

The mathematical content is that `stepV C n` is the *disjoint union* of the open `(n+1)`-cells:
* the open cells of a fixed dimension are pairwise disjoint (`RelCWComplex.pairwiseDisjoint`), so a
  point of `stepV C n` determines its cell uniquely;
* each open `(n+1)`-cell is open in `stepV C n`. This is the only point where the weak topology of
  a CW complex is used: since `skel C (n+1) \ openCell (n+1) j` is closed in `X`
  (`Work.CWTOP.isClosed_skel_diff_openCell`), the open cell is open in `stepV C n` (compare
  `Work.CWTOP.isOpen_openCell_stepV`);
* each open cell is contractible (`Work.CWTOP.contractibleSpace_openCell`), hence homotopy
  equivalent to `PUnit`; homotopy equivalences of `ι`-indexed disjoint unions are computed
  fibre-wise (`Work.CWTOP.homotopyEquiv_sigma`).
-/

open CategoryTheory Topology Set Function Metric

noncomputable section

namespace Work.CWTOP

universe u

variable {X : Type} [TopologicalSpace X] [T2Space X] {C : Set X} [CWComplex C]

/-! ## §1 Uniqueness of the cell of a point -/

/-- Two open cells of the same dimension with a common point coincide. -/
lemma openCell_cell_eq {m : ℕ} {j j' : RelCWComplex.cell C m} {x : X}
    (h : x ∈ RelCWComplex.openCell m j) (h' : x ∈ RelCWComplex.openCell m j') : j = j' :=
  eq_of_heq (Sigma.mk.inj (eq_of_openCell_mem (C := C) h h')).2

/-! ## §2 Every open top cell is open in `stepV` -/

lemma stepV_subset_skel (n : ℕ) : stepV C n ⊆ skel C (n + 1) :=
  Set.iUnion_subset fun j => RelCWComplex.openCell_subset_skeleton (n + 1) j

/-- Each open `(n+1)`-cell is open in `stepV C n`. -/
lemma isOpen_openCell_stepV (n : ℕ) (j : RelCWComplex.cell C (n + 1)) :
    IsOpen (Subtype.val ⁻¹' RelCWComplex.openCell (n + 1) j : Set {x : X // x ∈ stepV C n}) := by
  have hA : IsClosed ((skel C (n + 1) : Set X) \ RelCWComplex.openCell (n + 1) j) :=
    isClosed_skel_diff_openCell (C := C) n j
  have hset :
      (Subtype.val ⁻¹' (RelCWComplex.openCell (n + 1) j) : Set {x : X // x ∈ stepV C n}) =
        Subtype.val ⁻¹' (((skel C (n + 1) : Set X) \ RelCWComplex.openCell (n + 1) j)ᶜ) := by
    ext x
    constructor
    · intro hx hmem
      exact hmem.2 hx
    · intro hx
      by_contra hcon
      exact hx ⟨stepV_subset_skel (C := C) n x.2, hcon⟩
  rw [hset]
  exact hA.isOpen_compl.preimage continuous_subtype_val

/-! ## §3 The canonical bijection with the disjoint union of the open top cells -/

/-- The canonical map from the disjoint union of the open `(n+1)`-cells to `stepV C n`. -/
def stepVIncl (n : ℕ) :
    (Σ j : RelCWComplex.cell C (n + 1), {x : X // x ∈ RelCWComplex.openCell (n + 1) j}) →
      {x : X // x ∈ stepV C n} :=
  fun p => ⟨p.2.1, Set.mem_iUnion.mpr ⟨p.1, p.2.2⟩⟩

lemma continuous_stepVIncl (n : ℕ) : Continuous (stepVIncl (C := C) n) :=
  continuous_sigma fun _ => Continuous.subtype_mk continuous_subtype_val _

lemma injective_stepVIncl (n : ℕ) : Function.Injective (stepVIncl (C := C) n) := by
  rintro ⟨j, x⟩ ⟨j', x'⟩ h
  have hx : (x : X) = (x' : X) := congrArg Subtype.val h
  have hmem : (x : X) ∈ RelCWComplex.openCell (n + 1) j' := hx ▸ x'.2
  have hjj : j = j' := openCell_cell_eq (C := C) x.2 hmem
  subst hjj
  exact Sigma.ext rfl (heq_of_eq (Subtype.ext hx))

lemma surjective_stepVIncl (n : ℕ) : Function.Surjective (stepVIncl (C := C) n) := by
  intro x
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp x.2
  exact ⟨⟨j, ⟨x.1, hj⟩⟩, Subtype.ext rfl⟩

lemma isOpenMap_stepVIncl (n : ℕ) : IsOpenMap (stepVIncl (C := C) n) := by
  rw [isOpenMap_sigma]
  intro j V hV
  obtain ⟨W, hW, hWV⟩ := isOpen_induced_iff.mp hV
  have himg :
      (fun a : {x : X // x ∈ RelCWComplex.openCell (n + 1) j} =>
          stepVIncl (C := C) n ⟨j, a⟩) '' V =
        (Subtype.val ⁻¹' W : Set {x : X // x ∈ stepV C n}) ∩
          Subtype.val ⁻¹' (RelCWComplex.openCell (n + 1) j) := by
    ext y
    constructor
    · rintro ⟨a, ha, rfl⟩
      have haW : (a : X) ∈ W := by
        have h : a ∈ Subtype.val ⁻¹' W := by rw [hWV]; exact ha
        exact h
      exact ⟨haW, a.2⟩
    · rintro ⟨hyW, hyO⟩
      refine ⟨⟨y.1, hyO⟩, ?_, ?_⟩
      · have h : (⟨y.1, hyO⟩ : {x : X // x ∈ RelCWComplex.openCell (n + 1) j}) ∈
            Subtype.val ⁻¹' W := hyW
        rwa [hWV] at h
      · exact Subtype.ext rfl
  rw [himg]
  exact (hW.preimage continuous_subtype_val).inter (isOpen_openCell_stepV (C := C) n j)

/-- A bijective open continuous map is a homeomorphism: the inverse of an open map is
continuous, because for a bijection `e` one has `e.symm ⁻¹' U = e '' U`. -/
lemma continuous_equiv_symm_of_isOpenMap {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    (e : α ≃ β) (h : IsOpenMap e.toFun) : Continuous e.symm := by
  rw [continuous_def]
  intro U hU
  rw [← Equiv.image_eq_preimage_symm e U]
  exact h U hU

/-- The canonical bijection `Σ j, openCell (n+1) j ≃ stepV C n`. -/
noncomputable def stepVEquiv (n : ℕ) :
    (Σ j : RelCWComplex.cell C (n + 1), {x : X // x ∈ RelCWComplex.openCell (n + 1) j}) ≃
      {x : X // x ∈ stepV C n} :=
  Equiv.ofBijective (stepVIncl (C := C) n)
    ⟨injective_stepVIncl (C := C) n, surjective_stepVIncl (C := C) n⟩

lemma continuous_stepVEquiv (n : ℕ) : Continuous (stepVEquiv (C := C) n) :=
  continuous_stepVIncl (C := C) n

lemma isOpenMap_stepVEquiv (n : ℕ) : IsOpenMap (stepVEquiv (C := C) n) :=
  isOpenMap_stepVIncl (C := C) n

/-- `stepV C n` is homeomorphic to the disjoint union of the open `(n+1)`-cells. -/
noncomputable def stepVHomeomorph (n : ℕ) :
    (Σ j : RelCWComplex.cell C (n + 1), {x : X // x ∈ RelCWComplex.openCell (n + 1) j}) ≃ₜ
      {x : X // x ∈ stepV C n} where
  toEquiv := stepVEquiv (C := C) n
  continuous_toFun := continuous_stepVEquiv (C := C) n
  continuous_invFun := continuous_equiv_symm_of_isOpenMap _ (isOpenMap_stepVEquiv (C := C) n)

/-! ## §4 Each open cell is homotopy equivalent to a point -/

lemma nonempty_homotopyEquiv_openCell_punit (n : ℕ) (j : RelCWComplex.cell C (n + 1)) :
    Nonempty (ContinuousMap.HomotopyEquiv
      (TopCat.of {x : X // x ∈ RelCWComplex.openCell (n + 1) j}) (TopCat.of PUnit)) := by
  haveI : ContractibleSpace {x : X // x ∈ RelCWComplex.openCell (n + 1) j} :=
    contractibleSpace_openCell (C := C) (n + 1) j
  exact ContractibleSpace.hequiv _ _

/-- The disjoint union of one-point fibres over a fixed index type is independent of the universe
in which the one-point type lives. -/
noncomputable def sigmaPUnitHomeomorph.{w, v} (ι : Type v) :
    (Σ _ : ι, PUnit) ≃ₜ (Σ _ : ι, PUnit.{w + 1}) where
  toFun p := ⟨p.1, PUnit.unit⟩
  invFun p := ⟨p.1, PUnit.unit⟩
  left_inv p := by obtain ⟨i, x⟩ := p; cases x; rfl
  right_inv p := by obtain ⟨i, x⟩ := p; cases x; rfl
  continuous_toFun := by
    refine continuous_sigma
      (f := fun p : (Σ _ : ι, PUnit) => (⟨p.1, PUnit.unit⟩ : Σ _ : ι, PUnit.{w + 1})) ?_
    intro i
    show Continuous fun _ : PUnit => (⟨i, PUnit.unit⟩ : Σ _ : ι, PUnit.{w + 1})
    exact continuous_const
  continuous_invFun := by
    refine continuous_sigma
      (f := fun p : (Σ _ : ι, PUnit.{w + 1}) => (⟨p.1, PUnit.unit⟩ : Σ _ : ι, PUnit)) ?_
    intro i
    show Continuous fun _ : PUnit.{w + 1} => (⟨i, PUnit.unit⟩ : Σ _ : ι, PUnit)
    exact continuous_const

/-! ## §5 The homotopy equivalence -/

/-- `stepV C n` is homotopy equivalent to the discrete space of `(n+1)`-cells. The target is the
`PUnit`-indexed sigma type `Σ j, PUnit`, which is discrete on the index set `cell C (n+1)`; the
universe of `PUnit` is kept general because that is how the statement of
`Work.CWTOP.homotopyEquiv_stepV` elaborates (its `PUnit` sits at a higher universe than the
open cells, so the two sides of the homotopy equivalence live in different universes). -/
theorem homotopyEquiv_stepV_aux (n : ℕ) :
    Nonempty (ContinuousMap.HomotopyEquiv (TopCat.of (stepV C n))
      (TopCat.of (Σ j : RelCWComplex.cell C (n + 1), PUnit.{u + 1}))) := by
  obtain ⟨hσ⟩ := homotopyEquiv_sigma (ι := RelCWComplex.cell C (n + 1))
    (A := fun j => {x : X // x ∈ RelCWComplex.openCell (n + 1) j})
    (B := fun _ => PUnit)
    (fun j => (nonempty_homotopyEquiv_openCell_punit (C := C) n j).some)
  exact ⟨((stepVHomeomorph (C := C) n).symm.toHomotopyEquiv.trans hσ).trans
    (sigmaPUnitHomeomorph.{u, 0} (RelCWComplex.cell C (n + 1))).toHomotopyEquiv⟩

theorem homotopyEquiv_stepV (n : ℕ) :
    Nonempty (ContinuousMap.HomotopyEquiv (TopCat.of (stepV C n))
      (TopCat.of (Σ j : RelCWComplex.cell C (n + 1), PUnit))) :=
  homotopyEquiv_stepV_aux (C := C) n

end Work.CWTOP
