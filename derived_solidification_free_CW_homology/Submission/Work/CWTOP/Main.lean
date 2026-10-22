/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.Work.CWTOP.Closed
import Submission.Work.CWTOP.Basic
import Submission.Work.CWTOP.Pieces
import Submission.Work.CWTOP.Collar
import Submission.Work.CWTOP.Radial
import Submission.Work.CWTOP.isQuotientMap_stepGlue
import Submission.Work.CWTOP.isOpen_stepCollarSubtype
import Submission.Work.CWTOP.g_skel_zero
import Submission.Work.CWTOP.g_modelSphere
import Submission.Work.CWTOP.homotopyEquiv_stepV
import Submission.Work.CWTOP.homotopyEquiv_stepAnnuli
import Submission.Work.CWTOP.exists_skel_superset_of_isCompact

/-!
# CWTOP: Hausdorff CW complexes lie in every `CWClosed` class

Main results:

* `Work.CWTOP.g_skel_succ` : the Mayer–Vietoris induction step from the `n`-skeleton to the
  `(n+1)`-skeleton, using the collar space `stepCollar C n` (homotopy equivalent to the
  `n`-skeleton by `homotopyEquiv_stepCollar_skel`) and the union of the open top cells;
* `Submission.Blueprint.CWTopProp` : **every Hausdorff CW complex lies in every class satisfying
  the `CWClosed` axioms** (`cwTop_prop`).
-/

open CategoryTheory Limits Topology Set Function Metric

noncomputable section

namespace Work.CWTOP

variable {X : Type} [TopologicalSpace X] [T2Space X] {C : Set X} [CWComplex C]

/-- The subtype of a subtype given by a subset, when the subsets are nested. -/
noncomputable def subSubHomeomorph (S T : Set X) (h : S ⊆ T) :
    {x : ↥T // (x : X) ∈ S} ≃ₜ ↥S where
  toFun x := ⟨(x : ↥T).1, x.2⟩
  invFun x := ⟨⟨(x : X), h x.2⟩, x.2⟩
  left_inv x := rfl
  right_inv x := rfl
  continuous_toFun := Continuous.subtype_mk
    (continuous_subtype_val.comp continuous_subtype_val) _
  continuous_invFun := Continuous.subtype_mk
    (Continuous.subtype_mk continuous_subtype_val _) _

/-- The collar space, viewed as a subset of the `(n+1)`-skeleton. -/
def collarSubtype (n : ℕ) : Set ↥(skel C (n + 1)) := {x | (x : X) ∈ stepCollar C n}

/-- The union of the open top cells, viewed as a subset of the `(n+1)`-skeleton. -/
def vSubtype (n : ℕ) : Set ↥(skel C (n + 1)) := {x | (x : X) ∈ stepV C n}

lemma stepV_subset_skel_succ {n : ℕ} : stepV C n ⊆ skel C (n + 1) := by
  intro x hx
  rw [stepV] at hx
  obtain ⟨j, hx⟩ := Set.mem_iUnion.mp hx
  exact RelCWComplex.openCell_subset_skeleton (n + 1) j hx

lemma skel_disjoint_stepV {n m : ℕ} (h : m ≤ n) : Disjoint (skel C m) (stepV C n) := by
  rw [stepV, Set.disjoint_iUnion_right]
  intro j
  exact RelCWComplex.disjoint_skeletonLT_openCell (C := C) (n := ((m + 1 : ℕ) : ℕ∞))
    (m := n + 1) (j := j) (by exact_mod_cast (Nat.succ_le_succ h))

lemma stepCollar_union_stepV {n : ℕ} : stepCollar C n ∪ stepV C n = skel C (n + 1) := by
  refine Set.Subset.antisymm (union_subset stepCollar_subset_skel_succ stepV_subset_skel_succ) ?_
  intro x hx
  rw [SetLike.mem_coe, CWComplex.mem_skeleton_iff] at hx
  obtain ⟨m, hm, j, hj⟩ := hx
  have hm' : m ≤ n + 1 := by exact_mod_cast hm
  rcases Nat.lt_or_ge m (n + 1) with hlt | hge
  · refine Or.inl (Or.inl ?_)
    exact CWComplex.mem_skeleton_iff.mpr
      ⟨m, (Nat.cast_le (α := ℕ∞)).mpr (Nat.lt_succ_iff.mp hlt), j, hj⟩
  · have hm_eq : m = n + 1 := le_antisymm hm' hge
    subst hm_eq
    obtain ⟨y, hy, rfl⟩ := hj
    by_cases hcy : y ∈ modelCollar n
    · exact Or.inl (Or.inr (Set.mem_iUnion.mpr ⟨j, y, hcy, rfl⟩))
    · exact Or.inr (Set.mem_iUnion.mpr ⟨j, ⟨y, hy, rfl⟩⟩)

lemma isOpen_vSubtype (n : ℕ) : IsOpen (vSubtype (C := C) n) := by
  have hcomp : (vSubtype (C := C) n)ᶜ = Subtype.val ⁻¹' (skel C n : Set X) := by
    ext x
    constructor
    · intro hx
      rw [Set.mem_compl_iff] at hx
      by_contra hxn
      refine hx ?_
      have hx1 : (x : X) ∈ skel C (n + 1) := x.2
      rw [SetLike.mem_coe, CWComplex.mem_skeleton_iff] at hx1
      obtain ⟨m, hm, j, hj⟩ := hx1
      have hm' : m ≤ n + 1 := by exact_mod_cast hm
      rcases Nat.lt_or_ge m (n + 1) with hlt | hge
      · exact absurd (CWComplex.mem_skeleton_iff.mpr
          ⟨m, (Nat.cast_le (α := ℕ∞)).mpr (Nat.lt_succ_iff.mp hlt), j, hj⟩) hxn
      · have hm_eq : m = n + 1 := le_antisymm hm' hge
        subst hm_eq
        exact Set.mem_iUnion.mpr ⟨j, hj⟩
    · intro hx hxV
      exact Set.disjoint_left.mp (skel_disjoint_stepV (C := C) (Nat.le_refl n)) hx hxV
  refine isClosed_compl_iff.mp ?_
  rw [hcomp]
  exact (RelCWComplex.skeleton C n).closed.preimage continuous_subtype_val

lemma isOpen_collarSubtype (n : ℕ) : IsOpen (collarSubtype (C := C) n) :=
  isOpen_stepCollarSubtype (C := C) n

/-- **The induction step**: if `G` holds for the `n`-skeleton and for the disjoint union of the
model spheres over the `(n+1)`-cells, then it holds for the `(n+1)`-skeleton. -/
theorem g_skel_succ (G : TopCat.{0} → Prop) (hG : Submission.Blueprint.CWClosed G) (n : ℕ)
    (hS : G (TopCat.of (skel C n)))
    (hSphere : G (TopCat.of (Σ j : RelCWComplex.cell C (n + 1), modelSphere n))) :
    G (TopCat.of (skel C (n + 1))) := by
  have hPt : G (TopCat.of (Σ _j : RelCWComplex.cell C (n + 1), PUnit)) :=
    hG.sigma _ (fun _ => TopCat.of PUnit) (fun _ => hG.point)
  have hU : G (TopCat.of (collarSubtype (C := C) n)) := by
    obtain ⟨e⟩ := homotopyEquiv_stepCollar_skel (C := C) n
    refine hG.of_homotopyEquiv _ _ ?_ hS
    exact ((subSubHomeomorph (stepCollar C n) (skel C (n + 1))
      stepCollar_subset_skel_succ).toHomotopyEquiv).trans e
  have hV : G (TopCat.of (vSubtype (C := C) n)) := by
    obtain ⟨e⟩ := homotopyEquiv_stepV (C := C) n
    refine hG.of_homotopyEquiv _ _ ?_ hPt
    exact ((subSubHomeomorph (stepV C n) (skel C (n + 1))
      stepV_subset_skel_succ).toHomotopyEquiv).trans e
  have hUV : G (TopCat.of (Set.inter (collarSubtype (C := C) n) (vSubtype (C := C) n))) := by
    obtain ⟨e⟩ := homotopyEquiv_stepAnnuli (C := C) n
    refine hG.of_homotopyEquiv _ _ ?_ hSphere
    exact ((subSubHomeomorph (Set.inter (stepCollar C n) (stepV C n)) (skel C (n + 1))
      (Set.Subset.trans Set.inter_subset_left stepCollar_subset_skel_succ)).toHomotopyEquiv).trans e
  refine hG.mv _ _ _ (isOpen_collarSubtype n) (isOpen_vSubtype n) ?_ hU hV hUV
  refine Set.eq_univ_iff_forall.mpr fun x => ?_
  have hx : (x : X) ∈ stepCollar C n ∪ stepV C n := by
    rw [stepCollar_union_stepV]; exact x.2
  rcases hx with h | h
  · exact Or.inl h
  · exact Or.inr h

end Work.CWTOP

namespace Work.CWTOP

open Submission.Blueprint

/-- **AREA CWTOP.** Every Hausdorff CW complex lies in every class satisfying the `CWClosed`
axioms. -/
theorem cwTop_prop : CWTopProp := by
  intro G hG X _ _
  have hskel : ∀ n : ℕ, G (TopCat.of (skel (Set.univ : Set X) n)) := by
    intro n
    induction n with
    | zero => exact g_skel_zero (C := (Set.univ : Set X)) G hG
    | succ n ih =>
        refine g_skel_succ (C := (Set.univ : Set X)) G hG n ih ?_
        exact hG.sigma _ (fun _ : RelCWComplex.cell (Set.univ : Set X) (n + 1) =>
          TopCat.of (modelSphere n)) (fun _ => g_modelSphere G hG n)
  refine hG.exhaust X (fun n => skel (Set.univ : Set X) n) ?_ ?_ hskel
  · intro a b hab
    exact RelCWComplex.skeleton_mono (C := (Set.univ : Set X))
      (show ((a : ℕ∞) ≤ (b : ℕ∞)) from by exact_mod_cast hab)
  · intro K hK
    obtain ⟨n, hn⟩ := exists_skel_superset_of_isCompact (C := (Set.univ : Set X)) hK
      (Set.subset_univ K)
    exact ⟨n, hn⟩

end Work.CWTOP
