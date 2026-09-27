import Mathlib
import Submission.Work.PL.Defs
import Submission.Work.PL.Generic.Basic
import Submission.Work.PL.Generic.Hull
import Submission.Work.PL.Generic.domDim_of_isBounded_subset_affineSubspace
import Submission.Work.PL.Generic.exists_mem_ball_notMem_iUnion_affineSubspace
import Submission.Work.PL.Generic.affineSpan_insert_inf_finrank_le
import Submission.Work.PL.Generic.exists_ioc_smul_add_of_mem_convexHull_insert
import Submission.Work.PL.Generic.domDim_join_step
import Submission.Work.PL.Generic.mem_hullOf
import Submission.Work.PL.Generic.eq_of_sum_smul_eq_of_affineIndependent
import Submission.Work.PL.Generic.mem_union_of_sum_smul_eq_of_frozen
import Submission.Work.PL.Generic.affineSpan_eq_top_of_sum_smul_ne
import Submission.Work.PL.Generic.gp_pairs_pairwise
import Submission.Work.PL.Generic.gp_pairs_fixed
import Submission.Work.PL.Generic.affineIndependent_of_gp
import Submission.Work.PL.Generic.exists_avoiding_list
import Submission.Work.PL.Generic.affineSpan_eq_top_of_forall_avoid

/-!
# `PL/Generic/GpPairs`: the corrected general position statement G6a′

`Work.PL.Generic.gp_pairs` is the statement A3 owes the lead (see
`Submission/Work/NOTES_LEAD_poincare_engulf.md` §4.1): after a small perturbation of the *free*
vertices of a finite vertex map `y₀ : ι → ℝⁿ` (the frozen set `fz` stays fixed), every pair `pr` of
index sets has (a) its first member affinely independent, (b) its two hulls meeting only in the
shared hull, the frozen-frozen face and a set of dimension `≤ |pr.1| + |pr.2| - 2 - n`, and (c) its
hull meeting any fixed simplex `simp S` only in the frozen face and a set of dimension
`≤ |pr.1| + |S| - 2 - n`.  The collision precondition `hcol` is what makes the pairwise bound true
(it fails for two coincident frozen images sharing a free vertex).
-/

open Set Metric PL

namespace Work.PL.Generic

variable {n : ℕ} {ι : Type*}

/-- `hullOf` only depends on the vertex map on the index set. -/
theorem hullOf_congr {y y' : ι → E n} {s : Finset ι} (h : ∀ i ∈ s, y i = y' i) :
    hullOf y s = hullOf y' s := by
  rw [hullOf, hullOf, Set.image_congr (fun i hi => h i (Finset.mem_coe.1 hi))]

theorem gp_pairs {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (fz : Finset ι) (y₀ : ι → E n)
    (Pairs : Finset (Finset ι × Finset ι)) (Fixed : Finset (Finset (E n)))
    (hfree : ∀ pr ∈ Pairs, ∃ v ∈ pr.1, v ∉ fz)
    (hcard : ∀ pr ∈ Pairs, pr.1.card ≤ n + 1)
    (hnd₁ : ∀ pr ∈ Pairs, AffineIndependent ℝ (fun v : ↥(pr.1 ∩ fz) => y₀ v))
    (hnd₂ : ∀ pr ∈ Pairs, AffineIndependent ℝ (fun v : ↥(pr.2 ∩ fz) => y₀ v))
    (hcol : ∀ pr ∈ Pairs, (∃ v ∈ pr.1 ∩ pr.2, v ∉ fz) →
        hullOf y₀ (pr.1 ∩ fz) ∩ hullOf y₀ (pr.2 ∩ fz) ⊆ hullOf y₀ (pr.1 ∩ pr.2 ∩ fz))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ y : ι → E n, (∀ i, dist (y i) (y₀ i) < ε) ∧ (∀ i ∈ fz, y i = y₀ i) ∧
      (∀ pr ∈ Pairs, AffineIndependent ℝ (fun v : ↥pr.1 => y v)) ∧
      (∀ pr ∈ Pairs, ∃ D : Set (E n), DomDim D ((pr.1.card : ℤ) + pr.2.card - 2 - n) ∧
          hullOf y pr.1 ∩ hullOf y pr.2 ⊆
            hullOf y (pr.1 ∩ pr.2) ∪ (hullOf y (pr.1 ∩ fz) ∩ hullOf y (pr.2 ∩ fz)) ∪ D) ∧
      (∀ pr ∈ Pairs, ∀ S ∈ Fixed, ∃ D : Set (E n), DomDim D ((pr.1.card : ℤ) + S.card - 2 - n) ∧
          hullOf y pr.1 ∩ simp S ⊆ hullOf y (pr.1 ∩ fz) ∪ D) := by
  classical
  -- an enumeration of the free vertices
  have hex : ∃ l : List ι, (∀ i, i ∈ l ↔ i ∉ fz) ∧ l.Nodup := by
    refine ⟨((List.finRange (Fintype.card ι)).map (Fintype.equivFin ι).symm).filter
      (fun i => decide (i ∉ fz)), ?_, ?_⟩
    · intro i
      rw [List.mem_filter, decide_eq_true_iff]
      constructor
      · intro h; exact h.2
      · intro h
        exact ⟨List.mem_map.2 ⟨Fintype.equivFin ι i, List.mem_finRange _,
          Equiv.symm_apply_apply _ _⟩, h⟩
    · exact ((List.nodup_finRange _).map (Fintype.equivFin ι).symm.injective).filter _
  obtain ⟨l, hl, hl'⟩ := hex
  have huniv : fz ∪ l.toFinset = Finset.univ := by
    ext i
    simp only [Finset.mem_union, List.mem_toFinset, Finset.mem_univ, iff_true]
    exact or_iff_not_imp_left.mpr (hl i).mpr
  -- the fixed sets, with `∅` added so that the plain spans are covered
  set Fixed' : Finset (Finset (E n)) := insert (∅ : Finset (E n)) Fixed with hFix
  have hmem_empty : (∅ : Finset (E n)) ∈ Fixed' :=
    hFix ▸ Finset.mem_insert_self _ _
  have hsubFixed : ∀ S ∈ Fixed, S ∈ Fixed' := fun S hS => hFix ▸ Finset.mem_insert_of_mem hS
  -- perturb the free vertices
  obtain ⟨y, hdist, hfz, hav⟩ := exists_avoiding_list fz y₀ l hl hl' Fixed' ε hε
  have hav' : ∀ j (hj : j < l.length), ∀ T : Finset ι, T ⊆ fz ∪ (l.take j).toFinset →
      ∀ S ∈ Fixed', y (l[j]) ∈
          (affineSpan ℝ ((y '' (T : Set ι)) ∪ (S : Set (E n))) : Set (E n)) →
        affineSpan ℝ ((y '' (T : Set ι)) ∪ (S : Set (E n))) = ⊤ :=
    fun j hj T hT S hS => (hav j hj T hT).2 S hS
  -- the general position properties
  have hgp : ∀ (σ : Finset ι), ∀ u, u ∉ fz → ∀ T : Finset ι, T ⊆ σ → u ∉ T →
      y u ∈ (affineSpan ℝ (y '' (T : Set ι)) : Set (E n)) →
        affineSpan ℝ (y '' (T : Set ι)) = ⊤ := by
    intro σ u huf T _ huT hmem
    have hT : T ⊆ fz ∪ l.toFinset := by rw [huniv]; exact Finset.subset_univ T
    have := affineSpan_eq_top_of_forall_avoid fz y l hl hl' Fixed' hav' u huf T hT huT ∅ hmem_empty
      (by simpa using hmem)
    simpa using this
  have hgpS : ∀ (σ : Finset ι) (S : Finset (E n)), S ∈ Fixed → ∀ u, u ∉ fz →
      ∀ T : Finset ι, T ⊆ σ → u ∉ T →
      y u ∈ (affineSpan ℝ ((y '' (T : Set ι)) ∪ (S : Set (E n))) : Set (E n)) →
        affineSpan ℝ ((y '' (T : Set ι)) ∪ (S : Set (E n))) = ⊤ := by
    intro σ S hS u huf T _ huT hmem
    have hT : T ⊆ fz ∪ l.toFinset := by rw [huniv]; exact Finset.subset_univ T
    exact affineSpan_eq_top_of_forall_avoid fz y l hl hl' Fixed' hav' u huf T hT huT S
      (hsubFixed S hS) hmem
  -- (a) affine independence
  have hInd : ∀ pr ∈ Pairs, AffineIndependent ℝ (fun v : ↥pr.1 => y v) := by
    intro pr hpr
    have hg := hgp pr.1
    have hnd : AffineIndependent ℝ (fun v : ↥(pr.1 ∩ fz) => y v) := by
      have hfun : (fun v : ↥(pr.1 ∩ fz) => y v) = (fun v : ↥(pr.1 ∩ fz) => y₀ v) := by
        funext v
        exact hfz v.1 (Finset.mem_of_mem_inter_right v.2)
      rw [hfun]
      exact hnd₁ pr hpr
    exact affineIndependent_of_gp fz y pr.1 (hcard pr hpr) (fun u huf T hT => hg u huf T hT) hnd
  refine ⟨y, hdist, hfz, hInd, ?_, ?_⟩
  -- (b) the pairwise conjunct
  · intro pr hpr
    refine gp_pairs_pairwise fz y pr.1 pr.2 (hgp (pr.1 ∪ pr.2)) ?_
    intro z hz hpre
    have e1 : hullOf y (pr.1 ∩ fz) = hullOf y₀ (pr.1 ∩ fz) :=
      hullOf_congr fun i hi => hfz i (Finset.mem_of_mem_inter_right hi)
    have e2 : hullOf y (pr.2 ∩ fz) = hullOf y₀ (pr.2 ∩ fz) :=
      hullOf_congr fun i hi => hfz i (Finset.mem_of_mem_inter_right hi)
    have e3 : hullOf y (pr.1 ∩ pr.2 ∩ fz) = hullOf y₀ (pr.1 ∩ pr.2 ∩ fz) :=
      hullOf_congr fun i hi => hfz i (Finset.mem_of_mem_inter_right hi)
    rw [e1, e2] at hz
    rw [e3]
    exact hcol pr hpr hpre hz
  -- (c) the fixed conjunct
  · intro pr hpr S hS
    exact gp_pairs_fixed fz y pr.1 S (fun u huf T hT => hgp pr.1 u huf T hT)
      (fun u huf T hT => hgpS pr.1 S hS u huf T hT) (hInd pr hpr)

end Work.PL.Generic
