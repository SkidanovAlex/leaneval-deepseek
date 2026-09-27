import Mathlib
import Submission.Work.Engulf.Defs
import Submission.Work.PL.Defs
import Submission.Work.PL.Generic.Basic
import Submission.Work.PL.Generic.Hull
import Submission.Work.PL.Generic.exists_avoiding_list
import Submission.Work.PL.Generic.affineSpan_eq_top_of_forall_avoid
import Submission.Work.PL.Generic.gp_pairs_pairwise
import Submission.Work.PL.Generic.gp_pairs_fixed
import Submission.Work.PL.Generic.affineIndependent_of_gp

/-!
# `Work.Engulf.Alt.Gp` — the perturbation behind `E4a`, with the general-position condition as an
explicit output.

`Work.PL.Generic.gp_pairs` bundles the general position statement, but its conclusion does not
expose the *hypothesis* (`hgp`) that its internal argument
(`Work.PL.Generic.gp_pairs_pairwise`, `Work.PL.Generic.gp_pairs_fixed`) actually needs.  In `E4alt`
the family of "pairs" to be bounded is not known in advance (it depends on the shelling order and
on the analysis), so we need `hgp` itself; this file provides it.  The statement is exactly the
first half of the proof of `Work.PL.Generic.gp_pairs` (`hgp` and `hgpS` there), and its proof is a
verbatim copy of that half.
-/

open Set Metric PL

namespace Work.Engulf.Alt

universe u

/-- **The perturbation lemma for `E4a`.**  A finite vertex map `y₀ : ι → ℝⁿ` can be perturbed in
the `ε`-ball of every *free* vertex (`fz` = frozen, kept pointwise), so that the order-free general
position condition holds: for every free `u`, every `T ∌ u`, and every fixed finite point set
`S ∈ Fixed`, if `y u` lies in the affine span of `y '' T` (resp. of `y '' T ∪ S`), then that span is
everything. -/
theorem exists_gp_perturb {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (fz : Finset ι) (y₀ : ι → E n) (Fixed : Finset (Finset (E n)))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ y : ι → E n, (∀ i, dist (y i) (y₀ i) < ε) ∧ (∀ i ∈ fz, y i = y₀ i) ∧
      (∀ u, u ∉ fz → ∀ T : Finset ι, u ∉ T →
        y u ∈ (affineSpan ℝ (y '' (T : Set ι)) : Set (E n)) →
          affineSpan ℝ (y '' (T : Set ι)) = ⊤) ∧
      (∀ u, u ∉ fz → ∀ T : Finset ι, u ∉ T → ∀ S ∈ Fixed,
        y u ∈ (affineSpan ℝ ((y '' (T : Set ι)) ∪ (S : Set (E n))) : Set (E n)) →
          affineSpan ℝ ((y '' (T : Set ι)) ∪ (S : Set (E n))) = ⊤) := by
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
  set Fixed' : Finset (Finset (E n)) := insert (∅ : Finset (E n)) Fixed with hFix
  have hmem_empty : (∅ : Finset (E n)) ∈ Fixed' := hFix ▸ Finset.mem_insert_self _ _
  have hsubFixed : ∀ S ∈ Fixed, S ∈ Fixed' := fun S hS => hFix ▸ Finset.mem_insert_of_mem hS
  obtain ⟨y, hdist, hfz, hav⟩ := Work.PL.Generic.exists_avoiding_list fz y₀ l hl hl' Fixed' ε hε
  have hav' : ∀ j (hj : j < l.length), ∀ T : Finset ι, T ⊆ fz ∪ (l.take j).toFinset →
      ∀ S ∈ Fixed', y (l[j]) ∈
          (affineSpan ℝ ((y '' (T : Set ι)) ∪ (S : Set (E n))) : Set (E n)) →
        affineSpan ℝ ((y '' (T : Set ι)) ∪ (S : Set (E n))) = ⊤ :=
    fun j hj T hT S hS => (hav j hj T hT).2 S hS
  refine ⟨y, hdist, hfz, ?_, ?_⟩
  · intro u huf T huT hmem
    have hT : T ⊆ fz ∪ l.toFinset := by rw [huniv]; exact Finset.subset_univ T
    have := Work.PL.Generic.affineSpan_eq_top_of_forall_avoid fz y l hl hl' Fixed' hav' u huf T hT huT ∅
      hmem_empty (by simpa using hmem)
    simpa using this
  · intro u huf T huT S hS hmem
    have hT : T ⊆ fz ∪ l.toFinset := by rw [huniv]; exact Finset.subset_univ T
    exact Work.PL.Generic.affineSpan_eq_top_of_forall_avoid fz y l hl hl' Fixed' hav' u huf T hT huT S
      (hsubFixed S hS) hmem

end Work.Engulf.Alt
