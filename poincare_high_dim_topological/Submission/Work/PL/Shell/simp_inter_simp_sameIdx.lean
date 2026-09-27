import Mathlib
import Submission.Work.PL.Defs
import Submission.Work.PL.Shell.Basic
import Submission.Work.PL.Shell.bary_inj
import Submission.Work.PL.Shell.convexHull_inter_bary
import Submission.Work.PL.Sd1.Defs

/-!
# `Work.PL.Shell.simp_inter_simp_sameIdx`

The intersection of the top simplices of the barycentric subdivision of a simplex `Δ`
spanned by two flags `l`, `l'` of `Δ` is the face of the simplex of `l` spanned by those
of its vertices (the centroids of the prefix sets) that are also vertices of the simplex
of `l'`.

The proof combines

* `Work.PL.Shell.convexHull_inter_bary`, which computes the intersection of the convex
  hulls of the centroids of two chains of nonempty subsets of an affinely independent set
  as the convex hull of the common centroids;
* the identification `prefixes l ∩ prefixes l' = (sameIdx l l').image (prefAt l)` of the
  common prefix sets with the image of the index set `sameIdx l l'` under `prefAt l`.
-/

namespace Work.PL.Shell

open Set Metric Finset
open scoped BigOperators

noncomputable section

variable {N : ℕ}

/-! ### Elementary facts about the prefix chain (self-contained copies) -/

private theorem prefAt_mono_s {l : List (PL.E N)} {j k : ℕ} (hjk : j ≤ k) :
    prefAt l j ⊆ prefAt l k := by
  intro x hx
  rw [prefAt, List.mem_toFinset] at hx ⊢
  exact List.take_subset_take_left l (by omega : j + 1 ≤ k + 1) hx

private theorem prefAt_card_s {l : List (PL.E N)} (hl : l.Nodup) {j : ℕ}
    (hj : j < l.length) : (prefAt l j).card = j + 1 := by
  have hnod : (l.take (j + 1)).Nodup := List.Pairwise.sublist (List.take_sublist (j + 1) l) hl
  rw [prefAt, List.toFinset_card_of_nodup hnod,
      List.length_take_of_le (by omega : j + 1 ≤ l.length)]

private theorem prefAt_nonempty_s {l : List (PL.E N)} (hl : l.Nodup) {j : ℕ}
    (hj : j < l.length) : (prefAt l j).Nonempty :=
  Finset.card_pos.mp (by rw [prefAt_card_s hl hj]; omega)

private theorem prefAt_mem_prefixes_s {l : List (PL.E N)} {j : ℕ} (hj : j < l.length) :
    prefAt l j ∈ prefixes l :=
  Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr hj, rfl⟩

private theorem prefAt_subset_toFinset_s {l : List (PL.E N)} {j : ℕ} :
    prefAt l j ⊆ l.toFinset := by
  intro x hx
  rw [prefAt, List.mem_toFinset] at hx
  exact List.mem_toFinset.mpr (List.mem_of_mem_take hx)

private theorem prefixes_chain_s {l : List (PL.E N)} :
    ∀ A ∈ prefixes l, ∀ B ∈ prefixes l, A ⊆ B ∨ B ⊆ A := by
  intro A hA B hB
  obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hA
  obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hB
  rcases le_total j k with h | h
  · exact Or.inl (prefAt_mono_s h)
  · exact Or.inr (prefAt_mono_s h)

private theorem prefixes_subset_toFinset_s {l : List (PL.E N)} :
    ∀ A ∈ prefixes l, A ⊆ l.toFinset := by
  intro A hA
  obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hA
  exact prefAt_subset_toFinset_s

private theorem prefixes_nonempty_s {l : List (PL.E N)} (hl : l.Nodup) :
    ∀ A ∈ prefixes l, A.Nonempty := by
  intro A hA
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hA
  exact prefAt_nonempty_s hl (Finset.mem_range.mp hj)

/-! ### The main lemma -/

theorem simp_inter_simp_sameIdx {N : ℕ} {Δ : Finset (PL.E N)}
    (hΔ : AffineIndependent ℝ ((↑) : Δ → PL.E N))
    {l l' : List (PL.E N)} (hl : l.Nodup) (hl' : l'.Nodup)
    (hlt : l.toFinset = Δ) (hlt' : l'.toFinset = Δ) :
    PL.simp ((Work.PL.Shell.prefixes l).image Work.PL.Shell.bary) ∩
      PL.simp ((Work.PL.Shell.prefixes l').image Work.PL.Shell.bary) =
      Work.PL.Sd1.face l (Work.PL.Sd1.sameIdx l l') := by
  classical
  -- The prefix sets common to `l` and `l'` are exactly the `prefAt l j` for `j ∈ sameIdx`.
  have hSet : Work.PL.Shell.prefixes l ∩ Work.PL.Shell.prefixes l' =
      (Work.PL.Sd1.sameIdx l l').image (Work.PL.Shell.prefAt l) := by
    ext A
    rw [Finset.mem_inter]
    constructor
    · rintro ⟨hA, hA'⟩
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hA
      refine Finset.mem_image.mpr ⟨j, ?_, rfl⟩
      rw [Work.PL.Sd1.sameIdx, Work.PL.Sd1.flagIdx, Finset.mem_filter, Finset.mem_range]
      exact ⟨Finset.mem_range.mp hj, hA'⟩
    · intro hA
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hA
      rw [Work.PL.Sd1.sameIdx, Work.PL.Sd1.flagIdx, Finset.mem_filter, Finset.mem_range] at hj
      obtain ⟨hjf, hj'⟩ := hj
      exact ⟨prefAt_mem_prefixes_s hjf, hj'⟩
  rw [Work.PL.Shell.convexHull_inter_bary hΔ
        (fun A hA => ⟨prefixes_nonempty_s hl A hA,
          by rw [← hlt]; exact prefixes_subset_toFinset_s A hA⟩)
        (fun A hA => ⟨prefixes_nonempty_s hl' A hA,
          by rw [← hlt']; exact prefixes_subset_toFinset_s A hA⟩)
        prefixes_chain_s prefixes_chain_s,
      Work.PL.Sd1.face, hSet]

end

end Work.PL.Shell
