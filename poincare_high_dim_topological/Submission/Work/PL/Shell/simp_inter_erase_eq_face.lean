import Mathlib
import Submission.Work.PL.Defs
import Submission.Work.PL.Shell.Basic
import Submission.Work.PL.Shell.bary_inj
import Submission.Work.PL.Shell.convexHull_inter_bary
import Submission.Work.PL.Sd1.Defs
import Submission.Work.PL.Subdiv.Coord

/-!
# `Work.PL.Shell.simp_inter_erase_eq_face`

The top simplex of the barycentric subdivision of `Δ` cut out by the facet `simp (Δ \ {w})`.

Let `Δ ⊆ E N` be affinely independent, `l` a `Nodup` list enumerating `Δ`, and `w ∈ Δ`.
The vertices of the subdivision simplex `PL.simp ((prefixes l).image bary)` are the
centroids of the prefix sets `prefAt l j` (`j < l.length`), and the barycentric coordinate
of a centroid at a vertex `w` is positive exactly when `w` lies in the corresponding prefix
set.  Hence the intersection of the subdivision simplex with the facet `simp (Δ.erase w)`
is exactly the convex hull of the centroids of the prefix sets that miss `w`, i.e. the face
`Work.PL.Sd1.face l (missIdx l w)`.

The two inclusions are proved as the private lemmas `aux_face_subset` and
`aux_subset_face` below.

* `aux_subset_face` (the substantive direction) is proved by writing a point `x` of the
  subdivision simplex as a convex combination `∑ λ_S • bary S` of the centroids of the
  prefix sets (`Work.PL.Subdiv.exists_sum_smul_of_mem_simp`), regrouping it as a
  combination of the vertices of `Δ` (`Work.PL.Subdiv.sum_smul_bary_eq_sum_smul`), and
  using the uniqueness of barycentric coordinates on an affinely independent set
  (`Work.PL.Subdiv.coords_eq_zero_of_mem_simp_subset`) to see that every `λ_S` with
  `w ∈ S` vanishes, because `x` has vanishing coordinate at `w` inside `simp (Δ.erase w)`.
* `aux_face_subset` is the convexity argument in the other direction.

These are stated as general lemmas about arbitrary families `C` of nonempty subsets of `Δ`
(`aux_subset_face`) resp. about the prefix chain (`aux_face_subset`).
-/

open Set Metric Finset
open scoped BigOperators

namespace Work.PL.Shell

noncomputable section

variable {N : ℕ}

/-! ### Small facts about the prefix chain -/

/-- The index set of a flag is the range of its length. -/
private theorem aux_mem_flagIdx {l : List (PL.E N)} {j : ℕ} :
    j ∈ Work.PL.Sd1.flagIdx l ↔ j < l.length := by
  simp [Work.PL.Sd1.flagIdx]

/-- Each prefix set of a flag is a member of the prefix chain. -/
private theorem aux_prefAt_mem_prefixes {l : List (PL.E N)} {j : ℕ} (hj : j < l.length) :
    Work.PL.Shell.prefAt l j ∈ Work.PL.Shell.prefixes l := by
  simp only [Work.PL.Shell.prefixes, Finset.mem_image, Finset.mem_range]
  exact ⟨j, hj, rfl⟩

/-- Each prefix set of a `Nodup` list is nonempty. -/
private theorem aux_prefAt_nonempty {l : List (PL.E N)} (hl : l.Nodup) {j : ℕ}
    (hj : j < l.length) : (Work.PL.Shell.prefAt l j).Nonempty := by
  apply Finset.card_pos.mp
  rw [Work.PL.Shell.prefAt, List.toFinset_card_of_nodup]
  · rw [List.length_take, Nat.min_eq_left (by omega : j + 1 ≤ l.length)]
    omega
  · exact List.Nodup.sublist (List.take_sublist (j + 1) l) hl

/-- Each prefix set of a list is contained in the set of its entries. -/
private theorem aux_prefAt_subset_toFinset {l : List (PL.E N)} {j : ℕ} :
    Work.PL.Shell.prefAt l j ⊆ l.toFinset := by
  intro y hy
  rw [Work.PL.Shell.prefAt, List.mem_toFinset] at hy
  exact List.mem_toFinset.mpr (List.mem_of_mem_take hy)

/-- The prefix chain with the prefix sets missing `w` removed is exactly the family of
prefix sets indexed by `missIdx l w`. -/
private theorem aux_filter_notMem_eq_image_missIdx {l : List (PL.E N)} {w : PL.E N} :
    (Work.PL.Shell.prefixes l).filter (fun S => w ∉ S) =
      (Work.PL.Sd1.missIdx l w).image (Work.PL.Shell.prefAt l) := by
  ext S
  simp only [Finset.mem_filter, Finset.mem_image, Work.PL.Shell.prefixes,
    Finset.mem_range, Work.PL.Sd1.missIdx, Work.PL.Sd1.flagIdx]
  constructor
  · rintro ⟨⟨j, hj, hje⟩, hwj⟩
    exact ⟨j, ⟨hj, by rw [hje]; exact hwj⟩, hje⟩
  · rintro ⟨j, ⟨hj, hwj⟩, hje⟩
    exact ⟨⟨j, hj, hje⟩, by rw [← hje]; exact hwj⟩

/-! ### The substantive inclusion: a point of the subdivision simplex inside the facet
`simp (Δ.erase w)` uses only centroids of sets missing `w` -/

private theorem aux_subset_face {Δ : Finset (PL.E N)}
    (hΔ : AffineIndependent ℝ ((↑) : Δ → PL.E N))
    {C : Finset (Finset (PL.E N))} (hC : ∀ A ∈ C, A.Nonempty ∧ A ⊆ Δ)
    {w : PL.E N} (hw : w ∈ Δ) {x : PL.E N}
    (hx1 : x ∈ PL.simp (C.image Work.PL.Shell.bary))
    (hx2 : x ∈ PL.simp (Δ.erase w)) :
    x ∈ PL.simp ((C.filter (fun A => w ∉ A)).image Work.PL.Shell.bary) := by
  classical
  -- a convex combination of the centroids of the members of `C` representing `x`
  obtain ⟨a, ha0, ha1, hax1, -⟩ := Work.PL.Subdiv.exists_sum_smul_of_mem_simp hx1
  set lam : Finset (PL.E N) → ℝ := fun A => a (Work.PL.Shell.bary A) with hlam
  have hsub : ∀ A ∈ C, A ⊆ Δ := fun A hA => (hC A hA).2
  have hne : ∀ A ∈ C, A.Nonempty := fun A hA => (hC A hA).1
  have hinj : Set.InjOn Work.PL.Shell.bary (↑C : Set (Finset (PL.E N))) := by
    intro A hA B hB hAB
    exact Work.PL.Shell.bary_inj hΔ (hne A (by simpa using hA)) (hne B (by simpa using hB))
      (hsub A (by simpa using hA)) (hsub B (by simpa using hB)) hAB
  have hlam0 : ∀ A ∈ C, 0 ≤ lam A := by
    intro A hA
    exact ha0 (Work.PL.Shell.bary A) (Finset.mem_image.mpr ⟨A, hA, rfl⟩)
  have hlam_sum : ∑ A ∈ C, lam A = 1 := by
    change ∑ A ∈ C, a (Work.PL.Shell.bary A) = 1
    rw [← Finset.sum_image hinj]
    exact ha1
  have hlam_smul : ∑ A ∈ C, lam A • Work.PL.Shell.bary A = x := by
    change ∑ A ∈ C, a (Work.PL.Shell.bary A) • Work.PL.Shell.bary A = x
    rw [← Finset.sum_image (f := fun y => a y • y) hinj]
    exact hax1
  -- the same point, written in the vertices of `Δ`
  set ap : PL.E N → ℝ :=
    fun v => ∑ A ∈ C.filter (fun A => v ∈ A), lam A / (A.card : ℝ) with hap
  have hcoord := Work.PL.Subdiv.sum_smul_bary_eq_sum_smul C Δ hsub lam
  have hax : ∑ v ∈ Δ, ap v • v = x := by
    rw [← hcoord]
    exact hlam_smul
  have hasum : ∑ v ∈ Δ, ap v = 1 := by
    change ∑ v ∈ Δ, (∑ A ∈ C.filter (fun A => v ∈ A), lam A / ↑A.card) = 1
    rw [Work.PL.Subdiv.sum_coeff_filter C Δ hsub hne lam, hlam_sum]
  have hap0 : ∀ v ∈ Δ, 0 ≤ ap v := by
    intro v _
    apply Finset.sum_nonneg
    intro A hA
    exact div_nonneg (hlam0 A (Finset.mem_filter.mp hA).1) (Nat.cast_nonneg _)
  -- uniqueness of the coordinates at the vertex `w`
  have hzero : ap w = 0 :=
    Work.PL.Subdiv.coords_eq_zero_of_mem_simp_subset (Finset.erase_subset w Δ) hΔ hap0 hasum
      hax hx2 w hw (Finset.notMem_erase w Δ)
  have hzw : ∑ A ∈ C.filter (fun A => w ∈ A), lam A / (A.card : ℝ) = 0 := by
    change ap w = 0
    exact hzero
  have hnonneg : ∀ A ∈ C.filter (fun A => w ∈ A), 0 ≤ lam A / (A.card : ℝ) :=
    fun A hA => div_nonneg (hlam0 A (Finset.mem_filter.mp hA).1) (Nat.cast_nonneg _)
  have hlam_zero : ∀ A ∈ C, w ∈ A → lam A = 0 := by
    intro A hA hwA
    have ht := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hzw A
      (Finset.mem_filter.mpr ⟨hA, hwA⟩)
    rcases div_eq_zero_iff.mp ht with h | h
    · exact h
    · exact absurd h (Nat.cast_ne_zero.mpr (Finset.card_ne_zero.mpr (hne A hA)))
  -- the combination survives only on the members of `C` missing `w`
  have hsumD : ∑ A ∈ C.filter (fun A => w ∉ A), lam A = 1 := by
    have hsplit := Finset.sum_filter_add_sum_filter_not C (fun A => w ∉ A) lam
    have hzero2 : ∑ A ∈ C.filter (fun A => ¬ (w ∉ A)), lam A = 0 := by
      apply Finset.sum_eq_zero
      intro A hA
      exact hlam_zero A (Finset.mem_filter.mp hA).1
        (by simpa using (Finset.mem_filter.mp hA).2)
    rw [hzero2, hlam_sum, add_zero] at hsplit
    exact hsplit
  have hsmulD : ∑ A ∈ C.filter (fun A => w ∉ A), lam A • Work.PL.Shell.bary A = x := by
    rw [← hlam_smul]
    refine Finset.sum_subset (Finset.filter_subset _ _) ?_
    intro A hAC hAnD
    have hwA : w ∈ A := by
      by_contra hwA
      exact hAnD (Finset.mem_filter.mpr ⟨hAC, hwA⟩)
    rw [hlam_zero A hAC hwA, zero_smul]
  -- conclude the convex-hull membership
  rw [PL.simp]
  have hcenter :
      (C.filter (fun A => w ∉ A)).centerMass lam (fun A => Work.PL.Shell.bary A) = x := by
    rw [Finset.centerMass_eq_of_sum_1 _ _ hsumD]
    exact hsmulD
  rw [← hcenter]
  refine Finset.centerMass_mem_convexHull (C.filter (fun A => w ∉ A))
    (z := fun A => Work.PL.Shell.bary A) ?_ ?_ ?_
  · intro A hA
    exact hlam0 A (Finset.mem_filter.mp hA).1
  · rw [hsumD]; norm_num
  · intro A hA
    rw [Finset.mem_coe, Finset.mem_image]
    exact ⟨A, hA, rfl⟩

/-! ### The easy inclusion -/

private theorem aux_face_subset {Δ : Finset (PL.E N)}
    {l : List (PL.E N)} (hl : l.Nodup) (hlt : l.toFinset = Δ)
    {w : PL.E N} (_hw : w ∈ Δ) :
    Work.PL.Sd1.face l (Work.PL.Sd1.missIdx l w) ⊆
      PL.simp ((Work.PL.Shell.prefixes l).image Work.PL.Shell.bary) ∩
        PL.simp (Δ.erase w) := by
  intro x hx
  rw [Work.PL.Sd1.face, PL.simp] at hx
  constructor
  · -- the face is a face of the subdivision simplex
    rw [PL.simp]
    refine convexHull_mono ?_ hx
    intro y hy
    simp only [Finset.mem_coe, Finset.mem_image] at hy ⊢
    obtain ⟨S, ⟨j, hj, rfl⟩, rfl⟩ := hy
    exact ⟨Work.PL.Shell.prefAt l j,
      aux_prefAt_mem_prefixes ((aux_mem_flagIdx.mp (Finset.mem_filter.mp hj).1)), rfl⟩
  · -- the centroids of the prefix sets missing `w` lie in the facet
    rw [PL.simp]
    have hpref : ∀ j ∈ Work.PL.Sd1.missIdx l w, Work.PL.Shell.prefAt l j ⊆ Δ.erase w := by
      intro j hj
      have hwj : w ∉ Work.PL.Shell.prefAt l j := (Finset.mem_filter.mp hj).2
      intro y hy
      rw [Finset.mem_erase]
      refine ⟨fun hyw => hwj (hyw ▸ hy), ?_⟩
      rw [← hlt]
      exact aux_prefAt_subset_toFinset hy
    refine (convexHull_min ?_ (convex_convexHull ℝ _)) hx
    intro y hy
    simp only [Finset.mem_coe, Finset.mem_image] at hy
    obtain ⟨S, ⟨j, hj, rfl⟩, rfl⟩ := hy
    have hjlt : j < l.length := aux_mem_flagIdx.mp (Finset.mem_filter.mp hj).1
    exact convexHull_mono (Finset.coe_subset.mpr (hpref j hj))
      (Work.PL.Subdiv.bary_mem_simp (aux_prefAt_nonempty hl hjlt))

/-! ### The target -/

theorem simp_inter_erase_eq_face {N : ℕ} {Δ : Finset (PL.E N)}
    (hΔ : AffineIndependent ℝ ((↑) : Δ → PL.E N))
    {l : List (PL.E N)} (hl : l.Nodup) (hlt : l.toFinset = Δ)
    {w : PL.E N} (hw : w ∈ Δ) :
    PL.simp ((Work.PL.Shell.prefixes l).image Work.PL.Shell.bary) ∩ PL.simp (Δ.erase w) =
      Work.PL.Sd1.face l (Work.PL.Sd1.missIdx l w) := by
  have hC : ∀ A ∈ Work.PL.Shell.prefixes l, A.Nonempty ∧ A ⊆ Δ := by
    intro A hA
    simp only [Work.PL.Shell.prefixes, Finset.mem_image, Finset.mem_range] at hA
    obtain ⟨j, hj, rfl⟩ := hA
    exact ⟨aux_prefAt_nonempty hl hj, fun y hy => by
      rw [← hlt]; exact aux_prefAt_subset_toFinset hy⟩
  apply Set.Subset.antisymm
  · intro x hx
    have hh := aux_subset_face hΔ hC hw hx.1 hx.2
    rw [aux_filter_notMem_eq_image_missIdx] at hh
    exact hh
  · exact aux_face_subset hl hlt hw

end

end Work.PL.Shell
