import Mathlib
import Submission.Work.PL.Defs
import Submission.Work.PL.Shell.Basic
import Submission.Work.PL.Shell.subList_spec
import Submission.Work.PL.Shell.flagEnum_mem
import Submission.Work.PL.Shell.affineIndependent_bary_image

/-!
# `Work.PL.Sd1.Red` — reducing `sd1Data_spec` to the general `sd1_spec`-shaped statement

`Work.PL.Shell.sd1Data_spec` is the specialization of `Work.PL.Shell.sd1_spec` to the flag
list `subList σ T` with rank `subRank σ T` (the `T`-first ordering), read off the definition
of `Work.PL.Shell.sd1Data`.  This module isolates that rewriting:

* `Shell1` is the (unfolded) conclusion of the general statement, as an explicit hypothesis;
* `sd1Data_spec_of_shell1` derives the `sd1Data` form from it;
* `shell1_of_general` specializes a general statement in that shape to `subList`/`subRank`.

Everything here is independent of the module that proves the general statement; the small
auxiliary facts about prefix sets and centroids that are needed are reproved locally.
-/

open Set Metric Finset
open scoped BigOperators

namespace Work.PL.Sd1

noncomputable section

variable {N : ℕ}

/-! ### Elementary facts about the prefix chain -/

/-- Membership in `prefixes l`. -/
theorem mem_prefixes_iff {A : Finset (PL.E N)} {l : List (PL.E N)} :
    A ∈ Work.PL.Shell.prefixes l ↔ ∃ k < l.length, Work.PL.Shell.prefAt l k = A := by
  simp [Work.PL.Shell.prefixes, Finset.mem_image, Finset.mem_range, eq_comm]

/-- Every prefix set consists of elements of the list. -/
theorem prefAt_subset_toFinset {l : List (PL.E N)} {k : ℕ} :
    Work.PL.Shell.prefAt l k ⊆ l.toFinset := by
  intro x hx
  simp only [Work.PL.Shell.prefAt, List.mem_toFinset] at hx ⊢
  exact List.Sublist.subset (List.take_sublist (k + 1) l) hx

/-- Every prefix set is nonempty. -/
theorem prefAt_nonempty {l : List (PL.E N)} {k : ℕ} (hk : k < l.length) :
    (Work.PL.Shell.prefAt l k).Nonempty := by
  rw [Work.PL.Shell.prefAt, Finset.nonempty_iff_ne_empty]
  intro h
  have hlen := congrArg List.length ((List.toFinset_eq_empty_iff _).mp h)
  rw [List.length_take, List.length_nil, min_eq_left (Nat.succ_le_of_lt hk)] at hlen
  exact Nat.succ_ne_zero k hlen

/-- Prefix sets are monotone in the index. -/
theorem prefAt_subset_of_le {l : List (PL.E N)} {i j : ℕ} (hij : i ≤ j) :
    Work.PL.Shell.prefAt l i ⊆ Work.PL.Shell.prefAt l j := by
  intro x hx
  simp only [Work.PL.Shell.prefAt, List.mem_toFinset] at hx ⊢
  have hsub : (l.take (i + 1)).Sublist (l.take (j + 1)) := by
    have h : l.take (i + 1) = (l.take (j + 1)).take (i + 1) := by
      rw [List.take_take, min_eq_left (by omega)]
    rw [h]
    exact List.take_sublist _ _
  exact hsub.subset hx

/-- Every prefix set is a nonempty subset of `σ`, for `l` enumerating `σ`. -/
theorem prefixes_spec {σ : Finset (PL.E N)} {l : List (PL.E N)} (hσl : l.toFinset = σ)
    {A : Finset (PL.E N)} (hA : A ∈ Work.PL.Shell.prefixes l) : A.Nonempty ∧ A ⊆ σ := by
  obtain ⟨k, hk, rfl⟩ := mem_prefixes_iff.mp hA
  refine ⟨prefAt_nonempty hk, ?_⟩
  intro x hx
  have h := prefAt_subset_toFinset hx
  rwa [hσl] at h

/-- The prefix sets of a list form a chain. -/
theorem prefixes_chain {l : List (PL.E N)} {A B : Finset (PL.E N)}
    (hA : A ∈ Work.PL.Shell.prefixes l) (hB : B ∈ Work.PL.Shell.prefixes l) :
    A ⊆ B ∨ B ⊆ A := by
  obtain ⟨i, _, rfl⟩ := mem_prefixes_iff.mp hA
  obtain ⟨j, _, rfl⟩ := mem_prefixes_iff.mp hB
  rcases le_total i j with h | h
  · exact Or.inl (prefAt_subset_of_le h)
  · exact Or.inr (prefAt_subset_of_le h)

/-- The vertices of the subdivision simplex of a flag are affinely independent. -/
theorem entry_affineIndependent {σ : Finset (PL.E N)}
    (hσ : AffineIndependent ℝ ((↑) : σ → PL.E N)) {l : List (PL.E N)}
    (hσl : l.toFinset = σ) :
    AffineIndependent ℝ
      ((↑) : ((Work.PL.Shell.prefixes l).image Work.PL.Shell.bary) → PL.E N) :=
  Work.PL.Shell.affineIndependent_bary_image (Δ := σ) hσ
    (fun _ hA => prefixes_spec hσl hA) (fun _ hA _ hB => prefixes_chain hA hB)

/-! ### Centroids -/

/-- The centroid of a nonempty `S ⊆ σ` is a point of the simplex on `σ`. -/
theorem bary_mem_simp {σ : Finset (PL.E N)} {S : Finset (PL.E N)} (hS : S.Nonempty)
    (h : S ⊆ σ) : Work.PL.Shell.bary S ∈ PL.simp σ := by
  have hcard : (S.card : ℝ) ≠ 0 := by exact_mod_cast hS.card_ne_zero
  have hsum : ∑ y ∈ S, (S.card : ℝ)⁻¹ = 1 := by
    rw [Finset.sum_const, nsmul_eq_mul]
    exact mul_inv_cancel₀ hcard
  have hcm : S.centerMass (fun _ => (S.card : ℝ)⁻¹) id = Work.PL.Shell.bary S := by
    rw [Finset.centerMass_eq_of_sum_1 _ _ hsum, Work.PL.Shell.bary]
    simp only [id_eq]
    rw [Finset.smul_sum]
  have hmem : Work.PL.Shell.bary S ∈ (convexHull ℝ) ((S : Finset (PL.E N)) : Set (PL.E N)) := by
    rw [Finset.mem_convexHull]
    exact ⟨fun _ => (S.card : ℝ)⁻¹, fun y hy => inv_nonneg.mpr (Nat.cast_nonneg _), hsum, hcm⟩
  rw [PL.simp]
  exact convexHull_mono (fun x hx => h hx) hmem

/-- The centroid of an affinely independent `σ` is not in the simplex spanned by
`σ.erase w` for any `w ∈ σ`. -/
theorem bary_not_mem_simp_erase {σ : Finset (PL.E N)} {w : PL.E N}
    (hσ : AffineIndependent ℝ ((↑) : σ → PL.E N)) (hw : w ∈ σ) :
    Work.PL.Shell.bary σ ∉ PL.simp (σ.erase w) := by
  classical
  intro hmem
  rw [PL.simp, Finset.mem_convexHull'] at hmem
  obtain ⟨w', hnn, hsum, hvec⟩ := hmem
  have hcard : (σ.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Finset.card_ne_zero.mpr ⟨w, hw⟩)
  set w₁ : PL.E N → ℝ := fun y => if y = w then 0 else w' y with hw₁def
  set w₂ : PL.E N → ℝ := fun _ => (σ.card : ℝ)⁻¹ with hw₂def
  have hw1w : w₁ w = 0 := by simp [hw₁def]
  have hw1_eq' : ∀ i ∈ σ.erase w, w₁ i = w' i := by
    intro i hi
    have hiw : i ≠ w := (Finset.mem_erase.mp hi).1
    simp [hw₁def, hiw]
  have hsum1 : ∑ i ∈ σ, w₁ i = 1 := by
    rw [← Finset.sum_erase_add σ w₁ hw, Finset.sum_congr rfl hw1_eq', hsum, hw1w, add_zero]
  have hsum2 : ∑ i ∈ σ, w₂ i = 1 := by
    simp only [hw₂def, Finset.sum_const, nsmul_eq_mul, mul_inv_cancel₀ hcard]
  have hvec1 : ∑ i ∈ σ, w₁ i • i = Work.PL.Shell.bary σ := by
    rw [← Finset.sum_erase_add σ (fun i => w₁ i • i) hw,
      Finset.sum_congr rfl (fun i hi => by rw [hw1_eq' i hi]), hvec, hw1w]
    simp
  have hC : ∑ i ∈ σ, w₂ i • i = Work.PL.Shell.bary σ := by
    simp only [hw₂def]
    rw [← Finset.smul_sum, Work.PL.Shell.bary]
  have hvec_eq : ∑ i ∈ σ, w₁ i • i = ∑ i ∈ σ, w₂ i • i := hvec1.trans hC.symm
  have hpoint := hσ.eq_of_sum_eq_sum_subtype (s := σ) (w₁ := w₁) (w₂ := w₂)
    (hsum1.trans hsum2.symm) hvec_eq w hw
  rw [hw1w] at hpoint
  exact (inv_ne_zero hcard) hpoint.symm

/-- If a shelving order attaches every simplex to the previous ones along a nonempty union
of its facets, then its simplices are pairwise distinct. -/
theorem nodup_map_fst_of_shelling {L : List (Finset (PL.E N) × Finset (PL.E N))}
    {B : Set (PL.E N)}
    (hAI : ∀ i (hi : i < L.length),
      AffineIndependent ℝ ((↑) : (L.get ⟨i, hi⟩).1 → PL.E N))
    (hT : ∀ i (hi : i < L.length),
      (L.get ⟨i, hi⟩).2.Nonempty ∧ (L.get ⟨i, hi⟩).2 ⊆ (L.get ⟨i, hi⟩).1)
    (hint : ∀ i (hi : i < L.length),
      PL.simp (L.get ⟨i, hi⟩).1 ∩ (B ∪ Work.PL.Shell.preUnion (L.map Prod.fst) i) =
        ⋃ w ∈ (L.get ⟨i, hi⟩).2, PL.simp ((L.get ⟨i, hi⟩).1.erase w)) :
    (L.map Prod.fst).Nodup := by
  classical
  rw [List.nodup_iff_pairwise_ne, List.pairwise_iff_get]
  intro i j hij heq
  have hii : i.val < L.length := by
    rw [← List.length_map (as := L) (f := Prod.fst)]; exact i.isLt
  have hjj : j.val < L.length := by
    rw [← List.length_map (as := L) (f := Prod.fst)]; exact j.isLt
  have hlt : i.val < j.val := hij
  have hgi : (L.map Prod.fst).get i = (L.get ⟨i.val, hii⟩).1 := by
    rw [List.get_eq_getElem, List.getElem_map, List.get_eq_getElem]
  have hgj : (L.map Prod.fst).get j = (L.get ⟨j.val, hjj⟩).1 := by
    rw [List.get_eq_getElem, List.getElem_map, List.get_eq_getElem]
  have hσ : (L.get ⟨i.val, hii⟩).1 = (L.get ⟨j.val, hjj⟩).1 := by
    rw [← hgi, ← hgj]; exact heq
  have hgetD : (L.map Prod.fst).getD i.val ∅ = (L.get ⟨i.val, hii⟩).1 := by
    rw [List.getD_eq_getElem (L.map Prod.fst) ∅ i.isLt, List.getElem_map, List.get_eq_getElem]
  have hpre : PL.simp (L.get ⟨i.val, hii⟩).1 ⊆
      Work.PL.Shell.preUnion (L.map Prod.fst) j.val := by
    intro x hx
    rw [Work.PL.Shell.preUnion]
    exact Set.mem_iUnion₂.mpr ⟨i.val, Finset.mem_range.mpr hlt, by rwa [hgetD]⟩
  have hprej : PL.simp (L.get ⟨j.val, hjj⟩).1 ⊆
      B ∪ Work.PL.Shell.preUnion (L.map Prod.fst) j.val := by
    rw [← hσ]
    exact hpre.trans Set.subset_union_right
  have hsub : PL.simp (L.get ⟨j.val, hjj⟩).1 ⊆
      ⋃ w ∈ (L.get ⟨j.val, hjj⟩).2, PL.simp ((L.get ⟨j.val, hjj⟩).1.erase w) := by
    rw [← hint j.val hjj]
    exact Set.subset_inter (Subset.refl _) hprej
  obtain ⟨hτne, hτsub⟩ := hT j.val hjj
  have hσjne : (L.get ⟨j.val, hjj⟩).1.Nonempty := Finset.Nonempty.mono hτsub hτne
  have hb := hsub (bary_mem_simp hσjne (Finset.Subset.refl _))
  rw [Set.mem_iUnion₂] at hb
  obtain ⟨w, hwτ, hwb⟩ := hb
  exact (bary_not_mem_simp_erase (hAI j.val hjj) (hτsub hwτ)) hwb

/-! ### The reduction -/

/-- The conclusion of the general `r = 1` shelling statement, with the `let B` unfolded. -/
def Shell1 (Δ T : Finset (PL.E N)) (vs : List (PL.E N)) (rk : PL.E N → ℕ) : Prop :=
  (∀ i (hi : i < (Work.PL.Shell.flagEnum vs).length),
      let l := (Work.PL.Shell.flagEnum vs).get ⟨i, hi⟩
      (Work.PL.Shell.splitOf Δ T rk l).Nonempty ∧
        (Work.PL.Shell.splitOf Δ T rk l) ⊂ (Work.PL.Shell.prefixes l).image Work.PL.Shell.bary ∧
      PL.simp ((Work.PL.Shell.prefixes l).image Work.PL.Shell.bary) ∩
        ((⋃ w ∈ T, PL.simp (Δ.erase w)) ∪ ⋃ j ∈ Finset.range i,
          PL.simp ((Work.PL.Shell.prefixes ((Work.PL.Shell.flagEnum vs).getD j [])).image
            Work.PL.Shell.bary)) =
        ⋃ w ∈ Work.PL.Shell.splitOf Δ T rk l,
          PL.simp (((Work.PL.Shell.prefixes l).image Work.PL.Shell.bary).erase w)) ∧
    (Work.PL.Shell.flagEnum vs).Nodup ∧
    (⋃ l ∈ (Work.PL.Shell.flagEnum vs).toFinset,
        PL.simp ((Work.PL.Shell.prefixes l).image Work.PL.Shell.bary)) = PL.simp Δ

/-- The target statement of `Work.PL.Shell.sd1Data_spec`, in the `sd1Data` form. -/
def Sd1DataConcl (σ T : Finset (PL.E N)) : Prop :=
  let B : Set (PL.E N) := ⋃ w ∈ T, PL.simp (σ.erase w)
  (∀ i (hi : i < (Work.PL.Shell.sd1Data σ T).length),
    let s := (Work.PL.Shell.sd1Data σ T).get ⟨i, hi⟩
    s.2.Nonempty ∧ s.2 ⊂ s.1 ∧
    PL.simp s.1 ∩ (B ∪ ⋃ j ∈ Finset.range i,
        PL.simp ((Work.PL.Shell.sd1Data σ T).getD j (∅, ∅)).1)
      = ⋃ w ∈ s.2, PL.simp (s.1.erase w)) ∧
  (Work.PL.Shell.sd1Data σ T).Nodup ∧
  (⋃ p ∈ (Work.PL.Shell.sd1Data σ T).toFinset, PL.simp p.1) = PL.simp σ

/-- The union over the `toFinset` of a `map` is the union over the `toFinset` of the source. -/
theorem iUnion_toFinset_map {α γ β : Type*} [DecidableEq α] [DecidableEq γ] (l : List α)
    (f : α → γ) (g : γ → Set β) :
    (⋃ y ∈ (l.map f).toFinset, g y) = ⋃ x ∈ l.toFinset, g (f x) := by
  ext z
  simp only [Set.mem_iUnion, List.mem_toFinset]
  constructor
  · rintro ⟨y, hy, hz⟩
    rw [List.mem_map] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨x, hx, hz⟩
  · rintro ⟨x, hx, hz⟩
    exact ⟨f x, List.mem_map.mpr ⟨x, hx, rfl⟩, hz⟩

/-- `preUnion` of the list of first components, in `getD` form. -/
theorem preUnion_map_fst_eq {L : List (Finset (PL.E N) × Finset (PL.E N))} {i : ℕ}
    (hi : i ≤ L.length) :
    Work.PL.Shell.preUnion (L.map Prod.fst) i
      = ⋃ j ∈ Finset.range i, PL.simp ((L.getD j (∅, ∅)).1) := by
  rw [Work.PL.Shell.preUnion]
  refine iUnion₂_congr fun j hj => ?_
  have hjlen : j < L.length := lt_of_lt_of_le (Finset.mem_range.mp hj) hi
  rw [List.getD_eq_getElem (L.map Prod.fst) (∅ : Finset (PL.E N))
        (by simpa only [List.length_map] using hjlen),
      List.getElem_map, List.getD_eq_getElem L (∅, ∅) hjlen]

theorem sd1Data_spec_of_shell1 {N : ℕ} (σ T : Finset (PL.E N))
    (hσ : AffineIndependent ℝ ((↑) : σ → PL.E N))
    (h₁ : T.Nonempty) (h₂ : T ⊂ σ)
    (H : Shell1 (N := N) σ T (Work.PL.Shell.subList σ T) (Work.PL.Shell.subRank σ T)) :
    Sd1DataConcl σ T := by
  classical
  dsimp only [Sd1DataConcl]
  rw [Shell1] at H
  obtain ⟨hmain, _, hcov⟩ := H
  obtain ⟨hvsn, hvs, -, -⟩ := Work.PL.Shell.subList_spec (σ := σ) (T := T)
  have hsd : Work.PL.Shell.sd1Data σ T =
      (Work.PL.Shell.flagEnum (Work.PL.Shell.subList σ T)).map
        (fun l => ((Work.PL.Shell.prefixes l).image Work.PL.Shell.bary,
          Work.PL.Shell.splitOf σ T (Work.PL.Shell.subRank σ T) l)) := rfl
  have hlen : ∀ i, i < (Work.PL.Shell.sd1Data σ T).length ↔
      i < (Work.PL.Shell.flagEnum (Work.PL.Shell.subList σ T)).length := by
    intro i
    rw [hsd, List.length_map]
  have hget : ∀ (i : ℕ) (hi : i < (Work.PL.Shell.sd1Data σ T).length),
      (Work.PL.Shell.sd1Data σ T).get ⟨i, hi⟩ =
        (((Work.PL.Shell.prefixes ((Work.PL.Shell.flagEnum (Work.PL.Shell.subList σ T)).get
            ⟨i, (hlen i).mp hi⟩)).image Work.PL.Shell.bary),
         Work.PL.Shell.splitOf σ T (Work.PL.Shell.subRank σ T)
           ((Work.PL.Shell.flagEnum (Work.PL.Shell.subList σ T)).get ⟨i, (hlen i).mp hi⟩)) := by
    intro i hi
    rw [List.get_eq_getElem, List.get_eq_getElem]
    exact List.getElem_map _
  have hgetD : ∀ (j : ℕ) (hj : j < (Work.PL.Shell.sd1Data σ T).length),
      (Work.PL.Shell.sd1Data σ T).getD j (∅, ∅) =
        (((Work.PL.Shell.prefixes
            ((Work.PL.Shell.flagEnum (Work.PL.Shell.subList σ T)).getD j [])).image
            Work.PL.Shell.bary),
         Work.PL.Shell.splitOf σ T (Work.PL.Shell.subRank σ T)
           ((Work.PL.Shell.flagEnum (Work.PL.Shell.subList σ T)).getD j [])) := by
    intro j hj
    rw [List.getD_eq_getElem _ _ hj, List.getD_eq_getElem _ _ ((hlen j).mp hj)]
    exact List.getElem_map _
  have hstep : ∀ (i : ℕ) (hi : i < (Work.PL.Shell.sd1Data σ T).length),
      ((Work.PL.Shell.sd1Data σ T).get ⟨i, hi⟩).2.Nonempty ∧
      ((Work.PL.Shell.sd1Data σ T).get ⟨i, hi⟩).2 ⊂
        ((Work.PL.Shell.sd1Data σ T).get ⟨i, hi⟩).1 ∧
      PL.simp ((Work.PL.Shell.sd1Data σ T).get ⟨i, hi⟩).1 ∩
        ((⋃ w ∈ T, PL.simp (σ.erase w)) ∪ ⋃ j ∈ Finset.range i,
          PL.simp ((Work.PL.Shell.sd1Data σ T).getD j (∅, ∅)).1) =
        ⋃ w ∈ ((Work.PL.Shell.sd1Data σ T).get ⟨i, hi⟩).2,
          PL.simp (((Work.PL.Shell.sd1Data σ T).get ⟨i, hi⟩).1.erase w) := by
    intro i hi
    have hi' : i < (Work.PL.Shell.flagEnum (Work.PL.Shell.subList σ T)).length := (hlen i).mp hi
    have hg := hget i hi
    have hun : (⋃ j ∈ Finset.range i,
          PL.simp ((Work.PL.Shell.sd1Data σ T).getD j (∅, ∅)).1)
        = ⋃ j ∈ Finset.range i,
            PL.simp ((Work.PL.Shell.prefixes
              ((Work.PL.Shell.flagEnum (Work.PL.Shell.subList σ T)).getD j [])).image
                Work.PL.Shell.bary) := by
      refine iUnion₂_congr fun j hj => ?_
      rw [hgetD j (lt_trans (Finset.mem_range.mp hj) hi)]
    obtain ⟨hne, hprop, heq⟩ := hmain i hi'
    rw [hg, hun]
    exact ⟨hne, hprop, heq⟩
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    exact hstep i hi
  · refine List.Nodup.of_map Prod.fst ?_
    refine nodup_map_fst_of_shelling
      (L := Work.PL.Shell.sd1Data σ T) (B := ⋃ w ∈ T, PL.simp (σ.erase w)) ?_ ?_ ?_
    · intro i hi
      rw [hget i hi]
      have hmem : (Work.PL.Shell.flagEnum (Work.PL.Shell.subList σ T)).get ⟨i, (hlen i).mp hi⟩ ∈
          Work.PL.Shell.flagEnum (Work.PL.Shell.subList σ T) := List.get_mem _ _
      have hperm := Work.PL.Shell.flagEnum_mem.mp hmem
      have hto : ((Work.PL.Shell.flagEnum (Work.PL.Shell.subList σ T)).get
          ⟨i, (hlen i).mp hi⟩).toFinset = σ := by
        rw [List.toFinset_eq_of_perm _ _ hperm, hvs]
      exact entry_affineIndependent hσ hto
    · intro i hi
      exact ⟨(hstep i hi).1, (hstep i hi).2.1.1⟩
    · intro i hi
      rw [preUnion_map_fst_eq (L := Work.PL.Shell.sd1Data σ T) (i := i) (le_of_lt hi)]
      exact (hstep i hi).2.2
  · refine Eq.trans ?_ hcov
    rw [hsd, iUnion_toFinset_map
      (l := Work.PL.Shell.flagEnum (Work.PL.Shell.subList σ T))
      (f := fun l => ((Work.PL.Shell.prefixes l).image Work.PL.Shell.bary,
        Work.PL.Shell.splitOf σ T (Work.PL.Shell.subRank σ T) l))
      (g := fun p => PL.simp p.1)]

/-- A general statement in the `Shell1` shape specializes to `vs = subList σ T`,
`rk = subRank σ T` using `subList_spec`. -/
theorem shell1_of_general {N : ℕ} (σ T : Finset (PL.E N))
    (hσ : AffineIndependent ℝ ((↑) : σ → PL.E N))
    (h₁ : T.Nonempty) (h₂ : T ⊂ σ)
    (Hg : ∀ {Δ T' : Finset (PL.E N)}, AffineIndependent ℝ ((↑) : Δ → PL.E N) →
      ∀ (vs : List (PL.E N)) (rk : PL.E N → ℕ),
      vs.toFinset = Δ → vs.Nodup → (vs.map rk).Pairwise (· < ·) → T'.Nonempty → T' ⊂ Δ →
      (∀ u ∈ T', ∀ w ∈ Δ, w ∉ T' → rk u < rk w) → Shell1 Δ T' vs rk) :
    Shell1 (N := N) σ T (Work.PL.Shell.subList σ T) (Work.PL.Shell.subRank σ T) := by
  obtain ⟨hvs', hvs, hrk, hT⟩ := Work.PL.Shell.subList_spec (σ := σ) (T := T)
  have hT' : ∀ u ∈ T, ∀ w ∈ σ, w ∉ T →
      Work.PL.Shell.subRank σ T u < Work.PL.Shell.subRank σ T w :=
    fun u hu w hw hwT => hT u hu (h₂.1 hu) w hw hwT
  exact Hg hσ (Work.PL.Shell.subList σ T) (Work.PL.Shell.subRank σ T) hvs hvs' hrk h₁ h₂ hT'

end

end Work.PL.Sd1
