import Mathlib
import Submission.Work.PL.Defs
import Submission.Work.PL.Shell.Basic
import Submission.Work.PL.Shell.preUnion_eq_iUnion_take
import Submission.Work.PL.Shell.flagEnum_mem
import Submission.Work.PL.Shell.subList_spec
import Submission.Work.PL.Shell.bary_inj
import Submission.Work.PL.Shell.affineIndependent_bary_image

/-!
# Auxiliary lemmas for `Work.PL.Shell.sd_iter_shelling_strong`

Bookkeeping for the union `Work.PL.Shell.preUnion` of the simplices of the first `i` entries of
a list of vertex sets, in the forms needed to run an induction over the iterated barycentric
subdivision `Work.PL.Shell.sdIter r Δ τ₁`.

The list `sdIter (r+1) Δ τ₁` is the `flatMap` of `sdIter r Δ τ₁` over the one-step subdivision
`sd1Data`, so the `(r+1)`-st prefix union has to be split into the union over the whole blocks
coming strictly before the current one and the union over the first few entries of the current
block.  The lemmas below rewrite the relevant unions as unions over `List.toFinset`.
-/

namespace Work.PL.Shell

open Set Metric Finset
open scoped BigOperators

noncomputable section

variable {N : ℕ}

/-- Union over the `toFinset` of an appended list. -/
theorem iUnion_toFinset_append {α : Type*} [DecidableEq α] {β : Type*} (a b : List α)
    (f : α → Set β) :
    (⋃ x ∈ (a ++ b).toFinset, f x) = (⋃ x ∈ a.toFinset, f x) ∪ (⋃ x ∈ b.toFinset, f x) := by
  ext z
  simp only [Set.mem_iUnion₂, List.mem_toFinset, List.mem_append, Set.mem_union]
  constructor
  · rintro ⟨i, hi | hi, hz⟩
    · exact Or.inl ⟨i, hi, hz⟩
    · exact Or.inr ⟨i, hi, hz⟩
  · rintro (⟨i, hi, hz⟩ | ⟨i, hi, hz⟩)
    · exact ⟨i, Or.inl hi, hz⟩
    · exact ⟨i, Or.inr hi, hz⟩

/-- Union over the `toFinset` of a `flatMap`: the union over the blocks. -/
theorem iUnion_toFinset_flatMap {α γ : Type*} [DecidableEq α] [DecidableEq γ] {β : Type*}
    (M : List α) (G : α → List γ) (f : γ → Set β) :
    (⋃ x ∈ (M.flatMap G).toFinset, f x) = ⋃ p ∈ M.toFinset, ⋃ x ∈ (G p).toFinset, f x := by
  ext z
  simp only [Set.mem_iUnion₂, List.mem_toFinset, List.mem_flatMap]
  constructor
  · rintro ⟨i, ⟨a, ha, hiG⟩, hz⟩
    exact ⟨a, ha, i, hiG, hz⟩
  · rintro ⟨i, hi, j, hjG, hz⟩
    exact ⟨j, ⟨i, hi, hjG⟩, hz⟩

/-- Union over the `toFinset` of a truncated `map`. -/
theorem iUnion_toFinset_take_map {α γ : Type*} [DecidableEq α] [DecidableEq γ] {β : Type*}
    (M : List α) (g : α → γ) (f : γ → Set β) (i : ℕ) :
    (⋃ x ∈ ((M.map g).take i).toFinset, f x) = ⋃ p ∈ (M.take i).toFinset, f (g p) := by
  rw [← List.map_take]
  ext z
  simp only [Set.mem_iUnion₂, List.mem_toFinset, List.mem_map]
  constructor
  · rintro ⟨x, ⟨p, hp, hpx⟩, hz⟩
    exact ⟨p, hp, hpx ▸ hz⟩
  · rintro ⟨p, hp, hz⟩
    exact ⟨g p, ⟨p, hp, rfl⟩, hz⟩

/-- Union over the `toFinset` of a `map` (the untruncated case of
`iUnion_toFinset_take_map`). -/
theorem iUnion_toFinset_map {α γ : Type*} [DecidableEq α] [DecidableEq γ] {β : Type*}
    (M : List α) (g : α → γ) (f : γ → Set β) :
    (⋃ x ∈ (M.map g).toFinset, f x) = ⋃ p ∈ M.toFinset, f (g p) := by
  ext z
  simp only [Set.mem_iUnion₂, List.mem_toFinset, List.mem_map]
  constructor
  · rintro ⟨x, ⟨p, hp, hpx⟩, hz⟩
    exact ⟨p, hp, hpx ▸ hz⟩
  · rintro ⟨p, hp, hz⟩
    exact ⟨g p, ⟨p, hp, rfl⟩, hz⟩

/-- `getD` on a list of pairs, seen through the first components. -/
theorem getD_map_fst {N : ℕ} (l : List (Finset (PL.E N) × Finset (PL.E N))) (j : ℕ)
    (hj : j < l.length) :
    (l.map Prod.fst).getD j ∅ = (l.getD j (∅, ∅)).1 := by
  rw [List.getD_eq_getElem (l.map Prod.fst) ∅ (by simpa using hj),
    List.getD_eq_getElem l (∅, ∅) hj, List.getElem_map]

/-- **The prefix union of a `flatMap`.**  The union of the simplices of the first
`|(L.take k).flatMap G| + j` entries of `L.flatMap G` is the union over the whole blocks `L.take k`
together with the union over the first `j` entries of the block `k`. -/
theorem preUnion_flatMap {α : Type*} [DecidableEq α] (L : List α) (G : α → List (Finset (PL.E N)))
    (F : α → Finset (PL.E N))
    (hGF : ∀ p ∈ L, (⋃ x ∈ (G p).toFinset, PL.simp x) = PL.simp (F p))
    (k : ℕ) (hk : k < L.length) (j : ℕ) (hj : j ≤ (G (L.get ⟨k, hk⟩)).length) :
    preUnion (L.flatMap G) (((L.take k).flatMap G).length + j)
      = preUnion (L.map F) k ∪ preUnion (G (L.get ⟨k, hk⟩)) j := by
  have hdrop : L.drop k = L.get ⟨k, hk⟩ :: L.drop (k + 1) := List.drop_eq_getElem_cons hk
  have hflat : L.flatMap G
      = (L.take k).flatMap G ++ (G (L.get ⟨k, hk⟩) ++ (L.drop (k + 1)).flatMap G) := by
    calc L.flatMap G
        = ((L.take k) ++ (L.drop k)).flatMap G := by rw [List.take_append_drop]
      _ = (L.take k).flatMap G ++ (L.drop k).flatMap G := List.flatMap_append
      _ = (L.take k).flatMap G ++ ((L.get ⟨k, hk⟩ :: L.drop (k + 1)).flatMap G) := by rw [hdrop]
      _ = (L.take k).flatMap G ++ (G (L.get ⟨k, hk⟩) ++ (L.drop (k + 1)).flatMap G) := by
            rw [List.flatMap_cons]
  have htake : (L.flatMap G).take (((L.take k).flatMap G).length + j)
      = (L.take k).flatMap G ++ (G (L.get ⟨k, hk⟩)).take j := by
    rw [hflat, List.take_length_add_append, List.take_append_of_le_length hj]
  have hbound : ((L.take k).flatMap G).length + j ≤ (L.flatMap G).length := by
    rw [hflat, List.length_append]
    have h2 : j ≤ (G (L.get ⟨k, hk⟩) ++ (L.drop (k + 1)).flatMap G).length := by
      rw [List.length_append]; omega
    omega
  rw [preUnion_eq_iUnion_take _ _ hbound, htake, iUnion_toFinset_append,
    preUnion_eq_iUnion_take (L.map F) k (by rw [List.length_map]; exact le_of_lt hk),
    preUnion_eq_iUnion_take (G (L.get ⟨k, hk⟩)) j hj]
  congr 1
  rw [iUnion_toFinset_flatMap, iUnion_toFinset_take_map]
  exact iUnion₂_congr fun p hp =>
    hGF p (List.Sublist.subset (List.take_sublist k L) (List.mem_toFinset.mp hp))

/-! ### Prefix sets of a flag, and the subdivision simplices they span -/

/-- The `k`-th prefix set of a `Nodup` list has exactly `k + 1` elements. -/
theorem sd_iter_prefAt_card {l : List (PL.E N)} (hl : l.Nodup) {k : ℕ} (hk : k < l.length) :
    (prefAt l k).card = k + 1 := by
  unfold prefAt
  rw [List.toFinset_card_of_nodup, List.length_take]
  · omega
  · exact List.Nodup.sublist (List.take_sublist (k + 1) l) hl

/-- Prefix sets are monotone in the index. -/
theorem sd_iter_prefAt_subset_of_le {l : List (PL.E N)} {i j : ℕ} (hij : i ≤ j) :
    prefAt l i ⊆ prefAt l j := by
  intro x hx
  simp only [prefAt, List.mem_toFinset] at hx ⊢
  have hsub : (l.take (i + 1)).Sublist (l.take (j + 1)) := by
    have h : l.take (i + 1) = (l.take (j + 1)).take (i + 1) := by
      rw [List.take_take, min_eq_left (by omega)]
    rw [h]
    exact List.take_sublist _ _
  exact hsub.subset hx

/-- Distinct prefix sets of a `Nodup` list have distinct indices. -/
theorem sd_iter_prefAt_inj {l : List (PL.E N)} (hl : l.Nodup) {i j : ℕ}
    (hi : i < l.length) (hj : j < l.length) (h : prefAt l i = prefAt l j) : i = j := by
  have h1 := sd_iter_prefAt_card hl hi
  have h2 := sd_iter_prefAt_card hl hj
  have hc : i + 1 = j + 1 := by rw [← h1, ← h2, h]
  omega

/-- Membership in `prefixes l`. -/
theorem sd_iter_mem_prefixes_iff {A : Finset (PL.E N)} {l : List (PL.E N)} :
    A ∈ prefixes l ↔ ∃ k < l.length, prefAt l k = A := by
  simp [prefixes, Finset.mem_image, Finset.mem_range, eq_comm]

/-- Every prefix set consists of elements of the list. -/
theorem sd_iter_prefixes_subset_toFinset {A : Finset (PL.E N)} {l : List (PL.E N)}
    (hA : A ∈ prefixes l) : A ⊆ l.toFinset := by
  obtain ⟨k, -, rfl⟩ := sd_iter_mem_prefixes_iff.mp hA
  intro x hx
  simp only [prefAt, List.mem_toFinset] at hx ⊢
  exact List.Sublist.subset (List.take_sublist (k + 1) l) hx

/-- Every prefix set is nonempty. -/
theorem sd_iter_prefixes_nonempty {A : Finset (PL.E N)} {l : List (PL.E N)}
    (hA : A ∈ prefixes l) : A.Nonempty := by
  obtain ⟨k, hk, rfl⟩ := sd_iter_mem_prefixes_iff.mp hA
  rw [prefAt, List.toFinset_nonempty_iff]
  intro h
  have hlen := congrArg List.length h
  rw [List.length_take, min_eq_left (Nat.succ_le_of_lt hk), List.length_nil] at hlen
  exact Nat.succ_ne_zero k hlen

/-- The centroid of a nonempty set of points lies in the simplex it spans. -/
theorem sd_iter_bary_mem_simp {S : Finset (PL.E N)} (hS : S.Nonempty) :
    bary S ∈ PL.simp S := by
  rw [PL.simp, Finset.mem_convexHull']
  have hcard : (S.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Finset.card_ne_zero.mpr hS)
  refine ⟨fun _ => (S.card : ℝ)⁻¹, fun y hy => by positivity, ?_, ?_⟩
  · rw [Finset.sum_const, nsmul_eq_mul, mul_inv_cancel₀ hcard]
  · show (∑ y ∈ S, (S.card : ℝ)⁻¹ • y) = bary S
    rw [bary, Finset.smul_sum]

/-- The subdivision simplices of a flag `l` enumerating `σ`: as many as `σ` has elements,
affinely independent, and contained in `simp σ`. -/
theorem sd_iter_prefixes_image_spec {σ : Finset (PL.E N)}
    (hσ : AffineIndependent ℝ ((↑) : σ → PL.E N)) {l : List (PL.E N)}
    (hl : l.Nodup) (hvs : l.toFinset = σ) :
    ((prefixes l).image bary).card = σ.card ∧
    AffineIndependent ℝ ((↑) : ((prefixes l).image bary) → PL.E N) ∧
    PL.simp ((prefixes l).image bary) ⊆ PL.simp σ := by
  classical
  have hsub : ∀ {A : Finset (PL.E N)}, A ∈ prefixes l → A ⊆ σ := by
    intro A hA
    rw [← hvs]
    exact sd_iter_prefixes_subset_toFinset hA
  have hchain : ∀ A ∈ prefixes l, ∀ B ∈ prefixes l, A ⊆ B ∨ B ⊆ A := by
    intro A hA B hB
    obtain ⟨i, hi, hAi⟩ := sd_iter_mem_prefixes_iff.mp hA
    obtain ⟨j, hj, hBj⟩ := sd_iter_mem_prefixes_iff.mp hB
    rcases le_total i j with h | h
    · exact Or.inl (by rw [← hAi, ← hBj]; exact sd_iter_prefAt_subset_of_le h)
    · exact Or.inr (by rw [← hAi, ← hBj]; exact sd_iter_prefAt_subset_of_le h)
  have hbary_inj : Set.InjOn bary (↑(prefixes l) : Set (Finset (PL.E N))) := by
    intro A hA B hB hAB
    obtain ⟨i, hi, rfl⟩ := sd_iter_mem_prefixes_iff.mp hA
    obtain ⟨j, hj, rfl⟩ := sd_iter_mem_prefixes_iff.mp hB
    have hi_mem : prefAt l i ∈ prefixes l := sd_iter_mem_prefixes_iff.mpr ⟨i, hi, rfl⟩
    have hj_mem : prefAt l j ∈ prefixes l := sd_iter_mem_prefixes_iff.mpr ⟨j, hj, rfl⟩
    have hij : i = j :=
      sd_iter_prefAt_inj hl hi hj
        (bary_inj hσ (sd_iter_prefixes_nonempty hi_mem) (sd_iter_prefixes_nonempty hj_mem)
          (hsub hi_mem) (hsub hj_mem) hAB)
    rw [hij]
  have hcard : (prefixes l).card = l.length := by
    rw [prefixes, Finset.card_image_of_injOn]
    · simp
    · intro i hi j hj h
      exact sd_iter_prefAt_inj hl (Finset.mem_range.mp hi) (Finset.mem_range.mp hj) h
  refine ⟨?_, ?_, ?_⟩
  · rw [Finset.card_image_of_injOn hbary_inj, hcard, ← List.toFinset_card_of_nodup hl, hvs]
  · exact affineIndependent_bary_image (C := prefixes l) hσ
      (fun A hA => ⟨sd_iter_prefixes_nonempty hA, hsub hA⟩) hchain
  · rw [PL.simp, PL.simp]
    refine convexHull_min ?_ (convex_convexHull ℝ _)
    intro z hz
    rw [Finset.mem_coe] at hz
    obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hz
    exact convexHull_mono (fun x hx => hsub hS hx) (sd_iter_bary_mem_simp (sd_iter_prefixes_nonempty hS))

/-- Every element of `sd1Data σ T` has first component of cardinality `σ.card`, affinely
independent, and with simplex contained in `simp σ`. -/
theorem sd_iter_sd1Data_elem_spec {N : ℕ} {σ T : Finset (PL.E N)}
    (hσ : AffineIndependent ℝ ((↑) : σ → PL.E N)) :
    ∀ i (hi : i < (sd1Data σ T).length),
      ((sd1Data σ T).get ⟨i, hi⟩).1.card = σ.card ∧
      AffineIndependent ℝ ((↑) : ((sd1Data σ T).get ⟨i, hi⟩).1 → PL.E N) ∧
      PL.simp ((sd1Data σ T).get ⟨i, hi⟩).1 ⊆ PL.simp σ := by
  intro i hi
  have hlen : (sd1Data σ T).length = (flagEnum (subList σ T)).length := by
    simp only [sd1Data, List.length_map]
  have hi' : i < (flagEnum (subList σ T)).length := hlen ▸ hi
  have hget : (sd1Data σ T).get ⟨i, hi⟩ =
      ((prefixes ((flagEnum (subList σ T)).get ⟨i, hi'⟩)).image bary,
        splitOf σ T (subRank σ T) ((flagEnum (subList σ T)).get ⟨i, hi'⟩)) := by
    simp only [sd1Data, List.get_eq_getElem, List.getElem_map]
  rw [hget]
  set l : List (PL.E N) := (flagEnum (subList σ T)).get ⟨i, hi'⟩ with hl
  have hlmem : l ∈ flagEnum (subList σ T) := by rw [hl]; exact List.get_mem _ _
  have hperm : l.Perm (subList σ T) := flagEnum_mem.mp hlmem
  obtain ⟨hsubnod, hsubto, -, -⟩ := subList_spec (σ := σ) (T := T)
  have hlnod : l.Nodup := hperm.nodup_iff.mpr hsubnod
  have hlto : l.toFinset = σ := by
    rw [List.toFinset_eq_of_perm _ _ hperm, hsubto]
  exact sd_iter_prefixes_image_spec hσ hlnod hlto

end

end Work.PL.Shell


