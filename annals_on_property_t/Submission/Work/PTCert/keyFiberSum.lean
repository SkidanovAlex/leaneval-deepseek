import Mathlib
import Submission.Work.PTCert.labelData

namespace Work.PTCert

/-! Guidance from the project lead (the requester): this is the per-label key sum in the proof of
`LabelIdentity` (`Submission/Work/PTCert/labelIdentity.lean`).  Read
`Submission/Work/PTCert/labelData.lean` first: it contains the definitions and the `ClassSem` facts
`klist_flatten_perm`, `klist_gcls`, `klist_length`, `gcls_lt`, `ngE_lt_all`, `keyOf_inj`,
`mem_allKeys`, which are what you need.

The proof below follows the intended route.  The sum on the left is reindexed over the *set* of keys
`{keyOf r g | r < 18, g < ngE r}` (`Finset.sum_image`, injectivity of the key), which by
`mem_allKeys` is the set of members of `allKeys ngL`; filtering by the label `gcls · = l` gives
exactly the members of `klist[l]` (`mem_klist_getD`), and `klist[l]` has no repeated entries
(`klist_getD_nodup`, from `klist.flatten.Perm (allKeys ngL)` and the fact -- `allKeys_nodup` -- that
the blocks `2048 r + g` with `g < ngE r < 2048` are pairwise disjoint).  The last step is
`List.sum_toFinset`.

Do NOT unfold the data tables (`eM`, `canonW`, …) and do not use `decide` on them. -/

open Submission.PTCert Submission.PTCert.G
open scoped BigOperators

set_option maxRecDepth 5000

namespace KeyFiber

/-- **Injectivity of the key** on the index set `{(r, g) | r < 18, g < ngE r}` of the certificate. -/
theorem keyFiberInj :
    Function.Injective (fun t : Σ r : Fin 18, Fin (ngE r.1) => keyOf t.1.1 t.2.1) := by
  rintro ⟨r, g⟩ ⟨r', g'⟩ h
  obtain ⟨e1, e2⟩ := LabelData.keyOf_inj r.2 r'.2 g.2 g'.2 h
  have h1 : r = r' := Fin.ext e1
  subst h1
  have h2 : g = g' := Fin.ext e2
  subst h2
  rfl

/-- Membership in the image of the key map over the index set of the certificate. -/
theorem memKeyImage (k : ℕ) :
    k ∈ (Finset.univ : Finset (Σ r : Fin 18, Fin (ngE r.1))).image
        (fun t => keyOf t.1.1 t.2.1)
      ↔ ∃ r < 18, ∃ g < ngE r, k = keyOf r g := by
  rw [Finset.mem_image]
  constructor
  · rintro ⟨⟨r, g⟩, -, h⟩
    exact ⟨r.1, r.2, g.1, g.2, h.symm⟩
  · rintro ⟨r, hr, g, hg, h⟩
    exact ⟨⟨⟨r, hr⟩, ⟨g, hg⟩⟩, Finset.mem_univ _, h.symm⟩

/-- `allKeys ngL` has no repeated entries: the blocks `2048 r + g` (`g < ngE r < 2048`) of the
various rows `r < 18` are pairwise disjoint. -/
theorem allKeys_nodup (hC : ClassSem) : (allKeys D.ngL).Nodup := by
  have hlen : D.ngL.length = 18 := LabelData.ngL_length hC
  rw [allKeys, hlen]
  rw [List.nodup_flatMap]
  refine ⟨?_, ?_⟩
  · intro r hr
    rw [List.mem_range] at hr
    refine List.Nodup.map ?_ List.nodup_range
    intro a b hab
    dsimp only at hab
    omega
  · refine List.Pairwise.imp_of_mem ?_ List.pairwise_lt_range
    intro r r' hr hr' hlt
    rw [List.mem_range] at hr hr'
    intro a ha ha'
    simp only [List.mem_map, List.mem_range] at ha ha'
    obtain ⟨g, hg, rfl⟩ := ha
    obtain ⟨g', hg', heq⟩ := ha'
    obtain ⟨e1, -⟩ := LabelData.keyOf_inj hr hr' hg hg' heq.symm
    omega

/-- The class list `klist[l]` has no repeated entries. -/
theorem klist_getD_nodup (hC : ClassSem) (l : ℕ) : (klist.getD l []).Nodup := by
  have hall : (allKeys D.ngL).Nodup := allKeys_nodup hC
  have hfl : klist.flatten.Nodup := (LabelData.klist_flatten_perm hC).nodup_iff.mpr hall
  rw [List.nodup_flatten] at hfl
  obtain ⟨hparts, -⟩ := hfl
  by_cases hl : l < klist.length
  · exact hparts _ (by rw [List.getD_eq_getElem klist [] hl]; exact List.getElem_mem hl)
  · have hnil : klist.getD l [] = [] := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
      rfl
    rw [hnil]
    exact List.nodup_nil

/-- **Characterisation of the members of `klist[l]`**: they are exactly the keys `keyOf r g`
(`r < 18`, `g < ngE r`) of label `l`. -/
theorem mem_klist_getD (hC : ClassSem) (l k : ℕ) :
    k ∈ klist.getD l [] ↔ (∃ r < 18, ∃ g < ngE r, k = keyOf r g) ∧ gcls k = l := by
  constructor
  · intro hk
    have hl_lt : l < klist.length := by
      by_contra h
      have hnil : klist.getD l [] = [] := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
        rfl
      rw [hnil] at hk
      exact absurd hk List.not_mem_nil
    have hl_ncls : l < ncls := by rw [← LabelData.klist_length hC]; exact hl_lt
    have hkfl : k ∈ klist.flatten := by
      refine List.mem_flatten.mpr ⟨klist.getD l [], ?_, hk⟩
      rw [List.getD_eq_getElem klist [] hl_lt]
      exact List.getElem_mem hl_lt
    refine ⟨?_, ?_⟩
    · exact (LabelData.mem_allKeys hC).mp ((LabelData.klist_flatten_perm hC).mem_iff.mp hkfl)
    · exact LabelData.klist_gcls hC l hl_ncls k hk
  · rintro ⟨⟨r, hr, g, hg, rfl⟩, hgl⟩
    have hmem : keyOf r g ∈ klist.flatten :=
      (LabelData.klist_flatten_perm hC).mem_iff.mpr
        ((LabelData.mem_allKeys hC).mpr ⟨r, hr, g, hg, rfl⟩)
    obtain ⟨s, hs, hks⟩ := List.mem_flatten.mp hmem
    obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp hs
    have hks' : keyOf r g ∈ klist[i] := hget ▸ hks
    have hgetD : klist.getD i [] = klist[i] := List.getD_eq_getElem klist [] hi
    have hgl2 : gcls (keyOf r g) = i := by
      refine LabelData.klist_gcls hC i ?_ (keyOf r g) ?_
      · rw [← LabelData.klist_length hC]; exact hi
      · rw [hgetD]; exact hks'
    rw [show l = i from by omega, hgetD]
    exact hks'

end KeyFiber

/-- The aggregate element of `Work.PTCert.LabelData.TIdx` restricted to the group keys, as a set. -/
theorem keyFiberSum (hC : ClassSem) (v : ℕ → ℝ) (l : ℕ) :
    (∑ t : Σ r : Fin 18, Fin (ngE r.1),
        (if gcls (keyOf t.1.1 t.2.1) = l then v (keyOf t.1.1 t.2.1) else 0))
      = ((klist.getD l []).map v).sum := by
  have hinj : Set.InjOn (fun t : Σ r : Fin 18, Fin (ngE r.1) => keyOf t.1.1 t.2.1)
      ↑(Finset.univ : Finset (Σ r : Fin 18, Fin (ngE r.1))) :=
    fun t _ t' _ h => KeyFiber.keyFiberInj h
  have h0 : (∑ t : Σ r : Fin 18, Fin (ngE r.1),
        (if gcls (keyOf t.1.1 t.2.1) = l then v (keyOf t.1.1 t.2.1) else 0))
      = ∑ t : Σ r : Fin 18, Fin (ngE r.1),
          (fun k => if gcls k = l then v k else 0) (keyOf t.1.1 t.2.1) := rfl
  have hsum : (∑ t : Σ r : Fin 18, Fin (ngE r.1),
          (fun k => if gcls k = l then v k else 0) (keyOf t.1.1 t.2.1))
      = ∑ k ∈ (Finset.univ : Finset (Σ r : Fin 18, Fin (ngE r.1))).image
            (fun t => keyOf t.1.1 t.2.1),
          (if gcls k = l then v k else 0) :=
    (Finset.sum_image (s := (Finset.univ : Finset (Σ r : Fin 18, Fin (ngE r.1))))
      (g := fun t => keyOf t.1.1 t.2.1) (f := fun k => if gcls k = l then v k else 0) hinj).symm
  have hset : (((Finset.univ : Finset (Σ r : Fin 18, Fin (ngE r.1))).image
            (fun t => keyOf t.1.1 t.2.1)).filter (fun k => gcls k = l))
      = (klist.getD l []).toFinset := by
    ext k
    rw [Finset.mem_filter, List.mem_toFinset, KeyFiber.memKeyImage]
    exact (KeyFiber.mem_klist_getD hC l k).symm
  rw [h0]
  rw [hsum]
  rw [← Finset.sum_filter]
  rw [hset]
  exact List.sum_toFinset v (KeyFiber.klist_getD_nodup hC l)

end Work.PTCert
