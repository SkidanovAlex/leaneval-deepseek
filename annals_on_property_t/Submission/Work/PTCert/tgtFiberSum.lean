import Mathlib
import Submission.Work.PTCert.labelData

namespace Work.PTCert

/-! Guidance from the project lead (the requester): this is the per-label target sum in the proof of
`LabelIdentity` (`Submission/Work/PTCert/labelIdentity.lean`).  Read
`Submission/Work/PTCert/labelData.lean` first (`tlist_flatten_perm`, `tlist_tcls`, `tlist_length`).

Intended route: `tlist.flatten.Perm (List.range 6561)`, so every `p < 6561` lies in `tlist.flatten`,
hence in one of the parts `tlist.getD c []` (`List.mem_flatten`); by `tlist_tcls` that part index `c`
is exactly `tcls p`.  Therefore
`{p : Fin 6561 | tcls p = l} = (tlist.getD l []).toFinset` (for `l ≥ ncls` both sides are empty, using
`tlist_length`): the `⊆` direction uses the permutation and `tlist_tcls`, the `⊇` direction uses
`tlist_tcls` in the other direction plus `tlist.getD l [] = []` when `l ≥ ncls`.  Then
`((tlist.getD l []).map w).sum = ∑ p ∈ (tlist.getD l []).toFinset, w p` by `List.sum_toFinset`, which
needs `Nodup (tlist.getD l [])`: from `List.Perm.nodup_iff` with `(List.range 6561).Nodup` and
`List.nodup_flatten` (a sublist of a nodup list is nodup).  Finish with `Finset.sum_filter` /
`Finset.sum_congr`.

Do NOT unfold the data tables and do not use `decide` on them. -/

open Submission.PTCert Submission.PTCert.G
open scoped BigOperators

theorem tgtFiberSum (hC : ClassSem) (w : ℕ → ℝ) (l : ℕ) :
    (∑ p : Fin 6561, (if tcls p.1 = l then w p.1 else 0))
      = ((tlist.getD l []).map w).sum := by
  have hlen : tlist.length = ncls := LabelData.tlist_length hC
  have hperm : tlist.flatten.Perm (List.range 6561) := LabelData.tlist_flatten_perm hC
  have hpart : ∀ c < ncls, ∀ p ∈ tlist.getD c [], tcls p = c := LabelData.tlist_tcls hC
  -- The part `tlist.getD l []` has no repeated element: `tlist.flatten` is a permutation of
  -- `List.range 6561`, which is `Nodup`, and `Nodup.flatten` says each part is `Nodup`.
  have hnodup : (tlist.getD l []).Nodup := by
    have hfl : tlist.flatten.Nodup := hperm.nodup_iff.mpr (List.nodup_range)
    have hall : ∀ a ∈ tlist, a.Nodup := (List.nodup_flatten.mp hfl).1
    by_cases hl : l < tlist.length
    · rw [List.getD_eq_getElem tlist [] hl]
      exact hall _ (List.getElem_mem hl)
    · rw [List.getD_eq_default (l := tlist) (d := ([] : List ℕ)) (n := l) (by omega)]
      exact List.nodup_nil
  -- Characterisation of the part: `{x < 6561 | tcls x = l} = (tlist.getD l []).toFinset`.
  have hset : (Finset.range 6561).filter (fun x => tcls x = l) = (tlist.getD l []).toFinset := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_range, List.mem_toFinset]
    constructor
    · -- `x < 6561` and `tcls x = l` ⇒ `x` lies in the part of index `tcls x = l`.
      rintro ⟨hx, hxl⟩
      have hxmem : x ∈ tlist.flatten := hperm.mem_iff.mpr (List.mem_range.mpr hx)
      obtain ⟨t, ht, hxt⟩ := List.mem_flatten.mp hxmem
      obtain ⟨n, hn⟩ := List.mem_iff_get.mp ht
      have hnlt : n.1 < ncls := lt_of_lt_of_eq n.2 hlen
      have hget : tlist.getD n.1 [] = t := by
        rw [List.getD_eq_getElem tlist [] n.2]; exact hn
      have hx' : x ∈ tlist.getD n.1 [] := by rw [hget]; exact hxt
      have htcls : tcls x = n.1 := hpart n.1 hnlt x hx'
      have hln : l = n.1 := by rw [← hxl, htcls]
      rwa [hln]
    · -- Conversely, the part of index `l` consists of elements `< 6561` of label `l`
      -- (and is empty when `l ≥ ncls`).
      intro hx
      have hl : l < tlist.length := by
        by_contra h
        rw [List.getD_eq_default (l := tlist) (d := ([] : List ℕ)) (n := l) (by omega)] at hx
        exact List.not_mem_nil hx
      have hlncls : l < ncls := lt_of_lt_of_eq hl hlen
      have hmem : x ∈ tlist.flatten := by
        rw [List.mem_flatten]
        exact ⟨tlist.getD l [],
          by rw [List.getD_eq_getElem tlist [] hl]; exact List.getElem_mem hl, hx⟩
      have hxrange : x ∈ List.range 6561 := hperm.mem_iff.mp hmem
      exact ⟨List.mem_range.mp hxrange, hpart l hlncls x hx⟩
  rw [Fin.sum_univ_eq_sum_range (fun x => if tcls x = l then w x else 0) 6561]
  rw [← Finset.sum_filter]
  rw [hset]
  exact List.sum_toFinset w hnodup

end Work.PTCert
