import Mathlib
import Submission.Work.ConvR.permDefs

/-!
# Positions of `posList` are valid indices

For `t` a permutation of `List.range n` (so `t` has length `n` and consists exactly of the values
`0, …, n-1`), every entry of `posList t` is `< n`.

Mathematically: the `j`-th entry is `j + t_j - #{l < j : t_l < t_j}`, and

* `t_j - #{l < j : t_l < t_j} = #{l ≥ j+1 : t_l < t_j} ≤ n - j - 1`,

the middle equality because among the values `0, …, t_j - 1` there are `t_j` of them, `#{l < j : t_l < t_j}`
of which occur in `t.take j` (all elements of `t` are distinct and `< n`), hence the remaining ones
occur in `t.drop (j+1)`; the inequality because `t.drop (j+1)` has `n - j - 1` elements.
-/

set_option autoImplicit false

namespace Work.ConvR

/-- In a list that is a permutation of `List.range n`, exactly `v` entries are `< v` (for `v ≤ n`). -/
lemma filter_lt_length_perm {t : List ℕ} {n v : ℕ} (h : t.Perm (List.range n)) (hv : v ≤ n) :
    (t.filter (fun i => i < v)).length = v := by
  have htmem : ∀ x, x ∈ t ↔ x < n := fun x => h.mem_iff.trans List.mem_range
  have hnod : t.Nodup := h.nodup_iff.mpr List.nodup_range
  have hcard := List.toFinset_card_of_nodup (hnod.filter (fun i => i < v))
  rw [List.toFinset_filter] at hcard
  rw [← hcard]
  have hset : {x ∈ t.toFinset | decide (x < v) = true}
      = (Finset.range n).filter (fun x => x < v) := by
    ext x
    simp only [Finset.mem_filter, List.mem_toFinset, Finset.mem_range, decide_eq_true_iff]
    rw [htmem x]
  rw [hset]
  have h2 : (Finset.range n).filter (fun x => x < v) = Finset.range v := by
    ext x; simp only [Finset.mem_filter, Finset.mem_range]; omega
  rw [h2, Finset.card_range]

lemma posList_lt_aux (t : List ℕ) (n : ℕ) (htlen : t.length = n)
    (htperm : t.Perm (List.range n)) : ∀ p ∈ posList t, p < n := by
  intro p hp
  have htmem : ∀ x, x ∈ t ↔ x < n := fun x => htperm.mem_iff.trans List.mem_range
  rw [posList, List.mem_map] at hp
  obtain ⟨j, hj, hpj⟩ := hp
  rw [List.mem_range] at hj
  rw [← hpj]
  set v := t.getD j 0 with hv
  have hveq : v = t[j] := by rw [hv, List.getD_eq_getElem t 0 hj]
  have hvmem : v ∈ t := by rw [hveq]; exact List.getElem_mem hj
  have hcount : (t.filter (fun i => i < v)).length = v :=
    filter_lt_length_perm htperm (le_of_lt ((htmem v).mp hvmem))
  have hsplit : (t.filter (fun i => i < v)).length
      = ((t.take j).filter (fun i => i < v)).length
        + ((t.drop j).filter (fun i => i < v)).length := by
    conv_lhs => rw [← List.take_append_drop j t]
    rw [List.filter_append, List.length_append]
  have hdrop : t.drop j = t[j] :: t.drop (j + 1) := List.drop_eq_getElem_cons hj
  have hBeq : ((t.drop j).filter (fun i => i < v)).length
      = ((t.drop (j + 1)).filter (fun i => i < v)).length := by
    rw [hdrop, List.filter_cons_of_neg]
    simp [hveq]
  have hDle : ((t.drop (j + 1)).filter (fun i => i < v)).length ≤ n - j - 1 := by
    calc ((t.drop (j + 1)).filter (fun i => i < v)).length
        ≤ (t.drop (j + 1)).length := List.length_filter_le _ _
      _ = t.length - (j + 1) := List.length_drop
      _ = n - j - 1 := by rw [htlen]; omega
  have hjlt : j < n := by rw [← htlen]; exact hj
  omega

theorem posList_lt (σ : List ℕ) (n : ℕ) (hσ : σ.length = n) (hperm : σ.Perm (List.range n)) :
    ∀ p ∈ posList σ.reverse, p < n := fun p hp =>
  posList_lt_aux σ.reverse n (by simpa using hσ) ((List.reverse_perm σ).trans hperm) p hp

end Work.ConvR
