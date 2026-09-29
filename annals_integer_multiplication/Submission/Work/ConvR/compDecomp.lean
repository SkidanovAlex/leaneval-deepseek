import Mathlib

namespace Work.ConvR

/-- Decomposition of `List.range n` at an element `a < n`:
`range n = range a ++ a :: range' (a+1) (n-a-1)`. -/
lemma rangeDecomp (a n : ℕ) (h : a < n) :
    List.range n = List.range a ++ a :: List.range' (a + 1) (n - a - 1) := by
  have h1 : List.range' (0:ℕ) n = List.range' 0 a ++ List.range' a (n - a) := by
    nth_rewrite 1 [show n = a + (n - a) by omega]
    rw [← List.range'_append]
    simp
  rw [List.range_eq_range' (n := n), List.range_eq_range' (n := a), h1]
  have htail : List.range' a (n - a) = a :: List.range' (a + 1) (n - a - 1) := by
    rw [← List.range'_succ (s := a) (n := n - a - 1) (step := 1)]
    congr 1
    omega
  rw [htail]

/-- The number of elements of `range a` avoiding `u` is `a` minus the number of
elements of `range a` lying in `u`. -/
lemma lengthFilterNot (u : List ℕ) (a : ℕ) :
    ((List.range a).filter (fun i => i ∉ u)).length
      = a - ((List.range a).filter (fun i => i ∈ u)).length := by
  have h := List.length_eq_length_filter_add (l := List.range a) (f := fun i => decide (i ∈ u))
  rw [List.length_range] at h
  have h2 : (List.filter (fun x => !decide (x ∈ u)) (List.range a))
      = (List.range a).filter (fun x => x ∉ u) := by
    apply List.filter_congr
    intro x _
    exact decide_not.symm
  rw [h2] at h
  omega

/-- Counting the elements of `u` that are `< a` by intersecting `range a` with `u`
(needs `u.Nodup`, so that each value is counted at most once). -/
lemma lengthFilterMemRange (u : List ℕ) (hnd : u.Nodup) (a : ℕ) :
    ((List.range a).filter (fun i => i ∈ u)).length = (u.filter (fun i => i < a)).length := by
  rw [← List.toFinset_card_of_nodup (List.nodup_range.filter _),
      ← List.toFinset_card_of_nodup (hnd.filter _)]
  rw [List.toFinset_filter, List.toFinset_filter, List.toFinset_range]
  congr 1
  ext x
  simp [Finset.mem_filter, List.mem_toFinset, and_comm]

/-- Every element of `List.range' (a+1) m` is strictly greater than `a`. -/
lemma range'_mem_gt (a m i : ℕ) (h : i ∈ List.range' (a + 1) m) : a < i := by
  rw [List.mem_range'] at h
  obtain ⟨j, _, rfl⟩ := h
  omega

theorem compDecomp (u : List ℕ) (a n : ℕ) (hnd : u.Nodup) (hlt : ∀ i ∈ u, i < n)
    (ha : a < n) (han : a ∉ u) :
    ∃ ca cr : List ℕ,
      (List.range n).filter (fun i => i ∉ u) = ca ++ a :: cr ∧
      ca.length = a - (u.filter (fun i => i < a)).length ∧
      (List.range n).filter (fun i => i ∉ (u ++ [a])) = ca ++ cr := by
  refine ⟨(List.range a).filter (fun i => i ∉ u),
          (List.range' (a + 1) (n - a - 1)).filter (fun i => i ∉ u), ?_, ?_, ?_⟩
  · rw [rangeDecomp a n ha, List.filter_append]
    have h : (a :: List.range' (a + 1) (n - a - 1)).filter (fun i => i ∉ u)
        = a :: (List.range' (a + 1) (n - a - 1)).filter (fun i => i ∉ u) := by
      simp [han]
    rw [h]
  · rw [lengthFilterNot, lengthFilterMemRange u hnd]
  · rw [rangeDecomp a n ha, List.filter_append]
    have h1 : (List.range a).filter (fun i => i ∉ (u ++ [a]))
        = (List.range a).filter (fun i => i ∉ u) := by
      apply List.filter_congr
      intro i hi
      simp only [List.mem_range] at hi
      simp [List.mem_append, show i ≠ a by omega]
    have h2 : (a :: List.range' (a + 1) (n - a - 1)).filter (fun i => i ∉ (u ++ [a]))
        = (List.range' (a + 1) (n - a - 1)).filter (fun i => i ∉ u) := by
      rw [List.filter_cons_of_neg (by simp [List.mem_append])]
      apply List.filter_congr
      intro i hi
      have hai : a < i := range'_mem_gt a (n - a - 1) i hi
      simp [List.mem_append, show i ≠ a by omega]
    rw [h1, h2]

end Work.ConvR
