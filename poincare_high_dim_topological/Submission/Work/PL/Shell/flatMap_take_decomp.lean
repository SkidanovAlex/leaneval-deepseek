import Mathlib

namespace Work.PL.Shell

/-- Decomposition of a list `L.flatMap G` at an index `m` lying in the block
`G (L.get ⟨k, hk⟩)`: the index splits as `m = k-prefix length + j`, the `m`-th
element of the flattened list is the `j`-th element of that block, and the
`m`-prefix of the flattened list is the flattened `k`-prefix followed by the
`j`-prefix of the block. -/
theorem flatMap_take_decomp {α β : Type*} (L : List α) (G : α → List β) {m : ℕ}
    (hm : m < (L.flatMap G).length) :
    ∃ (k : ℕ) (hk : k < L.length) (j : ℕ) (hj : j < (G (L.get ⟨k, hk⟩)).length),
      m = ((L.take k).flatMap G).length + j ∧
      (L.flatMap G).get ⟨m, hm⟩ = (G (L.get ⟨k, hk⟩)).get ⟨j, hj⟩ ∧
      (L.flatMap G).take m = (L.take k).flatMap G ++ (G (L.get ⟨k, hk⟩)).take j := by
  induction L generalizing m with
  | nil => simp at hm
  | cons a t ih =>
    by_cases hm1 : m < (G a).length
    · refine ⟨0, by simp, m, hm1, ?_, ?_, ?_⟩
      · simp
      · simp only [List.get_eq_getElem, List.flatMap_cons, List.getElem_append_left hm1]
        simp [List.getElem_cons_zero]
      · simp [List.flatMap_cons, List.take_append_of_le_length (le_of_lt hm1),
          List.get_eq_getElem, List.getElem_cons_zero]
    · have hle : (G a).length ≤ m := not_lt.mp hm1
      have hm' : m - (G a).length < (List.flatMap G t).length := by
        rw [List.flatMap_cons, List.length_append] at hm; omega
      obtain ⟨k', hk', j, hj', h1, h2, h3⟩ := ih hm'
      have hk : k' + 1 < (a :: t).length := by simpa using hk'
      have hget : (a :: t).get ⟨k' + 1, hk⟩ = t.get ⟨k', hk'⟩ := by
        simp [List.get_eq_getElem, List.getElem_cons_succ]
      refine ⟨k' + 1, hk, j, ?_, ?_, ?_, ?_⟩
      · rw [hget]; exact hj'
      · rw [List.take_succ_cons, List.flatMap_cons, List.length_append]; omega
      · simp only [List.get_eq_getElem, List.flatMap_cons]
        rw [List.getElem_append_right hle]; rw [List.get_eq_getElem] at h2; rw [h2]
        simp [List.get_eq_getElem, List.getElem_cons_succ]
      · simp only [List.take_succ_cons, List.flatMap_cons]
        rw [List.take_append, List.take_of_length_le hle, hget, h3, List.append_assoc]

end Work.PL.Shell
