import Mathlib

namespace Work.Transform

/-- Length of a flattened matrix: if every row of `w` has length `r`, then `w.flatten` has
length `w.length * r`. -/
private lemma flatten_length_aux {α : Type} (r : ℕ) :
    ∀ (w : List (List α)), (∀ a < w.length, (w.getD a []).length = r) →
      w.flatten.length = w.length * r := by
  intro w
  induction w with
  | nil => simp
  | cons h t ih =>
      intro hrow
      have hh : h.length = r := by simpa using hrow 0 (by simp)
      have ht : ∀ a < t.length, (t.getD a []).length = r := by
        intro a ha
        have hlt : a + 1 < (h :: t).length := by simpa using Nat.succ_lt_succ ha
        have := hrow (a + 1) hlt
        simpa using this
      rw [List.flatten_cons, List.length_append, ih ht, hh, List.length_cons]
      rw [Nat.succ_mul]
      omega

/-- Indexing a flattened matrix whose rows all have length `r`: for `i < w.length * r`, the
`i`-th entry of `w.flatten` is the entry `i % r` of row `i / r`. -/
private lemma flatten_getD_aux {α : Type} (d : α) (r : ℕ) :
    ∀ (w : List (List α)), (∀ a < w.length, (w.getD a []).length = r) →
      ∀ i, i < w.length * r →
        w.flatten.getD i d = (w.getD (i / r) []).getD (i % r) d := by
  intro w
  induction w with
  | nil => intro _ i hi; simp at hi
  | cons h t ih =>
      intro hrow i hi
      have hh : h.length = r := by simpa using hrow 0 (by simp)
      have ht : ∀ a < t.length, (t.getD a []).length = r := by
        intro a ha
        have hlt : a + 1 < (h :: t).length := by simpa using Nat.succ_lt_succ ha
        have := hrow (a + 1) hlt
        simpa using this
      by_cases hr : r = 0
      · subst hr
        simp at hi
      · have hr' : 0 < r := Nat.pos_of_ne_zero hr
        rw [List.flatten_cons]
        by_cases hi1 : i < h.length
        · -- the index falls inside the first row
          have hir : i < r := by rw [← hh]; exact hi1
          have hd0 : i / r = 0 := Nat.div_eq_of_lt hir
          have hm0 : i % r = i := Nat.mod_eq_of_lt hir
          rw [List.getD_append h t.flatten d i hi1, hd0, hm0, List.getD_cons_zero]
        · -- the index falls in the remaining rows
          have hle : h.length ≤ i := Nat.le_of_not_lt hi1
          obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le hle
          have hjlt : j < t.length * r := by
            have h1 : i < (t.length + 1) * r := by simpa using hi
            rw [hj, hh] at h1
            have h2 : (t.length + 1) * r = t.length * r + r := by
              rw [Nat.add_mul, Nat.one_mul]
            rw [h2] at h1
            omega
          have hL : (h ++ t.flatten).getD i d = t.flatten.getD j d := by
            rw [hj, List.getD_append_right h t.flatten d (h.length + j) (Nat.le_add_right _ _)]
            simp
          have hkey : r + j = j + r * 1 := by rw [Nat.mul_one, Nat.add_comm]
          have hdiv : i / r = j / r + 1 := by
            rw [hj, hh, hkey, Nat.add_mul_div_left j 1 hr']
          have hmod : i % r = j % r := by
            rw [hj, hh, hkey, Nat.add_mul_mod_self_left]
          have hR : ((h :: t).getD (i / r) []).getD (i % r) d =
              (t.getD (j / r) []).getD (j % r) d := by
            rw [hdiv, hmod, List.getD_cons_succ]
          rw [hL, hR]
          exact ih ht j hjlt

/-- Indexing a flattened `M × r` matrix: if `w` has `M` rows, each of length `r`, then
`w.flatten` has length `M * r` and its `i`-th entry is the entry `i % r` of its row `i / r`.
Guidance: keep every auxiliary lemma `private` (modules written in parallel in the same
`Work.Transform` namespace must remain importable together). -/
theorem flattenIdx {α : Type} (d : α) (w : List (List α)) (M r : ℕ)
    (hlen : w.length = M) (hrow : ∀ a < M, (w.getD a []).length = r) :
    w.flatten.length = M * r ∧
      ∀ i < M * r, w.flatten.getD i d = (w.getD (i / r) []).getD (i % r) d := by
  have hrow' : ∀ a < w.length, (w.getD a []).length = r :=
    fun a ha => hrow a (hlen ▸ ha)
  refine ⟨?_, ?_⟩
  · rw [flatten_length_aux r w hrow', hlen]
  · intro i hi
    exact flatten_getD_aux d r w hrow' i (by rw [← hlen] at hi; exact hi)

end Work.Transform
