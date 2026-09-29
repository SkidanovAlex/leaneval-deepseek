import Mathlib
import Submission.Work.Layout.AA.PureDefs

namespace Work.Layout.AA

/-- Reading a list of length `n` through its own indices recovers the list. -/
lemma range_map_getD {α : Type*} (l : List α) (d : α) :
    (List.range l.length).map (fun i => l.getD i d) = l := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map]
    have hf : ((fun i => (a :: t).getD i d) ∘ Nat.succ) = (fun i => t.getD i d) := by
      funext i
      simp [Function.comp_apply]
    rw [hf, ih]
    rfl

/-- Splitting `List.range (m * C)` into `m` blocks of `C` consecutive indices. -/
lemma flatMap_range_mul {α : Type*} (m C : ℕ) (g : ℕ → α) :
    (List.range m).flatMap (fun j => (List.range C).map (fun i => g (j*C + i)))
      = (List.range (m*C)).map g := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, ih, Nat.succ_mul,
        List.range_add, List.map_append]
    congr 1
    rw [List.map_map]
    congr 1

theorem rowsOf_facts (m C : ℕ) (L : List HvdH.Val) (h : L.length = m * C) :
    (Work.Layout.AA.rowsOf m C L).length = m ∧
    (∀ r ∈ Work.Layout.AA.rowsOf m C L, r.length = C) ∧
    (Work.Layout.AA.rowsOf m C L).flatten = L := by
  refine ⟨?_, ?_, ?_⟩
  · simp [rowsOf]
  · intro r hr
    simp only [rowsOf, List.mem_map, List.mem_range] at hr
    obtain ⟨j, -, rfl⟩ := hr
    simp
  · have h1 : (List.range m).flatMap
        (fun j => (List.range C).map (fun i => L.getD (j * C + i) default))
        = (List.range (m * C)).map (fun k => L.getD k default) :=
      flatMap_range_mul m C (fun k => L.getD k default)
    show (List.range m).flatMap
        (fun j => (List.range C).map (fun i => L.getD (j * C + i) default)) = L
    rw [h1, ← h]
    exact range_map_getD L default

end Work.Layout.AA
