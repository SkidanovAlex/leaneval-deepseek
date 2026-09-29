import Mathlib

namespace Work.SB

/-- If every list in `S` has length `m`, then `S.flatten.length = m * S.length`. -/
lemma flatten_length_eq {α : Type} : ∀ (S : List (List α)) (m : ℕ),
    (∀ l ∈ S, l.length = m) → S.flatten.length = m * S.length
  | [], m, _ => by simp
  | l :: t, m, hl => by
    have hl' : ∀ x ∈ t, x.length = m := fun x hx => hl x (List.mem_cons_of_mem l hx)
    have hlen_l : l.length = m := hl l List.mem_cons_self
    have ih := flatten_length_eq t m hl'
    rw [List.flatten_cons, List.length_append, hlen_l, ih, List.length_cons]
    ring

lemma chunksFlatten {α : Type} (S : List (List α)) (m : ℕ) (hm : 0 < m) (hl : ∀ l ∈ S, l.length = m) :
    (List.range (S.flatten.length / m)).map (fun i => (S.flatten.drop (i * m)).take m) = S := by
  induction S with
  | nil => simp
  | cons l t ih =>
    have hl' : ∀ x ∈ t, x.length = m := fun x hx => hl x (List.mem_cons_of_mem l hx)
    have hlen_l : l.length = m := hl l List.mem_cons_self
    have hlen_t : t.flatten.length = m * t.length := flatten_length_eq t m hl'
    have ih' := ih hl'
    have hdiv : t.flatten.length / m = t.length := by
      rw [hlen_t, Nat.mul_div_cancel_left t.length hm]
    have hlen : (l ++ t.flatten).length = m * (t.length + 1) := by
      rw [List.length_append, hlen_l, hlen_t]; ring
    rw [List.flatten_cons, hlen, Nat.mul_div_cancel_left (t.length + 1) hm,
        List.range_succ_eq_map, List.map_cons]
    have hf0 : ((l ++ t.flatten).drop (0 * m)).take m = l := by
      rw [Nat.zero_mul, List.drop_zero, ← hlen_l, List.take_left]
    have hfun : (fun i => ((l ++ t.flatten).drop (i * m)).take m) ∘ Nat.succ
        = (fun j => (t.flatten.drop (j * m)).take m) := by
      funext j
      simp only [Function.comp_apply]
      congr 1
      rw [Nat.succ_mul, ← hlen_l, Nat.add_comm, ← List.drop_drop, List.drop_left]
    have hf : List.map (fun i => ((l ++ t.flatten).drop (i * m)).take m)
                (List.map Nat.succ (List.range t.length))
            = List.map (fun j => (t.flatten.drop (j * m)).take m) (List.range t.length) := by
      rw [List.map_map, hfun]
    rw [hf0, hf, ← hdiv, ih']

end Work.SB
