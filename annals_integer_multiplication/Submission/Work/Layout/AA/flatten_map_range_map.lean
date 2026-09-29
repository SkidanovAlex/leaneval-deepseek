import Mathlib

/-!
# Flattening a `range`-indexed block matrix

`(List.range A).map (fun a => (List.range B).map (fun i => F a i))` is `A` blocks of `B` elements;
its flattening is a flat `A × B` array, whose element at flat index `s` is read back by splitting
`s` as `(s / B, s % B)` (row-major order, last index fastest).

The auxiliary lemma is stated in `flatMap` form, which is the shape that the induction over `A`
takes naturally; the main statement then only rewrites `flatten` in terms of `flatMap`.
-/

namespace Work.Layout.AA

/-- Flattening `m` blocks of `B` elements: `(range m).flatMap (fun j => (range B).map (f j ·))` is
obtained by mapping over `range (m*B)` and re-splitting the index as `(t / B, t % B)`. -/
private lemma flatMap_range_range_map {α : Type} (m B : ℕ) (g : ℕ → ℕ → α) :
    (List.range m).flatMap (fun j => (List.range B).map (fun b => g j b))
      = (List.range (m * B)).map (fun t => g (t / B) (t % B)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, ih]
    have hmap : (List.range B).map (fun b => g m b)
        = (List.range B).map (fun x => g ((m * B + x) / B) ((m * B + x) % B)) := by
      refine List.map_congr_left (fun x hx => ?_)
      simp only [List.mem_range] at hx
      have hB : 0 < B := by omega
      have h1 : (m * B + x) / B = m := by
        rw [Nat.mul_comm m B, Nat.mul_add_div hB, Nat.div_eq_of_lt hx, Nat.add_zero]
      have h2 : (m * B + x) % B = x := by
        rw [Nat.add_comm (m * B) x, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hx]
      rw [h1, h2]
    rw [hmap, Nat.succ_mul, List.range_add, List.map_append]
    simp only [List.map_map, Function.comp_def]

theorem flatten_map_range_map {α : Type} (A B : ℕ) (F : ℕ → ℕ → α) :
    ((List.range A).map fun a => (List.range B).map fun i => F a i).flatten =
      (List.range (A * B)).map fun s => F (s / B) (s % B) := by
  simp only [List.flatten_eq_flatMap, List.flatMap_map, id_eq]
  exact flatMap_range_range_map A B F

end Work.Layout.AA
