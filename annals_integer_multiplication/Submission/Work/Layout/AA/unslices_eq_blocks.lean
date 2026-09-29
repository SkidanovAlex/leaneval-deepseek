import Mathlib
import Submission.Work.Layout.AA.PureDefs

namespace Work.Layout.AA

set_option linter.unusedVariables false

/-!
# `unslices` as a triple block flattening

`HvdH.unslices A n B outs` is the flat `A × n × B` array obtained from `A*B` output slices of
length `n`, indexed lexicographically (last index fastest): flat index `idx` reads slice
`idx / (n*B) * B + idx % B` at offset `idx / B % n`.

The goal of this file is to identify it with the *triple block flattening*
`a ↦ j ↦ b ↦ outs[a*B+b][j]` of `outs`.  We prove this in two steps.

* `flatMap_range_range_map` — the two-dimensional case: flattening `m` blocks of `B` elements is
  the same as mapping over `range (m*B)` and re-dividing the index by `B`.
* `flatMap_three` — applying it twice converts the triple flattening over `A`, `n`, `B` into a
  single `map` over `range (A*n*B)` whose index decomposition is by `n*B`, then `B`, then the
  remainder.  The bridge between the two index decompositions is
  `Nat.mod_mul_left_div_self` / `Nat.mod_mul_left_mod`.

Since `unslices` is defined with `getD`, neither hypothesis (`outs.length = A*B` and the slice
lengths being `n`) is needed: the identity holds for an arbitrary list of slices.
-/

/-- Flattening `m` blocks of `B` elements: `(range m).flatMap (fun j => (range B).map (g j ·))`
is obtained by mapping over `range (m*B)` and re-splitting the index as `(t / B, t % B)`. -/
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

/-- Triple flattening over nested `range`s equals a single `map` over `range (A*n*B)`, with the
index decomposed as `a = idx / (n*B)`, `j = idx / B % n`, `b = idx % B`. -/
private lemma flatMap_three {α : Type} (A n B : ℕ) (g : ℕ → ℕ → ℕ → α) :
    (List.range A).flatMap
        (fun a => (List.range n).flatMap (fun j => (List.range B).map (fun b => g a j b)))
      = (List.range (A * n * B)).map
          (fun idx => g (idx / (n * B)) (idx / B % n) (idx % B)) := by
  have h1 : ∀ a, (List.range n).flatMap (fun j => (List.range B).map (fun b => g a j b))
      = (List.range (n * B)).map (fun t => g a (t / B) (t % B)) :=
    fun a => flatMap_range_range_map n B (fun j b => g a j b)
  simp only [h1]
  rw [flatMap_range_range_map A (n * B) (fun a t => g a (t / B) (t % B))]
  rw [show A * (n * B) = A * n * B from by ring]
  refine List.map_congr_left (fun idx _ => ?_)
  rw [Nat.mod_mul_left_div_self idx B n, Nat.mod_mul_left_mod idx n B]

theorem unslices_eq_blocks (A n B : ℕ) (outs : List (List HvdH.Val))
    (h : outs.length = A * B) (hn : ∀ s, s < A * B → (outs.getD s []).length = n) :
    HvdH.unslices A n B outs =
      ((List.range A).map fun a =>
        ((List.range n).map fun j =>
          (List.range B).map fun b => (outs.getD (a * B + b) []).getD j default).flatten).flatten := by
  rw [show ((List.range A).map fun a =>
        ((List.range n).map fun j =>
          (List.range B).map fun b => (outs.getD (a * B + b) []).getD j default).flatten).flatten
      = (List.range A).flatMap (fun a => (List.range n).flatMap (fun j =>
          (List.range B).map fun b => (outs.getD (a * B + b) []).getD j default)) from by
    simp only [List.flatten_eq_flatMap, List.flatMap_map, id_eq], flatMap_three]
  simp only [HvdH.unslices]

end Work.Layout.AA
