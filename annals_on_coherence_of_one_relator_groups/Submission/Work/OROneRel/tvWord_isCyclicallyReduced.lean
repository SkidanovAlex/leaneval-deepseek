import Mathlib
import Submission.Work.OROneRel.transvectionNielsenDefs

/-!
# `tvWord p q m` is cyclically reduced

For `1 ≤ p`, `m < 0` and `0 ≤ m + q`, the explicit reduced word

`tvWord p q m = (x * y ^ m) ^ (p - 1) * x * y ^ (m + q)`

of the transvection image of the torus relator is cyclically reduced.

The whole word has the shape `(tvBlk m) ^ (p - 1) ++ [(0,true)] ++ (1,true) ^ (m+q)` where
`tvBlk m = (0,true) :: (1,false) ^ |m|`.  Every occurrence of the generator `0` comes with the
positive sign, so no two letters of generator `0` ever cancel; the occurrences of generator `1`
inside the blocks all carry the negative sign whereas those in the tail carry the positive sign,
and the two families are separated by a `(0,true)`.  Consequently the word is reduced, and its
first letter `(0,true)` and last letter never cancel either, i.e. it is cyclically reduced.

The proof only uses the elementary combinatorial description of the list, so the hypotheses
`m < 0` and `0 ≤ m + q` are in fact not needed; they are kept to match the statement requested by
the sibling development.
-/

namespace Work.OROneRel

open FreeGroup

-- The hypotheses `hm` and `hmq` of the requested statement are not needed by the argument below.
set_option linter.unusedVariables false

/-- A word of the form `(a,b) :: (c,d) ^ n` with `a ≠ c` is cyclically reduced: it is reduced
(the sign pattern of the two letters involved is irrelevant because the first coordinates differ),
and its first letter is `(a,b)` while its last letter is `(a,b)` (when `n = 0`) or `(c,d)`, neither
of which cancels `(a,b)`. -/
private theorem isCyclicallyReduced_cons_replicate {α : Type*} {a c : α} {b d : Bool}
    (hac : a ≠ c) (n : ℕ) :
    FreeGroup.IsCyclicallyReduced ((a, b) :: List.replicate n (c, d)) := by
  rw [FreeGroup.isCyclicallyReduced_iff]
  refine ⟨?_, ?_⟩
  · rw [FreeGroup.IsReduced, List.isChain_cons]
    refine ⟨?_, ?_⟩
    · intro y hy
      rw [List.head?_replicate] at hy
      split at hy
      · exact absurd hy (Option.not_mem_none y)
      · simp only [Option.mem_def, Option.some.injEq] at hy
        subst hy
        exact fun h => absurd h hac
    · exact List.isChain_replicate_of_rel n (fun _ => rfl)
  · intro a' ha' b' hb'
    simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hb'
    subst hb'
    have hmem : a' ∈ (a, b) :: List.replicate n (c, d) := List.mem_of_mem_getLast? ha'
    simp only [List.mem_cons, List.mem_replicate] at hmem
    rcases hmem with h | ⟨-, h⟩
    · rw [h]; intro _; rfl
    · rw [h]
      exact fun hca => absurd hca.symm hac

/-- Concatenation of two cyclically reduced words with no cancellation at the two junctions is
cyclically reduced. -/
private theorem isCyclicallyReduced_append {α : Type*} {L₁ L₂ : List (α × Bool)}
    (h₁ : FreeGroup.IsCyclicallyReduced L₁) (h₂ : FreeGroup.IsCyclicallyReduced L₂)
    (hne₁ : L₁ ≠ []) (hne₂ : L₂ ≠ [])
    (hmid : ∀ a ∈ L₁.getLast?, ∀ b ∈ L₂.head?, a.1 = b.1 → a.2 = b.2)
    (hc : ∀ a ∈ L₂.getLast?, ∀ b ∈ L₁.head?, a.1 = b.1 → a.2 = b.2) :
    FreeGroup.IsCyclicallyReduced (L₁ ++ L₂) := by
  rw [FreeGroup.isCyclicallyReduced_iff]
  refine ⟨?_, ?_⟩
  · rw [FreeGroup.IsReduced, List.isChain_append]
    exact ⟨h₁.1, h₂.1, hmid⟩
  · intro a ha b hb
    rw [List.getLast?_append_of_ne_nil _ hne₂] at ha
    rw [List.head?_append_of_ne_nil _ hne₁] at hb
    exact hc a ha b hb

theorem tvWord_isCyclicallyReduced (p q : ℕ) (m : ℤ) (hp : 1 ≤ p) (hm : m < 0) (hmq : 0 ≤ m + (q : ℤ)) :
    FreeGroup.IsCyclicallyReduced (Work.OROneRel.tvWord p q m) := by
  obtain ⟨k, rfl⟩ : ∃ k, p = k + 1 := ⟨p - 1, by omega⟩
  rw [tvWord]
  simp only [Nat.add_sub_cancel]
  cases k with
  | zero =>
    simp only [List.replicate_zero, List.flatten_nil, List.nil_append]
    exact isCyclicallyReduced_cons_replicate (a := (0 : Fin 2)) (c := 1) (b := true) (d := true)
      (by decide) _
  | succ j =>
    have hblk : FreeGroup.IsCyclicallyReduced (tvBlk m) := by
      rw [tvBlk]
      exact isCyclicallyReduced_cons_replicate (a := (0 : Fin 2)) (c := 1) (b := true) (d := false)
        (by decide) m.natAbs
    have hA : FreeGroup.IsCyclicallyReduced (List.replicate (j + 1) (tvBlk m)).flatten :=
      hblk.flatten_replicate (j + 1)
    have hE : FreeGroup.IsCyclicallyReduced
        (((0 : Fin 2), true) :: List.replicate (m + (q : ℤ)).toNat ((1 : Fin 2), true)) :=
      isCyclicallyReduced_cons_replicate (a := (0 : Fin 2)) (c := 1) (b := true) (d := true)
        (by decide) _
    have hAhead : (List.replicate (j + 1) (tvBlk m)).flatten.head? = some ((0 : Fin 2), true) := by
      rw [List.head?_flatten_replicate (by omega : j + 1 ≠ 0) (tvBlk m), tvBlk]
      rfl
    have hAne : (List.replicate (j + 1) (tvBlk m)).flatten ≠ [] := by
      intro h; rw [h] at hAhead; simp at hAhead
    have hEne : (((0 : Fin 2), true) :: List.replicate (m + (q : ℤ)).toNat ((1 : Fin 2), true)) ≠ [] :=
      List.cons_ne_nil _ _
    have hmid : ∀ a ∈ (List.replicate (j + 1) (tvBlk m)).flatten.getLast?,
        ∀ b ∈ (((0 : Fin 2), true) :: List.replicate (m + (q : ℤ)).toNat ((1 : Fin 2), true)).head?,
        a.1 = b.1 → a.2 = b.2 := by
      intro a ha b hb
      rw [List.getLast?_flatten_replicate (by omega : j + 1 ≠ 0) (tvBlk m)] at ha
      rw [List.head?_cons, Option.mem_def, Option.some.injEq] at hb
      subst hb
      have hmem : a ∈ tvBlk m := List.mem_of_mem_getLast? ha
      simp only [tvBlk, List.mem_cons, List.mem_replicate] at hmem
      rcases hmem with h | ⟨-, h⟩
      · rw [h]; intro _; rfl
      · rw [h]; intro hc'; exact absurd hc' (by decide)
    have hc : ∀ a ∈ (((0 : Fin 2), true) :: List.replicate (m + (q : ℤ)).toNat ((1 : Fin 2), true)).getLast?,
        ∀ b ∈ (List.replicate (j + 1) (tvBlk m)).flatten.head?,
        a.1 = b.1 → a.2 = b.2 := by
      intro a ha b hb
      rw [List.head?_flatten_replicate (by omega : j + 1 ≠ 0) (tvBlk m), tvBlk] at hb
      rw [List.head?_cons, Option.mem_def, Option.some.injEq] at hb
      subst hb
      have hmem : a ∈ ((0 : Fin 2), true) :: List.replicate (m + (q : ℤ)).toNat ((1 : Fin 2), true) :=
        List.mem_of_mem_getLast? ha
      simp only [List.mem_cons, List.mem_replicate] at hmem
      rcases hmem with h | ⟨-, h⟩
      · rw [h]; intro _; rfl
      · rw [h]; intro hc'; exact absurd hc' (by decide)
    exact isCyclicallyReduced_append hA hE hAne hEne hmid hc

end Work.OROneRel
