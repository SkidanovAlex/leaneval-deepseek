import Submission.Work.Deep.GKO.NarrowImports

/-!
# `exists_pairClosedSubset_card`

A fixed-point-free involution `f` of a finite set `S` (here: `f` maps `S` into itself, is an
involution on `S` and has no fixed point in `S`) partitions `S` into two-element orbits
`{x, f x}`.  This module proves that `S` contains an `f`-closed subset of *every* even
cardinality `2d ≤ |S|`: pick `d` of the orbits.

This is the combinatorial input of the balancing step N5b of the GKO one-factorisation
chapter (`Work.Deep.GKO.OneFact.N5.exists_dumpSet`), where `f` is the mate map of a matching.

## Proof

Strong induction on `d`.  If `d = 0` take `D = ∅`.  Otherwise `S` is nonempty, so choose
`x ∈ S`; then `f x ∈ S` and `f x ≠ x`.  The set `S' := (S \ {x}) \ {f x}` satisfies
`|S'| = |S| - 2 ≥ 2(d-1)` and is again `f`-invariant: for `y ∈ S'` the image `f y` avoids
`x` and `f x` because `f (f y) = y` and `f (f x) = x` would otherwise force
`y = f x` or `y = x`.  By induction `S'` contains an `f`-closed `D'` with `|D'| = 2(d-1)`,
and `D := {x, f x} ∪ D'` is `f`-closed of cardinality `2d`.

(The chapter's convention is to import `Submission.Work.Deep.GKO.NarrowImports` rather than
`Mathlib`, so that this module may be imported by cone modules without making the root-level
`Hypergraph` ambiguity of `import Mathlib` appear.)
-/

namespace Work.Deep.GKO.OneFact.N5

theorem exists_pairClosedSubset_card {α : Type*} [LinearOrder α] [DecidableEq α] (S : Finset α) (f : α → α) (d : ℕ) (hmem : ∀ x ∈ S, f x ∈ S) (hinv : ∀ x ∈ S, f (f x) = x) (hfix : ∀ x ∈ S, f x ≠ x) (hcard : 2 * d ≤ S.card) : ∃ D : Finset α, D ⊆ S ∧ D.card = 2 * d ∧ ∀ x ∈ D, f x ∈ D := by
  have aux : ∀ (k : ℕ) (S : Finset α) (f : α → α),
      (∀ x ∈ S, f x ∈ S) → (∀ x ∈ S, f (f x) = x) → (∀ x ∈ S, f x ≠ x) →
      2 * k ≤ S.card → ∃ D : Finset α, D ⊆ S ∧ D.card = 2 * k ∧ ∀ x ∈ D, f x ∈ D := by
    intro k
    induction k with
    | zero =>
      intro S f hmem hinv hfix hcard
      exact ⟨∅, Finset.empty_subset S, by simp, by simp⟩
    | succ k ih =>
      intro S f hmem hinv hfix hcard
      -- `S` is nonempty; remove a two-element orbit `{x, f x}` and induct
      have hSpos : 0 < S.card := by omega
      obtain ⟨x, hxS⟩ := Finset.card_pos.mp hSpos
      have hfxS : f x ∈ S := hmem x hxS
      have hne : f x ≠ x := hfix x hxS
      set S' : Finset α := (S.erase x).erase (f x) with hS'def
      have hmem' : ∀ y ∈ S', f y ∈ S' := by
        intro y hy
        rw [hS'def, Finset.mem_erase, Finset.mem_erase] at hy
        obtain ⟨hyfx, hyx, hyS⟩ := hy
        rw [hS'def, Finset.mem_erase, Finset.mem_erase]
        refine ⟨?_, ?_, hmem y hyS⟩
        · intro h
          -- `f y = f x` would give `y = f (f y) = f (f x) = x`
          have h1 : f (f y) = f (f x) := by rw [h]
          rw [hinv y hyS, hinv x hxS] at h1
          exact hyx h1
        · intro h
          -- `f y = x` would give `y = f (f y) = f x`
          have h1 : y = f x := by rw [← hinv y hyS, h]
          exact hyfx h1
      have hinv' : ∀ y ∈ S', f (f y) = y := by
        intro y hy
        rw [hS'def, Finset.mem_erase, Finset.mem_erase] at hy
        exact hinv y hy.2.2
      have hfix' : ∀ y ∈ S', f y ≠ y := by
        intro y hy
        rw [hS'def, Finset.mem_erase, Finset.mem_erase] at hy
        exact hfix y hy.2.2
      have hS'card : 2 * k ≤ S'.card := by
        rw [hS'def, Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hne, hfxS⟩),
          Finset.card_erase_of_mem hxS]
        omega
      obtain ⟨D', hD'sub, hD'card, hD'cl⟩ := ih S' f hmem' hinv' hfix' hS'card
      have hS'sub : S' ⊆ S := by
        intro y hy
        rw [hS'def, Finset.mem_erase, Finset.mem_erase] at hy
        exact hy.2.2
      have hxS' : x ∉ S' := by
        rw [hS'def, Finset.mem_erase, Finset.mem_erase]
        exact fun h => h.2.1 rfl
      have hfxS' : f x ∉ S' := by
        rw [hS'def, Finset.mem_erase, Finset.mem_erase]
        exact fun h => h.1 rfl
      have hxsub : x ∉ insert (f x) D' := by
        simp only [Finset.mem_insert, not_or]
        exact ⟨Ne.symm hne, fun h => hxS' (hD'sub h)⟩
      have hfxnotin : f x ∉ D' := fun h => hfxS' (hD'sub h)
      refine ⟨insert x (insert (f x) D'), ?_, ?_, ?_⟩
      · intro y hy
        rw [Finset.mem_insert] at hy
        rcases hy with h | hy
        · rw [h]; exact hxS
        · rw [Finset.mem_insert] at hy
          rcases hy with h | hy
          · rw [h]; exact hfxS
          · exact hS'sub (hD'sub hy)
      · have h1 : (insert x (insert (f x) D')).card = (insert (f x) D').card + 1 :=
          Finset.card_insert_of_notMem hxsub
        have h2 : (insert (f x) D').card = D'.card + 1 :=
          Finset.card_insert_of_notMem hfxnotin
        rw [h1, h2, hD'card]
        ring
      · intro y hy
        rw [Finset.mem_insert] at hy
        rcases hy with h | hy
        · rw [h]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_self (f x) D')
        · rw [Finset.mem_insert] at hy
          rcases hy with h | hy
          · rw [h, hinv x hxS]
            exact Finset.mem_insert_self x _
          · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hD'cl y hy))
  exact aux d S f hmem hinv hfix hcard

end Work.Deep.GKO.OneFact.N5
