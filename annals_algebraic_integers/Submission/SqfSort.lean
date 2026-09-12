import Mathlib

/-!
# Sorting a finite family by a real key

`exists_sorted_perm`: for any real-valued function `g` on `Fin (N+1)`, there is
a permutation `σ` of `Fin (N+1)` such that, along the natural order of the
index, the values `g (σ i)` are nondecreasing:
`i.val ≤ j.val  →  g (σ i) ≤ g (σ j)`.

## Proof (tie-broken total order + `Finset.sort`)

The relation `g a ≤ g b` is not antisymmetric when `g a = g b` for `a ≠ b`,
so sort instead by the LINEAR order on `Fin (N+1)` which refines it:

    r a b := g a < g b ∨ (g a = g b ∧ a ≤ b)

on the type `α := Fin (N+1)` (which has the usual `[LinearOrder (Fin (N+1))]`).

1. `r` is reflexive, transitive, antisymmetric and total (`Std.Antisymm` /
   `Std.Total` are the required instances for `Finset.sort`).
2. Let `L : List (Fin (N+1)) := (Finset.univ : Finset (Fin (N+1))).sort r`.
   Then `L.Nodup`, `L.length = N + 1` and `List.Pairwise r L`
   (`Finset.sort_nodup`, `Finset.length_sort`, `Finset.pairwise_sort`).
3. Define `σ i := L.get ⟨i.val, _⟩`.  `List.Pairwise r L` is the strong form,
   so `List.Pairwise.rel_get_of_le` gives `r (σ i) (σ j)` whenever
   `i.val ≤ j.val`; by definition of `r` this yields `g (σ i) ≤ g (σ j)`.
4. `σ` is injective because `L` is `Nodup`; as the two types have the same
   cardinality, it is bijective (`Fintype.bijective_iff_injective_and_card`)
   and we upgrade it to an equivalence (`Equiv.ofBijective`).
-/

noncomputable section

namespace Submission.SqfSort

/-- Any real-valued function on `Fin (N + 1)` can be made nondecreasing by a
permutation of the index type. -/
theorem exists_sorted_perm {N : ℕ} (g : Fin (N + 1) → ℝ) :
    ∃ σ : Equiv.Perm (Fin (N + 1)),
      ∀ ⦃i j : Fin (N + 1)⦄, i.val ≤ j.val → g (σ i) ≤ g (σ j) := by
  classical
  -- Lexicographic-style refinement of the preorder induced by `g`, breaking
  -- ties by the natural linear order on `Fin (N + 1)`.
  let r : Fin (N + 1) → Fin (N + 1) → Prop := fun a b =>
    g a < g b ∨ (g a = g b ∧ a ≤ b)
  have htrans : IsTrans (Fin (N + 1)) r := by
    refine ⟨?_⟩
    intro a b c hab hbc
    rcases hab with hab | ⟨habe, habl⟩
    · rcases hbc with hbc | ⟨hbce, _⟩
      · exact Or.inl (lt_trans hab hbc)
      · exact Or.inl (by simpa [hbce] using hab)
    · rcases hbc with hbc | ⟨hbce, hbcl⟩
      · exact Or.inl (by simpa [habe] using hbc)
      · exact Or.inr ⟨habe.trans hbce, le_trans habl hbcl⟩
  have hantisymm : Std.Antisymm r := by
    refine ⟨?_⟩
    intro a b hab hba
    rcases hab with hab | ⟨habe, habl⟩
    · rcases hba with hba | ⟨hbae, _⟩
      · exfalso; exact (not_lt_of_gt hba) hab
      · exfalso; exact (lt_irrefl (g a)) (by simpa [hbae] using hab)
    · rcases hba with hba | ⟨hbae, hbal⟩
      · exfalso; exact (lt_irrefl (g b)) (by simpa [habe] using hba)
      · exact le_antisymm habl hbal
  have htotal : Std.Total r := by
    refine ⟨?_⟩
    intro a b
    rcases lt_trichotomy (g a) (g b) with hlt | heq | hgt
    · exact Or.inl (Or.inl hlt)
    · rcases le_total a b with hle | hle
      · exact Or.inl (Or.inr ⟨heq, hle⟩)
      · exact Or.inr (Or.inr ⟨heq.symm, hle⟩)
    · exact Or.inr (Or.inl hgt)
  have hrefl : Std.Refl r := by
    refine ⟨?_⟩
    intro a
    exact Or.inr ⟨rfl, le_rfl⟩
  letI : DecidableRel r := Classical.decRel r
  letI : IsTrans (Fin (N + 1)) r := htrans
  letI : Std.Antisymm r := hantisymm
  letI : Std.Total r := htotal
  letI : Std.Refl r := hrefl
  -- Sort all indices by `r`.
  let L : List (Fin (N + 1)) := (Finset.univ : Finset (Fin (N + 1))).sort r
  have hLnodup : L.Nodup := by
    simpa [L] using (Finset.sort_nodup (Finset.univ : Finset (Fin (N + 1))) r)
  have hLpair : List.Pairwise r L := by
    simpa [L] using (Finset.pairwise_sort (Finset.univ : Finset (Fin (N + 1))) r)
  have hLlen : L.length = N + 1 := by
    simp [L]
  -- Read off the sorted list; every index `i : Fin (N + 1)` is a valid
  -- position in `L`.
  let idx (i : Fin (N + 1)) : Fin L.length := ⟨i.val, by
    rw [hLlen]
    exact i.isLt⟩
  let σfun : Fin (N + 1) → Fin (N + 1) := fun i => L.get (idx i)
  have hσfun_inj : Function.Injective σfun := by
    intro a b hab
    have hget : L.get (idx a) = L.get (idx b) := by
      simpa [σfun] using hab
    have hidx : idx a = idx b := hLnodup.injective_get hget
    exact Fin.ext (by simpa [idx] using congrArg Fin.val hidx)
  have hbij : Function.Bijective σfun := by
    rw [Fintype.bijective_iff_injective_and_card]
    exact ⟨hσfun_inj, rfl⟩
  have hmain : ∀ ⦃i j : Fin (N + 1)⦄, i.val ≤ j.val → g (σfun i) ≤ g (σfun j) := by
    intro i j hij
    have hle : idx i ≤ idx j := by
      exact Fin.mk_le_mk.mpr hij
    have hrel : r (L.get (idx i)) (L.get (idx j)) := hLpair.rel_get_of_le hle
    rcases hrel with hlt | ⟨heq, _⟩
    · exact le_of_lt hlt
    · exact le_of_eq heq
  refine ⟨Equiv.ofBijective σfun hbij, ?_⟩
  intro i j hij
  simpa [σfun] using (hmain (i := i) (j := j) hij)

end Submission.SqfSort
