import Mathlib

/-!
# Sorting a finite family by a permutation

Given any function `f : Fin q → α` into a linearly ordered type, there is a permutation
`σ` of `Fin q` such that `i ↦ f (σ i)` is monotone: the permutation that lists the
elements of `Fin q` in nondecreasing order of their `f`-values (breaking ties by the
value of the index itself).

The construction is by rank: the map `key i = (f i, i)` is injective into the
lexicographically ordered type `Lex (α × Fin q)`, so its image `s` is a finset of
cardinality `q`. The order isomorphism `s.orderIsoOfFin` identifies `Fin q` with `s`
in increasing order, and composing with the inverse of `key : Fin q ≃ s` gives the
desired permutation.
-/

namespace Work.WilE7.CoreStep

theorem exists_perm_monotone {q : ℕ} {α : Type*} [LinearOrder α] (f : Fin q → α) : ∃ σ : Equiv.Perm (Fin q), Monotone fun i : Fin q => f (σ i) := by
  classical
  -- The `key` map, ordered lexicographically by value first, index second.
  let key : Fin q → Lex (α × Fin q) := fun i => toLex (f i, i)
  have hkey : Function.Injective key := by
    intro i j hij
    exact congrArg Prod.snd (congrArg ofLex hij)
  -- The set of keys has cardinality `q`.
  let s : Finset (Lex (α × Fin q)) := (Finset.univ : Finset (Fin q)).image key
  have hcard : s.card = q := by
    rw [Finset.card_image_of_injective _ hkey, Finset.card_univ, Fintype.card_fin]
  -- Increasing bijection from `Fin q` onto the set of keys.
  let iso : Fin q ≃o ↥s := Finset.orderIsoOfFin s hcard
  -- `key` as an equivalence onto its image.
  let ke : Fin q ≃ ↥s := Equiv.ofBijective
      (fun i => (⟨key i, Finset.mem_image_of_mem key (Finset.mem_univ i)⟩ : ↥s)) (by
        constructor
        · intro i j hij
          exact hkey (Subtype.ext_iff.mp hij)
        · intro x
          obtain ⟨i, -, hi⟩ := Finset.mem_image.mp x.2
          exact ⟨i, Subtype.ext hi⟩)
  -- The permutation sending rank `i` to the index whose key has rank `i`.
  let σ : Equiv.Perm (Fin q) := (iso : Fin q ≃ ↥s).trans ke.symm
  refine ⟨σ, ?_⟩
  intro i j hij
  have h1 : ke (σ i) = (iso i : ↥s) := by
    simp only [σ, Equiv.trans_apply]
    exact Equiv.apply_symm_apply ke (iso i)
  have h2 : ke (σ j) = (iso j : ↥s) := by
    simp only [σ, Equiv.trans_apply]
    exact Equiv.apply_symm_apply ke (iso j)
  have hle : key (σ i) ≤ key (σ j) := by
    have hm : (iso i : ↥s) ≤ (iso j : ↥s) := iso.monotone hij
    have hsub : ke (σ i) ≤ ke (σ j) := by rw [h1, h2]; exact hm
    have hval1 : ((ke (σ i) : ↥s) : Lex (α × Fin q)) = key (σ i) := rfl
    have hval2 : ((ke (σ j) : ↥s) : Lex (α × Fin q)) = key (σ j) := rfl
    rw [← hval1, ← hval2]
    exact hsub
  -- Lexicographic comparison: the first components (the values of `f`) are ordered.
  rcases Prod.Lex.toLex_le_toLex.mp hle with hlt | ⟨heq, _⟩
  · exact hlt.le
  · exact heq.le

end Work.WilE7.CoreStep
