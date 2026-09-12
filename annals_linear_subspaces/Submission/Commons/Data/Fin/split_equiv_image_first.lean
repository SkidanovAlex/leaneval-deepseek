import Mathlib.Data.Finset.Sort

namespace Commons.Data.Fin

/-! # Splitting `Fin n` into the image of an embedding first and its complement after

For an injective `e : Fin m ↪ Fin n` (`m ≤ n`), there is a bijection
`ρ : Fin (m + (n - m)) ≃ Fin n` that puts the image of `e` in the first `m` positions and
the complement in the remaining `n - m` positions:

  * `ρ (Fin.castAdd (n - m) i) = e i` for `i : Fin m` (the initial segment is the
    `e`-image, in order);
  * for `k : Fin (n - m)`, `ρ (Fin.natAdd m k)` is NOT in the range of `e`;
  * every `j : Fin n` is either `e i` for some `i`, or `ρ (Fin.natAdd m k)` for some `k`.

**Proof route (all Mathlib):** consider the finset
`s := (Finset.univ : Finset (Fin n)).filter (fun j => j ∉ Set.range e)`.  Its cardinality
is `n - m` (the image of `e` has cardinality `m` since `e` is injective, and the
complement of a `card m` subset of a `card n` type has card `n - m` — use
`Finset.card_univ`, `Finset.card_image_of_injective`, `Finset.card_filter`, and the
complement-cardinality arithmetic, or `Finset.card_compl`-style facts).  The monotone
enumeration of `s` (`Finset.orderIsoOfFin`, or `Finset.orderEmbOfFin`) gives an order
isomorphism `Fin (n - m) ≃ s` after reindexing by the cardinality; compose with the
subtype inclusion to obtain `c : Fin (n - m) ↪ Fin n` whose range is exactly `s`.  Then
define `ρ : Fin (m + (n - m)) ≃ Fin n` by `ρ (Fin.castAdd (n - m) i) = e i` and
`ρ (Fin.natAdd m k) = c k` (every element of `Fin (m + (n - m))` is either
`Fin.castAdd (n - m) i` for some `i : Fin m` or `Fin.natAdd m k` for some
`k : Fin (n - m)` — the standard `Fin.castAdd`/`Fin.natAdd` case split).  Injectivity of
`ρ` follows from the disjointness of the range of `e` and the range of `c` (the latter
equals `s`, the complement) plus the injectivity of `e` and `c`; surjectivity from the
partition of `Fin n` into `Set.range e ⊔ s`.
-/
theorem split_equiv_image_first {m n : ℕ} (hmn : m ≤ n) (e : Fin m ↪ Fin n) :
    ∃ ρ : Fin (m + (n - m)) ≃ Fin n,
      (∀ i : Fin m, ρ (Fin.castAdd (n - m) i) = e i) ∧
      (∀ k : Fin (n - m), ρ (Fin.natAdd m k) ∉ Set.range e) ∧
      (∀ j : Fin n, j ∈ Set.range e ∨ ∃ k : Fin (n - m), ρ (Fin.natAdd m k) = j) := by
  classical
  let t : Finset (Fin n) := Finset.univ.image e
  let s : Finset (Fin n) := tᶜ
  have ht_mem : ∀ j : Fin n, j ∈ t ↔ j ∈ Set.range e := by
    intro j
    simp [t]
  have hs_mem : ∀ j : Fin n, j ∈ s ↔ j ∉ Set.range e := by
    intro j
    simp [s, Finset.mem_compl, ht_mem j]
  have ht_card : t.card = m := by
    change (Finset.image (⇑e) (Finset.univ : Finset (Fin m))).card = m
    rw [Finset.card_image_of_injective (s := Finset.univ) (f := ⇑e) e.injective]
    simp
  have hs_card : s.card = n - m := by
    dsimp [s]
    rw [Finset.card_compl]
    rw [ht_card]
    simp
  let oE : Fin (n - m) ↪o Fin n := Finset.orderEmbOfFin s hs_card
  have ho_mem : ∀ j : Fin (n - m), oE j ∉ Set.range e := by
    intro j
    exact (hs_mem (oE j)).mp (by simpa [oE] using (Finset.orderEmbOfFin_mem s hs_card j))
  let f : Fin (m + (n - m)) → Fin n :=
    Fin.append (fun i : Fin m => e i) (fun j : Fin (n - m) => oE j)
  have hf1 : ∀ i : Fin m, f (Fin.castAdd (n - m) i) = e i := by
    intro i
    simp [f]
  have hf2 : ∀ k : Fin (n - m), f (Fin.natAdd m k) ∉ Set.range e := by
    intro k
    simpa [f] using ho_mem k
  have hdisj : ∀ (i : Fin m) (j : Fin (n - m)), e i ≠ oE j := by
    intro i j h
    exact ho_mem j ⟨i, h⟩
  have hfinj : Function.Injective f := by
    rw [Fin.append_injective_iff]
    refine ⟨?_, ?_, ?_⟩
    · simpa using e.injective
    · simpa using oE.injective
    · exact hdisj
  have hcomplete : ∀ y : Fin n,
      y ∈ Set.range e ∨ ∃ k : Fin (n - m), f (Fin.natAdd m k) = y := by
    intro y
    by_cases hy : y ∈ Set.range e
    · exact Or.inl hy
    · right
      have hys : y ∈ s := (hs_mem y).mpr hy
      have hyr : y ∈ Set.range (⇑oE) := by
        change y ∈ Set.range (⇑(Finset.orderEmbOfFin s hs_card))
        rw [Finset.range_orderEmbOfFin]
        simpa using hys
      rcases hyr with ⟨k, hk⟩
      exact ⟨k, by simp [f, hk]⟩
  have hfsurj : Function.Surjective f := by
    intro y
    rcases hcomplete y with hy | ⟨k, hk⟩
    · rcases hy with ⟨i, rfl⟩
      exact ⟨Fin.castAdd (n - m) i, hf1 i⟩
    · exact ⟨Fin.natAdd m k, hk⟩
  let ρ : Fin (m + (n - m)) ≃ Fin n := Equiv.ofBijective f ⟨hfinj, hfsurj⟩
  refine ⟨ρ, ?_, ?_, ?_⟩
  · intro i
    exact hf1 i
  · intro k
    exact hf2 k
  · intro j
    rcases hcomplete j with h | ⟨k, hk⟩
    · exact Or.inl h
    · right
      exact ⟨k, hk⟩

end Commons.Data.Fin