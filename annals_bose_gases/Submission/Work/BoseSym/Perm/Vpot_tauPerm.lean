import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseSym.Interface
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Invariance of the pair interaction `Vpot` under the particle permutation

The pair interaction `Vpot N v x = ∑_{i < j} v (x i - x j)` is the sum over the
*pairs* of particles of the two-particle potential, each pair being counted once,
in the order induced by the index order `<` on `Fin N`.  Since the ordering of
the index set is not permutation invariant, the invariance of `Vpot` under the
relabelling `tauPerm N σ` — which acts on configurations by `x ↦ x ∘ σ` — is not
a formal triviality: one has to identify the two "fundamental domains"
`{p | p.1 < p.2}` and `{p | σ p.1 < σ p.2}` of the pair set.  Evenness of `v`
(`v (-y) = v y`) is exactly what makes the two identifications agree.

The route taken here avoids both fundamental domains.  Writing `A p = v (y p.1 - y p.2)`
for the summand on `Fin N × Fin N`, we use

* `two_mul_Vpot_eq_sum_offDiag` : `2 * Vpot N v y` is the sum of `A` over the
  *off-diagonal* `Finset.offDiag`, i.e. over all ordered pairs of distinct
  particles.  (Here evenness of `v` enters: the two orientations of a pair
  contribute the same value `v (y i - y j) = v (y j - y i)`, so each unordered
  pair contributes twice.)
* `sum_offDiag_tauPerm` : the off-diagonal sum is invariant under the relabelling
  `(i, j) ↦ (σ i, σ j)` of the ordered pairs — a pure reindexing, no evenness
  needed.

Combining the two for `y = tauPerm N σ x` and for `y = x` and cancelling the
factor `2` gives `Vpot N v (tauPerm N σ x) = Vpot N v x`.
-/

namespace Work.BoseSym.Perm

/-- The off-diagonal double sum of the pair potential is twice `Vpot`.

The three sets `{p | p.1 < p.2}`, `{p | p.2 < p.1}` and `{p | p.1 = p.2}`
partition all pairs; dropping the diagonal leaves the off-diagonal, and on it
the two orientations `(i,j)` and `(j,i)` of an unordered pair carry equal
values by evenness of `v`. -/
lemma two_mul_Vpot_eq_sum_offDiag {N : ℕ} {v : E3 → ℝ} (heven : ∀ z : E3, v (-z) = v z)
    (y : Conf N) :
    2 * Vpot N v y
      = ∑ p ∈ (Finset.univ : Finset (Fin N)).offDiag, v (y p.1 - y p.2) := by
  have hUV : (Finset.univ : Finset (Fin N × Fin N)).filter (fun p => p.1 < p.2)
        ∪ (Finset.univ : Finset (Fin N × Fin N)).filter (fun p => p.2 < p.1)
      = (Finset.univ : Finset (Fin N)).offDiag := by
    ext p
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_offDiag]
    constructor
    · rintro (h | h)
      · exact ne_of_lt h
      · exact ne_of_gt h
    · intro hne
      rcases lt_or_gt_of_ne hne with h | h
      · exact Or.inl h
      · exact Or.inr h
  have hdisj : Disjoint ((Finset.univ : Finset (Fin N × Fin N)).filter (fun p => p.1 < p.2))
      ((Finset.univ : Finset (Fin N × Fin N)).filter (fun p => p.2 < p.1)) := by
    rw [Finset.disjoint_left]
    intro p hp hp'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp hp'
    exact lt_asymm hp hp'
  have hswap : ∑ p ∈ (Finset.univ : Finset (Fin N × Fin N)).filter (fun p => p.2 < p.1),
        v (y p.1 - y p.2)
      = ∑ p ∈ (Finset.univ : Finset (Fin N × Fin N)).filter (fun p => p.1 < p.2),
          v (y p.1 - y p.2) := by
    refine Finset.sum_bijective (fun p : Fin N × Fin N => (p.2, p.1)) ?_ ?_ ?_
    · constructor
      · intro a b h
        exact Prod.ext (by simpa using congrArg Prod.snd h) (by simpa using congrArg Prod.fst h)
      · intro q
        exact ⟨(q.2, q.1), by simp⟩
    · intro p
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    · intro p _
      have h : y p.2 - y p.1 = -(y p.1 - y p.2) := by abel
      rw [h, heven]
  calc 2 * Vpot N v y
      = ∑ p ∈ (Finset.univ : Finset (Fin N × Fin N)).filter (fun p => p.1 < p.2),
          v (y p.1 - y p.2)
        + ∑ p ∈ (Finset.univ : Finset (Fin N × Fin N)).filter (fun p => p.1 < p.2),
          v (y p.1 - y p.2) := by rw [Vpot, two_mul]
    _ = ∑ p ∈ (Finset.univ : Finset (Fin N × Fin N)).filter (fun p => p.1 < p.2),
          v (y p.1 - y p.2)
        + ∑ p ∈ (Finset.univ : Finset (Fin N × Fin N)).filter (fun p => p.2 < p.1),
          v (y p.1 - y p.2) := by rw [hswap]
    _ = ∑ p ∈ (Finset.univ : Finset (Fin N × Fin N)).filter (fun p => p.1 < p.2)
          ∪ (Finset.univ : Finset (Fin N × Fin N)).filter (fun p => p.2 < p.1),
          v (y p.1 - y p.2) := (Finset.sum_union hdisj).symm
    _ = ∑ p ∈ (Finset.univ : Finset (Fin N)).offDiag, v (y p.1 - y p.2) := by rw [hUV]

/-- The off-diagonal sum `∑_{i ≠ j} v (y i - y j)` is invariant under the
relabelling of particles by a permutation: the map `(i, j) ↦ (σ i, σ j)` is a
bijection of the set of ordered pairs of distinct particles. -/
lemma sum_offDiag_tauPerm {N : ℕ} (v : E3 → ℝ) (σ : Equiv.Perm (Fin N)) (y : Conf N) :
    ∑ p ∈ (Finset.univ : Finset (Fin N)).offDiag,
        v (tauPerm N σ y p.1 - tauPerm N σ y p.2)
      = ∑ p ∈ (Finset.univ : Finset (Fin N)).offDiag, v (y p.1 - y p.2) := by
  refine Finset.sum_bijective (fun p : Fin N × Fin N => (σ p.1, σ p.2)) ?_ ?_ ?_
  · exact show Function.Bijective (Prod.map (⇑σ) (⇑σ)) from (σ.prodCongr σ).bijective
  · intro p
    simp only [Finset.mem_offDiag, Finset.mem_univ, true_and]
    exact ⟨fun h h2 => h (σ.injective h2), fun h h2 => h (by rw [h2])⟩
  · intro p _
    rfl

theorem Vpot_tauPerm {N : ℕ} {v : E3 → ℝ} (heven : ∀ y : E3, v (-y) = v y)
    (σ : Equiv.Perm (Fin N)) (x : Conf N) : Vpot N v (tauPerm N σ x) = Vpot N v x := by
  have h1 := two_mul_Vpot_eq_sum_offDiag (v := v) heven (tauPerm N σ x)
  have h2 := sum_offDiag_tauPerm v σ x
  have h3 := two_mul_Vpot_eq_sum_offDiag (v := v) heven x
  exact mul_left_cancel₀ two_ne_zero (h1.trans (h2.trans h3.symm))

end Work.BoseSym.Perm
