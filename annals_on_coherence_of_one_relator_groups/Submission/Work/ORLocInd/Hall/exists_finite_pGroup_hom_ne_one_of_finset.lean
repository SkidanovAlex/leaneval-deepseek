import Mathlib
import Submission.Work.ORLocInd.Hall.Basic

universe u

namespace Work.ORLocInd.Hall

/-- If `g ^ (p ^ k) = 1` and `k ≤ K`, then also `g ^ (p ^ K) = 1` in a group. -/
theorem pow_pow_eq_one_of_le {G : Type*} [Group G] {p : ℕ} {g : G} {k K : ℕ}
    (h : g ^ p ^ k = 1) (hk : k ≤ K) : g ^ p ^ K = 1 := by
  calc g ^ p ^ K = g ^ (p ^ k * p ^ (K - k)) := by rw [← pow_add, Nat.add_sub_of_le hk]
    _ = (g ^ p ^ k) ^ p ^ (K - k) := by rw [pow_mul]
    _ = 1 := by rw [h, one_pow]

/-- A direct product of two `p`-groups is a `p`-group. -/
theorem isPGroup_prod {p : ℕ} {G H : Type*} [Group G] [Group H]
    (hG : IsPGroup p G) (hH : IsPGroup p H) : IsPGroup p (G × H) := by
  intro g
  obtain ⟨k, hk⟩ := hG g.1
  obtain ⟨l, hl⟩ := hH g.2
  refine ⟨max k l, Prod.ext ?_ ?_⟩
  · simpa using pow_pow_eq_one_of_le hk (le_max_left k l)
  · simpa using pow_pow_eq_one_of_le hl (le_max_right k l)

/-- **Simultaneous separation by a finite `p`-group quotient.**  If the free group on `α` is
residually a finite `p`-group (`Work.ORLocInd.ResiduallyFinitePGroup`, P. Hall 1950), then one finite
`p`-group quotient separates all elements of a given finite set of nontrivial words at once.  (Proof:
take the product of the finitely many separating quotients; a product of finite `p`-groups is a
finite `p`-group.) -/
theorem exists_finite_pGroup_hom_ne_one_of_finset {α : Type u} (H : ResiduallyFinitePGroup α)
    (p : ℕ) (hp : p.Prime) (s : Finset (FreeGroup α)) (hs : ∀ w ∈ s, w ≠ 1) :
    ∃ (Q : Type u) (_ : Group Q) (_ : Finite Q) (_ : IsPGroup p Q) (ψ : FreeGroup α →* Q),
      ∀ w ∈ s, ψ w ≠ 1 := by
  classical
  revert hs
  refine Finset.induction_on s ?_ ?_
  · intro _
    exact ⟨↥(⊥ : Subgroup (FreeGroup α)), inferInstance, inferInstance,
      IsPGroup.of_bot (p := p), 1, by simp⟩
  · intro w s hw ih hs
    have hs' : ∀ x ∈ s, x ≠ 1 := fun x hx => hs x (Finset.mem_insert_of_mem hx)
    obtain ⟨Q, hQgrp, hQfin, hQp, ψ, hψ⟩ := ih hs'
    obtain ⟨Q', hQ'grp, hQ'fin, hQ'p, ψ', hψ'⟩ := H p hp w (hs w (Finset.mem_insert_self w s))
    refine ⟨Q × Q', inferInstance, inferInstance, isPGroup_prod hQp hQ'p, ψ.prod ψ', ?_⟩
    intro x hx hcontra
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hψ' (by simpa using congrArg Prod.snd hcontra)
    · exact hψ x hx (by simpa using congrArg Prod.fst hcontra)

end Work.ORLocInd.Hall
