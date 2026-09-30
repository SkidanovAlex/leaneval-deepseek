import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.mr_direct

/-- Reindexing lemma: a finite set `S` of integers whose `p`-images are pairwise
`1`-separated and lie in `U` can be enumerated as a `Fin R`-family with the same
properties and the same total `f`-mass. -/
lemma enum_sep {p : ℤ → ℝ} {S : Finset ℤ} {U : Set ℝ} {f : ℝ → ℝ}
    (hsep : ∀ k ∈ S, ∀ l ∈ S, k ≠ l → 1 ≤ |p k - p l|)
    (hpn : ∀ k ∈ S, p k ∈ U) :
    ∃ (R : ℕ) (t : Fin R → ℝ),
      (∀ i, t i ∈ U) ∧
      (∀ i j, i ≠ j → 1 ≤ |t i - t j|) ∧
      (∑ i, f (t i)) = ∑ k ∈ S, f (p k) := by
  refine ⟨S.card, fun i => p ((Finset.equivFin S).symm i : ℤ), ?_, ?_, ?_⟩
  · intro i
    exact hpn _ ((Finset.equivFin S).symm i).prop
  · intro i j hij
    refine hsep _ ((Finset.equivFin S).symm i).prop _ ((Finset.equivFin S).symm j).prop ?_
    intro h
    exact hij (by
      have h2 : (Finset.equivFin S).symm i = (Finset.equivFin S).symm j := Subtype.ext h
      exact (Finset.equivFin S).symm.injective h2)
  · rw [Fintype.sum_equiv (Finset.equivFin S).symm
        (fun i : Fin S.card => f (p ((Finset.equivFin S).symm i : ℤ)))
        (fun k : S => f (p (k : ℤ))) (fun x => rfl)]
    exact (Finset.sum_subtype S (fun x => Iff.rfl) (fun k => f (p k))).symm

end Work.BMF.mr_direct
