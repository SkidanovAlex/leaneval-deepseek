import Mathlib

namespace Work.DSM5b.HCF

/-- If `F : Equiv.Perm (Fin (m+1)) → N` vanishes at `1` and satisfies
`F (π * Equiv.swap i.castSucc i.succ) = - F π` for all `π` and all `i : Fin m`, then `F`
vanishes identically.

Route: `Equiv.Perm.mclosure_swap_castSucc_succ m` says the adjacent transpositions
`Equiv.swap i.castSucc i.succ` generate `Equiv.Perm (Fin (m+1))`; combine it with
`Submonoid.closure_induction` applied to the predicate `Q t := ∀ π, F π = 0 → F (π * t) = 0`. -/
theorem perm_eq_zero_of_step {N : Type*} [AddCommGroup N] {m : ℕ}
    (F : Equiv.Perm (Fin (m + 1)) → N) (h1 : F 1 = 0)
    (hstep : ∀ (π : Equiv.Perm (Fin (m + 1))) (i : Fin m),
      F (π * Equiv.swap i.castSucc i.succ) = - F π) :
    ∀ π, F π = 0 := by
  have main : ∀ t ∈ Submonoid.closure (Set.range fun i : Fin m => Equiv.swap i.castSucc i.succ),
      (∀ σ, F σ = 0 → F (σ * t) = 0) := by
    intro t
    refine Submonoid.closure_induction (motive := fun x _ => ∀ σ, F σ = 0 → F (σ * x) = 0)
      ?_ ?_ ?_
    · rintro x ⟨i, rfl⟩ σ hσ
      rw [hstep σ i, hσ, neg_zero]
    · intro σ hσ; rw [mul_one]; exact hσ
    · intro x y hx hy ihx ihy σ hσ
      rw [← mul_assoc]
      exact ihy _ (ihx _ hσ)
  intro π
  have hπ : π ∈ Submonoid.closure (Set.range fun i : Fin m => Equiv.swap i.castSucc i.succ) := by
    rw [Equiv.Perm.mclosure_swap_castSucc_succ m]; exact Submonoid.mem_top π
  simpa using main π hπ 1 h1

end Work.DSM5b.HCF
