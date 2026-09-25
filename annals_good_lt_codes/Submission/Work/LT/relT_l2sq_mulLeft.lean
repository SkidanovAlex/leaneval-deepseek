import Mathlib
import Submission.Work.LT.relT_defs
import Submission.Work.LT.relT_l2

/-!
# Invariance of the `ℓ²`-norm (squared) under left translations

For a finite group `G` and a complex-valued function `h : G → ℂ`, the maps `g ↦ y * g` are
permutations of `G`, so both `l2sq h = ∑ g, Complex.normSq (h g)` and `l2norm h = √(l2sq h)`
are invariant under left translation of the argument.  This is the elementary reindexing fact
used when translating the hypothesis `‖h‖₂ = 1` along the column subgroup `U` of `SL₃(ℤ/p)`.
-/

namespace Work.LT

/-- **Left translation invariance of `l2sq`.**  Reindexing the sum `∑ g, Complex.normSq (h g)`
by the permutation `g ↦ y * g` of the finite group `G`. -/
theorem relT_l2sq_mulLeft :
    (∀ {G : Type*} [Group G] [Fintype G] (y : G) (h : G → ℂ), l2sq (fun g => h (y * g)) = l2sq h)
  ∧ (∀ {G : Type*} [Group G] [Fintype G] (y : G) (h : G → ℂ), l2norm (fun g => h (y * g)) = l2norm h) := by
  constructor
  · intro G _ _ y h
    simp only [l2sq]
    exact Equiv.sum_comp (Equiv.mulLeft y) (fun x => Complex.normSq (h x))
  · intro G _ _ y h
    rw [l2norm, l2norm,
      show (l2sq (fun g => h (y * g))) = l2sq h from by
        simp only [l2sq]
        exact Equiv.sum_comp (Equiv.mulLeft y) (fun x => Complex.normSq (h x))]

end Work.LT
