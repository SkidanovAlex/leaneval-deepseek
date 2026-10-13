import Mathlib
import Submission.Work.WilkiesH.Strat.omega_closure_defs

/-!
# Closures of `Ω`-sets: the "pure" identification

`closureSet W` is the set of limit points of `W`, written with the box (sup) metric:
`x ∈ closureSet W ↔ ∀ ε > 0, ∃ y ∈ W, ∀ i, |y i - x i| < ε`.

`interiorComp W` is the set of points admitting a ball disjoint from `W`, i.e. the
complement of the closure of `W`; here "ball" is the *cube* given by the squared
coordinate distances: `x ∈ fatSet W t ↔ ∃ y ∈ W, ∀ i, (x i - y i)² < t²`.

The two descriptions of the closure agree, because for `t > 0`
`(x i - y i)² < t² ↔ |x i - y i| < t`.  This is the elementary set-theoretic fact
behind the `Ω`-definability of the closure, kept separate from any definability
statement: `closureSet W = (interiorComp W)ᶜ`.
-/

set_option autoImplicit false

namespace Work.WilkiesH.Strat

/-- Unfolding the complement of `interiorComp` gives the statement that every positive
radius `t` admits a witness `y ∈ W` within the cube of side `t`. -/
theorem interiorComp_compl_iff {n : ℕ} (W : Set (Fin n → ℝ)) (x : Fin n → ℝ) :
    (x ∈ (interiorComp W)ᶜ) ↔
      ∀ t, 0 < t → ∃ y, y ∈ W ∧ ∀ i, (x i - y i) ^ 2 < t ^ 2 := by
  simp only [Set.mem_compl_iff, interiorComp, Set.mem_ofPred_eq, not_exists, not_and,
    not_forall, not_not, exists_prop, fatSet]

theorem omega_closure_pure {n : ℕ} (W : Set (Fin n → ℝ)) :
    closureSet W = (interiorComp W)ᶜ := by
  ext x
  rw [interiorComp_compl_iff]
  constructor
  · intro h t ht
    obtain ⟨y, hyW, hy⟩ := h t ht
    refine ⟨y, hyW, fun i => ?_⟩
    have h1 : |x i - y i| < t := by
      have h' := hy i
      rwa [abs_sub_comm] at h'
    exact sq_lt_sq.mpr (by rwa [abs_of_pos ht])
  · intro h ε hε
    obtain ⟨y, hyW, hy⟩ := h ε hε
    refine ⟨y, hyW, fun i => ?_⟩
    have h1 : |x i - y i| < ε := by
      have h' := sq_lt_sq.mp (hy i)
      rwa [abs_of_pos hε] at h'
    rwa [abs_sub_comm]

end Work.WilkiesH.Strat
