import Mathlib
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.finite_bounded_lattice
import Submission.Work.Diff.STE.Energy_basic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE

/-- The Friedrichs truncation `trunc ρ ε` has finite support: `ρ` vanishes on the frequencies
`y` with `Σᵢ yᵢ² > 2`, so `trunc ρ ε c k = ρ (ε • k) c k` can only be nonzero for the finitely
many `k` with `Σᵢ (ε kᵢ)² ≤ 2`, i.e. `Σᵢ kᵢ² ≤ 2 / ε²`. -/
theorem exists_trunc_support {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ : (ι → ℝ) → ℝ) (hρ0 : ∀ y : ι → ℝ, 2 < (∑ i, (y i) ^ 2) → ρ y = 0)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ S : Finset (ι → ℤ), ∀ (c : (ι → ℤ) → ℂ) (k : ι → ℤ),
      k ∉ S → Work.Diff.STE.trunc ρ ε c k = 0 := by
  -- the finite set of frequencies on which the multiplier can fail to vanish
  have hfin : ({k : ι → ℤ | ∑ i, ((k i : ℝ)) ^ 2 ≤ 2 / ε ^ 2}).Finite :=
    finite_bounded_lattice (2 / ε ^ 2)
  refine ⟨hfin.toFinset, ?_⟩
  intro c k hk
  apply trunc_eq_zero_of_far ρ hρ0 ε c k
  -- `k` is outside the bounded lattice, so `Σᵢ (ε kᵢ)² > 2`
  have hk' : ¬ (∑ i, ((k i : ℝ)) ^ 2 ≤ 2 / ε ^ 2) := fun h =>
    hk ((Set.Finite.mem_toFinset (s := {k : ι → ℤ | ∑ i, ((k i : ℝ)) ^ 2 ≤ 2 / ε ^ 2})
      hfin).mpr h)
  have hlt : 2 / ε ^ 2 < ∑ i, ((k i : ℝ)) ^ 2 := lt_of_not_ge hk'
  have hε2 : 0 < ε ^ 2 := by positivity
  have h2 : 2 < ε ^ 2 * ∑ i, ((k i : ℝ)) ^ 2 := by
    rw [div_lt_iff₀ hε2] at hlt
    linarith
  have hsum : ∑ i, (ε * (k i : ℝ)) ^ 2 = ε ^ 2 * ∑ i, ((k i : ℝ)) ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [hsum]
  exact h2

end Work.Diff.STE
