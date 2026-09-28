import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.MDBasic.finite_sets

set_option linter.unusedVariables false

namespace Work.HP.BCS

/-- The Euclidean norm of an integer vector depends only on the natural number
`∑ i, (v i).natAbs ^ 2`, of which it is the square root. -/
private lemma eNorm_eq_sqrt_cast_sumSq {ι : Type*} [Fintype ι] (v : ι → ℤ) :
    eNorm v = Real.sqrt ((∑ i, (v i).natAbs ^ 2 : ℕ) : ℝ) := by
  rw [eNorm]
  congr 1
  rw [Nat.cast_sum]
  exact Finset.sum_congr rfl fun i _ => by
    rw [Nat.cast_pow, Nat.cast_natAbs, Int.cast_abs]
    exact (sq_abs ((v i : ℝ))).symm

/-- Any nonempty subset of a lattice `L ⊆ ℤ^ι` contains an element of minimal Euclidean norm. -/
theorem min_norm_sub {ι : Type*} [Fintype ι] [DecidableEq ι] (L : Submodule ℤ (ι → ℤ))
    {S : Set (ι → ℤ)} (hS : S.Nonempty) (hSL : ∀ s ∈ S, s ∈ L) :
    ∃ s ∈ S, ∀ t ∈ S, eNorm s ≤ eNorm t := by
  classical
  -- Norms of integer vectors are square roots of natural numbers, and `ℕ` is well ordered:
  -- the squared norms attained on `S` have a least element, which is attained by some `s ∈ S`.
  obtain ⟨s₀, hs₀⟩ := hS
  have hex : ∃ n : ℕ, ∃ s : ι → ℤ, s ∈ S ∧ ∑ i, (s i).natAbs ^ 2 = n :=
    ⟨_, s₀, hs₀, rfl⟩
  obtain ⟨s, hsS, hgs⟩ := Nat.find_spec hex
  refine ⟨s, hsS, fun t ht => ?_⟩
  have hle : Nat.find hex ≤ ∑ i, (t i).natAbs ^ 2 :=
    Nat.find_min' hex ⟨t, ht, rfl⟩
  rw [eNorm_eq_sqrt_cast_sumSq s, eNorm_eq_sqrt_cast_sumSq t, hgs]
  exact Real.sqrt_le_sqrt (by exact_mod_cast hle)

end Work.HP.BCS
