import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.MDBasic.finite_sets

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

/-- A nonzero sublattice `L ⊆ ℤ^ι` contains a nonzero vector of minimal Euclidean norm. -/
theorem shortest_vec {ι : Type*} [Fintype ι] [DecidableEq ι] (L : Submodule ℤ (ι → ℤ))
    (h : L ≠ ⊥) : ∃ u ∈ L, u ≠ 0 ∧ ∀ v ∈ L, v ≠ 0 → eNorm u ≤ eNorm v := by
  classical
  -- norms of nonzero vectors of `L` are square roots of natural numbers,
  -- so well-ordering of `ℕ` supplies a minimiser.
  obtain ⟨u₀, hu₀L, hu₀ne⟩ := (Submodule.ne_bot_iff L).mp h
  have hex : ∃ n : ℕ, ∃ v ∈ L, v ≠ 0 ∧ ∑ i, (v i).natAbs ^ 2 = n :=
    ⟨_, u₀, hu₀L, hu₀ne, rfl⟩
  obtain ⟨u, huL, hune, hgu⟩ := Nat.find_spec hex
  refine ⟨u, huL, hune, fun v hvL hvne => ?_⟩
  have hle : Nat.find hex ≤ ∑ i, (v i).natAbs ^ 2 :=
    Nat.find_min' hex ⟨v, hvL, hvne, rfl⟩
  rw [eNorm_eq_sqrt_cast_sumSq u, eNorm_eq_sqrt_cast_sumSq v, hgu]
  exact Real.sqrt_le_sqrt (by exact_mod_cast hle)

end Work.HP.BCS
