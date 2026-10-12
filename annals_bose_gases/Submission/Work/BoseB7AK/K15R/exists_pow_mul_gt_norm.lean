import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseB7AK.K15R.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB7AK.K15R.exists_pow_mul_gt_norm` — the dyadic radius of a finite lattice set

`Work.BoseB4.vec n = 2π n` is the lattice momentum attached to `n : Fin 3 → ℤ`.
This file supplies the elementary *uniformity in `k`* statement used whenever a
finite lattice sum is split into dyadic annuli of radii `2^k R` (`R ≥ 1`): any
finite set of lattice indices fits into a dyadic ball of *some* radius
`2^(K+1)·R`.

The proof is exactly the finiteness: `∑_{n∈S} ‖vec n‖` bounds every `‖vec n‖`,
and `pow_unbounded_of_one_lt` (the Archimedean property of `ℝ`) produces `K` with
that bound below `2^K`; since `R ≥ 1` and `2^(K+1) ≥ 0`, we get
`‖vec n‖ < 2^K ≤ 2^(K+1) ≤ 2^(K+1)·R`.
-/

noncomputable section

namespace Work.BoseB7AK.K15R

/-- **Every finite lattice set lies in some dyadic ball.**  For `R ≥ 1` and any
finite `S : Finset (Fin 3 → ℤ)` there is `K` with `‖vec n‖ < 2^(K+1)·R` for all
`n ∈ S`. -/
theorem exists_pow_mul_gt_norm (R : ℝ) (hR : 1 ≤ R) (S : Finset (Fin 3 → ℤ)) :
    ∃ K : ℕ, ∀ n ∈ S, ‖Work.BoseB4.vec n‖ < (2:ℝ)^(K+1) * R := by
  -- the finite set has a finite norm bound
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ n ∈ S, ‖Work.BoseB4.vec n‖ ≤ M :=
    ⟨∑ n ∈ S, ‖Work.BoseB4.vec n‖,
      fun n hn => Finset.single_le_sum (fun i _ => norm_nonneg _) hn⟩
  -- push that bound below a dyadic power
  obtain ⟨K, hK⟩ := pow_unbounded_of_one_lt M (by norm_num : (1 : ℝ) < 2)
  refine ⟨K, fun n hn => ?_⟩
  have h1 : ‖Work.BoseB4.vec n‖ < (2:ℝ)^K := lt_of_le_of_lt (hM n hn) hK
  have h2 : (2:ℝ)^K ≤ (2:ℝ)^(K+1) :=
    pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) (Nat.le_succ K)
  have h3 : (0:ℝ) ≤ (2:ℝ)^(K+1) := by positivity
  calc ‖Work.BoseB4.vec n‖ < (2:ℝ)^K := h1
    _ ≤ (2:ℝ)^(K+1) := h2
    _ = (2:ℝ)^(K+1) * 1 := (mul_one _).symm
    _ ≤ (2:ℝ)^(K+1) * R := mul_le_mul_of_nonneg_left hR h3

end Work.BoseB7AK.K15R
