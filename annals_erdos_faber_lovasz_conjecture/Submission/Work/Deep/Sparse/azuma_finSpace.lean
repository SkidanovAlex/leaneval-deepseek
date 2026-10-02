/-
# Azuma--Hoeffding (bounded differences) for the uniform colouring space

The uniform measure on the colourings `V → Fin k` of a finite vertex set (`colSpace`, defined in
`Submission/Work/Deep/Sparse/ProbBasic.lean`) is the product of the uniform measures on the
coordinate spaces `Fin k`.  This module transports the bounded-differences inequality
`Work.Deep.Reed.Prob.hoeffding_bounded_differences` — proved for an abstract product of finite
probability spaces in `Submission/Work/Deep/Reed/Prob/` — to `colSpace`.

The bridge is elementary: both measures have constant weight, and

* the weight of the product measure `FinProb.pi (fun _ : V => FinProb.uniform (Fin k))` at a
  colouring `f` is `∏ i, k⁻¹ = (k ^ card V)⁻¹`, which by `card_colSpace` is exactly the weight
  of `colSpace V k` at `f` (`pi_uniform_wt_colSpace`),
* hence the two measures agree on probabilities (`colSpace_prob_eq_pi_prob`) and on
  expectations (`colSpace_expect_eq_pi_exp`).

`azuma_finSpace` is then immediate for `k > 0`.  When `k = 0` the hypothesis
`Nonempty (V → Fin k)` forces `V` to be empty, so the variance `∑ i, c i ^ 2` vanishes, the right
hand side is `2·exp 0 = 2`, and the (crude) bound `prob ≤ 1` finishes.

This is the concentration input of the naive colouring procedure of Molloy--Reed.
-/
import Submission.Work.Deep.Sparse.Prelude
import Submission.Work.Deep.Sparse.ProbBasic
import Submission.Work.Deep.Reed.Prob.hoeffding_bounded_differences

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open scoped BigOperators

namespace Work.Deep.Sparse

variable {V : Type*} [Fintype V] [DecidableEq V] {k : ℕ} [Nonempty (Fin k)]

/-- The product of the uniform measures on the coordinates `V` carries the same weight as the
uniform measure `colSpace V k` on the colourings. -/
theorem pi_uniform_wt_colSpace (f : V → Fin k) :
    (Work.Deep.Reed.FinProb.pi (fun _ : V => Work.Deep.Reed.FinProb.uniform (Fin k))).wt f
      = (colSpace (V := V) k).mass f := by
  have h1 : ∀ i : V, (Work.Deep.Reed.FinProb.uniform (Fin k)).wt (f i) = (k : ℝ)⁻¹ := by
    intro i; simp [Work.Deep.Reed.FinProb.uniform]
  rw [Work.Deep.Reed.FinProb.pi_wt, colSpace_mass, card_colSpace]
  rw [Finset.prod_congr rfl (fun i _ => h1 i)]
  rw [Finset.prod_const, Finset.card_univ, Nat.cast_pow, inv_pow]

/-- `colSpace` and the product of the uniform measures on the coordinates have the same
probabilities. -/
theorem colSpace_prob_eq_pi_prob (A : Set (V → Fin k)) :
    (colSpace (V := V) k).prob A
      = (Work.Deep.Reed.FinProb.pi (fun _ : V => Work.Deep.Reed.FinProb.uniform (Fin k))).prob A := by
  classical
  rw [Work.Deep.Reed.FinProb.prob, FinSpace.prob]
  refine Finset.sum_congr rfl fun f _ => ?_
  by_cases h : f ∈ A
  · rw [if_pos h, Set.indicator_of_mem h, pi_uniform_wt_colSpace f]
  · rw [if_neg h, Set.indicator_of_notMem h]

/-- `colSpace` and the product of the uniform measures on the coordinates have the same
expectations. -/
theorem colSpace_expect_eq_pi_exp (X : (V → Fin k) → ℝ) :
    (colSpace (V := V) k).expect X
      = (Work.Deep.Reed.FinProb.pi (fun _ : V => Work.Deep.Reed.FinProb.uniform (Fin k))).exp X := by
  rw [Work.Deep.Reed.FinProb.exp, FinSpace.expect]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [pi_uniform_wt_colSpace f]

/-- **Azuma--Hoeffding (McDiarmid's bounded differences inequality) for the uniform colouring
space.**  If changing the colour of a single vertex `i` changes `X` by at most `c i`, then `X` is
concentrated around its mean: `Pr[|X - E X| > t] ≤ 2 exp(-2t² / ∑ i, c i²)`. -/
theorem azuma_finSpace {V : Type*} [Fintype V] [DecidableEq V] {k : ℕ} [Nonempty (V → Fin k)]
    (X : (V → Fin k) → ℝ) (c : V → ℝ) (hc : ∀ i, 0 ≤ c i)
    (hlip : ∀ (i : V) (f : V → Fin k) (x : Fin k),
      |X (Function.update f i x) - X f| ≤ c i) :
    ∀ t : ℝ, 0 ≤ t →
      (Work.Deep.Sparse.colSpace (V := V) k).prob
          {f : V → Fin k | t < |X f - (Work.Deep.Sparse.colSpace (V := V) k).expect X|}
        ≤ 2 * Real.exp (-(2 * t ^ 2) / ∑ i, (c i) ^ 2) := by
  intro t ht
  classical
  rcases k with _ | k'
  · -- `k = 0`: then `V` is empty, the variance term vanishes and the bound is `2`.
    have hsum0 : ∑ i : V, (c i) ^ 2 = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      obtain ⟨f⟩ := (inferInstance : Nonempty (V → Fin 0))
      exact absurd (f i).isLt (Nat.not_lt_zero _)
    have hRHS : 2 * Real.exp (-(2 * t ^ 2) / ∑ i, (c i) ^ 2) = 2 := by
      rw [hsum0, div_zero, Real.exp_zero, mul_one]
    rw [hRHS]
    exact le_trans (FinSpace.prob_le_one _ _) (by norm_num)
  · -- `k = k' + 1 > 0`: transfer to the product measure and apply Azuma--Hoeffding.
    haveI : Nonempty (Fin (k' + 1)) := ⟨⟨0, Nat.succ_pos k'⟩⟩
    rw [colSpace_prob_eq_pi_prob (A := {f : V → Fin (k' + 1) |
          t < |X f - (colSpace (V := V) (k' + 1)).expect X|}),
      colSpace_expect_eq_pi_exp (X := X)]
    exact Work.Deep.Reed.Prob.hoeffding_bounded_differences
      (fun _ : V => Work.Deep.Reed.FinProb.uniform (Fin (k' + 1))) X c hc hlip ht

end Work.Deep.Sparse
