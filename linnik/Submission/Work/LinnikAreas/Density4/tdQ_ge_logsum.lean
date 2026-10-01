/-
# Area 4 / HB §11 — the saving sum `tdQ` dominates the log-sum `Σ (M-1-log n)/n`

The saving sum `tdQ σ A M = Σ_{2 ≤ n ≤ ⌊e^{M-1}⌋} (M - log n - 1) n^{σ-1} e^{-n/A}` of the
diagonal evaluation is compared, term by term, with the elementary log-sum
`Σ_{2 ≤ n ≤ ⌊e^{M-2}⌋} (M - 1 - log n)/n` (which is evaluated by
`diag_logsum_lower`: it is `≥ 0.45 M²`, while `thetaDiag_Q_lower` shows
`tdQ ≥ 0.34 M²`; the present lemma is the bridge between the two, with the constant `6/7`).

On the smaller range `n ≤ e^{M-2}` both the weight `c n = M - 1 - log n ≥ 1` and `n` are
positive, and

  `tdH σ A n = n^{σ-1} e^{-n/A} = (n^σ / n) · e^{-n/A} ≥ (6/7)/n`,

because `n ≥ 2` and `σ > 0` give `n^σ ≥ 1`, while `n/A ≤ e^{M-2}/e^M = e^{-2}` gives
`e^{-n/A} ≥ 1 - n/A ≥ 1 - e^{-2} ≥ 6/7`.  This is `tdH_termwise_ge`.  The remaining terms
(`e^{M-2} < n ≤ e^{M-1}`) are nonnegative (`tdQ_summand_nonneg`), and the range inclusion is
monotonicity of `Nat.floor`.

It is sorry-free.
-/
import Mathlib
import Submission.Work.LinnikAreas.Density4.thetaDiag_eval_defs
import Submission.Work.LinnikAreas.Density4.tdH_termwise_ge
import Submission.Work.LinnikAreas.Density4.tdQ_summand_nonneg

open scoped BigOperators
noncomputable section

namespace Work.LinnikAreas.Density4

theorem tdQ_ge_logsum (M σ A : ℝ) (hM : 15000 ≤ M) (hσ : 0 < σ) (hA : Real.exp M ≤ A) :
    (6/7) * (∑ n ∈ Finset.Icc 2 ⌊Real.exp (M-2)⌋₊, (M - 1 - Real.log n)/(n:ℝ))
      ≤ Work.LinnikAreas.Density4.tdQ σ A M := by
  -- rewrite `tdQ` with the coefficient written as `M - 1 - log n`
  have hQ : tdQ σ A M = ∑ n ∈ Finset.Icc 2 ⌊Real.exp (M-1)⌋₊,
      (M - 1 - Real.log (n:ℝ))*tdH σ A n := by
    rw [tdQ]
    apply Finset.sum_congr rfl
    intro n _
    ring
  -- the range of the log-sum is contained in the range of `tdQ`
  have hsub : Finset.Icc 2 ⌊Real.exp (M-2)⌋₊ ⊆ Finset.Icc 2 ⌊Real.exp (M-1)⌋₊ :=
    Finset.Icc_subset_Icc le_rfl (Nat.floor_mono (Real.exp_le_exp.mpr (by linarith)))
  -- the extra terms are nonnegative
  have hnonneg : ∀ n ∈ Finset.Icc 2 ⌊Real.exp (M-1)⌋₊,
      n ∉ Finset.Icc 2 ⌊Real.exp (M-2)⌋₊ → 0 ≤ (M - 1 - Real.log (n:ℝ)) * tdH σ A n := by
    intro n hn _
    have h := tdQ_summand_nonneg M σ A hM n hn
    have heq : M - 1 - Real.log (n:ℝ) = M - Real.log (n:ℝ) - 1 := by ring
    rwa [heq]
  rw [hQ]
  calc (6/7) * (∑ n ∈ Finset.Icc 2 ⌊Real.exp (M-2)⌋₊, (M - 1 - Real.log (n:ℝ))/(n:ℝ))
      = ∑ n ∈ Finset.Icc 2 ⌊Real.exp (M-2)⌋₊,
          (6/7) * ((M - 1 - Real.log (n:ℝ))/(n:ℝ)) := by
        rw [Finset.mul_sum]
    _ ≤ ∑ n ∈ Finset.Icc 2 ⌊Real.exp (M-2)⌋₊, (M - 1 - Real.log (n:ℝ))*tdH σ A n :=
        Finset.sum_le_sum fun n hn => tdH_termwise_ge M σ A hM hσ hA n hn
    _ ≤ ∑ n ∈ Finset.Icc 2 ⌊Real.exp (M-1)⌋₊, (M - 1 - Real.log (n:ℝ))*tdH σ A n :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub hnonneg

end Work.LinnikAreas.Density4
