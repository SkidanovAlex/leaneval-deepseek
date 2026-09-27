import Mathlib
import Submission.Work.EKLComp.Core
import Submission.Work.EKLComp.sum_prod_mul_log_fst
import Submission.Work.EKLComp.sum_prod_mul_log_snd

/-!
# Subadditivity of the entropy of a joint weight on a product of finite types

For a nonnegative weight `p : ι × κ → ℝ` (not assumed to be normalised to mass `1`),
the entropy `∑ -p log p` of the joint weight is at most the sum of the entropies of
its two marginals minus the entropy of the total mass `P = ∑ p`:

`∑ q, negMulLog (p q) ≤ ∑ i, negMulLog (∑ j, p (i,j))
                       + ∑ j, negMulLog (∑ i, p (i,j)) - negMulLog (∑ q, p q)`.

The proof is the finite Gibbs (log-sum) inequality applied to the comparison weight
`q ↦ (∑_j p (i,j)) (∑_i p (i,j)) / P`, whose total mass equals that of `p`.  The
termwise computation which turns the resulting `∑ p log (p / q)` into the stated
combination of marginal entropies is isolated in `negMulLog_prod_split`, and the
cross sum is computed in `sum_prod_div_eq`.
-/

open scoped BigOperators

namespace Work.EKLComp

/-- Splitting the logarithm of `a` against the three factors `u`, `v`, `P` which
satisfy `u ≥ a`, `v ≥ a`, `0 < P`.  Writing `a = (u v / P) · (a / (u v / P))` and
expanding `log (u v / P) = log u + log v - log P` gives the termwise identity used
in the proof of `entropy_prod_le`. -/
theorem negMulLog_prod_split {a u v P : ℝ} (ha : 0 ≤ a) (hu : a ≤ u) (hv : a ≤ v)
    (hP : 0 < P) :
    Real.negMulLog a = -(a * Real.log u) - (a * Real.log v) + a * Real.log P
      - a * Real.log (a / (u * v / P)) := by
  rcases eq_or_lt_of_le ha with h0 | h0
  · rw [← h0]
    simp [Real.negMulLog_def]
  · have hu' : 0 < u := lt_of_lt_of_le h0 hu
    have hv' : 0 < v := lt_of_lt_of_le h0 hv
    have huv : u * v ≠ 0 := ne_of_gt (mul_pos hu' hv')
    have huvP : u * v / P ≠ 0 := div_ne_zero huv (ne_of_gt hP)
    have hlog : Real.log a = Real.log u + Real.log v - Real.log P
        + Real.log (a / (u * v / P)) := by
      have h1 : Real.log a = Real.log (u * v / P) + Real.log (a / (u * v / P)) := by
        rw [← Real.log_mul huvP (div_ne_zero (ne_of_gt h0) huvP)]
        congr 1
        field_simp
      rw [h1, Real.log_div huv (ne_of_gt hP), Real.log_mul (ne_of_gt hu') (ne_of_gt hv')]
    simp only [Real.negMulLog_def]
    rw [hlog]
    ring

/-- The cross sum of a product weight factors: `∑_{i,j} A i B j / P = (∑ A)(∑ B)/P`.
No hypothesis on `P` is needed, the identity is an algebraic one for the total
division convention of `ℝ`. -/
theorem sum_prod_div_eq {ι κ : Type*} [Fintype ι] [Fintype κ] (A : ι → ℝ) (B : κ → ℝ)
    (P : ℝ) :
    ∑ q : ι × κ, A q.1 * B q.2 / P = (∑ i, A i) * (∑ j, B j) / P := by
  have h1 : ∑ q : ι × κ, A q.1 * B q.2 = (∑ i, A i) * (∑ j, B j) := by
    rw [Core.sum_prod_univ]
    rw [Finset.sum_congr rfl (fun i _ => (Finset.mul_sum Finset.univ B (A i)).symm)]
    exact (Finset.sum_mul Finset.univ A (∑ j, B j)).symm
  rw [← Finset.sum_div, h1]

theorem entropy_prod_le {ι κ : Type*} [Fintype ι] [Fintype κ] (p : ι × κ → ℝ)
    (hp : ∀ q, 0 ≤ p q) :
    ∑ q, Real.negMulLog (p q) ≤ ∑ i, Real.negMulLog (∑ j, p (i, j))
      + ∑ j, Real.negMulLog (∑ i, p (i, j)) - Real.negMulLog (∑ q, p q) := by
  classical
  set P : ℝ := ∑ q : ι × κ, p q with hPdef
  have hPnn : 0 ≤ P := by
    rw [hPdef]; exact Finset.sum_nonneg fun q _ => hp q
  by_cases hP0 : P = 0
  · -- degenerate case: all the weight is zero
    have hpz : ∀ q : ι × κ, p q = 0 := by
      intro q
      have hle := Finset.single_le_sum (f := p) (fun q _ => hp q) (Finset.mem_univ q)
      have hzero : ∑ q : ι × κ, p q = 0 := by rw [← hPdef]; exact hP0
      linarith [hp q]
    have h1 : ∑ q : ι × κ, Real.negMulLog (p q) = 0 :=
      Finset.sum_eq_zero fun q _ => by rw [hpz q, Real.negMulLog_zero]
    have h2 : ∑ i, Real.negMulLog (∑ j, p (i, j)) = 0 :=
      Finset.sum_eq_zero fun i _ => by
        rw [Finset.sum_eq_zero fun j _ => hpz (i, j), Real.negMulLog_zero]
    have h3 : ∑ j, Real.negMulLog (∑ i, p (i, j)) = 0 :=
      Finset.sum_eq_zero fun j _ => by
        rw [Finset.sum_eq_zero fun i _ => hpz (i, j), Real.negMulLog_zero]
    rw [h1, h2, h3, hP0, Real.negMulLog_zero]
    simp
  · have hPpos : 0 < P := lt_of_le_of_ne hPnn (Ne.symm hP0)
    have hAnn : ∀ i, 0 ≤ ∑ j, p (i, j) := fun i => Finset.sum_nonneg fun j _ => hp (i, j)
    have hBnn : ∀ j, 0 ≤ ∑ i, p (i, j) := fun j => Finset.sum_nonneg fun i _ => hp (i, j)
    have hrow : ∑ i, (∑ j, p (i, j)) = P := by
      rw [← Core.sum_prod_univ (f := p), ← hPdef]
    have hcol : ∑ j, (∑ i, p (i, j)) = P := by
      rw [Finset.sum_comm, ← Core.sum_prod_univ (f := p), ← hPdef]
    -- the comparison weight `(∑_j p) (∑_i p) / P` has the same total mass as `p`
    have hcross : ∑ q : ι × κ, (∑ j, p (q.1, j)) * (∑ i, p (i, q.2)) / P = P := by
      rw [sum_prod_div_eq (fun i => ∑ j, p (i, j)) (fun j => ∑ i, p (i, j)) P, hrow, hcol]
      field_simp
    -- finite Gibbs inequality
    have hgibbs : 0 ≤ ∑ q : ι × κ,
        p q * Real.log (p q / ((∑ j, p (q.1, j)) * (∑ i, p (i, q.2)) / P)) := by
      refine Core.sum_mul_log_div_nonneg (fun q : ι × κ => p q)
        (fun q : ι × κ => (∑ j, p (q.1, j)) * (∑ i, p (i, q.2)) / P) hp ?_ ?_ ?_
      · intro q
        exact div_nonneg (mul_nonneg (hAnn q.1) (hBnn q.2)) (le_of_lt hPpos)
      · rw [← hPdef, hcross]
      · intro q hq
        refine div_pos (mul_pos ?_ ?_) hPpos
        · exact lt_of_lt_of_le hq
            (Finset.single_le_sum (fun j _ => hp (q.1, j)) (Finset.mem_univ q.2))
        · exact lt_of_lt_of_le hq
            (Finset.single_le_sum (fun i _ => hp (i, q.2)) (Finset.mem_univ q.1))
    -- termwise splitting of `negMulLog`
    have hterm : ∀ q : ι × κ,
        Real.negMulLog (p q) = -(p q * Real.log (∑ j, p (q.1, j)))
          - (p q * Real.log (∑ i, p (i, q.2))) + p q * Real.log P
          - p q * Real.log (p q / ((∑ j, p (q.1, j)) * (∑ i, p (i, q.2)) / P)) := by
      intro q
      exact negMulLog_prod_split (hp q)
        (Finset.single_le_sum (fun j _ => hp (q.1, j)) (Finset.mem_univ q.2))
        (Finset.single_le_sum (fun i _ => hp (i, q.2)) (Finset.mem_univ q.1)) hPpos
    have hsum1 : ∑ q : ι × κ, p q * Real.log (∑ j, p (q.1, j))
        = ∑ i, (∑ j, p (i, j)) * Real.log (∑ j, p (i, j)) :=
      sum_prod_mul_log_fst p (fun i => ∑ j, p (i, j))
    have hsum2 : ∑ q : ι × κ, p q * Real.log (∑ i, p (i, q.2))
        = ∑ j, (∑ i, p (i, j)) * Real.log (∑ i, p (i, j)) :=
      sum_prod_mul_log_snd p (fun j => ∑ i, p (i, j))
    have hsum3 : ∑ q : ι × κ, p q * Real.log P = P * Real.log P :=
      (Finset.sum_mul Finset.univ p (Real.log P)).symm
    have hkey : ∑ q : ι × κ, Real.negMulLog (p q)
        = -(∑ i, (∑ j, p (i, j)) * Real.log (∑ j, p (i, j)))
          - (∑ j, (∑ i, p (i, j)) * Real.log (∑ i, p (i, j)))
          + P * Real.log P
          - ∑ q : ι × κ,
              p q * Real.log (p q / ((∑ j, p (q.1, j)) * (∑ i, p (i, q.2)) / P)) := by
      rw [Finset.sum_congr rfl (fun q _ => hterm q)]
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_sub_distrib,
        Finset.sum_neg_distrib, hsum1, hsum2, hsum3]
    have e1 : (∑ i, (∑ j, p (i, j)) * Real.log (∑ j, p (i, j)))
        = - ∑ i, Real.negMulLog (∑ j, p (i, j)) := by
      simp only [Real.negMulLog_eq_neg, Finset.sum_neg_distrib, neg_neg]
    have e2 : (∑ j, (∑ i, p (i, j)) * Real.log (∑ i, p (i, j)))
        = - ∑ j, Real.negMulLog (∑ i, p (i, j)) := by
      simp only [Real.negMulLog_eq_neg, Finset.sum_neg_distrib, neg_neg]
    have e3 : P * Real.log P = - Real.negMulLog P := by
      simp only [Real.negMulLog_eq_neg, neg_neg]
    have hD : ∑ q : ι × κ, Real.negMulLog (p q)
        = (∑ i, Real.negMulLog (∑ j, p (i, j))
            + ∑ j, Real.negMulLog (∑ i, p (i, j)) - Real.negMulLog P)
          - ∑ q : ι × κ,
              p q * Real.log (p q / ((∑ j, p (q.1, j)) * (∑ i, p (i, q.2)) / P)) := by
      rw [hkey, e1, e2, e3]
      ring
    linarith [hD, hgibbs]

end Work.EKLComp
