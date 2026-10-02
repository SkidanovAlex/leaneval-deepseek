import Submission.Work.Deep.Sparse.Prelude
import Submission.Work.Deep.Reed.Prob.Expectation
import Submission.Work.Deep.Reed.Prob.pi_prob_inter_eq_mul_of_disjoint

namespace Work.Deep.Reed.Prob

/-- **Disintegration at one coordinate, for expectations** (the `exp` analogue of
`FinProb.freeze_sum`): `(pi μ).exp Z = ∑ x, (μ j).wt x * (pi (freeze μ j x)).exp Z`.

Proof sketch: mirror the proof of `FinProb.freeze_sum` in
`Submission/Work/Deep/Reed/Prob/pi_prob_inter_eq_mul_of_disjoint.lean`: unfold `exp` via
`show (∑ f, (pi μ).wt f * Z f) = …` and `pi_wt_split`, apply `FinProb.freeze_wt_sum`
pointwise to replace `(μ j).wt (f j) * P` by `∑ x, (μ j).wt x * (P * (point x).wt (f j))`,
distribute the sum (`Finset.sum_mul`), interchange the two sums (`Finset.sum_comm`,
`Finset.mul_sum`) — using `Finset.sum_congr … (fun x _ => by ring)` for reassociation —
and recognise `FinProb.pi_freeze_wt`. -/
lemma freeze_exp {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)] (μ : ∀ i, Work.Deep.Reed.FinProb (Ω i)) (j : ι)
    (Z : (∀ i, Ω i) → ℝ) :
    (Work.Deep.Reed.FinProb.pi μ).exp Z
      = ∑ x : Ω j, (μ j).wt x * (Work.Deep.Reed.FinProb.pi (Work.Deep.Reed.FinProb.freeze μ j x)).exp Z := by
  have hLHS : (Work.Deep.Reed.FinProb.pi μ).exp Z
      = ∑ f, ((μ j).wt (f j) * ∏ i ∈ Finset.univ.erase j, (μ i).wt (f i)) * Z f := by
    rw [Work.Deep.Reed.FinProb.exp]
    exact Finset.sum_congr rfl fun f _ => by rw [Work.Deep.Reed.FinProb.pi_wt_split]
  have hRHS : ∀ x : Ω j,
      (Work.Deep.Reed.FinProb.pi (Work.Deep.Reed.FinProb.freeze μ j x)).exp Z
      = ∑ f, ((∏ i ∈ Finset.univ.erase j, (μ i).wt (f i))
          * (Work.Deep.Reed.FinProb.point x).wt (f j)) * Z f := by
    intro x
    rw [Work.Deep.Reed.FinProb.exp]
    exact Finset.sum_congr rfl fun f _ => by rw [Work.Deep.Reed.FinProb.pi_freeze_wt]
  rw [hLHS]
  calc ∑ f, ((μ j).wt (f j) * ∏ i ∈ Finset.univ.erase j, (μ i).wt (f i)) * Z f
      = ∑ f, ∑ x : Ω j, (μ j).wt x * ((∏ i ∈ Finset.univ.erase j, (μ i).wt (f i))
          * (Work.Deep.Reed.FinProb.point x).wt (f j) * Z f) := by
        refine Finset.sum_congr rfl fun f _ => ?_
        calc ((μ j).wt (f j) * ∏ i ∈ Finset.univ.erase j, (μ i).wt (f i)) * Z f
            = Z f * ((μ j).wt (f j)
                * ∏ i ∈ Finset.univ.erase j, (μ i).wt (f i)) := by ring
          _ = Z f * ∑ x : Ω j, (μ j).wt x * ((∏ i ∈ Finset.univ.erase j, (μ i).wt (f i))
              * (Work.Deep.Reed.FinProb.point x).wt (f j)) := by
              rw [← Work.Deep.Reed.FinProb.freeze_wt_sum]
          _ = ∑ x : Ω j, (μ j).wt x * ((∏ i ∈ Finset.univ.erase j, (μ i).wt (f i))
              * (Work.Deep.Reed.FinProb.point x).wt (f j) * Z f) := by
              rw [Finset.mul_sum]
              exact Finset.sum_congr rfl fun x _ => by ring
    _ = ∑ x : Ω j, ∑ f, (μ j).wt x * ((∏ i ∈ Finset.univ.erase j, (μ i).wt (f i))
          * (Work.Deep.Reed.FinProb.point x).wt (f j) * Z f) := Finset.sum_comm
    _ = ∑ x : Ω j, (μ j).wt x * ∑ f, ((∏ i ∈ Finset.univ.erase j, (μ i).wt (f i))
          * (Work.Deep.Reed.FinProb.point x).wt (f j)) * Z f := by
        exact Finset.sum_congr rfl fun x _ => (Finset.mul_sum _ _ _).symm
    _ = ∑ x : Ω j, (μ j).wt x * (Work.Deep.Reed.FinProb.pi
          (Work.Deep.Reed.FinProb.freeze μ j x)).exp Z := by
        exact Finset.sum_congr rfl fun x _ => by rw [hRHS x]

end Work.Deep.Reed.Prob
