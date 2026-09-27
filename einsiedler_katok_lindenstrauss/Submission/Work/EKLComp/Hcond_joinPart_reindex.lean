import Mathlib
import Submission.Work.EKLComp.USCBasic

namespace Work.EKLComp

open MeasureTheory

/-- Reindexing the join `joinPart__USCBasic P Q` (indexed by `Fin (P.n * Q.n)` via
`finProdFinEquiv`) turns `Hcond μ (joinPart__USCBasic P Q) m` into the double sum over the
pairs of atoms `P.parts i ∩ Q.parts j`. This is a purely combinatorial rewriting:
the two sides are the integrals of pointwise equal functions. -/
theorem Hcond_joinPart_reindex {X : Type} {m : MeasurableSpace X} [mX : MeasurableSpace X]
    (μ : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure μ]
    (P Q : Work.EKLContract.FinPart X) :
    @Work.EKLContract.Hcond X mX μ (@Work.EKLComp.joinPart__USCBasic X mX P Q) m
      = ∫ x, ∑ i : Fin P.n, ∑ j : Fin Q.n,
          Real.negMulLog (MeasureTheory.condExp m μ
            ((P.parts i ∩ Q.parts j).indicator (fun _ => (1 : ℝ))) x) ∂μ := by
  unfold Work.EKLContract.Hcond
  congr 1
  funext x
  have hF : (∑ k : Fin ((Work.EKLComp.joinPart__USCBasic P Q).n),
        Real.negMulLog (MeasureTheory.condExp m μ
          (((Work.EKLComp.joinPart__USCBasic P Q).parts k).indicator (fun _ => (1 : ℝ))) x))
      = ∑ p : Fin P.n × Fin Q.n,
        Real.negMulLog (MeasureTheory.condExp m μ
          (((Work.EKLComp.joinPart__USCBasic P Q).parts (finProdFinEquiv p)).indicator
            (fun _ => (1 : ℝ))) x) :=
    (Equiv.sum_comp finProdFinEquiv _).symm
  refine hF.trans ?_
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  rw [Work.EKLComp.joinPart_parts__USCBasic, Equiv.symm_apply_apply]

end Work.EKLComp
