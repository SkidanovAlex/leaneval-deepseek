import Mathlib
import Submission.Work.EKLC6Core.Hcond_mono
import Submission.Work.EKLComp.Hcond_joinTwo
import Submission.Work.EKLC6Core.Basic
import Submission.Work.EKLC6Core.Hcond_nonneg

/-!
# Subadditivity of the conditional entropy: `H_μ(P|m) ≤ H_μ(Q|m) + H_μ(P|m ∨ σ(Q))`

The conditional entropy of a finite partition `P` given a σ-algebra `m` satisfies

`H_μ(P | m) ≤ H_μ(Q | m) + H_μ(P | m ∨ σ(Q))`

for every second finite partition `Q`: the information that `Q` carries about `P` is at most the
entropy of `Q` itself.  Equivalently, the conditional mutual information `I_μ(P; Q | m)` is
nonnegative.

The proof is the entropy chain rule for the join `P ∨ Q` (`Work.EKLComp.Hcond_joinTwo`),

`H_μ(P ∨ Q | m) = H_μ(P | m) + H_μ(Q | m ∨ σ P) = H_μ(Q | m) + H_μ(P | m ∨ σ Q)`,

of which the first term on the right is `≥ 0`, so `H_μ(P|m) ≤ H_μ(P|m) + H_μ(Q | m ∨ σ P)`, and
`P ∨ Q` and `Q ∨ P` have the same conditional entropy (their atoms are the same sets, in a
different index order).  We therefore need only the nonnegativity of the conditional entropy and
the order independence of the join; both are proved below.

**Formalisation note.**  A local hypothesis of class type (`m : MeasurableSpace X`) is an instance
candidate for Lean's typeclass search and is *more recent* than the ambient instance `mX`, so
inside the proofs below every occurrence of a structure projection of `P : @FinPart X mX`
(`P.parts`, `P.measurable`, …) is written with its instance argument explicit: typeclass search
would otherwise silently instantiate it at `m`.
-/

open MeasureTheory Filter
open scoped BigOperators

noncomputable section

namespace Work.EKLC6Core

/-- **Nonnegativity of the conditional entropy**: `H_μ(P | m) ≥ 0` for every finite partition `P`
and every σ-algebra `m`.  Each summand `-𝔼[1_{P_i}|m] log 𝔼[1_{P_i}|m]` of the integrand is
nonnegative because `𝔼[1_{P_i}|m] ∈ [0,1]` a.e.; if `m` is not a sub-σ-algebra of the ambient one
the conditional expectation vanishes identically. -/
lemma Hcond_nonneg_aux {X : Type*} [mX : MeasurableSpace X] (μ : MeasureTheory.Measure X)
    [MeasureTheory.IsProbabilityMeasure μ] (P : @Work.EKLContract.FinPart X mX)
    (m : MeasurableSpace X) :
    0 ≤ @Work.EKLContract.Hcond X mX μ P m := by
  by_cases hm : m ≤ mX
  · rw [Hcond_eq_sum_integral (mX := mX) (m := m) (μ := μ) P]
    refine Finset.sum_nonneg (fun i _ => ?_)
    refine integral_nonneg_of_ae ?_
    have hIcc := condExp_mem_Icc (mX := mX) (m := m) (μ := μ) hm
      (Filter.Eventually.of_forall fun x =>
        (indicator_mem_Icc (@Work.EKLContract.FinPart.parts X mX P i) x).1)
      (Filter.Eventually.of_forall fun x =>
        (indicator_mem_Icc (@Work.EKLContract.FinPart.parts X mX P i) x).2)
      ((integrable_const (1 : ℝ)).indicator (@Work.EKLContract.FinPart.measurable X mX P i))
    filter_upwards [hIcc] with x hx
    exact Real.negMulLog_nonneg hx.1 hx.2
  · rw [Hcond_eq_zero_of_not_le (mX := mX) (m := m) (μ := μ) P hm]

/-- **Order independence of the join**: the conditional entropy of the common refinement
`joinTwo P Q` does not depend on the order of the two factors.  The atoms of `joinTwo P Q` are the
sets `P.parts i ∩ Q.parts j`, those of `joinTwo Q P` the same sets with the two indices exchanged;
the two sums are exchanged by `Finset.sum_comm`. -/
lemma Hcond_joinTwo_comm {X : Type*} [mX : MeasurableSpace X] (μ : MeasureTheory.Measure X)
    [MeasureTheory.IsProbabilityMeasure μ] (P Q : @Work.EKLContract.FinPart X mX)
    (m : MeasurableSpace X) :
    @Work.EKLContract.Hcond X mX μ (@Work.EKLComp.joinTwo X mX P Q) m
      = @Work.EKLContract.Hcond X mX μ (@Work.EKLComp.joinTwo X mX Q P) m := by
  rw [Work.EKLComp.Hcond_joinTwo_reindex (mX := mX) (m := m) (μ := μ) P Q,
    Work.EKLComp.Hcond_joinTwo_reindex (mX := mX) (m := m) (μ := μ) Q P]
  congr 1
  funext x
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun i _ => ?_))
  rw [Set.inter_comm]

theorem Hcond_le_Hcond_add {X : Type*} [mX : MeasurableSpace X] (μ : MeasureTheory.Measure X)
    [MeasureTheory.IsProbabilityMeasure μ] (P Q : @Work.EKLContract.FinPart X mX) (m : MeasurableSpace X) :
    @Work.EKLContract.Hcond X mX μ P m
      ≤ @Work.EKLContract.Hcond X mX μ Q m
        + @Work.EKLContract.Hcond X mX μ P ((@Work.EKLContract.partSigma X mX Q) ⊔ m) := by
  have h1 : @Work.EKLContract.Hcond X mX μ P m
      ≤ @Work.EKLContract.Hcond X mX μ (@Work.EKLComp.joinTwo X mX P Q) m := by
    rw [Work.EKLComp.Hcond_joinTwo (mX := mX) (μ := μ) P Q m]
    exact le_add_of_nonneg_right
      (Hcond_nonneg_aux (mX := mX) (μ := μ) Q (m ⊔ @Work.EKLContract.partSigma X mX P))
  calc @Work.EKLContract.Hcond X mX μ P m
      ≤ @Work.EKLContract.Hcond X mX μ (@Work.EKLComp.joinTwo X mX P Q) m := h1
    _ = @Work.EKLContract.Hcond X mX μ (@Work.EKLComp.joinTwo X mX Q P) m :=
        Hcond_joinTwo_comm (mX := mX) (μ := μ) P Q m
    _ = @Work.EKLContract.Hcond X mX μ Q m
        + @Work.EKLContract.Hcond X mX μ P (m ⊔ @Work.EKLContract.partSigma X mX Q) :=
        Work.EKLComp.Hcond_joinTwo (mX := mX) (μ := μ) Q P m
    _ = @Work.EKLContract.Hcond X mX μ Q m
        + @Work.EKLContract.Hcond X mX μ P ((@Work.EKLContract.partSigma X mX Q) ⊔ m) := by
        rw [sup_comm]

end Work.EKLC6Core

end
