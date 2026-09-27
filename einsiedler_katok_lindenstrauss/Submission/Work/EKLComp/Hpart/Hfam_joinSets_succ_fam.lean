import Mathlib
import Submission.Work.EKLComp.Entropy

namespace Work.EKLComp.Hpart

open MeasureTheory
open Work.EKLContract

/-- Splitting off the first coordinate of a word.  The `(N+1)`-fold join of `P` along `T`
evaluated at `Fin.cons i v` is the intersection of `P.parts i` with the preimage under `T`
of the `N`-fold join at the tail `v`: this is exactly `(cons i v) 0 = i` together with
`T^[k.succ] x = T^[k] (T x)`. -/
theorem joinSets_succ_cons {X : Type} [MeasurableSpace X] (T : X → X) (P : FinPart X)
    (N : ℕ) (i : Fin P.n) (v : Fin N → Fin P.n) :
    joinSets T P (N + 1) (Fin.cons i v) = P.parts i ∩ T ⁻¹' joinSets T P N v := by
  ext x
  simp only [joinSets, Set.mem_iInter, Set.mem_preimage, Set.mem_inter_iff]
  rw [Fin.forall_fin_succ]
  constructor
  · rintro ⟨h0, hrest⟩
    refine ⟨?_, fun k => ?_⟩
    · simpa using h0
    · have hk := hrest k
      rw [show ((k.succ : Fin (N + 1)) : ℕ) = Nat.succ (k : ℕ) from rfl,
        Function.iterate_succ_apply] at hk
      exact hk
  · rintro ⟨h0, hrest⟩
    refine ⟨?_, fun k => ?_⟩
    · simpa using h0
    · rw [show ((k.succ : Fin (N + 1)) : ℕ) = Nat.succ (k : ℕ) from rfl,
        Function.iterate_succ_apply]
      exact hrest k

theorem Hfam_joinSets_succ_fam {X : Type} [mX : MeasurableSpace X] (μ : MeasureTheory.Measure X)
    [MeasureTheory.IsProbabilityMeasure μ] (T : X → X) (P : Work.EKLContract.FinPart X) (N : ℕ) :
    Work.EKLContract.Hfam μ (fun p : Fin P.n × (Fin N → Fin P.n) =>
        P.parts p.1 ∩ T ⁻¹' Work.EKLContract.joinSets T P N p.2)
      = Work.EKLContract.Hfam μ (Work.EKLContract.joinSets T P (N + 1)) := by
  rw [Hfam, Hfam]
  rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (N + 1) => Fin P.n))
        (fun w => Real.negMulLog (μ (joinSets T P (N + 1) w)).toReal)]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  change Real.negMulLog (μ (P.parts p.1 ∩ T ⁻¹' joinSets T P N p.2)).toReal
      = Real.negMulLog (μ (joinSets T P (N + 1) (Fin.cons p.1 p.2))).toReal
  rw [joinSets_succ_cons]

end Work.EKLComp.Hpart
