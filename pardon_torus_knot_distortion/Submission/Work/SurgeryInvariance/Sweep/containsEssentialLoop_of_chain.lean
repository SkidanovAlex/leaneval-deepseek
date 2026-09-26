import Mathlib
import Submission.Work.SurgeryInvariance.Core

namespace Work.SurgeryInvariance.Sweep

/-- A single step of the chain — a `2`-surgery (`SurgeryShape`) or a regular variation
(`RegionIsotopic`) — does not change the winding span of the region.  This is the combination of
the two "no change" steps `SurgeryShape.windingSpan_eq` and `RegionIsotopic.windingSpan_eq`. -/
theorem windingSpan_eq_of_step {P : Work.CoreTopology.ParamTorus}
    {A A' : Set LeanEval.KnotTheory.PardonDistortion.R3}
    (h : Work.SurgeryInvariance.SurgeryShape P A A' ∨
      Work.SurgeryInvariance.RegionIsotopic P A A') :
    Work.SurgeryInvariance.WindingSpan P A = Work.SurgeryInvariance.WindingSpan P A' :=
  h.elim Work.SurgeryInvariance.SurgeryShape.windingSpan_eq
    Work.SurgeryInvariance.RegionIsotopic.windingSpan_eq

/-- **The winding span is invariant along a finite chain of `2`-surgeries and regular
variations.** -/
theorem windingSpan_chain_eq {P : Work.CoreTopology.ParamTorus}
    {A : ℕ → Set LeanEval.KnotTheory.PardonDistortion.R3} {n : ℕ}
    (hstep : ∀ i : ℕ, i < n →
      Work.SurgeryInvariance.SurgeryShape P (A i) (A (i + 1)) ∨
        Work.SurgeryInvariance.RegionIsotopic P (A i) (A (i + 1))) :
    Work.SurgeryInvariance.WindingSpan P (A n) = Work.SurgeryInvariance.WindingSpan P (A 0) := by
  have key : ∀ k : ℕ,
      (∀ i : ℕ, i < k →
        Work.SurgeryInvariance.SurgeryShape P (A i) (A (i + 1)) ∨
          Work.SurgeryInvariance.RegionIsotopic P (A i) (A (i + 1))) →
      Work.SurgeryInvariance.WindingSpan P (A k) =
        Work.SurgeryInvariance.WindingSpan P (A 0) := by
    intro k
    induction k with
    | zero => intro _; rfl
    | succ m ih =>
      intro hs
      have hsm : ∀ i : ℕ, i < m →
          Work.SurgeryInvariance.SurgeryShape P (A i) (A (i + 1)) ∨
            Work.SurgeryInvariance.RegionIsotopic P (A i) (A (i + 1)) :=
        fun i hi => hs i (Nat.lt_succ_of_lt hi)
      have hmem : Work.SurgeryInvariance.WindingSpan P (A m) =
          Work.SurgeryInvariance.WindingSpan P (A (m + 1)) :=
        windingSpan_eq_of_step (hs m (Nat.lt_succ_self m))
      exact hmem.symm.trans (ih hsm)
  exact key n hstep

theorem containsEssentialLoop_of_chain {P : Work.CoreTopology.ParamTorus}
    {A : ℕ → Set LeanEval.KnotTheory.PardonDistortion.R3} {n : ℕ}
    (hstep : ∀ i : ℕ, i < n →
      Work.SurgeryInvariance.SurgeryShape P (A i) (A (i + 1)) ∨
        Work.SurgeryInvariance.RegionIsotopic P (A i) (A (i + 1)))
    (h : P.ContainsEssentialLoop (A 0)) : P.ContainsEssentialLoop (A n) := by
  rw [← Work.SurgeryInvariance.windingSpan_ne_bot_iff P (A n),
    windingSpan_chain_eq hstep]
  exact (Work.SurgeryInvariance.windingSpan_ne_bot_iff P (A 0)).mpr h

end Work.SurgeryInvariance.Sweep
