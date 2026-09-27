import Mathlib
import Submission.Work.EKLComp.C8Defs

namespace Work.EKLCompLeaf

open MeasureTheory Filter Topology
open scoped ENNReal Matrix

/-- **(U9) contrapositive + (U5), Step 0.**  If `μ` is `A`-ergodic and not `U_01`-invariant,
then the leafwise measures at `x` and at `u(s) • x` differ for every nonzero `s`, off a null
set.  The null set contains `X'ᶜ` and, crucially, is arranged so that the conclusion is only
asserted when both `x` and `u(s) • x` lie outside it -- so the equivariance of the leafwise
system (which is only available on `X'`) applies. -/
theorem step0_nontrivial {μ : MeasureTheory.Measure Work.EKLContract.X3}
    [MeasureTheory.IsProbabilityMeasure μ]
    {ν : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3}
    {X' : Set Work.EKLContract.X3}
    (hErg : Work.EKLContract.IsAErgodic μ)
    (hL : Work.EKLContract.IsLeafwise μ (Work.EKLContract.Uij Work.EKLComp.h01) ν X')
    (hU5 : Work.EKLComp.U5clause μ ν) (hU9 : Work.EKLComp.U9clause μ ν)
    (hninv : ¬ Work.EKLContract.IsUInvariant μ (Work.EKLContract.Uij Work.EKLComp.h01)) :
    ∃ N : Set Work.EKLContract.X3, μ N = 0 ∧ X'ᶜ ⊆ N ∧
      ∀ x ∉ N, ∀ s : ℝ, s ≠ 0 → Work.EKLComp.u s • x ∉ N →
        ν (Work.EKLComp.u s • x) ≠ ν x := by
  -- (U9) contrapositive: for a.e. `x` and every `s ≠ 0`, the pushed measure differs from `ν x`.
  have hAe9 : ∀ᵐ x ∂μ, ∀ s : ℝ, s ≠ 0 →
      (ν x).map (fun g => g * Work.EKLComp.u s) ≠ ν x := by
    by_contra h
    exact hninv (hU9 hErg h)
  -- (U5): proportionality implies equality, a.e.
  have hAe5 : ∀ᵐ x ∂μ, ∀ u ∈ (Work.EKLContract.Uij Work.EKLComp.h01 : Set Work.EKLContract.SL3),
      ∀ c : ℝ≥0∞, (ν x).map (fun g => g * u) = c • ν x →
        (ν x).map (fun g => g * u) = ν x := hU5
  rw [MeasureTheory.ae_iff] at hAe9 hAe5
  refine ⟨X'ᶜ ∪ {x | ¬ (∀ s : ℝ, s ≠ 0 →
            (ν x).map (fun g => g * Work.EKLComp.u s) ≠ ν x)}
          ∪ {x | ¬ (∀ u ∈ (Work.EKLContract.Uij Work.EKLComp.h01 : Set Work.EKLContract.SL3),
              ∀ c : ℝ≥0∞, (ν x).map (fun g => g * u) = c • ν x →
                (ν x).map (fun g => g * u) = ν x)}, ?_, ?_, ?_⟩
  · refine MeasureTheory.measure_union_null
      (MeasureTheory.measure_union_null hL.conull hAe9) hAe5
  · intro x hx
    exact Or.inl (Or.inl hx)
  · intro x hxN s hs husxN
    have hxX' : x ∈ X' := by
      by_contra h
      exact hxN (Or.inl (Or.inl h))
    have husxX' : Work.EKLComp.u s • x ∈ X' := by
      by_contra h
      exact husxN (Or.inl (Or.inl h))
    have hxA : ∀ s : ℝ, s ≠ 0 →
        (ν x).map (fun g => g * Work.EKLComp.u s) ≠ ν x := by
      by_contra hAll
      exact hxN (Or.inl (Or.inr hAll))
    have hxQ : ∀ u ∈ (Work.EKLContract.Uij Work.EKLComp.h01 : Set Work.EKLContract.SL3),
        ∀ c : ℝ≥0∞, (ν x).map (fun g => g * u) = c • ν x →
          (ν x).map (fun g => g * u) = ν x := by
      by_contra hAll
      exact hxN (Or.inr hAll)
    intro hν
    obtain ⟨c, hc0, hct, hce⟩ :=
      hL.equivariant x hxX' (Work.EKLComp.u s) (Work.EKLComp.u_mem s) husxX'
    rw [hν] at hce
    have hM : (ν x).map (fun g => g * Work.EKLComp.u s) = c⁻¹ • ν x := by
      have h := congrArg (fun m => c⁻¹ • m) hce
      rw [smul_smul, ENNReal.inv_mul_cancel hc0 hct, one_smul] at h
      exact h.symm
    exact hxA s hs (hxQ (Work.EKLComp.u s) (Work.EKLComp.u_mem s) c⁻¹ hM)

end Work.EKLCompLeaf
