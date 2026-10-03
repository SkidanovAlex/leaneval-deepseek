import Mathlib
import Submission.Work.FITop4.Red5.piecesSetup
import Submission.Work.FITop4.Red5.pieceDefs
import Submission.Work.FITop4.Red5.angular_partition_le

namespace Work.FITop4.Red5

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

theorem cfVal_eq_Q {Pa : Work.FITop.Params} {Pz : ℕ} (φ : ℝ) (q p : ℝ → ℝ)
    (hPz : Pa.Pz = Pz) (z : GaussianInt) (hz : Work.FIPlan.IsPrimary z)
    (hpsup : ∀ u : ℝ, p u ≠ 0 → Pa.N < u ∧ u ≤ (1 + Pa.θ) * Pa.N)
    (hq0z : q 0 = 0)
    (hqsup : ∀ α : ℝ, q α ≠ 0 → 0 ≤ α ∧ α ≤ 2 * Real.pi * Pa.θ) :
    cfVal Pa φ q p z
      = QInd Pz Pa (Work.FIPlan.gnorm z) * (q (Complex.arg z.toComplex - φ)
          * p (Work.FIPlan.gnorm z)
          * (ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℝ)
          * Work.FIPlan.gammaTrunc Pa.C (Work.FIPlan.gnorm z)) := by
  rw [cfVal_apply]
  by_cases hX : q (Complex.arg z.toComplex - φ) * p ((Work.FIPlan.gnorm z : ℕ) : ℝ)
      * (ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℝ)
      * Work.FIPlan.gammaTrunc Pa.C (Work.FIPlan.gnorm z) = 0
  · rw [hX, mul_zero, mul_zero]
  · have hqne : q (Complex.arg z.toComplex - φ) ≠ 0 := fun h => hX (by simp [h])
    have hpne : p ((Work.FIPlan.gnorm z : ℕ) : ℝ) ≠ 0 := fun h => hX (by simp [h])
    have hbox : InPolarBox Pa φ z := by
      have hqs := hqsup (Complex.arg z.toComplex - φ) hqne
      have hps := hpsup ((Work.FIPlan.gnorm z : ℕ) : ℝ) hpne
      have hne : Complex.arg z.toComplex - φ ≠ 0 := fun h =>
        hqne (by rw [h]; exact hq0z)
      have hpos : 0 < Complex.arg z.toComplex - φ := lt_of_le_of_ne hqs.1 (Ne.symm hne)
      exact ⟨hz, hps.1, hps.2, by linarith, by linarith⟩
    have hiff : pcCond Pa φ z ↔ QPred Pz Pa (Work.FIPlan.gnorm z) := by
      unfold pcCond QPred
      constructor
      · rintro ⟨_, hns, ht⟩
        exact ⟨fun r hr hre => hns r hr (by rw [hPz]; exact hre), ht⟩
      · rintro ⟨hpi, ht⟩
        exact ⟨hbox, fun r hr hre => hpi r hr (by rw [← hPz]; exact hre), ht⟩
    rw [pcInd, QInd]
    by_cases hc : pcCond Pa φ z
    · rw [if_pos hc, if_pos (hiff.mp hc)]
    · rw [if_neg hc, if_neg (fun h => hc (hiff.mpr h))]

end

end Work.FITop4.Red5
