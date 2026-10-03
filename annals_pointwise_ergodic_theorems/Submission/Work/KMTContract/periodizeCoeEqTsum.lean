import Mathlib
import Submission.Work.Analysis.IonescuWainger.Symbol

namespace Work.KMTContract

/-
`periodize φ ξ = ∑' k : ℤ, φ (x₀ + k)`, where `x₀ = (AddCircle.equivIco 1 0 ξ).val ∈ [0,1)` is the
canonical representative of `ξ` in the half-open interval `[0,1)`.

For `ξ = (x : ℝ/ℤ)` the representative differs from `x` by an integer: `x₀ = x + m` with `m : ℤ`
because `(x₀ : ℝ/ℤ) = (x : ℝ/ℤ)`.  Hence the periodisation is the sum of the shifts
`φ (x + m + k)`, and reindexing the sum over `ℤ` by `k ↦ k + m` turns it into `∑' n, φ (x + n)`.
This is the identification of the periodisation with the `ℤ`-orbit sum used throughout the
Ionescu–Wainger major-arc analysis.
-/
theorem periodizeCoeEqTsum (φ : ℝ → ℂ) (x : ℝ) :
    Work.Analysis.IonescuWainger.periodize φ (x : Work.Analysis.IonescuWainger.Circle)
      = ∑' n : ℤ, φ (x + n) := by
  -- Unfold the periodisation: the contributions are the shifts by all integers of the canonical
  -- representative of `(x : ℝ/ℤ)` in `[0,1)`.
  have hper : Work.Analysis.IonescuWainger.periodize φ
        (x : Work.Analysis.IonescuWainger.Circle)
      = ∑' k : ℤ,
          φ (((AddCircle.equivIco (1 : ℝ) 0
                (x : Work.Analysis.IonescuWainger.Circle)).val) + (k : ℝ)) := rfl
  -- The canonical representative differs from `x` by an integer `m`.
  obtain ⟨m, hm⟩ : ∃ m : ℤ,
      (m : ℝ) = ((AddCircle.equivIco (1 : ℝ) 0
                (x : Work.Analysis.IonescuWainger.Circle)).val) - x := by
    have h : (((AddCircle.equivIco (1 : ℝ) 0
          (x : Work.Analysis.IonescuWainger.Circle)).val) :
            Work.Analysis.IonescuWainger.Circle)
        = (x : Work.Analysis.IonescuWainger.Circle) :=
      AddCircle.coe_equivIco
    have h2 : ((((AddCircle.equivIco (1 : ℝ) 0
          (x : Work.Analysis.IonescuWainger.Circle)).val) - x : ℝ) :
            Work.Analysis.IonescuWainger.Circle) = 0 := by
      rw [AddCircle.coe_sub, h, sub_self]
    obtain ⟨k, hk⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp h2
    exact ⟨k, by simpa using hk⟩
  have hy : ((AddCircle.equivIco (1 : ℝ) 0
        (x : Work.Analysis.IonescuWainger.Circle)).val) = x + (m : ℝ) := by linarith
  rw [hper, hy]
  -- Reindex the sum over `ℤ` by the translation `k ↦ k + m`.
  calc ∑' k : ℤ, φ (x + (m : ℝ) + (k : ℝ))
      = ∑' k : ℤ, φ (x + ((k + m : ℤ) : ℝ)) :=
        tsum_congr fun k => by congr 1; push_cast; ring
    _ = ∑' n : ℤ, φ (x + (n : ℝ)) := by
        simpa using Equiv.tsum_eq (Equiv.addRight m) (fun n : ℤ => φ (x + (n : ℝ)))

end Work.KMTContract
