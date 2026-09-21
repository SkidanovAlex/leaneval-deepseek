import Mathlib
import Submission.Work.OddVolterra.Defs
import Submission.Work.OddVolterra.Kernel.Diag
import Submission.Work.OddVolterra.Existence.krad_pos_state_region

namespace Work.OddVolterra.WinData

open Work.OddVolterra
open scoped Topology ContDiff Interval

noncomputable section

/-- The divided difference is symmetric. -/
lemma hquot_comm (h : ℝ → ℝ) (u σ : ℝ) : hquot h u σ = hquot h σ u := by
  have h1 : (∫ x in (0:ℝ)..1, deriv h (u + (1 - x) * (σ - u)))
      = ∫ x in (0:ℝ)..1, deriv h (σ + x * (u - σ)) := by
    refine intervalIntegral.integral_congr (fun x _ => ?_)
    congr 1
    ring
  have h2 : (∫ x in (0:ℝ)..1, deriv h (u + (1 - x) * (σ - u)))
      = ∫ x in (0:ℝ)..1, deriv h (u + x * (σ - u)) := by
    have h3 := intervalIntegral.integral_comp_sub_left
      (f := fun x : ℝ => deriv h (u + x * (σ - u))) (a := (0:ℝ)) (b := 1) 1
    simpa using h3
  rw [hquot, hquot, ← h2]
  exact h1

/-- `krad` is symmetric in its two slope slots. -/
lemma krad_comm (h : ℝ → ℝ) (σ t u : ℝ) : krad h σ t u = krad h u t σ := by
  rw [krad_apply, krad_apply, hquot_comm h u σ]
  unfold line
  ring

/-- Positivity of the Abel radicand on a general slope box. -/
theorem krad_pos_box {h : ℝ → ℝ}
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * tau) (1 - tau))
    (hsmall : ∀ k : ℕ, k ≤ 1 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100)
    {A u σ t : ℝ} (hA : 0 < A) (hu : A ≤ u) (hσ : A ≤ σ) (hσ1 : σ ≤ 1) (hu1 : u ≤ 1)
    (ht : 1 / 5 ≤ |t|) : 0 < krad h σ t u := by
  rcases le_total u σ with hle | hle
  · exact Work.OddVolterra.Existence.krad_pos_state_region hsupp hsmall hA hu hle hσ1 ht
  · rw [krad_comm]
    exact Work.OddVolterra.Existence.krad_pos_state_region hsupp hsmall hA hσ hle hu1 ht

end

end Work.OddVolterra.WinData
