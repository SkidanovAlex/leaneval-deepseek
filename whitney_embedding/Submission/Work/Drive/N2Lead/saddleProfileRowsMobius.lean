import Mathlib
import Submission.Work.Drive.N2Lead.saddleProfileRows

namespace Work.Drive.N2Lead

open scoped ContDiff Topology
open Set Filter

/-- **The radial-profile rows of the Möbius saddle packet.**  The same existence statement as
`Work.Drive.N2Lead.saddleProfileRows`, except that the *lower* branch clause is asked at the
Möbius double-cover angle `3 * π / 2 + (1/2) * arctan (w / ηs)` instead of
`-(π / 2) - (1/2) * arctan (w / ηs)` (the two angles differ by `π` in the *curve* variable but the
`cos (2 * ·)` value agrees, since `cos (3π + x) = cos (π + x) = -cos x`).

The profile used is the explicit `leadProfileR` of `mobius_lowerProfile`, which is `π`-periodic; this
is what makes the two lower-angle forms interchangeable. -/
theorem saddleProfileRowsMobius {ηs m R : ℝ} (hηs : 0 < ηs) (hηs1 : ηs < 1 / 10) (hm : 1 < m)
    (hm2 : m < 2) (hR : 2 ≤ R) :
    ∃ r : ℝ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) r ∧ (∀ φ : ℝ, 0 < r φ) ∧
      (∀ φ : ℝ, r (φ + 2 * Real.pi) = r φ) ∧ (∀ φ : ℝ, r φ ≤ R) ∧
      (∀ w ∈ Set.Icc (-m) m,
        r (Real.pi / 2 - (1 / 2) * Real.arctan (w / ηs))
          = Real.sqrt (ηs / -Real.cos (2 * (Real.pi / 2 - (1 / 2) * Real.arctan (w / ηs))))) ∧
      (∀ w ∈ Set.Icc (-m) m,
        r (3 * Real.pi / 2 + (1 / 2) * Real.arctan (w / ηs))
          = Real.sqrt (ηs / -Real.cos (2 * (3 * Real.pi / 2 + (1 / 2) * Real.arctan (w / ηs))))) ∧
      (∀ (φ : ℝ) (k : ℤ), |φ - k * Real.pi| ≤ Work.Drive.N2Lead.mobiusPhiE ηs m →
        Real.sqrt (ηs ^ 2 + m ^ 2) ≤ r φ ^ 2) := by
  have hm0 : 0 < m := by linarith
  have hR0 : 0 < R := by linarith
  obtain ⟨hEcos, hEpos, hElt⟩ := leadProfile_phiE hηs hm0
  have hA2lt : Real.sqrt (ηs ^ 2 + m ^ 2) < R ^ 2 := leadProfile_sqrt_lt hηs hηs1 hm hm2.le hR
  have hL : 0 < leadProfileC2 ηs R - leadProfileC1 ηs m := by
    have := leadProfileC1_lt_C2 hηs hA2lt; linarith
  have hper : Function.Periodic (leadProfileR ηs m R) Real.pi := leadProfileR_periodic_pi ηs m R
  refine ⟨leadProfileR ηs m R, leadProfileR_contDiff hηs hR0 hL, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro φ
    exact leadProfileF_pos hηs hR0 hL
  · intro φ
    calc leadProfileR ηs m R (φ + 2 * Real.pi)
        = leadProfileR ηs m R ((φ + Real.pi) + Real.pi) := by
          rw [show φ + 2 * Real.pi = (φ + Real.pi) + Real.pi by ring]
      _ = leadProfileR ηs m R (φ + Real.pi) := hper (φ + Real.pi)
      _ = leadProfileR ηs m R φ := hper φ
  · intro φ
    exact leadProfileF_le_R hηs hR0 hL
  · intro w hw
    have hrange := phiU_mem_arcRange hηs hm0 hw
    exact leadProfileR_arc hL hEcos hEpos.le hrange.1 hrange.2
  · intro w hw
    have hwn : -w ∈ Set.Icc (-m) m := ⟨by linarith [hw.2], by linarith [hw.1]⟩
    have hrange := phiU_mem_arcRange hηs hm0 hwn
    -- shift the Möbius angle back by `π` (the profile is `π`-periodic)
    have hstep : leadProfileR ηs m R (3 * Real.pi / 2 + (1 / 2) * Real.arctan (w / ηs))
        = leadProfileR ηs m R (Real.pi / 2 + (1 / 2) * Real.arctan (w / ηs)) := by
      have h := hper (Real.pi / 2 + (1 / 2) * Real.arctan (w / ηs))
      rw [show Real.pi / 2 + (1 / 2) * Real.arctan (w / ηs) + Real.pi
            = 3 * Real.pi / 2 + (1 / 2) * Real.arctan (w / ηs) by ring] at h
      exact h
    -- `π/2 + (1/2) arctan (w/ηs) = π/2 - (1/2) arctan ((-w)/ηs)`, in the arc range
    have harg : Real.pi / 2 + (1 / 2) * Real.arctan (w / ηs)
        = Real.pi / 2 - (1 / 2) * Real.arctan ((-w) / ηs) := by
      rw [show (-w) / ηs = -(w / ηs) by ring, Real.arctan_neg]; ring
    rw [hstep, harg, leadProfileR_arc hL hEcos hEpos.le hrange.1 hrange.2, ← harg]
    have hcos : Real.cos (2 * (3 * Real.pi / 2 + (1 / 2) * Real.arctan (w / ηs)))
        = Real.cos (2 * (Real.pi / 2 + (1 / 2) * Real.arctan (w / ηs))) := by
      rw [show 2 * (3 * Real.pi / 2 + (1 / 2) * Real.arctan (w / ηs))
            = 2 * (Real.pi / 2 + (1 / 2) * Real.arctan (w / ηs)) + 2 * Real.pi by ring,
          Real.cos_add_two_pi]
    rw [hcos]
  · intro φ k hk
    have h1 : leadProfileR ηs m R (φ - (k : ℝ) * Real.pi) = leadProfileR ηs m R φ := by
      have hint := (hper.int_mul k) (φ - (k : ℝ) * Real.pi)
      rw [show φ - (k : ℝ) * Real.pi + (k : ℝ) * Real.pi = φ by ring] at hint
      exact hint.symm
    have hb := leadProfileR_bridge hηs hR0 hL hA2lt.le hEcos hEpos.le hElt.le
      (φ := φ - (k : ℝ) * Real.pi) hk
    rw [h1] at hb
    exact hb

end Work.Drive.N2Lead
