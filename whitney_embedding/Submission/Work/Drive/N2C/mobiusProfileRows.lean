import Mathlib
import Submission.Work.Drive.N2Lead.saddleProfileRowsMobius

/-!
# The *full* profile rows of the Möbius saddle packet (H7 lane)

`Work.Drive.N2Lead.saddleProfileRowsMobius` (H8) gives seven rows of the radial profile.  The star
rows of the twisted Möbius picture (`Work.Drive.N2Lead.mobiusUpperStarRows`, the diagnosis
`Submission/Work/Drive/N2Lead/NOTES_S48_starRows_DIAGNOSIS.md` §2) additionally need

* the **evenness** `r (-φ) = r φ`, and
* the **monotonicity** `deriv r φ ≤ 0` on the bridge zone `[0, φE]`,

exactly as the split lane's `Work.Drive.N2Lead.saddleProfileRowsPi` provides them (the two rows
`hrev` and `hmono` of its upgraded statement, proved there from `Work.Drive.N2Lead.leadProfileR_even`
and the chain rule).  This file records the same two rows *with the Möbius lower-arc row*, so that
the Möbius existence proof (or an extension of the packet interface) can supply them verbatim.
-/

namespace Work.Drive.N2C

open scoped ContDiff Topology
open Set Filter

/-- **The full radial-profile rows of the Möbius saddle packet**: the seven rows of
`Work.Drive.N2Lead.saddleProfileRowsMobius` plus evenness and the bridge-zone monotonicity. -/
theorem saddleProfileRowsMobiusFull {ηs m R : ℝ} (hηs : 0 < ηs) (hηs1 : ηs < 1 / 10)
    (hm : 1 < m) (hm2 : m < 2) (hR : 2 ≤ R) :
    ∃ r : ℝ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) r ∧ (∀ φ : ℝ, 0 < r φ) ∧
      (∀ φ : ℝ, r (φ + 2 * Real.pi) = r φ) ∧ (∀ φ : ℝ, r (φ + Real.pi) = r φ) ∧
      (∀ φ : ℝ, r φ ≤ R) ∧
      (∀ w ∈ Set.Icc (-m) m,
        r (Real.pi / 2 - (1 / 2) * Real.arctan (w / ηs))
          = Real.sqrt (ηs / -Real.cos (2 * (Real.pi / 2 - (1 / 2) * Real.arctan (w / ηs))))) ∧
      (∀ w ∈ Set.Icc (-m) m,
        r (3 * Real.pi / 2 + (1 / 2) * Real.arctan (w / ηs))
          = Real.sqrt (ηs / -Real.cos (2 * (3 * Real.pi / 2 + (1 / 2) * Real.arctan (w / ηs))))) ∧
      (∀ (φ : ℝ) (k : ℤ), |φ - k * Real.pi| ≤ Work.Drive.N2Lead.mobiusPhiE ηs m →
        Real.sqrt (ηs ^ 2 + m ^ 2) ≤ r φ ^ 2) ∧
      (∀ φ : ℝ, r (-φ) = r φ) ∧
      (∀ φ ∈ Set.Icc (0 : ℝ) (Work.Drive.N2Lead.mobiusPhiE ηs m), deriv r φ ≤ 0) := by
  have hm0 : 0 < m := by linarith
  have hR0 : 0 < R := by linarith
  obtain ⟨hEcos, hEpos, hElt⟩ := Work.Drive.N2Lead.leadProfile_phiE hηs hm0
  have hA2lt : Real.sqrt (ηs ^ 2 + m ^ 2) < R ^ 2 :=
    Work.Drive.N2Lead.leadProfile_sqrt_lt hηs hηs1 hm hm2.le hR
  have hL : 0 < Work.Drive.N2Lead.leadProfileC2 ηs R - Work.Drive.N2Lead.leadProfileC1 ηs m := by
    have := Work.Drive.N2Lead.leadProfileC1_lt_C2 hηs hA2lt; linarith
  have hper : Function.Periodic (Work.Drive.N2Lead.leadProfileR ηs m R) Real.pi :=
    Work.Drive.N2Lead.leadProfileR_periodic_pi ηs m R
  refine ⟨Work.Drive.N2Lead.leadProfileR ηs m R,
    Work.Drive.N2Lead.leadProfileR_contDiff hηs hR0 hL, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro φ
    exact Work.Drive.N2Lead.leadProfileF_pos hηs hR0 hL
  · intro φ
    calc Work.Drive.N2Lead.leadProfileR ηs m R (φ + 2 * Real.pi)
        = Work.Drive.N2Lead.leadProfileR ηs m R ((φ + Real.pi) + Real.pi) := by
          rw [show φ + 2 * Real.pi = (φ + Real.pi) + Real.pi by ring]
      _ = Work.Drive.N2Lead.leadProfileR ηs m R (φ + Real.pi) := hper (φ + Real.pi)
      _ = Work.Drive.N2Lead.leadProfileR ηs m R φ := hper φ
  · intro φ
    exact hper φ
  · intro φ
    exact Work.Drive.N2Lead.leadProfileF_le_R hηs hR0 hL
  · intro w hw
    have hrange := Work.Drive.N2Lead.phiU_mem_arcRange hηs hm0 hw
    exact Work.Drive.N2Lead.leadProfileR_arc hL hEcos hEpos.le hrange.1 hrange.2
  · intro w hw
    have hwn : -w ∈ Set.Icc (-m) m := ⟨by linarith [hw.2], by linarith [hw.1]⟩
    have hrange := Work.Drive.N2Lead.phiU_mem_arcRange hηs hm0 hwn
    have hstep : Work.Drive.N2Lead.leadProfileR ηs m R
        (3 * Real.pi / 2 + (1 / 2) * Real.arctan (w / ηs))
        = Work.Drive.N2Lead.leadProfileR ηs m R
          (Real.pi / 2 + (1 / 2) * Real.arctan (w / ηs)) := by
      have h := hper (Real.pi / 2 + (1 / 2) * Real.arctan (w / ηs))
      rw [show Real.pi / 2 + (1 / 2) * Real.arctan (w / ηs) + Real.pi
            = 3 * Real.pi / 2 + (1 / 2) * Real.arctan (w / ηs) by ring] at h
      exact h
    have harg : Real.pi / 2 + (1 / 2) * Real.arctan (w / ηs)
        = Real.pi / 2 - (1 / 2) * Real.arctan ((-w) / ηs) := by
      rw [show (-w) / ηs = -(w / ηs) by ring, Real.arctan_neg]; ring
    rw [hstep, harg, Work.Drive.N2Lead.leadProfileR_arc hL hEcos hEpos.le hrange.1 hrange.2,
      ← harg]
    have hcos : Real.cos (2 * (3 * Real.pi / 2 + (1 / 2) * Real.arctan (w / ηs)))
        = Real.cos (2 * (Real.pi / 2 + (1 / 2) * Real.arctan (w / ηs))) := by
      rw [show 2 * (3 * Real.pi / 2 + (1 / 2) * Real.arctan (w / ηs))
            = 2 * (Real.pi / 2 + (1 / 2) * Real.arctan (w / ηs)) + 2 * Real.pi by ring,
          Real.cos_add_two_pi]
    rw [hcos]
  · intro φ k hk
    have h1 : Work.Drive.N2Lead.leadProfileR ηs m R (φ - (k : ℝ) * Real.pi)
        = Work.Drive.N2Lead.leadProfileR ηs m R φ := by
      have hint := (hper.int_mul k) (φ - (k : ℝ) * Real.pi)
      rw [show φ - (k : ℝ) * Real.pi + (k : ℝ) * Real.pi = φ by ring] at hint
      exact hint.symm
    have hb := Work.Drive.N2Lead.leadProfileR_bridge hηs hR0 hL hA2lt.le hEcos hEpos.le hElt.le
      (φ := φ - (k : ℝ) * Real.pi) hk
    rw [h1] at hb
    exact hb
  · intro φ
    exact Work.Drive.N2Lead.leadProfileR_even ηs m R φ
  · intro φ hφ
    have hφ1 : φ ≤ Work.Drive.N2Lead.mobiusPhiE ηs m := hφ.2
    have hsin : 0 ≤ Real.sin (2 * φ) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hφ.1]) (by linarith [hElt])
    have hFdiff : DifferentiableAt ℝ (Work.Drive.N2Lead.leadProfileF ηs m R)
        (Real.cos (2 * φ)) :=
      ((Work.Drive.N2Lead.leadProfileF_contDiff hηs hR0 hL).differentiable (by simp)).differentiableAt
    have hderiv : deriv (Work.Drive.N2Lead.leadProfileR ηs m R) φ
        = deriv (Work.Drive.N2Lead.leadProfileF ηs m R) (Real.cos (2 * φ))
          * (-Real.sin (2 * φ) * 2) := by
      have hc : HasDerivAt (fun ψ : ℝ => Real.cos (2 * ψ)) (-Real.sin (2 * φ) * 2) φ := by
        have h1 : HasDerivAt (fun ψ : ℝ => (2 : ℝ) * ψ) 2 φ := by
          simpa using (hasDerivAt_id (x := φ)).const_mul (2 : ℝ)
        exact h1.cos
      exact ((hFdiff.hasDerivAt).comp φ hc).deriv
    rw [hderiv]
    exact mul_nonpos_of_nonneg_of_nonpos
      (Monotone.deriv_nonneg (Work.Drive.N2Lead.leadProfileF_mono hηs hR0 hL))
      (by linarith [hsin])

end Work.Drive.N2C
