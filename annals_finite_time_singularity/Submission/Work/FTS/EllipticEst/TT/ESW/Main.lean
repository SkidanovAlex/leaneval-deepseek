import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllipticEst.TT.ESW.Defs
import Submission.Work.FTS.EllipticEst.remov.high_chain_sum_self

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.TT.ESW

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ### The `η`-slot -/

/-- Almost every `θ ∈ Iθ` is in the open interval (where `sin(2θ) > 0`). -/
theorem ae_mem_Ioo_Iθ : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
    θ ∈ Set.Ioo 0 (Real.pi / 2) := by
  have h : (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)) : Measure ℝ)
      = MeasureTheory.volume.restrict Work.Spaces.Iθ :=
    MeasureTheory.Measure.restrict_congr_set
      (by rw [Work.Spaces.Iθ]; exact MeasureTheory.Ioo_ae_eq_Icc)
  rw [← h]
  exact MeasureTheory.ae_restrict_mem measurableSet_Ioo

/-- The pointwise weight identity `(w/σ^{η/2})² = w²·σ^{-η}` at points with `σ > 0`. -/
theorem Zu_sq_eq {z θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2
      = (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.sEta θ := by
  have hs : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have h1 : (Real.sin (2 * θ) ^ (Work.Spaces.eta / 2)) ^ 2
      = Real.sin (2 * θ) ^ Work.Spaces.eta := by
    rw [sq, ← Real.rpow_add hs]
    congr 1
    ring
  rw [Work.FTS.EllipticEst.sEta, div_pow, h1, div_eq_mul_inv, Real.rpow_neg hs.le]

/-- **The `η`-slot bound**: the pure (`i = 0`) slot of `HkIntegrand`. -/
theorem eta_slot_le {α : ℝ} {l : ℕ} {f : ℝ → ℝ → ℝ} (hmem : Work.Spaces.HkMem α l f) :
    (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
        (∫ θ in Work.Spaces.Iθ, (f z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ))
      ≤ Work.Spaces.HkSq α l f := by
  have hslot := Work.Spaces.L2Sq_DzIter_le_HkSq α l f hmem 0 (Nat.zero_le l)
  have hL2 : Work.Spaces.L2Sq (fun z θ => f z θ *
      (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)))
      = ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
        (∫ θ in Work.Spaces.Iθ, (f z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) := by
    rw [Work.Spaces.L2Sq]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
    show (∫ θ in Work.Spaces.Iθ,
        (f z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      = (Work.Spaces.w z) ^ 2 *
        ∫ θ in Work.Spaces.Iθ, (f z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
    rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.integral_congr_ae (ae_mem_Ioo_Iθ.mono (fun θ hθ => ?_))
    show (f z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      = (Work.Spaces.w z) ^ 2 * ((f z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
    rw [mul_pow, Zu_sq_eq hθ]
    ring
  rw [← hL2]
  simpa only [Work.Spaces.DzIter_zero, sq] using hslot

/-! ### The lower angular chain of `B` -/

/-- The lower `D_θ`-slots of `B = ∂_θθΨ` are controlled by `HkSq α (k-1) B`, with a
constant that is uniform in `α` and in `Ψ`. -/
theorem E_le_HkSq (k : ℕ) (hk : 1 ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (Ψ : ℝ → ℝ → ℝ), 0 < α →
      Work.FTS.EllipticEst.SmoothOpen Ψ →
      Work.Spaces.HkMem α (k - 1) (Bsl Ψ) →
      (∑ r ∈ Finset.Icc 1 (k - 1), ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
          ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter r (Bsl Ψ) z θ) ^ 2
            * (Real.sin (2 * θ)) ^ (2 * (r : ℝ) - Work.Spaces.gam α))
        ≤ C * Work.Spaces.HkSq α (k - 1) (Bsl Ψ) := by
  obtain ⟨C, hCpos, hC⟩ := Work.FTS.EllipticEst.remov.high_chain_sum_self (k - 1)
  exact ⟨C, hCpos, fun α Ψ hα hsm hmem => hC α (Bsl Ψ) hα (SmoothOpen.forall (hsm.pth.pth)) hmem⟩

end Work.FTS.EllipticEst.TT.ESW
