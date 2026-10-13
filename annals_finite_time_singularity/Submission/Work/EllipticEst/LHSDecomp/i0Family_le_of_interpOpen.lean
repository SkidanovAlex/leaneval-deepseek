import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.EllipticEst.Core.i0Aux.InterpDefs
import Submission.Work.EllipticEst.Core.i0Aux.Basic
import Submission.Work.EllipticEst.Core.i0Aux.Honest
import Submission.Work.EllipticEst.Core.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.EllipticEst.LHSDecomp

theorem i0Family_le_of_interpOpen {C : ℝ} (hC : 0 < C)
    (hopen : Work.EllipticEst.Core.i0Aux.InterpOpen C) (k : ℕ) : ∃ C' : ℝ, 0 < C' ∧
    ∀ (α : ℝ) (V : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.SmoothOpen V →
      (∀ z : ℝ, V z 0 = 0) → (∀ z : ℝ, V z (Real.pi / 2) = 0) →
      Work.Spaces.HkMem α k (Work.Spaces.DzIter 2 V) →
      Work.Spaces.HkMem α k (Work.Spaces.pthIter 2 V) →
      Work.Spaces.HkMem α k (Work.Spaces.Dz V) →
      α ^ 2 * (∑ r ∈ Finset.range (k + 1),
          ∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.mixIntS (Work.Spaces.DzIter r V) z)
        ≤ C' * (α ^ 4 * Work.Spaces.HkSq α k (Work.Spaces.DzIter 2 V)
            + Work.Spaces.HkSq α k (Work.Spaces.pthIter 2 V)
            + α ^ 2 * Work.Spaces.HkSq α k (Work.Spaces.Dz V)) := by
  refine ⟨((k : ℝ) + 1) * C, by positivity, ?_⟩
  intro α V hα hα14 hsm h0 hpi hdd htt hd
  -- the right-hand side of the target
  set R : ℝ := α ^ 4 * Work.Spaces.HkSq α k (Work.Spaces.DzIter 2 V)
      + Work.Spaces.HkSq α k (Work.Spaces.pthIter 2 V)
      + α ^ 2 * Work.Spaces.HkSq α k (Work.Spaces.Dz V) with hR
  have hRnn : 0 ≤ R := by
    rw [hR]
    have h1 := Work.Spaces.HkSq_nonneg α k (Work.Spaces.DzIter 2 V)
    have h2 := Work.Spaces.HkSq_nonneg α k (Work.Spaces.pthIter 2 V)
    have h3 := Work.Spaces.HkSq_nonneg α k (Work.Spaces.Dz V)
    have hα4 : (0 : ℝ) ≤ α ^ 4 := by positivity
    have hα2 : (0 : ℝ) ≤ α ^ 2 := by positivity
    nlinarith [mul_nonneg hα4 h1, mul_nonneg hα2 h3]
  -- the per-`r` estimate
  have key : ∀ r ∈ Finset.range (k + 1),
      α ^ 2 * (∫ z in Work.Spaces.Iz,
          Work.EllipticEst.Core.mixIntS (Work.Spaces.DzIter r V) z) ≤ C * R := by
    intro r hr
    have hrk : r ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
    by_cases hhon : MeasureTheory.IntegrableOn
        (fun z : ℝ => Work.EllipticEst.Core.mixIntS (Work.Spaces.DzIter r V) z)
        Work.Spaces.Iz
    · have hc := hopen α (Work.Spaces.DzIter r V) hα hα14 (hsm.DzIter r)
        (Work.EllipticEst.Core.i0Aux.DzIter_zero_theta h0 r)
        (Work.EllipticEst.Core.i0Aux.DzIter_pi_theta hpi r)
        (Work.EllipticEst.Core.i0Aux.sliceHonestOpen_dzIter hsm hdd htt hd hrk) hhon
        (Work.EllipticEst.Core.i0Aux.ddIntS_integrableOn hsm hdd hrk)
        (Work.EllipticEst.Core.i0Aux.ttIntS_integrableOn hsm htt hrk)
        (Work.EllipticEst.Core.i0Aux.dIntS_integrableOn hsm hd hrk)
      refine le_trans hc (mul_le_mul_of_nonneg_left ?_ hC.le)
      have h1 := Work.EllipticEst.Core.i0Aux.ddIntS_integral_le_HkSq (V := V) hdd hrk
      have h2 := Work.EllipticEst.Core.i0Aux.ttIntS_integral_le_HkSq (V := V) hsm htt hrk
      have h3 := Work.EllipticEst.Core.i0Aux.dIntS_integral_le_HkSq (V := V) hd hrk
      rw [hR]
      have hα4 : (0 : ℝ) ≤ α ^ 4 := by positivity
      have hα2 : (0 : ℝ) ≤ α ^ 2 := by positivity
      nlinarith [mul_le_mul_of_nonneg_left h1 hα4, h2, mul_le_mul_of_nonneg_left h3 hα2]
    · rw [MeasureTheory.integral_undef hhon, mul_zero]
      exact mul_nonneg hC.le hRnn
  -- summing over `r ≤ k`
  have hsum : (∑ r ∈ Finset.range (k + 1),
        α ^ 2 * (∫ z in Work.Spaces.Iz,
          Work.EllipticEst.Core.mixIntS (Work.Spaces.DzIter r V) z))
      ≤ ((k : ℝ) + 1) * (C * R) := by
    calc (∑ r ∈ Finset.range (k + 1),
          α ^ 2 * (∫ z in Work.Spaces.Iz,
            Work.EllipticEst.Core.mixIntS (Work.Spaces.DzIter r V) z))
        ≤ ∑ _r ∈ Finset.range (k + 1), C * R := Finset.sum_le_sum key
      _ = ((k : ℝ) + 1) * (C * R) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast
          ring
  calc α ^ 2 * (∑ r ∈ Finset.range (k + 1),
        ∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.mixIntS (Work.Spaces.DzIter r V) z)
      = ∑ r ∈ Finset.range (k + 1),
          α ^ 2 * (∫ z in Work.Spaces.Iz,
            Work.EllipticEst.Core.mixIntS (Work.Spaces.DzIter r V) z) := by
        rw [Finset.mul_sum]
    _ ≤ ((k : ℝ) + 1) * (C * R) := hsum
    _ = ((k : ℝ) + 1) * C * (α ^ 4 * Work.Spaces.HkSq α k (Work.Spaces.DzIter 2 V)
            + Work.Spaces.HkSq α k (Work.Spaces.pthIter 2 V)
            + α ^ 2 * Work.Spaces.HkSq α k (Work.Spaces.Dz V)) := by
        rw [hR]
        ring

end Work.EllipticEst.LHSDecomp
