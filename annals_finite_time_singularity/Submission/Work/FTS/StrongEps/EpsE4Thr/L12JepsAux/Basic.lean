import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Order.Group.Lattice
import Submission.Work.FTS.StrongEps.L12Sub4.ConvDiffBound
import Submission.Work.FTS.StrongEps.L12Sub4.L12ZeroLog
import Submission.Work.FTS.StrongEps.PZeroScheme
import Submission.Work.FTS.StrongEps.SmoothOpen_Jeps
import Submission.Work.FTS_MuLamOK.Rows.rl0_final
import Submission.Work.FTS_RegExport.RXB.sup_bound_all_alpha
import Submission.Work.FTS_RegExport.RXT.jc3_aux
import Submission.Work.FTS_StreamBdry.Inputs.theta_part_theta
import Submission.Work.Stability.mul_rpow_le
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv.logPlane_transfer_deriv =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `logPlane_transfer_deriv` — the derivative-priced plane transfer estimate

This file proves `PlaneTransferDeriv` (see `TransferDeriv/Defs.lean`) from scratch.

Write `A p = ∫ Q y G₁ (y−p) G₂ y`, `B p = ∫ Q y G₁ y G₂ (y+p)`, `C p = ∫ Q y G₁ y G₂ (y−p)`.
Fubini turns the defect `D = ∫ Q (k*G₁) G₂ − ∫ Q G₁ (k*G₂)` into `∫ p k p (A p − C p)`, which
splits as `∫ p k p (A p − B p) + ∫ p k p (B p − C p)`:

* the **weight-difference** piece obeys the one-sided log-Lipschitz estimate
  (`Pieces.dabsIntLe`), giving `O(ε)` with the norm `√(∫ Q G₂²)` of the second slot;
* the **shift-difference** piece is bounded by Cauchy–Schwarz (`shift_pair_bound`) against
  `√(∫ Q (G₂(·+p) − G₂(·−p))²)`, and the weighted second moment of the two-sided shift is
  `4‖p‖² e^{Cw|p|₁} ∫ Q ‖fderiv G₂‖²` (`shift_sq_bound`) — the derivative price.

Summing over `p` against `∫ |k| ≤ 1` and using `|p|₁ ≤ 2ε` gives the stated constant.
-/

noncomputable section

open MeasureTheory

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv

/-- Fubini for the pairing of a convolution: if the joint integrand `H y * (k p * G (y − p))` is
integrable on the product then the single integral is the iterated integral. -/
theorem conv_fubini_pair {k G H : ℝ × ℝ → ℝ}
    (hint : MeasureTheory.Integrable
      (Function.uncurry fun (y p : ℝ × ℝ) => H y * (k p * G (y - p)))) :
    (∫ y : ℝ × ℝ, H y * (∫ p : ℝ × ℝ, k p * G (y - p)))
      = ∫ p : ℝ × ℝ, ∫ y : ℝ × ℝ, H y * (k p * G (y - p)) := by
  rw [← MeasureTheory.integral_integral_swap hint]
  exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun y =>
    (MeasureTheory.integral_const_mul (H y) (fun p : ℝ × ℝ => k p * G (y - p))).symm)

theorem logPlane_transfer_deriv : PlaneTransferDeriv := by
  intro k Q ε Cw hε0 hε1 hCw hkm hkint hmass hksupp hQ0 hQm hQsh hQsh' G₁ G₂ hG1m hG2m hG2d
    hconv1 hconv2 hI1 hI2 hI3
  -- ### abbreviations
  set A : ℝ × ℝ → ℝ := fun p => ∫ y : ℝ × ℝ, Q y * G₁ (y - p) * G₂ y with hA
  set B : ℝ × ℝ → ℝ := fun p => ∫ y : ℝ × ℝ, Q y * G₁ y * G₂ (y + p) with hB
  set C : ℝ × ℝ → ℝ := fun p => ∫ y : ℝ × ℝ, Q y * G₁ y * G₂ (y - p) with hC
  -- ### Step 1: joint integrability of the three pairings, for the signed kernel
  have hkabs : MeasureTheory.Integrable (fun p : ℝ × ℝ => |k p|) := hkint.abs
  have hkabssupp : ∀ p : ℝ × ℝ, |k p| ≠ 0 → |p.1| + |p.2| ≤ 2 * ε := fun p hp =>
    hksupp p (by simpa [abs_eq_zero] using hp)
  have hI1a : MeasureTheory.Integrable (fun y : ℝ × ℝ => Q y * |G₁ y| ^ 2) :=
    hI1.congr (Filter.Eventually.of_forall fun y => by simp only [sq_abs])
  have hI2a : MeasureTheory.Integrable (fun y : ℝ × ℝ => Q y * |G₂ y| ^ 2) :=
    hI2.congr (Filter.Eventually.of_forall fun y => by simp only [sq_abs])
  have hJab := Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Pieces2.conv_joint_integrable
    (k := fun p : ℝ × ℝ => |k p|) (Q := Q) (G₁ := fun y : ℝ × ℝ => |G₁ y|)
    (G₂ := fun y : ℝ × ℝ => |G₂ y|) (Cw := Cw) (ε := ε)
    hCw hkabs (fun p => abs_nonneg _) hkabssupp hQ0 hQm hQsh hG1m.abs hG2m.abs hI1a hI2a
  have hJba := Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Pieces2.conv_joint_integrable
    (k := fun p : ℝ × ℝ => |k p|) (Q := Q) (G₁ := fun y : ℝ × ℝ => |G₂ y|)
    (G₂ := fun y : ℝ × ℝ => |G₁ y|) (Cw := Cw) (ε := ε)
    hCw hkabs (fun p => abs_nonneg _) hkabssupp hQ0 hQm hQsh hG2m.abs hG1m.abs hI2a hI1a
  have hJ1 : MeasureTheory.Integrable
      (Function.uncurry fun (y p : ℝ × ℝ) => k p * Q y * G₁ (y - p) * G₂ y) := by
    refine hJab.1.mono' ?_ ?_
    · exact (((hkm.comp measurable_snd).mul (hQm.comp measurable_fst)).mul
        (hG1m.comp (measurable_fst.sub measurable_snd))).mul
        (hG2m.comp measurable_fst) |>.aestronglyMeasurable
    · filter_upwards with z
      obtain ⟨y, p⟩ := z
      have h : ‖k p * Q y * G₁ (y - p) * G₂ y‖ = |k p| * Q y * |G₁ (y - p)| * |G₂ y| := by
        rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_of_nonneg (hQ0 y)]
      rw [Function.uncurry_apply_pair, Function.uncurry_apply_pair, h]
  have hJ2 : MeasureTheory.Integrable
      (Function.uncurry fun (y p : ℝ × ℝ) => k p * Q y * G₁ y * G₂ (y + p)) := by
    refine hJab.2.mono' ?_ ?_
    · exact (((hkm.comp measurable_snd).mul (hQm.comp measurable_fst)).mul
        (hG1m.comp measurable_fst)).mul
        (hG2m.comp (measurable_fst.add measurable_snd)) |>.aestronglyMeasurable
    · filter_upwards with z
      obtain ⟨y, p⟩ := z
      have h : ‖k p * Q y * G₁ y * G₂ (y + p)‖ = |k p| * Q y * |G₁ y| * |G₂ (y + p)| := by
        rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_of_nonneg (hQ0 y)]
      rw [Function.uncurry_apply_pair, Function.uncurry_apply_pair, h]
  have hJ3 : MeasureTheory.Integrable
      (Function.uncurry fun (y p : ℝ × ℝ) => k p * Q y * G₁ y * G₂ (y - p)) := by
    refine hJba.1.mono' ?_ ?_
    · exact (((hkm.comp measurable_snd).mul (hQm.comp measurable_fst)).mul
        (hG1m.comp measurable_fst)).mul
        (hG2m.comp (measurable_fst.sub measurable_snd)) |>.aestronglyMeasurable
    · filter_upwards with z
      obtain ⟨y, p⟩ := z
      have h : ‖k p * Q y * G₁ y * G₂ (y - p)‖ = |k p| * Q y * |G₁ y| * |G₂ (y - p)| := by
        rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_of_nonneg (hQ0 y)]
      rw [Function.uncurry_apply_pair, Function.uncurry_apply_pair, h]
      exact le_of_eq (by ring)
  -- ### Step 2: the fibre integrals `p ↦ k p * A p`, `k p * B p`, `k p * C p` are integrable
  have hKA : MeasureTheory.Integrable (fun p : ℝ × ℝ => k p * A p) := by
    refine (MeasureTheory.Integrable.integral_prod_right (μ := volume) (ν := volume) hJ1).congr
      (Filter.Eventually.of_forall fun p => ?_)
    simp only [Function.uncurry_apply_pair]
    rw [hA]
    rw [show (∫ y : ℝ × ℝ, k p * Q y * G₁ (y - p) * G₂ y)
        = ∫ y : ℝ × ℝ, k p * (Q y * G₁ (y - p) * G₂ y) from
      MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun y => by ring)]
    rw [MeasureTheory.integral_const_mul]
  have hKB : MeasureTheory.Integrable (fun p : ℝ × ℝ => k p * B p) := by
    refine (MeasureTheory.Integrable.integral_prod_right (μ := volume) (ν := volume) hJ2).congr
      (Filter.Eventually.of_forall fun p => ?_)
    simp only [Function.uncurry_apply_pair]
    rw [hB]
    rw [show (∫ y : ℝ × ℝ, k p * Q y * G₁ y * G₂ (y + p))
        = ∫ y : ℝ × ℝ, k p * (Q y * G₁ y * G₂ (y + p)) from
      MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun y => by ring)]
    rw [MeasureTheory.integral_const_mul]
  have hKC : MeasureTheory.Integrable (fun p : ℝ × ℝ => k p * C p) := by
    refine (MeasureTheory.Integrable.integral_prod_right (μ := volume) (ν := volume) hJ3).congr
      (Filter.Eventually.of_forall fun p => ?_)
    simp only [Function.uncurry_apply_pair]
    rw [hC]
    rw [show (∫ y : ℝ × ℝ, k p * Q y * G₁ y * G₂ (y - p))
        = ∫ y : ℝ × ℝ, k p * (Q y * G₁ y * G₂ (y - p)) from
      MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun y => by ring)]
    rw [MeasureTheory.integral_const_mul]
  -- ### Step 3: Fubini for the two single integrals
  have hintA : MeasureTheory.Integrable
      (Function.uncurry fun (y p : ℝ × ℝ) => (Q y * G₂ y) * (k p * G₁ (y - p))) :=
    hJ1.congr (Filter.Eventually.of_forall fun z => by
      obtain ⟨y, p⟩ := z
      simp only [Function.uncurry_apply_pair]
      ring)
  have hI₁ : (∫ y : ℝ × ℝ, Q y * (∫ p : ℝ × ℝ, k p * G₁ (y - p)) * G₂ y)
      = ∫ p : ℝ × ℝ, k p * A p := by
    rw [show (∫ y : ℝ × ℝ, Q y * (∫ p : ℝ × ℝ, k p * G₁ (y - p)) * G₂ y)
        = ∫ y : ℝ × ℝ, (Q y * G₂ y) * (∫ p : ℝ × ℝ, k p * G₁ (y - p)) from
      MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun y => by ring)]
    rw [conv_fubini_pair hintA]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    show (∫ y : ℝ × ℝ, Q y * G₂ y * (k p * G₁ (y - p))) = k p * A p
    rw [hA]
    rw [show (∫ y : ℝ × ℝ, (Q y * G₂ y) * (k p * G₁ (y - p)))
        = ∫ y : ℝ × ℝ, k p * (Q y * G₁ (y - p) * G₂ y) from
      MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun y => by ring)]
    rw [MeasureTheory.integral_const_mul]
  have hintC : MeasureTheory.Integrable
      (Function.uncurry fun (y p : ℝ × ℝ) => (Q y * G₁ y) * (k p * G₂ (y - p))) :=
    hJ3.congr (Filter.Eventually.of_forall fun z => by
      obtain ⟨y, p⟩ := z
      simp only [Function.uncurry_apply_pair]
      ring)
  have hI₂ : (∫ y : ℝ × ℝ, Q y * G₁ y * (∫ p : ℝ × ℝ, k p * G₂ (y - p)))
      = ∫ p : ℝ × ℝ, k p * C p := by
    rw [conv_fubini_pair hintC]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    show (∫ y : ℝ × ℝ, Q y * G₁ y * (k p * G₂ (y - p))) = k p * C p
    rw [hC]
    rw [show (∫ y : ℝ × ℝ, (Q y * G₁ y) * (k p * G₂ (y - p)))
        = ∫ y : ℝ × ℝ, k p * (Q y * G₁ y * G₂ (y - p)) from
      MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun y => by ring)]
    rw [MeasureTheory.integral_const_mul]
  -- ### Step 4: the defect as two pieces
  have hAsub : (∫ p : ℝ × ℝ, k p * A p) - (∫ p : ℝ × ℝ, k p * B p)
      = ∫ p : ℝ × ℝ, k p * (A p - B p) := by
    rw [← MeasureTheory.integral_sub hKA hKB]
    exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun p => by ring)
  have hBsub : (∫ p : ℝ × ℝ, k p * B p) - (∫ p : ℝ × ℝ, k p * C p)
      = ∫ p : ℝ × ℝ, k p * (B p - C p) := by
    rw [← MeasureTheory.integral_sub hKB hKC]
    exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun p => by ring)
  have hDI : (∫ y : ℝ × ℝ, Q y * (∫ p : ℝ × ℝ, k p * G₁ (y - p)) * G₂ y)
        - (∫ y : ℝ × ℝ, Q y * G₁ y * (∫ p : ℝ × ℝ, k p * G₂ (y - p)))
      = (∫ p : ℝ × ℝ, k p * (A p - B p)) + (∫ p : ℝ × ℝ, k p * (B p - C p)) := by
    rw [hI₁, hI₂]
    rw [show (∫ p : ℝ × ℝ, k p * A p) - (∫ p : ℝ × ℝ, k p * C p)
        = ((∫ p : ℝ × ℝ, k p * A p) - (∫ p : ℝ × ℝ, k p * B p))
          + ((∫ p : ℝ × ℝ, k p * B p) - (∫ p : ℝ × ℝ, k p * C p)) from by ring]
    rw [hAsub, hBsub]
  -- ### Step 5: the pointwise bound for the weight difference
  have keyAB : ∀ p : ℝ × ℝ, |A p - B p|
      ≤ (Real.exp (Cw * (|p.1| + |p.2|)) - 1) * Real.sqrt (∫ y : ℝ × ℝ, Q y * G₁ y ^ 2)
          * Real.sqrt (∫ y : ℝ × ℝ, Q y * G₂ y ^ 2) := by
    intro p
    have hmix := Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Pieces.integrable_mixed_pair
      (Q := Q) (G₁ := G₁) (G₂ := G₂) (Cw := Cw) hCw hQ0 hQm hQsh hQsh' hG1m hG2m hI1 hI2 p
    have hBtrans : B p = ∫ y : ℝ × ℝ, Q (y - p) * G₁ (y - p) * G₂ y := by
      have key : (∫ y : ℝ × ℝ, Q (y - p) * G₁ (y - p) * G₂ y)
          = ∫ u : ℝ × ℝ, Q u * G₁ u * G₂ (u + p) := by
        rw [show (∫ y : ℝ × ℝ, Q (y - p) * G₁ (y - p) * G₂ y)
            = ∫ y : ℝ × ℝ, (fun u : ℝ × ℝ => Q u * G₁ u * G₂ (u + p)) (y - p) from
          MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun y => by
            simp only [sub_add_cancel])]
        exact MeasureTheory.integral_sub_right_eq_self
          (fun u : ℝ × ℝ => Q u * G₁ u * G₂ (u + p)) p
      rw [hB]
      exact key.symm
    have hsub : A p - B p = ∫ y : ℝ × ℝ, (Q y - Q (y - p)) * G₁ (y - p) * G₂ y := by
      rw [hA, hBtrans, ← MeasureTheory.integral_sub hmix.1 hmix.2.1]
      exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun y => by ring)
    rw [hsub]
    exact Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Pieces.dabsIntLe
      (Q := Q) (G₁ := G₁) (G₂ := G₂) (Cw := Cw) hCw hQ0 hQm hQsh hQsh' hG1m hG2m hI1 hI2 p
  -- ### Step 6: the pointwise bound for the shift difference
  have keyBC : ∀ p : ℝ × ℝ, |B p - C p|
      ≤ 2 * (|p.1| + |p.2|) * Real.exp (Cw * (|p.1| + |p.2|) / 2)
          * Real.sqrt (∫ y : ℝ × ℝ, Q y * G₁ y ^ 2)
          * Real.sqrt (∫ y : ℝ × ℝ, Q y * ‖fderiv ℝ G₂ y‖ ^ 2) := by
    intro p
    have hsq := shift_sq_bound (Q := Q) (G₂ := G₂) (Cw := Cw) hCw hQ0 hQm hQsh' hG2d hI3 p
    have hmix := Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Pieces.integrable_mixed_pair
      (Q := Q) (G₁ := G₁) (G₂ := G₂) (Cw := Cw) hCw hQ0 hQm hQsh hQsh' hG1m hG2m hI1 hI2 p
    have hpair := shift_pair_bound (Q := Q) (G₁ := G₁) (G₂ := G₂) (p := p)
      hQ0 hQm hG1m hG2m hI1 hsq.1 hmix.2.2.1 hmix.2.2.2
    have hDv0 : 0 ≤ ∫ y : ℝ × ℝ, Q y * ‖fderiv ℝ G₂ y‖ ^ 2 :=
      MeasureTheory.integral_nonneg fun y => mul_nonneg (hQ0 y) (sq_nonneg _)
    have hY0 : 0 ≤ 2 * ‖p‖ * Real.exp (Cw * (|p.1| + |p.2|) / 2)
        * Real.sqrt (∫ y : ℝ × ℝ, Q y * ‖fderiv ℝ G₂ y‖ ^ 2) := by positivity
    have hY2 : (2 * ‖p‖ * Real.exp (Cw * (|p.1| + |p.2|) / 2)
          * Real.sqrt (∫ y : ℝ × ℝ, Q y * ‖fderiv ℝ G₂ y‖ ^ 2)) ^ 2
        = 4 * ‖p‖ ^ 2 * Real.exp (Cw * (|p.1| + |p.2|))
          * ∫ y : ℝ × ℝ, Q y * ‖fderiv ℝ G₂ y‖ ^ 2 := by
      have hθ : Real.exp (Cw * (|p.1| + |p.2|) / 2) ^ 2
          = Real.exp (Cw * (|p.1| + |p.2|)) := by
        rw [sq, ← Real.exp_add]
        congr 1
        ring
      simp only [mul_pow, hθ, Real.sq_sqrt hDv0]
      ring
    have hsqrtX : Real.sqrt (∫ y : ℝ × ℝ, Q y * (G₂ (y + p) - G₂ (y - p)) ^ 2)
        ≤ 2 * (|p.1| + |p.2|) * Real.exp (Cw * (|p.1| + |p.2|) / 2)
          * Real.sqrt (∫ y : ℝ × ℝ, Q y * ‖fderiv ℝ G₂ y‖ ^ 2) := by
      have hnorm : ‖p‖ ≤ |p.1| + |p.2| := by
        rw [Prod.norm_def]
        exact max_le (le_add_of_nonneg_right (abs_nonneg _))
          (le_add_of_nonneg_left (abs_nonneg _))
      have hexp0 : 0 ≤ Real.exp (Cw * (|p.1| + |p.2|) / 2) := Real.exp_nonneg _
      have hsd : 0 ≤ Real.sqrt (∫ y : ℝ × ℝ, Q y * ‖fderiv ℝ G₂ y‖ ^ 2) := Real.sqrt_nonneg _
      calc Real.sqrt (∫ y : ℝ × ℝ, Q y * (G₂ (y + p) - G₂ (y - p)) ^ 2)
          ≤ Real.sqrt ((2 * ‖p‖ * Real.exp (Cw * (|p.1| + |p.2|) / 2)
              * Real.sqrt (∫ y : ℝ × ℝ, Q y * ‖fderiv ℝ G₂ y‖ ^ 2)) ^ 2) :=
            Real.sqrt_le_sqrt (by rw [hY2]; exact hsq.2)
        _ = 2 * ‖p‖ * Real.exp (Cw * (|p.1| + |p.2|) / 2)
              * Real.sqrt (∫ y : ℝ × ℝ, Q y * ‖fderiv ℝ G₂ y‖ ^ 2) := Real.sqrt_sq hY0
        _ ≤ 2 * (|p.1| + |p.2|) * Real.exp (Cw * (|p.1| + |p.2|) / 2)
              * Real.sqrt (∫ y : ℝ × ℝ, Q y * ‖fderiv ℝ G₂ y‖ ^ 2) := by
            have h3 : 2 * ‖p‖ ≤ 2 * (|p.1| + |p.2|) := by linarith
            calc 2 * ‖p‖ * Real.exp (Cw * (|p.1| + |p.2|) / 2)
                  * Real.sqrt (∫ y : ℝ × ℝ, Q y * ‖fderiv ℝ G₂ y‖ ^ 2)
                = (2 * ‖p‖) * (Real.exp (Cw * (|p.1| + |p.2|) / 2)
                    * Real.sqrt (∫ y : ℝ × ℝ, Q y * ‖fderiv ℝ G₂ y‖ ^ 2)) := by ring
              _ ≤ (2 * (|p.1| + |p.2|)) * (Real.exp (Cw * (|p.1| + |p.2|) / 2)
                    * Real.sqrt (∫ y : ℝ × ℝ, Q y * ‖fderiv ℝ G₂ y‖ ^ 2)) :=
                  mul_le_mul_of_nonneg_right h3 (mul_nonneg hexp0 hsd)
              _ = 2 * (|p.1| + |p.2|) * Real.exp (Cw * (|p.1| + |p.2|) / 2)
                    * Real.sqrt (∫ y : ℝ × ℝ, Q y * ‖fderiv ℝ G₂ y‖ ^ 2) := by ring
    calc |B p - C p|
        = |(∫ y : ℝ × ℝ, Q y * G₁ y * G₂ (y + p))
            - (∫ y : ℝ × ℝ, Q y * G₁ y * G₂ (y - p))| := by rw [hB, hC]
      _ ≤ Real.sqrt (∫ y : ℝ × ℝ, Q y * G₁ y ^ 2)
            * Real.sqrt (∫ y : ℝ × ℝ, Q y * (G₂ (y + p) - G₂ (y - p)) ^ 2) := hpair
      _ ≤ Real.sqrt (∫ y : ℝ × ℝ, Q y * G₁ y ^ 2)
            * (2 * (|p.1| + |p.2|) * Real.exp (Cw * (|p.1| + |p.2|) / 2)
              * Real.sqrt (∫ y : ℝ × ℝ, Q y * ‖fderiv ℝ G₂ y‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left hsqrtX (Real.sqrt_nonneg _)
      _ = 2 * (|p.1| + |p.2|) * Real.exp (Cw * (|p.1| + |p.2|) / 2)
            * Real.sqrt (∫ y : ℝ × ℝ, Q y * G₁ y ^ 2)
            * Real.sqrt (∫ y : ℝ × ℝ, Q y * ‖fderiv ℝ G₂ y‖ ^ 2) := by ring
  -- ### Step 7: integrate the two pointwise bounds against the kernel
  set K₁ : ℝ := (Real.exp (2 * Cw * ε) - 1) * Real.sqrt (∫ y : ℝ × ℝ, Q y * G₁ y ^ 2)
      * Real.sqrt (∫ y : ℝ × ℝ, Q y * G₂ y ^ 2) with hK₁
  set K₂ : ℝ := 2 * (2 * ε) * Real.exp (Cw * ε) * Real.sqrt (∫ y : ℝ × ℝ, Q y * G₁ y ^ 2)
      * Real.sqrt (∫ y : ℝ × ℝ, Q y * ‖fderiv ℝ G₂ y‖ ^ 2) with hK₂
  have hK₁0 : 0 ≤ K₁ := by
    rw [hK₁]
    have h1 : 0 ≤ Real.exp (2 * Cw * ε) - 1 := by
      have := Real.one_le_exp (show (0 : ℝ) ≤ 2 * Cw * ε by positivity)
      linarith
    exact mul_nonneg (mul_nonneg h1 (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
  have hbound1 : |∫ p : ℝ × ℝ, k p * (A p - B p)| ≤ K₁ := by
    have hpt : ∀ p : ℝ × ℝ, |k p| * |A p - B p| ≤ K₁ * |k p| := by
      intro p
      by_cases hp : k p = 0
      · simp [hp]
      · have hθ : Cw * (|p.1| + |p.2|) ≤ 2 * Cw * ε := by
          have hs := hksupp p hp
          nlinarith [hCw, hs]
        have he1 : Real.exp (Cw * (|p.1| + |p.2|)) - 1 ≤ Real.exp (2 * Cw * ε) - 1 := by
          have h := Real.exp_le_exp.mpr hθ
          linarith
        have hS1 : 0 ≤ Real.sqrt (∫ y : ℝ × ℝ, Q y * G₁ y ^ 2) := Real.sqrt_nonneg _
        have hS2 : 0 ≤ Real.sqrt (∫ y : ℝ × ℝ, Q y * G₂ y ^ 2) := Real.sqrt_nonneg _
        have h1 : |A p - B p| ≤ K₁ := by
          rw [hK₁]
          calc |A p - B p| ≤ (Real.exp (Cw * (|p.1| + |p.2|)) - 1)
                * Real.sqrt (∫ y : ℝ × ℝ, Q y * G₁ y ^ 2)
                * Real.sqrt (∫ y : ℝ × ℝ, Q y * G₂ y ^ 2) := keyAB p
            _ ≤ (Real.exp (2 * Cw * ε) - 1) * Real.sqrt (∫ y : ℝ × ℝ, Q y * G₁ y ^ 2)
                * Real.sqrt (∫ y : ℝ × ℝ, Q y * G₂ y ^ 2) :=
                mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right he1 hS1) hS2
        calc |k p| * |A p - B p| ≤ |k p| * K₁ := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
          _ = K₁ * |k p| := by ring
    have hInt : MeasureTheory.Integrable (fun p : ℝ × ℝ => K₁ * |k p|) := hkabs.const_mul K₁
    calc |∫ p : ℝ × ℝ, k p * (A p - B p)|
        ≤ ∫ p : ℝ × ℝ, |k p * (A p - B p)| := MeasureTheory.abs_integral_le_integral_abs
      _ = ∫ p : ℝ × ℝ, |k p| * |A p - B p| := by
          refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
          show |k p * (A p - B p)| = |k p| * |A p - B p|
          rw [abs_mul]
      _ ≤ ∫ p : ℝ × ℝ, K₁ * |k p| := by
          refine MeasureTheory.integral_mono_of_nonneg
            (Filter.Eventually.of_forall fun p => mul_nonneg (abs_nonneg _) (abs_nonneg _)) hInt
            (Filter.Eventually.of_forall hpt)
      _ = K₁ * ∫ p : ℝ × ℝ, |k p| := by rw [MeasureTheory.integral_const_mul]
      _ ≤ K₁ * 1 := mul_le_mul_of_nonneg_left hmass hK₁0
      _ = K₁ := by ring
  have hK₂0 : 0 ≤ K₂ := by
    rw [hK₂]
    positivity
  have hbound2 : |∫ p : ℝ × ℝ, k p * (B p - C p)| ≤ K₂ := by
    have hpt : ∀ p : ℝ × ℝ, |k p| * |B p - C p| ≤ K₂ * |k p| := by
      intro p
      by_cases hp : k p = 0
      · simp [hp]
      · have hs := hksupp p hp
        have hθ : Cw * (|p.1| + |p.2|) / 2 ≤ Cw * ε := by nlinarith [hCw, hs]
        have he : Real.exp (Cw * (|p.1| + |p.2|) / 2) ≤ Real.exp (Cw * ε) :=
          Real.exp_le_exp.mpr hθ
        have hsu : 2 * (|p.1| + |p.2|) ≤ 2 * (2 * ε) := by linarith
        have hS1 : 0 ≤ Real.sqrt (∫ y : ℝ × ℝ, Q y * G₁ y ^ 2) := Real.sqrt_nonneg _
        have hSd : 0 ≤ Real.sqrt (∫ y : ℝ × ℝ, Q y * ‖fderiv ℝ G₂ y‖ ^ 2) :=
          Real.sqrt_nonneg _
        have h1 : |B p - C p| ≤ K₂ := by
          rw [hK₂]
          have hstep : 2 * (|p.1| + |p.2|) * Real.exp (Cw * (|p.1| + |p.2|) / 2)
                * Real.sqrt (∫ y : ℝ × ℝ, Q y * G₁ y ^ 2)
                * Real.sqrt (∫ y : ℝ × ℝ, Q y * ‖fderiv ℝ G₂ y‖ ^ 2)
              ≤ 2 * (2 * ε) * Real.exp (Cw * ε)
                * Real.sqrt (∫ y : ℝ × ℝ, Q y * G₁ y ^ 2)
                * Real.sqrt (∫ y : ℝ × ℝ, Q y * ‖fderiv ℝ G₂ y‖ ^ 2) := by
            calc 2 * (|p.1| + |p.2|) * Real.exp (Cw * (|p.1| + |p.2|) / 2)
                  * Real.sqrt (∫ y : ℝ × ℝ, Q y * G₁ y ^ 2)
                  * Real.sqrt (∫ y : ℝ × ℝ, Q y * ‖fderiv ℝ G₂ y‖ ^ 2)
                = (2 * (|p.1| + |p.2|)) * (Real.exp (Cw * (|p.1| + |p.2|) / 2)
                    * (Real.sqrt (∫ y : ℝ × ℝ, Q y * G₁ y ^ 2)
                      * Real.sqrt (∫ y : ℝ × ℝ, Q y * ‖fderiv ℝ G₂ y‖ ^ 2))) := by ring
              _ ≤ (2 * (2 * ε)) * (Real.exp (Cw * ε)
                    * (Real.sqrt (∫ y : ℝ × ℝ, Q y * G₁ y ^ 2)
                      * Real.sqrt (∫ y : ℝ × ℝ, Q y * ‖fderiv ℝ G₂ y‖ ^ 2))) := by
                  refine mul_le_mul hsu ?_ (by positivity) (by positivity)
                  exact mul_le_mul_of_nonneg_right he (mul_nonneg hS1 hSd)
              _ = 2 * (2 * ε) * Real.exp (Cw * ε)
                    * Real.sqrt (∫ y : ℝ × ℝ, Q y * G₁ y ^ 2)
                    * Real.sqrt (∫ y : ℝ × ℝ, Q y * ‖fderiv ℝ G₂ y‖ ^ 2) := by ring
          exact le_trans (keyBC p) hstep
        calc |k p| * |B p - C p| ≤ |k p| * K₂ := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
          _ = K₂ * |k p| := by ring
    have hInt : MeasureTheory.Integrable (fun p : ℝ × ℝ => K₂ * |k p|) := hkabs.const_mul K₂
    calc |∫ p : ℝ × ℝ, k p * (B p - C p)|
        ≤ ∫ p : ℝ × ℝ, |k p * (B p - C p)| := MeasureTheory.abs_integral_le_integral_abs
      _ = ∫ p : ℝ × ℝ, |k p| * |B p - C p| := by
          refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
          show |k p * (B p - C p)| = |k p| * |B p - C p|
          rw [abs_mul]
      _ ≤ ∫ p : ℝ × ℝ, K₂ * |k p| := by
          refine MeasureTheory.integral_mono_of_nonneg
            (Filter.Eventually.of_forall fun p => mul_nonneg (abs_nonneg _) (abs_nonneg _)) hInt
            (Filter.Eventually.of_forall hpt)
      _ = K₂ * ∫ p : ℝ × ℝ, |k p| := by rw [MeasureTheory.integral_const_mul]
      _ ≤ K₂ * 1 := mul_le_mul_of_nonneg_left hmass hK₂0
      _ = K₂ := by ring
  have hmain : |(∫ y : ℝ × ℝ, Q y * (∫ p : ℝ × ℝ, k p * G₁ (y - p)) * G₂ y)
        - (∫ y : ℝ × ℝ, Q y * G₁ y * (∫ p : ℝ × ℝ, k p * G₂ (y - p)))| ≤ K₁ + K₂ := by
    rw [hDI]
    exact le_trans (abs_add_le _ _) (add_le_add hbound1 hbound2)
  -- ### Step 8: the numerical bounds on the two constants
  have hce₁ : Real.exp (2 * Cw * ε) - 1 ≤ 100 * (Cw + 1) * Real.exp (4 * Cw) * ε := by
    have h0 : 0 ≤ 2 * Cw * ε := by positivity
    have hexp_le : Real.exp (2 * Cw * ε) - 1 ≤ (2 * Cw * ε) * Real.exp (2 * Cw * ε) := by
      have h1 : (1 : ℝ) - Real.exp (-(2 * Cw * ε)) ≤ 2 * Cw * ε := by
        have := Real.add_one_le_exp (-(2 * Cw * ε))
        linarith
      have h2 : Real.exp (2 * Cw * ε) - 1
          = Real.exp (2 * Cw * ε) * (1 - Real.exp (-(2 * Cw * ε))) := by
        rw [Real.exp_neg, mul_sub, mul_one, mul_inv_cancel₀ (Real.exp_ne_zero _)]
      rw [h2]
      calc Real.exp (2 * Cw * ε) * (1 - Real.exp (-(2 * Cw * ε)))
          ≤ Real.exp (2 * Cw * ε) * (2 * Cw * ε) :=
            mul_le_mul_of_nonneg_left h1 (Real.exp_nonneg _)
        _ = (2 * Cw * ε) * Real.exp (2 * Cw * ε) := by ring
    have h2 : (2 * Cw * ε) * Real.exp (2 * Cw * ε) ≤ (2 * Cw * ε) * Real.exp (4 * Cw) := by
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) h0
      nlinarith [hCw, hε0.le, hε1]
    have h3 : (2 * Cw * ε) * Real.exp (4 * Cw)
        ≤ 100 * (Cw + 1) * Real.exp (4 * Cw) * ε := by
      have h4 : 2 * Cw * ε ≤ 100 * (Cw + 1) * ε := by nlinarith [hCw, hε0.le]
      calc (2 * Cw * ε) * Real.exp (4 * Cw)
          ≤ (100 * (Cw + 1) * ε) * Real.exp (4 * Cw) :=
            mul_le_mul_of_nonneg_right h4 (Real.exp_nonneg _)
        _ = 100 * (Cw + 1) * Real.exp (4 * Cw) * ε := by ring
    exact le_trans hexp_le (le_trans h2 h3)
  have hce₂ : 2 * (2 * ε) * Real.exp (Cw * ε) ≤ 100 * (Cw + 1) * Real.exp (4 * Cw) * ε := by
    have h1 : Real.exp (Cw * ε) ≤ Real.exp (4 * Cw) :=
      Real.exp_le_exp.mpr (by nlinarith [hCw, hε0.le, hε1])
    have h2 : 2 * (2 * ε) * Real.exp (Cw * ε) ≤ 2 * (2 * ε) * Real.exp (4 * Cw) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have h3 : 2 * (2 * ε) * Real.exp (4 * Cw) ≤ 100 * (Cw + 1) * Real.exp (4 * Cw) * ε := by
      have h4 : (4 : ℝ) * ε ≤ 100 * (Cw + 1) * ε := by nlinarith [hCw, hε0.le]
      calc 2 * (2 * ε) * Real.exp (4 * Cw) = (4 * ε) * Real.exp (4 * Cw) := by ring
        _ ≤ (100 * (Cw + 1) * ε) * Real.exp (4 * Cw) :=
              mul_le_mul_of_nonneg_right h4 (Real.exp_nonneg _)
        _ = 100 * (Cw + 1) * Real.exp (4 * Cw) * ε := by ring
    exact le_trans h2 h3
  refine le_trans hmain ?_
  rw [hK₁, hK₂]
  have hS1 : 0 ≤ Real.sqrt (∫ y : ℝ × ℝ, Q y * G₁ y ^ 2) := Real.sqrt_nonneg _
  have hS2 : 0 ≤ Real.sqrt (∫ y : ℝ × ℝ, Q y * G₂ y ^ 2) := Real.sqrt_nonneg _
  have hSd : 0 ≤ Real.sqrt (∫ y : ℝ × ℝ, Q y * ‖fderiv ℝ G₂ y‖ ^ 2) := Real.sqrt_nonneg _
  have hB1 : (Real.exp (2 * Cw * ε) - 1) * Real.sqrt (∫ y : ℝ × ℝ, Q y * G₁ y ^ 2)
        * Real.sqrt (∫ y : ℝ × ℝ, Q y * G₂ y ^ 2)
      ≤ (100 * (Cw + 1) * Real.exp (4 * Cw) * ε) * Real.sqrt (∫ y : ℝ × ℝ, Q y * G₁ y ^ 2)
        * Real.sqrt (∫ y : ℝ × ℝ, Q y * G₂ y ^ 2) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hce₁ hS1) hS2
  have hB2 : 2 * (2 * ε) * Real.exp (Cw * ε) * Real.sqrt (∫ y : ℝ × ℝ, Q y * G₁ y ^ 2)
        * Real.sqrt (∫ y : ℝ × ℝ, Q y * ‖fderiv ℝ G₂ y‖ ^ 2)
      ≤ (100 * (Cw + 1) * Real.exp (4 * Cw) * ε) * Real.sqrt (∫ y : ℝ × ℝ, Q y * G₁ y ^ 2)
        * Real.sqrt (∫ y : ℝ × ℝ, Q y * ‖fderiv ℝ G₂ y‖ ^ 2) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hce₂ hS1) hSd
  calc (Real.exp (2 * Cw * ε) - 1) * Real.sqrt (∫ y : ℝ × ℝ, Q y * G₁ y ^ 2)
          * Real.sqrt (∫ y : ℝ × ℝ, Q y * G₂ y ^ 2)
        + 2 * (2 * ε) * Real.exp (Cw * ε) * Real.sqrt (∫ y : ℝ × ℝ, Q y * G₁ y ^ 2)
          * Real.sqrt (∫ y : ℝ × ℝ, Q y * ‖fderiv ℝ G₂ y‖ ^ 2)
      ≤ (100 * (Cw + 1) * Real.exp (4 * Cw) * ε) * Real.sqrt (∫ y : ℝ × ℝ, Q y * G₁ y ^ 2)
          * Real.sqrt (∫ y : ℝ × ℝ, Q y * G₂ y ^ 2)
        + (100 * (Cw + 1) * Real.exp (4 * Cw) * ε)
          * Real.sqrt (∫ y : ℝ × ℝ, Q y * G₁ y ^ 2)
          * Real.sqrt (∫ y : ℝ × ℝ, Q y * ‖fderiv ℝ G₂ y‖ ^ 2) := add_le_add hB1 hB2
    _ = 100 * (Cw + 1) * Real.exp (4 * Cw) * ε * Real.sqrt (∫ y : ℝ × ℝ, Q y * G₁ y ^ 2)
          * (Real.sqrt (∫ y : ℝ × ℝ, Q y * G₂ y ^ 2)
            + Real.sqrt (∫ y : ℝ × ℝ, Q y * ‖fderiv ℝ G₂ y‖ ^ 2)) := by ring

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.L12JepsAux.Basic =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Set Filter
open scoped Topology
open Work.FTS.StrongEps (Jeps Jker logPull zShift thShift sOf zetaOf IsMollKernel IsSmoothKernel)
open Work.FTS.Galerkin (Fn Fam slice)

namespace Work.FTS.StrongEps.EpsE4Thr.L12JepsAux

set_option autoImplicit false

/-! ## The kernel has a point of strict positivity -/


/-! ## The transport of `hint` to the log coordinates -/




/-! ## Integrability of the two `θ`-integrands -/



end Work.FTS.StrongEps.EpsE4Thr.L12JepsAux
end
end
