import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Function.SpecialFunctions.Arctan
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.UniformSpace.Uniformizable
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.LocDataExt.Defs
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS.Physical.BiotSavart.bsAdmissibleStripFull_comp_clock
import Submission.Work.FTS.StrongEps.SmoothOpen_Jeps
import Submission.Work.FTS_EllLimOK.IsBslSolPos_add
import Submission.Work.FTS_MuLamOK.Rows.rl0_final
import Submission.Work.FTS_RegExport.RXT.Slots.JetCalc.Expand
import Submission.Work.FTS_RegExport.RXT.SysAux.explicit_piece_bounds
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.bt_integral_weight_id
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Stability.Cutoff
import Submission.Work.Stability.mul_rpow_le
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.logPair_conv_transfer_iter =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer

set_option maxHeartbeats 1000000


/-! ## Elementary helpers -/

private theorem norm_le_abs_add {p : ℝ × ℝ} : ‖p‖ ≤ |p.1| + |p.2| := by
  have h1 : ‖p‖ ≤ |p.1| ∨ ‖p‖ ≤ |p.2| := by
    rw [Prod.norm_def]
    exact le_max_iff.mp le_rfl
  rcases h1 with h | h
  · linarith [abs_nonneg p.2]
  · linarith [abs_nonneg p.1]

private theorem integrable_of_cont_supp {k : ℝ × ℝ → ℝ} {ε : ℝ} (_hε : 0 < ε)
    (hkcont : Continuous k) (hksupp : ∀ p : ℝ × ℝ, k p ≠ 0 → |p.1| + |p.2| ≤ 2 * ε) :
    Integrable k := by
  refine hkcont.integrable_of_hasCompactSupport
    (HasCompactSupport.of_support_subset_isCompact (K := Metric.closedBall (0:ℝ×ℝ) (2*ε)) ?_ ?_)
  · exact isCompact_closedBall _ _
  · intro p hp
    rw [Metric.mem_closedBall, dist_zero_right]
    have h := hksupp p hp
    have h3 := norm_le_abs_add (p := p)
    linarith

private theorem two_mul_abs_mul_le (a b : ℝ) : 2 * |a * b| ≤ a ^ 2 + b ^ 2 := by
  have h : |a * b| = |a| * |b| := abs_mul a b
  have h1 : a ^ 2 = |a| ^ 2 := (sq_abs a).symm
  have h2 : b ^ 2 = |b| ^ 2 := (sq_abs b).symm
  nlinarith [sq_nonneg (|a| - |b|)]

private theorem abs_mul_weight_le {c x y : ℝ} (hc : 0 ≤ c) :
    |c * x * y| ≤ (c * x ^ 2 + c * y ^ 2) / 2 := by
  have hs : Real.sqrt c ^ 2 = c := Real.sq_sqrt hc
  have h := two_mul_abs_mul_le (Real.sqrt c * x) (Real.sqrt c * y)
  rw [mul_pow, mul_pow, hs] at h
  have h' : (Real.sqrt c * x) * (Real.sqrt c * y) = c * x * y := by
    rw [mul_mul_mul_comm, ← sq, hs]; ring
  rw [h'] at h
  linarith


/-! ## Integrability of the mixed pairings -/

private theorem integrable_mixed_pair {Q G₁ G₂ : ℝ × ℝ → ℝ} {Cw : ℝ} (hCw : 0 ≤ Cw)
    (hQ0 : ∀ y : ℝ × ℝ, 0 ≤ Q y) (hQm : Measurable Q)
    (hQsh : ∀ y p : ℝ × ℝ, Q (y + p) ≤ Real.exp (Cw * (|p.1| + |p.2|)) * Q y)
    (hQsh' : ∀ y p : ℝ × ℝ, Q y ≤ Real.exp (Cw * (|p.1| + |p.2|)) * Q (y + p))
    (hG1m : Measurable G₁) (hG2m : Measurable G₂)
    (hI1 : Integrable (fun y : ℝ × ℝ => Q y * G₁ y ^ 2))
    (hI2 : Integrable (fun y : ℝ × ℝ => Q y * G₂ y ^ 2)) (p : ℝ × ℝ) :
    Integrable (fun y : ℝ × ℝ => Q y * G₁ (y - p) * G₂ y)
      ∧ Integrable (fun y : ℝ × ℝ => Q (y - p) * G₁ (y - p) * G₂ y) := by
  have hshift : ∀ y : ℝ × ℝ, (y - p) + p = y := fun y => sub_add_cancel y p
  have hQlt : ∀ y : ℝ × ℝ, Q y ≤ Real.exp (Cw * (|p.1| + |p.2|)) * Q (y - p) := by
    intro y
    have h := hQsh (y - p) p
    rwa [hshift y] at h
  have hQgt : ∀ y : ℝ × ℝ, Q (y - p) ≤ Real.exp (Cw * (|p.1| + |p.2|)) * Q y := by
    intro y
    have h := hQsh' (y - p) p
    rwa [hshift y] at h
  have hms1 : Measurable (fun y : ℝ × ℝ => Q y * G₁ (y - p) ^ 2) := by fun_prop
  have hms2 : Measurable (fun y : ℝ × ℝ => Q (y - p) * G₂ y ^ 2) := by fun_prop
  have hsub1 : Integrable (fun y : ℝ × ℝ => Q (y - p) * G₁ (y - p) ^ 2) :=
    hI1.comp_sub_right p
  have hA1 : Integrable (fun y : ℝ × ℝ => Q y * G₁ (y - p) ^ 2) := by
    refine Integrable.mono' (hsub1.const_mul (Real.exp (Cw * (|p.1| + |p.2|))))
      hms1.aestronglyMeasurable (Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hQ0 y) (sq_nonneg _))]
    calc Q y * G₁ (y - p) ^ 2
        ≤ (Real.exp (Cw * (|p.1| + |p.2|)) * Q (y - p)) * G₁ (y - p) ^ 2 :=
          mul_le_mul_of_nonneg_right (hQlt y) (sq_nonneg _)
      _ = Real.exp (Cw * (|p.1| + |p.2|)) * (Q (y - p) * G₁ (y - p) ^ 2) := by ring
  have hB1 : Integrable (fun y : ℝ × ℝ => Q (y - p) * G₂ y ^ 2) := by
    refine Integrable.mono' (hI2.const_mul (Real.exp (Cw * (|p.1| + |p.2|))))
      hms2.aestronglyMeasurable (Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hQ0 _) (sq_nonneg _))]
    calc Q (y - p) * G₂ y ^ 2
        ≤ (Real.exp (Cw * (|p.1| + |p.2|)) * Q y) * G₂ y ^ 2 :=
          mul_le_mul_of_nonneg_right (hQgt y) (sq_nonneg _)
      _ = Real.exp (Cw * (|p.1| + |p.2|)) * (Q y * G₂ y ^ 2) := by ring
  have hms3 : Measurable (fun y : ℝ × ℝ => Q y * G₁ (y - p) * G₂ y) := by fun_prop
  have hms4 : Measurable (fun y : ℝ × ℝ => Q (y - p) * G₁ (y - p) * G₂ y) := by fun_prop
  constructor
  · refine Integrable.mono' ((hA1.add hI2).const_mul (1/2)) (Measurable.aestronglyMeasurable hms3)
      (Eventually.of_forall fun y => ?_)
    · rw [Real.norm_eq_abs]
      have h := abs_mul_weight_le (c := Q y) (x := G₁ (y - p)) (y := G₂ y) (hQ0 y)
      calc |Q y * G₁ (y - p) * G₂ y| ≤ (Q y * G₁ (y - p) ^ 2 + Q y * G₂ y ^ 2) / 2 := h
        _ = (1/2) * (Q y * G₁ (y - p) ^ 2 + Q y * G₂ y ^ 2) := by ring
  · refine Integrable.mono' ((hB1.add hsub1).const_mul (1/2))
      (Measurable.aestronglyMeasurable hms4) (Eventually.of_forall fun y => ?_)
    · rw [Real.norm_eq_abs]
      have h := abs_mul_weight_le (c := Q (y - p)) (x := G₁ (y - p)) (y := G₂ y) (hQ0 _)
      calc |Q (y - p) * G₁ (y - p) * G₂ y|
          ≤ (Q (y - p) * G₁ (y - p) ^ 2 + Q (y - p) * G₂ y ^ 2) / 2 := h
        _ = (1/2) * (Q (y - p) * G₂ y ^ 2 + Q (y - p) * G₁ (y - p) ^ 2) := by ring

/-! ## The iterated integral is the plane integral -/

private theorem iter_eq_plane (F : ℝ × ℝ → ℝ) (hF : Integrable F) :
    (∫ y : ℝ × ℝ, F y) = ∫ s, ∫ ζ, F (s, ζ) :=
  integral_prod (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ)) F hF


private theorem exp_sub_one_two_mono {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    2 * (Real.exp a - 1) * Real.exp a ≤ 2 * (Real.exp b - 1) * Real.exp b := by
  have h1 : Real.exp a ≤ Real.exp b := Real.exp_le_exp.mpr hab
  have h2 : Real.exp a - 1 ≤ Real.exp b - 1 := by linarith
  have h3 : 0 ≤ Real.exp a - 1 := by
    have := Real.one_le_exp ha; linarith
  have h4 : 0 ≤ Real.exp b - 1 := by
    have := Real.one_le_exp (ha.trans hab); linarith
  have h5 : (Real.exp a - 1) * Real.exp a ≤ (Real.exp b - 1) * Real.exp b :=
    mul_le_mul h2 h1 (Real.exp_pos a).le h4
  linarith

/-- The plane-integral version of the transfer estimate. -/
private theorem conv_transfer_plane {k Q G₁ G₂ : ℝ × ℝ → ℝ} {ε Cw : ℝ}
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hCw : 0 ≤ Cw)
    (hkcont : Continuous k) (hk0 : ∀ p : ℝ × ℝ, 0 ≤ k p)
    (hkmass : ∫ p : ℝ × ℝ, k p = 1)
    (hksupp : ∀ p : ℝ × ℝ, k p ≠ 0 → |p.1| + |p.2| ≤ 2 * ε)
    (hkeven : ∀ p : ℝ × ℝ, k (-p) = k p)
    (hkmomint : Integrable (fun p : ℝ × ℝ => k p * (|p.1| + |p.2|)))
    (hQ0 : ∀ y : ℝ × ℝ, 0 ≤ Q y) (hQm : Measurable Q)
    (hQsh : ∀ y p : ℝ × ℝ, Q (y + p) ≤ Real.exp (Cw * (|p.1| + |p.2|)) * Q y)
    (hQsh' : ∀ y p : ℝ × ℝ, Q y ≤ Real.exp (Cw * (|p.1| + |p.2|)) * Q (y + p))
    (hG1m : Measurable G₁) (hG2m : Measurable G₂)
    (hconv1 : ∀ y : ℝ × ℝ, Integrable (fun p : ℝ × ℝ => k p * G₁ (y - p)))
    (hconv2 : ∀ y : ℝ × ℝ, Integrable (fun p : ℝ × ℝ => k p * G₂ (y - p)))
    (hI1 : Integrable (fun y : ℝ × ℝ => Q y * G₁ y ^ 2))
    (hI2 : Integrable (fun y : ℝ × ℝ => Q y * G₂ y ^ 2)) :
    |(∫ y : ℝ × ℝ, Q y * (∫ p : ℝ × ℝ, k p * G₁ (y - p)) * G₂ y)
      - (∫ y : ℝ × ℝ, Q y * G₁ y * (∫ p : ℝ × ℝ, k p * G₂ (y - p)))|
      ≤ 100 * (Cw + 1) * Real.exp (4 * Cw) * ε
          * Real.sqrt (∫ y : ℝ × ℝ, Q y * G₁ y ^ 2) * Real.sqrt (∫ y : ℝ × ℝ, Q y * G₂ y ^ 2) := by
  have hk : Integrable k := integrable_of_cont_supp hε0 hkcont hksupp
  obtain ⟨hintA, hintB⟩ :=
    Pieces2.conv_joint_integrable hCw hk hk0 hksupp hQ0 hQm hQsh hG1m hG2m hI1 hI2
  -- ### Step 1: Fubini for the first pairing
  have hA₁ : (∫ y : ℝ × ℝ, Q y * (∫ p : ℝ × ℝ, k p * G₁ (y - p)) * G₂ y)
      = ∫ y : ℝ × ℝ, ∫ p : ℝ × ℝ, k p * Q y * G₁ (y - p) * G₂ y := by
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    calc Q y * (∫ p : ℝ × ℝ, k p * G₁ (y - p)) * G₂ y
        = (∫ p : ℝ × ℝ, k p * G₁ (y - p)) * (Q y * G₂ y) := by ring
      _ = ∫ p : ℝ × ℝ, (k p * G₁ (y - p)) * (Q y * G₂ y) :=
            (integral_mul_const (Q y * G₂ y) (fun p : ℝ × ℝ => k p * G₁ (y - p))).symm
      _ = ∫ p : ℝ × ℝ, k p * Q y * G₁ (y - p) * G₂ y :=
            integral_congr_ae (Eventually.of_forall fun p => by ring)
  have hA₂ : (∫ y : ℝ × ℝ, ∫ p : ℝ × ℝ, k p * Q y * G₁ (y - p) * G₂ y)
      = ∫ p : ℝ × ℝ, ∫ y : ℝ × ℝ, k p * Q y * G₁ (y - p) * G₂ y :=
    integral_integral_swap (μ := volume) (ν := volume) hintA
  have hA₃ : (∫ p : ℝ × ℝ, ∫ y : ℝ × ℝ, k p * Q y * G₁ (y - p) * G₂ y)
      = ∫ p : ℝ × ℝ, k p * (∫ y : ℝ × ℝ, Q y * G₁ (y - p) * G₂ y) := by
    refine integral_congr_ae (Eventually.of_forall fun p => ?_)
    simp only []
    rw [show (∫ y : ℝ × ℝ, k p * Q y * G₁ (y - p) * G₂ y)
        = ∫ y : ℝ × ℝ, k p * (Q y * G₁ (y - p) * G₂ y) from
      integral_congr_ae (Eventually.of_forall fun y => by ring), integral_const_mul]
  have hA : (∫ y : ℝ × ℝ, Q y * (∫ p : ℝ × ℝ, k p * G₁ (y - p)) * G₂ y)
      = ∫ p : ℝ × ℝ, k p * (∫ y : ℝ × ℝ, Q y * G₁ (y - p) * G₂ y) := by
    rw [hA₁, hA₂, hA₃]
  -- ### Step 2: Fubini for the second pairing
  have hB₁ : (∫ y : ℝ × ℝ, Q y * G₁ y * (∫ p : ℝ × ℝ, k p * G₂ (y - p)))
      = ∫ y : ℝ × ℝ, ∫ p : ℝ × ℝ, k p * Q y * G₁ y * G₂ (y - p) := by
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    calc Q y * G₁ y * (∫ p : ℝ × ℝ, k p * G₂ (y - p))
        = (∫ p : ℝ × ℝ, k p * G₂ (y - p)) * (Q y * G₁ y) := by ring
      _ = ∫ p : ℝ × ℝ, (k p * G₂ (y - p)) * (Q y * G₁ y) :=
            (integral_mul_const (Q y * G₁ y) (fun p : ℝ × ℝ => k p * G₂ (y - p))).symm
      _ = ∫ p : ℝ × ℝ, k p * Q y * G₁ y * G₂ (y - p) :=
            integral_congr_ae (Eventually.of_forall fun p => by ring)
  have hB₂ : (∫ y : ℝ × ℝ, ∫ p : ℝ × ℝ, k p * Q y * G₁ y * G₂ (y - p))
      = ∫ y : ℝ × ℝ, ∫ p : ℝ × ℝ, k p * Q y * G₁ y * G₂ (y + p) := by
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    have h := integral_neg_eq_self (μ := volume)
      (fun p : ℝ × ℝ => k p * Q y * G₁ y * G₂ (y - p))
    simp only [hkeven, sub_neg_eq_add] at h
    exact h.symm
  have hB₃ : (∫ y : ℝ × ℝ, ∫ p : ℝ × ℝ, k p * Q y * G₁ y * G₂ (y + p))
      = ∫ p : ℝ × ℝ, ∫ y : ℝ × ℝ, k p * Q y * G₁ y * G₂ (y + p) :=
    integral_integral_swap (μ := volume) (ν := volume) hintB
  have hB₄ : (∫ p : ℝ × ℝ, ∫ y : ℝ × ℝ, k p * Q y * G₁ y * G₂ (y + p))
      = ∫ p : ℝ × ℝ, k p * (∫ y : ℝ × ℝ, Q (y - p) * G₁ (y - p) * G₂ y) := by
    refine integral_congr_ae (Eventually.of_forall fun p => ?_)
    simp only []
    rw [show (∫ y : ℝ × ℝ, k p * Q y * G₁ y * G₂ (y + p))
        = ∫ y : ℝ × ℝ, k p * (Q y * G₁ y * G₂ (y + p)) from
      integral_congr_ae (Eventually.of_forall fun y => by ring), integral_const_mul]
    congr 1
    have h := integral_sub_right_eq_self (μ := volume)
      (fun y : ℝ × ℝ => Q y * G₁ y * G₂ (y + p)) p
    simpa [sub_add_cancel] using h.symm
  have hB : (∫ y : ℝ × ℝ, Q y * G₁ y * (∫ p : ℝ × ℝ, k p * G₂ (y - p)))
      = ∫ p : ℝ × ℝ, k p * (∫ y : ℝ × ℝ, Q (y - p) * G₁ (y - p) * G₂ y) := by
    rw [hB₁, hB₂, hB₃, hB₄]
  -- ### Step 3: the difference is the weighted difference integral
  have hIA : ∀ p : ℝ × ℝ, Integrable (fun y : ℝ × ℝ => Q y * G₁ (y - p) * G₂ y) :=
    fun p => (integrable_mixed_pair hCw hQ0 hQm hQsh hQsh' hG1m hG2m hI1 hI2 p).1
  have hIB : ∀ p : ℝ × ℝ, Integrable (fun y : ℝ × ℝ => Q (y - p) * G₁ (y - p) * G₂ y) :=
    fun p => (integrable_mixed_pair hCw hQ0 hQm hQsh hQsh' hG1m hG2m hI1 hI2 p).2
  have hIntA : Integrable (fun p : ℝ × ℝ => k p * (∫ y : ℝ × ℝ, Q y * G₁ (y - p) * G₂ y)) := by
    refine (Integrable.integral_prod_right hintA).congr (Eventually.of_forall fun p => ?_)
    simp only [Function.uncurry_apply_pair]
    rw [show (∫ y : ℝ × ℝ, k p * Q y * G₁ (y - p) * G₂ y)
        = ∫ y : ℝ × ℝ, k p * (Q y * G₁ (y - p) * G₂ y) from
      integral_congr_ae (Eventually.of_forall fun y => by ring), integral_const_mul]
  have hIntB : Integrable (fun p : ℝ × ℝ => k p * (∫ y : ℝ × ℝ, Q (y - p) * G₁ (y - p) * G₂ y)) := by
    refine (Integrable.integral_prod_right hintB).congr (Eventually.of_forall fun p => ?_)
    simp only [Function.uncurry_apply_pair]
    rw [show (∫ y : ℝ × ℝ, k p * Q y * G₁ y * G₂ (y + p))
        = ∫ y : ℝ × ℝ, k p * (Q y * G₁ y * G₂ (y + p)) from
      integral_congr_ae (Eventually.of_forall fun y => by ring), integral_const_mul]
    congr 1
    have h := integral_sub_right_eq_self (μ := volume)
      (fun y : ℝ × ℝ => Q y * G₁ y * G₂ (y + p)) p
    simpa [sub_add_cancel] using h.symm
  have hdiff : (∫ p : ℝ × ℝ, k p * (∫ y : ℝ × ℝ, Q y * G₁ (y - p) * G₂ y))
      - (∫ p : ℝ × ℝ, k p * (∫ y : ℝ × ℝ, Q (y - p) * G₁ (y - p) * G₂ y))
      = ∫ p : ℝ × ℝ, k p * (∫ y : ℝ × ℝ, (Q y - Q (y - p)) * G₁ (y - p) * G₂ y) := by
    rw [← integral_sub hIntA hIntB]
    refine integral_congr_ae (Eventually.of_forall fun p => ?_)
    simp only []
    have hJ : (∫ y : ℝ × ℝ, (Q y - Q (y - p)) * G₁ (y - p) * G₂ y)
        = (∫ y : ℝ × ℝ, Q y * G₁ (y - p) * G₂ y)
          - (∫ y : ℝ × ℝ, Q (y - p) * G₁ (y - p) * G₂ y) := by
      rw [← integral_sub (hIA p) (hIB p)]
      exact integral_congr_ae (Eventually.of_forall fun y => by ring)
    rw [hJ]
    ring
  rw [hA, hB, hdiff]
  -- ### Step 4: the weighted bound
  set A₁ : ℝ := ∫ y : ℝ × ℝ, Q y * G₁ y ^ 2 with hA₁def
  set A₂ : ℝ := ∫ y : ℝ × ℝ, Q y * G₂ y ^ 2 with hA₂def
  have hpt : ∀ p : ℝ × ℝ, |∫ y : ℝ × ℝ, (Q y - Q (y - p)) * G₁ (y - p) * G₂ y|
      ≤ 2 * (Real.exp (Cw * (|p.1| + |p.2|)) - 1) * Real.exp (Cw * (|p.1| + |p.2|))
          * Real.sqrt A₁ * Real.sqrt A₂ := by
    intro p
    have h := Pieces2.weight_diff_integral_le hCw hQ0 hQm hQsh hQsh' hG1m hG2m hI1 hI2 p
    rwa [← hA₁def, ← hA₂def] at h
  have hMaj : Integrable (fun p : ℝ × ℝ => k p * (2 * (Real.exp (Cw * (|p.1| + |p.2|)) - 1)
        * Real.exp (Cw * (|p.1| + |p.2|)) * Real.sqrt A₁ * Real.sqrt A₂)) := by
    refine Integrable.mono'
      (hk.mul_const (2 * (Real.exp (2 * Cw * ε) - 1) * Real.exp (2 * Cw * ε)
        * Real.sqrt A₁ * Real.sqrt A₂)) (by fun_prop) (Eventually.of_forall fun p => ?_)
    rcases eq_or_ne (k p) 0 with hkp | hkp
    · rw [hkp]; simp
    · have h1 := hksupp p hkp
      have h2 : Cw * (|p.1| + |p.2|) ≤ 2 * Cw * ε := by
        have := mul_le_mul_of_nonneg_left h1 hCw
        linarith
      have h3 := exp_sub_one_two_mono (by positivity) h2
      have h4 : 0 ≤ 2 * (Real.exp (Cw * (|p.1| + |p.2|)) - 1) * Real.exp (Cw * (|p.1| + |p.2|)) := by
        have he : 1 ≤ Real.exp (Cw * (|p.1| + |p.2|)) := Real.one_le_exp (by positivity)
        have hp := Real.exp_pos (Cw * (|p.1| + |p.2|))
        nlinarith
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hk0 p)
        (mul_nonneg (mul_nonneg h4 (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)))]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right h3 (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)) (hk0 p)
  have hK := Pieces2.kernel_exp_moment_le hε0.le hε1 hCw hk hk0 hkmass hksupp
  calc |∫ p : ℝ × ℝ, k p * (∫ y : ℝ × ℝ, (Q y - Q (y - p)) * G₁ (y - p) * G₂ y)|
      ≤ ∫ p : ℝ × ℝ, |k p * (∫ y : ℝ × ℝ, (Q y - Q (y - p)) * G₁ (y - p) * G₂ y)| :=
        abs_integral_le_integral_abs
    _ = ∫ p : ℝ × ℝ, k p * |∫ y : ℝ × ℝ, (Q y - Q (y - p)) * G₁ (y - p) * G₂ y| := by
        refine integral_congr_ae (Eventually.of_forall fun p => ?_)
        simp only []
        rw [abs_mul, abs_of_nonneg (hk0 p)]
    _ ≤ ∫ p : ℝ × ℝ, k p * (2 * (Real.exp (Cw * (|p.1| + |p.2|)) - 1)
          * Real.exp (Cw * (|p.1| + |p.2|)) * Real.sqrt A₁ * Real.sqrt A₂) := by
        refine integral_mono_of_nonneg
          (Eventually.of_forall fun p => mul_nonneg (hk0 p) (abs_nonneg _)) hMaj
          (Eventually.of_forall fun p => ?_)
        simp only []
        exact mul_le_mul_of_nonneg_left (hpt p) (hk0 p)
    _ = (∫ p : ℝ × ℝ, k p * (2 * (Real.exp (Cw * (|p.1| + |p.2|)) - 1)
          * Real.exp (Cw * (|p.1| + |p.2|)))) * (Real.sqrt A₁ * Real.sqrt A₂) := by
        rw [show (∫ p : ℝ × ℝ, k p * (2 * (Real.exp (Cw * (|p.1| + |p.2|)) - 1)
              * Real.exp (Cw * (|p.1| + |p.2|)) * Real.sqrt A₁ * Real.sqrt A₂))
            = ∫ p : ℝ × ℝ, (k p * (2 * (Real.exp (Cw * (|p.1| + |p.2|)) - 1)
              * Real.exp (Cw * (|p.1| + |p.2|)))) * (Real.sqrt A₁ * Real.sqrt A₂) from
          integral_congr_ae (Eventually.of_forall fun p => by ring)]
        rw [integral_mul_const]
    _ ≤ (100 * (Cw + 1) * Real.exp (4 * Cw) * ε) * (Real.sqrt A₁ * Real.sqrt A₂) :=
        mul_le_mul_of_nonneg_right hK (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    _ = 100 * (Cw + 1) * Real.exp (4 * Cw) * ε * Real.sqrt A₁ * Real.sqrt A₂ := by ring

/-- **The transfer estimate in the iterated-integral form of the log plane.** -/
theorem logPair_conv_transfer_iter {k : ℝ × ℝ → ℝ} {ε Cw : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hCw : 0 ≤ Cw)
    (hkcont : Continuous k) (hk0 : ∀ p : ℝ × ℝ, 0 ≤ k p)
    (hkmass : ∫ p : ℝ × ℝ, k p = 1)
    (hksupp : ∀ p : ℝ × ℝ, k p ≠ 0 → |p.1| + |p.2| ≤ 2 * ε)
    (hkeven : ∀ p : ℝ × ℝ, k (-p) = k p)
    (hkmomint : MeasureTheory.Integrable (fun p : ℝ × ℝ => k p * (|p.1| + |p.2|)))
    {Q : ℝ × ℝ → ℝ} (hQ0 : ∀ y : ℝ × ℝ, 0 ≤ Q y)
    (hQm : Measurable Q)
    (hQsh : ∀ y p : ℝ × ℝ, Q (y + p) ≤ Real.exp (Cw * (|p.1| + |p.2|)) * Q y)
    (hQsh' : ∀ y p : ℝ × ℝ, Q y ≤ Real.exp (Cw * (|p.1| + |p.2|)) * Q (y + p))
    {G₁ G₂ : ℝ × ℝ → ℝ} (hG1m : Measurable G₁) (hG2m : Measurable G₂)
    (hconv1 : ∀ y : ℝ × ℝ, MeasureTheory.Integrable (fun p : ℝ × ℝ => k p * G₁ (y - p)))
    (hconv2 : ∀ y : ℝ × ℝ, MeasureTheory.Integrable (fun p : ℝ × ℝ => k p * G₂ (y - p)))
    (hI1 : MeasureTheory.Integrable (fun y : ℝ × ℝ => Q y * G₁ y ^ 2))
    (hI2 : MeasureTheory.Integrable (fun y : ℝ × ℝ => Q y * G₂ y ^ 2)) :
    |(∫ s, ∫ ζ, Q (s, ζ) * (∫ p : ℝ × ℝ, k p * G₁ ((s, ζ) - p)) * G₂ (s, ζ))
      - (∫ s, ∫ ζ, Q (s, ζ) * G₁ (s, ζ) * (∫ p : ℝ × ℝ, k p * G₂ ((s, ζ) - p)))|
      ≤ 100 * (Cw + 1) * Real.exp (4 * Cw) * ε
          * Real.sqrt (∫ s, ∫ ζ, Q (s, ζ) * G₁ (s, ζ) ^ 2)
          * Real.sqrt (∫ s, ∫ ζ, Q (s, ζ) * G₂ (s, ζ) ^ 2) := by
  have hk : Integrable k := integrable_of_cont_supp hε0 hkcont hksupp
  obtain ⟨hintA', hintB'⟩ := Pieces2.conv_pair_integrable hCw hk hk0 hksupp hQ0 hQm hQsh
    hG1m hG2m hconv1 hconv2 hI1 hI2
  have e1 : (∫ s, ∫ ζ, Q (s, ζ) * (∫ p : ℝ × ℝ, k p * G₁ ((s, ζ) - p)) * G₂ (s, ζ))
      = ∫ y : ℝ × ℝ, Q y * (∫ p : ℝ × ℝ, k p * G₁ (y - p)) * G₂ y :=
    (iter_eq_plane (fun y : ℝ × ℝ => Q y * (∫ p : ℝ × ℝ, k p * G₁ (y - p)) * G₂ y) hintA').symm
  have e2 : (∫ s, ∫ ζ, Q (s, ζ) * G₁ (s, ζ) * (∫ p : ℝ × ℝ, k p * G₂ ((s, ζ) - p)))
      = ∫ y : ℝ × ℝ, Q y * G₁ y * (∫ p : ℝ × ℝ, k p * G₂ (y - p)) :=
    (iter_eq_plane (fun y : ℝ × ℝ => Q y * G₁ y * (∫ p : ℝ × ℝ, k p * G₂ (y - p))) hintB').symm
  have e3 : (∫ s, ∫ ζ, Q (s, ζ) * G₁ (s, ζ) ^ 2)
      = ∫ y : ℝ × ℝ, Q y * G₁ y ^ 2 :=
    (iter_eq_plane (fun y : ℝ × ℝ => Q y * G₁ y ^ 2) hI1).symm
  have e4 : (∫ s, ∫ ζ, Q (s, ζ) * G₂ (s, ζ) ^ 2)
      = ∫ y : ℝ × ℝ, Q y * G₂ y ^ 2 :=
    (iter_eq_plane (fun y : ℝ × ℝ => Q y * G₂ y ^ 2) hI2).symm
  rw [e1, e2, e3, e4]
  exact conv_transfer_plane hε0 hε1 hCw hkcont hk0 hkmass hksupp hkeven hkmomint hQ0 hQm
    hQsh hQsh' hG1m hG2m hconv1 hconv2 hI1 hI2


end Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Work.locG6_apply_ne_zero =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real

namespace Work.FTS.StrongEps.EpsE4Work


end Work.FTS.StrongEps.EpsE4Work
end
-- ===== merged: Submission.Work.FTS_EllLimOK.Fstar_zero =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK

set_option autoImplicit false

/-- Auxiliary algebra: if `x ≤ (π/2) z⁴ f` with `z > 0`, then `(2/π) x z⁻⁴ ≤ f`. -/
private lemma two_div_pi_mul_le {x f z : ℝ} (hz : 0 < z)
    (h : x ≤ (π / 2) * z ^ 4 * f) :
    (2 / π) * x * z ^ (-4 : ℝ) ≤ f := by
  have hz4ne : z ^ 4 ≠ 0 := ne_of_gt (pow_pos hz 4)
  have hzi : z ^ (-4 : ℝ) = (z ^ 4)⁻¹ := by
    rw [show (-4 : ℝ) = -((4 : ℕ) : ℝ) by norm_num, Real.rpow_neg (le_of_lt hz),
      Real.rpow_natCast]
  rw [hzi]
  have hk : 0 ≤ (z ^ 4)⁻¹ := inv_nonneg.mpr (le_of_lt (pow_pos hz 4))
  have h1 := mul_le_mul_of_nonneg_right h hk
  have h2 : (π / 2) * z ^ 4 * f * (z ^ 4)⁻¹ = (π / 2) * f := by
    rw [show (π / 2) * z ^ 4 * f * (z ^ 4)⁻¹ = (π / 2) * (z ^ 4 * (z ^ 4)⁻¹) * f by ring]
    rw [mul_inv_cancel₀ hz4ne, mul_one]
  rw [h2] at h1
  calc (2 / π) * x * (z ^ 4)⁻¹ = (2 / π) * (x * (z ^ 4)⁻¹) := by ring
    _ ≤ (2 / π) * ((π / 2) * f) := mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = f := by field_simp

theorem Fstar_zero {α : ℝ} (hα : 0 < α) {δ : ℝ → ℝ → ℝ}
    (hbox : Work.FTS_EllLimOK.BoxReg δ)
    (hsol : ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      Work.Elliptic.bslOp α δ z θ = 0)
    (h0 : ∀ z ∈ Set.Ioi (0 : ℝ), δ z 0 = 0)
    (h1 : ∀ z ∈ Set.Ioi (0 : ℝ), δ z (π / 2) = 0)
    (hHk : Work.Spaces.HkMem α 0 δ) :
    ∀ z ∈ Set.Ioi (0 : ℝ), Work.Elliptic.Fstar δ z = 0 := by
  -- the angular moment is `C²` and solves the Euler equation
  obtain ⟨hC2, hode⟩ := Work.FTS_EllLimOK.Fstar_ode_of_bslOp_zero hα hsol hbox h0 h1
  have hg1 : ∀ z ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (Work.Elliptic.Fstar δ) (deriv (Work.Elliptic.Fstar δ) z) z := fun z hz =>
    ((hC2.differentiableOn (by norm_num)).differentiableAt (isOpen_Ioi.mem_nhds hz)).hasDerivAt
  have hdc : ContDiffOn ℝ 1 (deriv (Work.Elliptic.Fstar δ)) (Set.Ioi (0 : ℝ)) :=
    hC2.deriv_of_isOpen isOpen_Ioi (by norm_num)
  have hg2 : ∀ z ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (deriv (Work.Elliptic.Fstar δ))
        (deriv (deriv (Work.Elliptic.Fstar δ)) z) z := fun z hz =>
    ((hdc.differentiableOn (by norm_num)).differentiableAt
      (isOpen_Ioi.mem_nhds hz)).hasDerivAt
  -- hence `F_*δ z = A z^{-5/α} + B`
  obtain ⟨A, B, hform⟩ :=
    Work.FTS_EllLimOK.FstarOde.rigidity_form_of_ode α hα hg1 hg2 hode
  -- the `ℋ⁰`-mass bounds the moment by the weighted angular energy
  have hbnd : ∀ z ∈ Set.Ioi (0 : ℝ), (Work.Elliptic.Fstar δ z) ^ 2
      ≤ (π / 2) * z ^ 4 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 δ z θ) :=
    Work.FTS_EllLimOK.FstarOde.Fstar_sq_HkIntegrand_le hbox hHk
  have hfint : MeasureTheory.IntegrableOn
      (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 δ z θ)
      Work.Spaces.Iz := hHk.2
  -- ... so no point of `(0,∞)` can be a non-zero value of `F_*δ`
  have key : ¬ ∃ z ∈ Set.Ioi (0 : ℝ), Work.Elliptic.Fstar δ z ≠ 0 := by
    rintro ⟨z₀, hz₀, hne₀⟩
    have hAB : A ≠ 0 ∨ B ≠ 0 := by
      by_contra h
      push_neg at h
      exact hne₀ (by rw [hform z₀ hz₀, h.1, h.2]; ring)
    have hmain : ∃ m b : ℝ, 0 < m ∧ 0 < b ∧
        ∀ z ∈ Set.Ioo (0 : ℝ) b, m * z ^ (-4 : ℝ)
          ≤ (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 δ z θ) := by
      by_cases hA : A = 0
      · -- `A = 0`, hence `B ≠ 0`: the moment is the constant `B`
        have hB : B ≠ 0 := by
          rcases hAB with h | h
          · exact absurd (h hA) (not_false)
          · exact h
        have hB2 : 0 < B ^ 2 := by
          have hBpos : 0 < |B| := abs_pos.mpr hB
          rw [← sq_abs B]
          exact pow_pos hBpos 2
        refine ⟨(2 / π) * B ^ 2, 1, ?_, by norm_num, ?_⟩
        · exact mul_pos (by positivity) hB2
        · intro z hz
          have hzp : 0 < z := hz.1
          have hgz : Work.Elliptic.Fstar δ z = B := by
            rw [hform z hz.1, hA]; ring
          have h1' := hbnd z hz.1
          rw [hgz] at h1'
          exact two_div_pi_mul_le hzp h1'
      · -- `A ≠ 0`: the moment blows up like `z^{-5/α}`, hence dominates `1` near `0`
        have hApos : 0 < |A| := abs_pos.mpr hA
        have hCpos : 0 < (2 * |B| + 1) / |A| :=
          div_pos (by positivity) hApos
        refine ⟨2 / π, ((2 * |B| + 1) / |A|) ^ (-(α / 5)), ?_, ?_, ?_⟩
        · positivity
        · exact Real.rpow_pos_of_pos hCpos _
        · intro z hz
          have hzp : 0 < z := hz.1
          have hbC' : (((2 * |B| + 1) / |A|) ^ (-(α / 5))) ^ (-(5 / α))
              = (2 * |B| + 1) / |A| := by
            rw [← Real.rpow_mul (le_of_lt hCpos)]
            have he : (-(α / 5)) * (-(5 / α)) = 1 := by field_simp
            rw [he, Real.rpow_one]
          have hzpow : (2 * |B| + 1) / |A| < z ^ (-(5 / α)) := by
            have h5 : (-(5 / α)) < 0 := by
              have : 0 < 5 / α := by positivity
              linarith
            have hlt := Real.rpow_lt_rpow_of_neg hzp hz.2 h5
            rwa [hbC'] at hlt
          have hAZ : 2 * |B| + 1 < |A| * z ^ (-(5 / α)) := by
            have h1 := mul_lt_mul_of_pos_left hzpow hApos
            have h2 : |A| * ((2 * |B| + 1) / |A|) = 2 * |B| + 1 := by
              rw [mul_comm]
              exact div_mul_cancel₀ (2 * |B| + 1) (ne_of_gt hApos)
            rwa [h2] at h1
          have hgz : 1 ≤ |Work.Elliptic.Fstar δ z| := by
            have hgv : Work.Elliptic.Fstar δ z = A * z ^ (-(5 / α)) + B :=
              hform z hz.1
            rw [hgv]
            have hzpowpos : 0 < z ^ (-(5 / α)) := Real.rpow_pos_of_pos hzp _
            have hkey := abs_sub_abs_le_abs_sub (A * z ^ (-(5 / α))) (-B)
            rw [abs_mul, abs_of_pos hzpowpos, abs_neg] at hkey
            have hsub : A * z ^ (-(5 / α)) - (-B) = A * z ^ (-(5 / α)) + B := by ring
            rw [hsub] at hkey
            linarith [abs_nonneg B]
          have hsq : 1 ≤ (Work.Elliptic.Fstar δ z) ^ 2 := by
            have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hgz 2
            simpa [sq_abs] using h
          have h1' := hbnd z hz.1
          have h1'' : (1 : ℝ) ≤ (π / 2) * z ^ 4
              * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 δ z θ) :=
            le_trans hsq h1'
          simpa using two_div_pi_mul_le hzp h1''
    obtain ⟨m, b, hm, hb, hlow⟩ := hmain
    exact (Work.FTS_EllLimOK.FstarOde.not_integrableOn_of_rpow_lower hm hb
      (by norm_num) hlow)
      (hfint.mono_set fun x hx => le_of_lt hx.1)
  intro z hz
  by_contra hne
  exact key ⟨z, hz, hne⟩

end Work.FTS_EllLimOK
end
end
-- ===== merged: Submission.Work.FTS_LocDatum3a.L12_Jeps_interchange_mine =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_LocDatum3a

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## Scratch: the interchange of `L₁₂dens` with the mollifier `J_ε` (backup development) -/

/-- `K` vanishes at the endpoints of `Iθ`. -/
lemma K_eq_zero_of_not_mem_Ioo_L12J {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ)
    (h : θ ∉ Set.Ioo (0 : ℝ) (π / 2)) : Work.Spaces.K θ = 0 := by
  have hcases : θ = 0 ∨ θ = π / 2 := by
    rcases not_and_or.mp h with h' | h'
    · exact Or.inl (le_antisymm (not_lt.mp h') hθ.1)
    · exact Or.inr (le_antisymm hθ.2 (not_lt.mp h'))
  rcases hcases with rfl | rfl <;> simp [Work.Spaces.K]

/-- `Work.Spaces.K` is continuous. -/
lemma continuous_K_L12J : Continuous Work.Spaces.K := by
  unfold Work.Spaces.K
  fun_prop

/-- `|K|` is integrable on `Iθ`. -/
lemma integrableOn_abs_K_L12J : IntegrableOn (fun θ : ℝ => |Work.Spaces.K θ|) Work.Spaces.Iθ := by
  simpa only [Work.Spaces.Iθ] using
    (continuous_K_L12J.abs.continuousOn.integrableOn_compact isCompact_Icc)

/-- **The interchange at the level of the angular density**, for fixed `s > 0`. -/
lemma L12dens_Jeps_eq {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsMollKernel ρ)
    {ε : ℝ} (hε : 0 < ε) {F : ℝ → ℝ → ℝ} {a C : ℝ} (ha : 0 < a)
    (hFm : Measurable (Function.uncurry F))
    (hF0 : ∀ z θ, 0 < z → z ≤ a → F z θ = 0)
    (hFg : ∀ z θ, 0 < z → |F z θ| ≤ C / (1 + z))
    {s : ℝ} (hs : 0 < s) :
    Work.FM.L12dens Work.Spaces.K (Work.FTS.StrongEps.Jeps ρ ε F) s
      = ∫ p : ℝ × ℝ, Work.FTS.StrongEps.Jker ρ ε p
          * Work.FM.L12dens Work.Spaces.K
              (fun z θ => F (Work.FTS.StrongEps.zShift z p.1)
                (Work.FTS.StrongEps.thShift θ p.2)) s := by
  have hCnn : 0 ≤ C := by
    have h1 : (0 : ℝ) < 1 + a / 2 := by linarith
    have h2 : 0 ≤ C / (1 + a / 2) := by
      have h := hFg (a / 2) 0 (by linarith)
      rw [hF0 (a / 2) 0 (by linarith) (by linarith), abs_zero] at h
      exact h
    have h3 : 0 ≤ C / (1 + a / 2) * (1 + a / 2) := mul_nonneg h2 h1.le
    rwa [div_mul_cancel₀ _ (ne_of_gt h1)] at h3
  -- the pointwise identity on `Iθ`
  have hpt : ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.K θ * (Work.FTS.StrongEps.Jeps ρ ε F) s θ / s
        = ∫ p : ℝ × ℝ, Work.Spaces.K θ * (Work.FTS.StrongEps.Jker ρ ε p
            * F (Work.FTS.StrongEps.zShift s p.1)
              (Work.FTS.StrongEps.thShift θ p.2)) / s := by
    intro θ hθ
    by_cases hθo : θ ∈ Set.Ioo (0 : ℝ) (π / 2)
    · rw [Work.FTS.StrongEps.Jeps_eq_integral ρ ε F hs hθo]
      rw [show (∫ p : ℝ × ℝ, Work.Spaces.K θ * (Work.FTS.StrongEps.Jker ρ ε p
              * F (Work.FTS.StrongEps.zShift s p.1)
                (Work.FTS.StrongEps.thShift θ p.2)) / s)
          = ∫ p : ℝ × ℝ, (Work.Spaces.K θ / s) * (Work.FTS.StrongEps.Jker ρ ε p
              * F (Work.FTS.StrongEps.zShift s p.1)
                (Work.FTS.StrongEps.thShift θ p.2)) from
        integral_congr_ae (Filter.Eventually.of_forall (fun p => by ring))]
      rw [MeasureTheory.integral_const_mul]
      ring
    · have hK0 := K_eq_zero_of_not_mem_Ioo_L12J hθ hθo
      rw [hK0]
      simp
  have hL : Work.FM.L12dens Work.Spaces.K (Work.FTS.StrongEps.Jeps ρ ε F) s
      = ∫ θ in Work.Spaces.Iθ, ∫ p : ℝ × ℝ, Work.Spaces.K θ
          * (Work.FTS.StrongEps.Jker ρ ε p * F (Work.FTS.StrongEps.zShift s p.1)
              (Work.FTS.StrongEps.thShift θ p.2)) / s := by
    rw [show Work.FM.L12dens Work.Spaces.K (Work.FTS.StrongEps.Jeps ρ ε F) s
        = ∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ
            * (Work.FTS.StrongEps.Jeps ρ ε F) s θ / s from rfl]
    exact setIntegral_congr_fun measurableSet_Icc hpt
  -- integrability of the `(θ,p)`-integrand
  have hInt : Integrable (fun z : ℝ × (ℝ × ℝ) => Work.Spaces.K z.1
      * (Work.FTS.StrongEps.Jker ρ ε z.2 * F (Work.FTS.StrongEps.zShift s z.2.1)
          (Work.FTS.StrongEps.thShift z.1 z.2.2)) / s)
      ((volume.restrict Work.Spaces.Iθ).prod volume) := by
    refine Integrable.mono'
      ((integrableOn_abs_K_L12J.mul_prod (Work.FTS.StrongEps.Jker_integrable hρ hε).abs).mul_const
        (C * Real.exp ε / s ^ 2)) ?_ ?_
    · -- measurability
      refine Measurable.aestronglyMeasurable ?_
      have hK' : Measurable fun z : ℝ × (ℝ × ℝ) => Work.Spaces.K z.1 :=
        continuous_K_L12J.measurable.comp measurable_fst
      have hJ' : Measurable fun z : ℝ × (ℝ × ℝ) => Work.FTS.StrongEps.Jker ρ ε z.2 :=
        (Work.FTS.StrongEps.Jker_continuous hρ ε).measurable.comp measurable_snd
      have hF' : Measurable fun z : ℝ × (ℝ × ℝ) => F (Work.FTS.StrongEps.zShift s z.2.1)
          (Work.FTS.StrongEps.thShift z.1 z.2.2) := by
        have hzc : Measurable fun z : ℝ × (ℝ × ℝ) => Work.FTS.StrongEps.zShift s z.2.1 := by
          unfold Work.FTS.StrongEps.zShift; measurability
        have htc : Measurable fun z : ℝ × (ℝ × ℝ) => Work.FTS.StrongEps.thShift z.1 z.2.2 := by
          unfold Work.FTS.StrongEps.thShift
          have hzz : Measurable fun z : ℝ × (ℝ × ℝ) => z.2.2 :=
            measurable_snd.comp measurable_snd
          have htan : Measurable fun z : ℝ × (ℝ × ℝ) => Real.tan z.1 := by
            rw [show (fun z : ℝ × (ℝ × ℝ) => Real.tan z.1)
                = fun z => Real.sin z.1 / Real.cos z.1 from
              funext fun z => Real.tan_eq_sin_div_cos z.1]
            exact (Real.measurable_sin.div Real.measurable_cos).comp measurable_fst
          exact Real.measurable_arctan.comp (htan.mul (Real.measurable_exp.comp hzz.neg))
        exact hFm.comp (hzc.prodMk htc)
      exact (hK'.mul (hJ'.mul hF')).div_const s
    · -- the pointwise domination
      filter_upwards with z
      rw [Real.norm_eq_abs]
      rcases eq_or_ne (Work.FTS.StrongEps.Jker ρ ε z.2) 0 with hj | hj
      · rw [hj]; simp
      · have hp : z.2 ∈ Metric.closedBall (0 : ℝ × ℝ) ε := by
          by_contra hp
          exact hj (Work.FTS.StrongEps.Jker_eq_zero_of_not_mem hρ hε hp)
        have hpabs : |z.2.1| ≤ ε := by
          have h := Metric.mem_closedBall.mp hp
          rw [dist_zero_right, Prod.norm_def, max_le_iff] at h
          exact h.1
        have hp1 : -ε ≤ z.2.1 := (abs_le.mp hpabs).1
        have hp2 : z.2.1 ≤ ε := (abs_le.mp hpabs).2
        have hzpos : 0 < Work.FTS.StrongEps.zShift s z.2.1 :=
          Work.FTS.StrongEps.zShift_pos hs
        have hb : |F (Work.FTS.StrongEps.zShift s z.2.1) (Work.FTS.StrongEps.thShift z.1 z.2.2)|
            ≤ C * Real.exp ε / s := by
          by_cases hza : Work.FTS.StrongEps.zShift s z.2.1 ≤ a
          · rw [hF0 _ _ hzpos hza, abs_zero]
            positivity
          · rw [not_le] at hza
            have h1 : |F (Work.FTS.StrongEps.zShift s z.2.1)
                (Work.FTS.StrongEps.thShift z.1 z.2.2)| ≤ C / (1 + s * Real.exp (-z.2.1)) := by
              simpa only [Work.FTS.StrongEps.zShift] using hFg _ _ hzpos
            have h2 : C / (1 + s * Real.exp (-z.2.1)) ≤ C * Real.exp ε / s := by
              have h3 : C / (1 + s * Real.exp (-z.2.1)) ≤ C / (s * Real.exp (-z.2.1)) :=
                div_le_div_of_nonneg_left hCnn (by positivity) (by linarith [Real.exp_pos (-z.2.1)])
              have h4 : C / (s * Real.exp (-z.2.1)) = C * Real.exp z.2.1 / s := by
                rw [Real.exp_neg]
                field_simp
              have h5 : C * Real.exp z.2.1 / s ≤ C * Real.exp ε / s := by
                have := Real.exp_le_exp.mpr hp2
                gcongr
              linarith [h3, h4.le, h4.ge]
            exact h1.trans h2
        calc |Work.Spaces.K z.1 * (Work.FTS.StrongEps.Jker ρ ε z.2
                * F (Work.FTS.StrongEps.zShift s z.2.1) (Work.FTS.StrongEps.thShift z.1 z.2.2)) / s|
            = |Work.Spaces.K z.1| * |Work.FTS.StrongEps.Jker ρ ε z.2|
                * |F (Work.FTS.StrongEps.zShift s z.2.1)
                    (Work.FTS.StrongEps.thShift z.1 z.2.2)| / s := by
              rw [abs_div, abs_mul, abs_mul, abs_of_pos hs]
              ring
          _ ≤ |Work.Spaces.K z.1| * |Work.FTS.StrongEps.Jker ρ ε z.2|
                * (C * Real.exp ε / s) / s := by
              gcongr
          _ = |Work.Spaces.K z.1| * |Work.FTS.StrongEps.Jker ρ ε z.2|
                * (C * Real.exp ε / s ^ 2) := by ring
  rw [hL, MeasureTheory.integral_integral_swap hInt]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
  show (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * (Work.FTS.StrongEps.Jker ρ ε p
        * F (Work.FTS.StrongEps.zShift s p.1) (Work.FTS.StrongEps.thShift θ p.2)) / s)
      = Work.FTS.StrongEps.Jker ρ ε p * (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ
          * F (Work.FTS.StrongEps.zShift s p.1) (Work.FTS.StrongEps.thShift θ p.2) / s)
  rw [show (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * (Work.FTS.StrongEps.Jker ρ ε p
          * F (Work.FTS.StrongEps.zShift s p.1) (Work.FTS.StrongEps.thShift θ p.2)) / s)
      = ∫ θ in Work.Spaces.Iθ, Work.FTS.StrongEps.Jker ρ ε p
          * (Work.Spaces.K θ * F (Work.FTS.StrongEps.zShift s p.1)
              (Work.FTS.StrongEps.thShift θ p.2) / s) from
    setIntegral_congr_fun measurableSet_Icc (fun θ _ => by ring)]
  rw [MeasureTheory.integral_const_mul]


/-- `(s²)⁻¹ = s^{-2}` for `s ≥ 0`. -/
lemma inv_sq_eq_rpow_L12J (s : ℝ) (hs : 0 ≤ s) : (s ^ 2)⁻¹ = s ^ (-2 : ℝ) := by
  rw [show (-2 : ℝ) = -(2 : ℝ) by norm_num, Real.rpow_neg hs, Real.rpow_two]

/-- **The mollifier `J_ε` commutes with `L₁₂` in the zero mode.** -/
theorem L12_Jeps_interchange_mine {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsMollKernel ρ)
    {ε : ℝ} (hε : 0 < ε) {F : ℝ → ℝ → ℝ} {a C : ℝ} (ha : 0 < a)
    (hFm : Measurable (Function.uncurry F))
    (hF0 : ∀ z θ, 0 < z → z ≤ a → F z θ = 0)
    (hFg : ∀ z θ, 0 < z → |F z θ| ≤ C / (1 + z)) :
    Work.FM.L12 Work.Spaces.K (Work.FTS.StrongEps.Jeps ρ ε F) 0
      = ∫ p : ℝ × ℝ, Work.FTS.StrongEps.Jker ρ ε p
          * (Work.FM.L12 Work.Spaces.K
              (fun z θ => F (Work.FTS.StrongEps.zShift z p.1)
                (Work.FTS.StrongEps.thShift θ p.2)) 0) := by
  have hCnn : 0 ≤ C := by
    have h1 : (0 : ℝ) < 1 + a / 2 := by linarith
    have h2 : 0 ≤ C / (1 + a / 2) := by
      have h := hFg (a / 2) 0 (by linarith)
      rw [hF0 (a / 2) 0 (by linarith) (by linarith), abs_zero] at h
      exact h
    have h3 : 0 ≤ C / (1 + a / 2) * (1 + a / 2) := mul_nonneg h2 h1.le
    rwa [div_mul_cancel₀ _ (ne_of_gt h1)] at h3
  set Kb : ℝ := ∫ θ in Work.Spaces.Iθ, |Work.Spaces.K θ| with hKb
  have hKbnn : 0 ≤ Kb := by rw [hKb]; exact integral_nonneg (fun θ => abs_nonneg _)
  set gpart : ℝ → ℝ := fun s => (C * Real.exp ε) * Kb
      * ((Set.Ici (a * Real.exp (-ε))).indicator (fun s => s ^ (-2 : ℝ)) s) with hgpart
  set ppart : ℝ × ℝ → ℝ := fun p => |Work.FTS.StrongEps.Jker ρ ε p| with hppart
  -- ### Step A: `L₁₂(J_ε F)(0)` as an iterated `s`–`p` integral
  have hA : Work.FM.L12 Work.Spaces.K (Work.FTS.StrongEps.Jeps ρ ε F) 0
      = ∫ s in Set.Ioi 0, ∫ p : ℝ × ℝ, Work.FTS.StrongEps.Jker ρ ε p
          * Work.FM.L12dens Work.Spaces.K
              (fun z θ => F (Work.FTS.StrongEps.zShift z p.1)
                (Work.FTS.StrongEps.thShift θ p.2)) s := by
    rw [show Work.FM.L12 Work.Spaces.K (Work.FTS.StrongEps.Jeps ρ ε F) 0
        = ∫ s in Set.Ioi 0, Work.FM.L12dens Work.Spaces.K
            (Work.FTS.StrongEps.Jeps ρ ε F) s from rfl]
    exact setIntegral_congr_fun measurableSet_Ioi
      (fun s hs => L12dens_Jeps_eq hρ hε ha hFm hF0 hFg hs)
  -- ### the integrability of the `s`–`p` integrand
  have hInt : Integrable (fun z : ℝ × (ℝ × ℝ) => if 0 < z.1 then
        Work.FTS.StrongEps.Jker ρ ε z.2 * Work.FM.L12dens Work.Spaces.K
          (fun z' θ => F (Work.FTS.StrongEps.zShift z' z.2.1)
            (Work.FTS.StrongEps.thShift θ z.2.2)) z.1 else 0)
      ((volume.restrict (Set.Ioi 0)).prod volume) := by
    have hs_int : Integrable gpart (volume.restrict (Set.Ioi 0)) := by
      rw [hgpart]
      have hIoi : IntegrableOn (fun s : ℝ => s ^ (-2 : ℝ))
          (Set.Ioi (a * Real.exp (-ε) / 2)) :=
        integrableOn_Ioi_rpow_of_lt (by norm_num) (by positivity)
      have hIci : IntegrableOn (fun s : ℝ => s ^ (-2 : ℝ))
          (Set.Ici (a * Real.exp (-ε))) := by
        refine hIoi.mono_set (fun s hs => ?_)
        simp only [Set.mem_Ici] at hs
        simp only [Set.mem_Ioi]
        have hpos : 0 < a * Real.exp (-ε) := by positivity
        linarith
      exact (((integrable_indicator_iff measurableSet_Ici).mpr hIci).integrableOn).const_mul _
    have hp_int : Integrable ppart volume := by
      rw [hppart]
      exact (Work.FTS.StrongEps.Jker_integrable hρ hε).abs
    have hdom : Integrable (fun z : ℝ × (ℝ × ℝ) => gpart z.1 * ppart z.2)
        ((volume.restrict (Set.Ioi 0)).prod volume) := hs_int.mul_prod hp_int
    have hdom_nn : ∀ z : ℝ × (ℝ × ℝ), 0 ≤ gpart z.1 * ppart z.2 := by
      intro z
      rw [hgpart, hppart]
      have h1 : 0 ≤ (Set.Ici (a * Real.exp (-ε))).indicator
          (fun s : ℝ => s ^ (-2 : ℝ)) z.1 := by
        by_cases h : z.1 ∈ Set.Ici (a * Real.exp (-ε))
        · rw [Set.indicator_of_mem h]
          have hpos : 0 < a * Real.exp (-ε) := by positivity
          have hge : a * Real.exp (-ε) ≤ z.1 := by simpa [Set.mem_Ici] using h
          exact Real.rpow_nonneg (by linarith) _
        · rw [Set.indicator_of_notMem h]
      exact mul_nonneg (mul_nonneg (mul_nonneg (by positivity) hKbnn) h1) (abs_nonneg _)
    refine Integrable.mono' hdom ?_ ?_
    · -- measurability
      have hL12meas : StronglyMeasurable (fun z : ℝ × (ℝ × ℝ) => ∫ θ : ℝ, Work.Spaces.K θ
          * F (Work.FTS.StrongEps.zShift z.1 z.2.1) (Work.FTS.StrongEps.thShift θ z.2.2) / z.1
          ∂(volume.restrict Work.Spaces.Iθ)) := by
        refine StronglyMeasurable.integral_prod_right (ν := volume.restrict Work.Spaces.Iθ) ?_
        have hW : Measurable (fun w : (ℝ × (ℝ × ℝ)) × ℝ => Work.Spaces.K w.2
            * F (Work.FTS.StrongEps.zShift w.1.1 w.1.2.1)
              (Work.FTS.StrongEps.thShift w.2 w.1.2.2) / w.1.1) := by
          have hK : Measurable fun w : (ℝ × (ℝ × ℝ)) × ℝ => Work.Spaces.K w.2 :=
            continuous_K_L12J.measurable.comp measurable_snd
          have hzc : Measurable fun w : (ℝ × (ℝ × ℝ)) × ℝ =>
              Work.FTS.StrongEps.zShift w.1.1 w.1.2.1 := by
            unfold Work.FTS.StrongEps.zShift; measurability
          have htc : Measurable fun w : (ℝ × (ℝ × ℝ)) × ℝ =>
              Work.FTS.StrongEps.thShift w.2 w.1.2.2 := by
            unfold Work.FTS.StrongEps.thShift
            have hzz : Measurable fun w : (ℝ × (ℝ × ℝ)) × ℝ => w.1.2.2 :=
              (measurable_snd.comp measurable_snd).comp measurable_fst
            have htan : Measurable fun w : (ℝ × (ℝ × ℝ)) × ℝ => Real.tan w.2 := by
              rw [show (fun w : (ℝ × (ℝ × ℝ)) × ℝ => Real.tan w.2)
                  = fun w => Real.sin w.2 / Real.cos w.2 from
                funext fun w => Real.tan_eq_sin_div_cos w.2]
              exact (Real.measurable_sin.div Real.measurable_cos).comp measurable_snd
            exact Real.measurable_arctan.comp (htan.mul (Real.measurable_exp.comp hzz.neg))
          have harg : Measurable fun w : (ℝ × (ℝ × ℝ)) × ℝ =>
              ((Work.FTS.StrongEps.zShift w.1.1 w.1.2.1,
                Work.FTS.StrongEps.thShift w.2 w.1.2.2) : ℝ × ℝ) := hzc.prodMk htc
          exact ((hK.mul (hFm.comp harg)).div measurable_fst.fst)
        exact hW.stronglyMeasurable
      refine Measurable.aestronglyMeasurable ?_
      show Measurable (fun z : ℝ × (ℝ × ℝ) => if 0 < z.1 then Work.FTS.StrongEps.Jker ρ ε z.2
          * (∫ θ : ℝ, Work.Spaces.K θ * F (Work.FTS.StrongEps.zShift z.1 z.2.1)
              (Work.FTS.StrongEps.thShift θ z.2.2) / z.1
              ∂(volume.restrict Work.Spaces.Iθ)) else 0)
      have hA : Measurable (fun z : ℝ × (ℝ × ℝ) => Work.FTS.StrongEps.Jker ρ ε z.2
          * (∫ θ : ℝ, Work.Spaces.K θ * F (Work.FTS.StrongEps.zShift z.1 z.2.1)
              (Work.FTS.StrongEps.thShift θ z.2.2) / z.1
              ∂(volume.restrict Work.Spaces.Iθ))) :=
        ((Work.FTS.StrongEps.Jker_continuous hρ ε).measurable.comp measurable_snd).mul
          hL12meas.measurable
      exact hA.indicator (measurableSet_lt measurable_const measurable_fst)
    · -- the pointwise bound
      filter_upwards with z
      by_cases hz1 : 0 < z.1
      · rw [if_pos hz1, Real.norm_eq_abs]
        by_cases hj : Work.FTS.StrongEps.Jker ρ ε z.2 = 0
        · rw [hj, zero_mul, abs_zero]
          exact hdom_nn z
        · have hp : z.2 ∈ Metric.closedBall (0 : ℝ × ℝ) ε := by
            by_contra hp
            exact hj (Work.FTS.StrongEps.Jker_eq_zero_of_not_mem hρ hε hp)
          have hpabs : |z.2.1| ≤ ε := by
            have h := Metric.mem_closedBall.mp hp
            rw [dist_zero_right, Prod.norm_def, max_le_iff] at h
            exact h.1
          have hp1 : -ε ≤ z.2.1 := (abs_le.mp hpabs).1
          have hp2 : z.2.1 ≤ ε := (abs_le.mp hpabs).2
          have hFb : ∀ θ : ℝ, |F (Work.FTS.StrongEps.zShift z.1 z.2.1)
              (Work.FTS.StrongEps.thShift θ z.2.2)| ≤ C * Real.exp ε / z.1 := by
            intro θ
            by_cases hza : Work.FTS.StrongEps.zShift z.1 z.2.1 ≤ a
            · rw [hF0 _ _ (Work.FTS.StrongEps.zShift_pos hz1) hza, abs_zero]
              positivity
            · rw [not_le] at hza
              have h1 : |F (Work.FTS.StrongEps.zShift z.1 z.2.1)
                  (Work.FTS.StrongEps.thShift θ z.2.2)|
                  ≤ C / (1 + z.1 * Real.exp (-z.2.1)) := by
                simpa only [Work.FTS.StrongEps.zShift] using
                  hFg _ _ (Work.FTS.StrongEps.zShift_pos hz1)
              have h2 : C / (1 + z.1 * Real.exp (-z.2.1)) ≤ C * Real.exp ε / z.1 := by
                have h3 : C / (1 + z.1 * Real.exp (-z.2.1))
                    ≤ C / (z.1 * Real.exp (-z.2.1)) :=
                  div_le_div_of_nonneg_left hCnn (by positivity)
                    (by linarith [Real.exp_pos (-z.2.1)])
                have h4 : C / (z.1 * Real.exp (-z.2.1)) = C * Real.exp z.2.1 / z.1 := by
                  rw [Real.exp_neg]; field_simp
                have h5 : C * Real.exp z.2.1 / z.1 ≤ C * Real.exp ε / z.1 := by
                  have := Real.exp_le_exp.mpr hp2
                  gcongr
                linarith [h3, h4.le, h4.ge]
              exact h1.trans h2
          have hLb : |Work.FM.L12dens Work.Spaces.K
              (fun z' θ => F (Work.FTS.StrongEps.zShift z' z.2.1)
                (Work.FTS.StrongEps.thShift θ z.2.2)) z.1|
              ≤ (C * Real.exp ε) * Kb * z.1 ^ (-2 : ℝ) := by
            rw [show Work.FM.L12dens Work.Spaces.K
                (fun z' θ => F (Work.FTS.StrongEps.zShift z' z.2.1)
                  (Work.FTS.StrongEps.thShift θ z.2.2)) z.1
                = ∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ
                    * F (Work.FTS.StrongEps.zShift z.1 z.2.1)
                      (Work.FTS.StrongEps.thShift θ z.2.2) / z.1 from rfl]
            have hbound : ∀ θ : ℝ, ‖Work.Spaces.K θ
                * F (Work.FTS.StrongEps.zShift z.1 z.2.1)
                  (Work.FTS.StrongEps.thShift θ z.2.2) / z.1‖
                ≤ ((C * Real.exp ε) * (z.1 ^ 2)⁻¹) * |Work.Spaces.K θ| := by
              intro θ
              rw [Real.norm_eq_abs, abs_div, abs_mul, abs_of_pos hz1]
              calc |Work.Spaces.K θ| * |F (Work.FTS.StrongEps.zShift z.1 z.2.1)
                    (Work.FTS.StrongEps.thShift θ z.2.2)| / z.1
                  ≤ |Work.Spaces.K θ| * (C * Real.exp ε / z.1) / z.1 := by
                    gcongr
                    exact hFb θ
                _ = ((C * Real.exp ε) * (z.1 ^ 2)⁻¹) * |Work.Spaces.K θ| := by
                    field_simp
            calc ‖∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ
                    * F (Work.FTS.StrongEps.zShift z.1 z.2.1)
                      (Work.FTS.StrongEps.thShift θ z.2.2) / z.1‖
                ≤ ∫ θ in Work.Spaces.Iθ, ‖Work.Spaces.K θ
                    * F (Work.FTS.StrongEps.zShift z.1 z.2.1)
                      (Work.FTS.StrongEps.thShift θ z.2.2) / z.1‖ :=
                  MeasureTheory.norm_integral_le_integral_norm _
              _ ≤ ∫ θ in Work.Spaces.Iθ, ((C * Real.exp ε) * (z.1 ^ 2)⁻¹)
                    * |Work.Spaces.K θ| := by
                  refine MeasureTheory.integral_mono_of_nonneg
                    (ae_of_all _ (fun θ => norm_nonneg _)) ?_ ?_
                  · exact integrableOn_abs_K_L12J.const_mul ((C * Real.exp ε) * (z.1 ^ 2)⁻¹)
                  · exact ae_of_all _ (fun θ => hbound θ)
              _ = (C * Real.exp ε) * Kb * (z.1 ^ 2)⁻¹ := by
                  rw [MeasureTheory.integral_const_mul, ← hKb]
                  ring
              _ = (C * Real.exp ε) * Kb * z.1 ^ (-2 : ℝ) := by
                  rw [show (z.1 ^ 2)⁻¹ = z.1 ^ (-2 : ℝ) from inv_sq_eq_rpow_L12J z.1 hz1.le]
          by_cases hs' : z.1 < a * Real.exp (-ε)
          · -- here the angular density vanishes
            have hzero : Work.FM.L12dens Work.Spaces.K
                (fun z' θ => F (Work.FTS.StrongEps.zShift z' z.2.1)
                  (Work.FTS.StrongEps.thShift θ z.2.2)) z.1 = 0 := by
              rw [show Work.FM.L12dens Work.Spaces.K
                  (fun z' θ => F (Work.FTS.StrongEps.zShift z' z.2.1)
                    (Work.FTS.StrongEps.thShift θ z.2.2)) z.1
                  = ∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ
                      * F (Work.FTS.StrongEps.zShift z.1 z.2.1)
                        (Work.FTS.StrongEps.thShift θ z.2.2) / z.1 from rfl]
              rw [show (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ
                      * F (Work.FTS.StrongEps.zShift z.1 z.2.1)
                        (Work.FTS.StrongEps.thShift θ z.2.2) / z.1)
                  = ∫ θ in Work.Spaces.Iθ, (0 : ℝ) from
                setIntegral_congr_fun measurableSet_Icc (fun θ _ => by
                  have hzf : Work.FTS.StrongEps.zShift z.1 z.2.1 ≤ a := by
                    have he : Real.exp (-z.2.1) ≤ Real.exp ε :=
                      Real.exp_le_exp.mpr (by linarith [hp1])
                    calc Work.FTS.StrongEps.zShift z.1 z.2.1
                        = z.1 * Real.exp (-z.2.1) := rfl
                      _ ≤ z.1 * Real.exp ε := mul_le_mul_of_nonneg_left he hz1.le
                      _ ≤ (a * Real.exp (-ε)) * Real.exp ε :=
                          mul_le_mul_of_nonneg_right hs'.le (Real.exp_pos _).le
                      _ = a := by
                          rw [mul_assoc, ← Real.exp_add, show -ε + ε = 0 by ring,
                            Real.exp_zero, mul_one]
                  rw [hF0 _ _ (Work.FTS.StrongEps.zShift_pos hz1) hzf]
                  ring)]
              simp
            have hind : (Set.Ici (a * Real.exp (-ε))).indicator
                (fun s : ℝ => s ^ (-2 : ℝ)) z.1 = 0 :=
              Set.indicator_of_notMem (by simpa [Set.mem_Ici] using not_le.mpr hs') _
            change ‖Work.FTS.StrongEps.Jker ρ ε z.2
                * Work.FM.L12dens Work.Spaces.K
                    (fun z' θ => F (Work.FTS.StrongEps.zShift z' z.2.1)
                      (Work.FTS.StrongEps.thShift θ z.2.2)) z.1‖
                ≤ ((C * Real.exp ε) * Kb * ((Set.Ici (a * Real.exp (-ε))).indicator
                    (fun s : ℝ => s ^ (-2 : ℝ)) z.1))
                  * |Work.FTS.StrongEps.Jker ρ ε z.2|
            rw [hzero, mul_zero, norm_zero, hind]
            simp
          · -- the general bound
            have hind : (Set.Ici (a * Real.exp (-ε))).indicator
                (fun s : ℝ => s ^ (-2 : ℝ)) z.1 = z.1 ^ (-2 : ℝ) :=
              Set.indicator_of_mem (by simpa [Set.mem_Ici] using not_lt.mp hs') _
            change ‖Work.FTS.StrongEps.Jker ρ ε z.2
                * Work.FM.L12dens Work.Spaces.K
                    (fun z' θ => F (Work.FTS.StrongEps.zShift z' z.2.1)
                      (Work.FTS.StrongEps.thShift θ z.2.2)) z.1‖
                ≤ ((C * Real.exp ε) * Kb * ((Set.Ici (a * Real.exp (-ε))).indicator
                    (fun s : ℝ => s ^ (-2 : ℝ)) z.1))
                  * |Work.FTS.StrongEps.Jker ρ ε z.2|
            rw [hind, Real.norm_eq_abs, abs_mul]
            calc |Work.FTS.StrongEps.Jker ρ ε z.2|
                  * |Work.FM.L12dens Work.Spaces.K
                      (fun z' θ => F (Work.FTS.StrongEps.zShift z' z.2.1)
                        (Work.FTS.StrongEps.thShift θ z.2.2)) z.1|
                ≤ |Work.FTS.StrongEps.Jker ρ ε z.2|
                    * ((C * Real.exp ε) * Kb * z.1 ^ (-2 : ℝ)) :=
                  mul_le_mul_of_nonneg_left hLb (abs_nonneg _)
              _ = ((C * Real.exp ε) * Kb * z.1 ^ (-2 : ℝ))
                    * |Work.FTS.StrongEps.Jker ρ ε z.2| := by ring
      · rw [if_neg hz1]
        simpa using hdom_nn z
  -- ### the `s`–`p` exchange and the final computation
  rw [hA]
  rw [show (∫ s in Set.Ioi 0, ∫ p : ℝ × ℝ, Work.FTS.StrongEps.Jker ρ ε p
        * Work.FM.L12dens Work.Spaces.K
            (fun z θ => F (Work.FTS.StrongEps.zShift z p.1)
              (Work.FTS.StrongEps.thShift θ p.2)) s)
      = ∫ p : ℝ × ℝ, ∫ s in Set.Ioi 0, Work.FTS.StrongEps.Jker ρ ε p
          * Work.FM.L12dens Work.Spaces.K
              (fun z θ => F (Work.FTS.StrongEps.zShift z p.1)
                (Work.FTS.StrongEps.thShift θ p.2)) s from ?_]
  · refine integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
    show (∫ s in Set.Ioi 0, Work.FTS.StrongEps.Jker ρ ε p
        * Work.FM.L12dens Work.Spaces.K
            (fun z θ => F (Work.FTS.StrongEps.zShift z p.1)
              (Work.FTS.StrongEps.thShift θ p.2)) s)
      = Work.FTS.StrongEps.Jker ρ ε p
        * (∫ s in Set.Ioi 0, Work.FM.L12dens Work.Spaces.K
            (fun z θ => F (Work.FTS.StrongEps.zShift z p.1)
              (Work.FTS.StrongEps.thShift θ p.2)) s)
    rw [MeasureTheory.integral_const_mul]
  · have h1 : (∫ s in Set.Ioi 0, ∫ p : ℝ × ℝ, Work.FTS.StrongEps.Jker ρ ε p
          * Work.FM.L12dens Work.Spaces.K
              (fun z θ => F (Work.FTS.StrongEps.zShift z p.1)
                (Work.FTS.StrongEps.thShift θ p.2)) s)
        = ∫ s in Set.Ioi 0, ∫ p : ℝ × ℝ, (if 0 < s then Work.FTS.StrongEps.Jker ρ ε p
            * Work.FM.L12dens Work.Spaces.K
                (fun z θ => F (Work.FTS.StrongEps.zShift z p.1)
                  (Work.FTS.StrongEps.thShift θ p.2)) s else 0) := by
      refine setIntegral_congr_fun measurableSet_Ioi (fun s hs => ?_)
      refine integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
      show Work.FTS.StrongEps.Jker ρ ε p * Work.FM.L12dens Work.Spaces.K
            (fun z θ => F (Work.FTS.StrongEps.zShift z p.1)
              (Work.FTS.StrongEps.thShift θ p.2)) s
          = (if 0 < s then Work.FTS.StrongEps.Jker ρ ε p
              * Work.FM.L12dens Work.Spaces.K
                  (fun z θ => F (Work.FTS.StrongEps.zShift z p.1)
                    (Work.FTS.StrongEps.thShift θ p.2)) s else 0)
      split_ifs with h
      · rfl
      · exact absurd hs h
    have h2 : (∫ s in Set.Ioi 0, ∫ p : ℝ × ℝ, (if 0 < s then Work.FTS.StrongEps.Jker ρ ε p
          * Work.FM.L12dens Work.Spaces.K
              (fun z θ => F (Work.FTS.StrongEps.zShift z p.1)
                (Work.FTS.StrongEps.thShift θ p.2)) s else 0))
        = ∫ p : ℝ × ℝ, ∫ s in Set.Ioi 0, (if 0 < s then Work.FTS.StrongEps.Jker ρ ε p
            * Work.FM.L12dens Work.Spaces.K
                (fun z θ => F (Work.FTS.StrongEps.zShift z p.1)
                  (Work.FTS.StrongEps.thShift θ p.2)) s else 0) :=
      MeasureTheory.integral_integral_swap hInt
    have h3 : (∫ p : ℝ × ℝ, ∫ s in Set.Ioi 0, (if 0 < s then Work.FTS.StrongEps.Jker ρ ε p
          * Work.FM.L12dens Work.Spaces.K
              (fun z θ => F (Work.FTS.StrongEps.zShift z p.1)
                (Work.FTS.StrongEps.thShift θ p.2)) s else 0))
        = ∫ p : ℝ × ℝ, ∫ s in Set.Ioi 0, Work.FTS.StrongEps.Jker ρ ε p
            * Work.FM.L12dens Work.Spaces.K
                (fun z θ => F (Work.FTS.StrongEps.zShift z p.1)
                  (Work.FTS.StrongEps.thShift θ p.2)) s := by
      refine integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
      refine setIntegral_congr_fun measurableSet_Ioi (fun s hs => ?_)
      show (if 0 < s then Work.FTS.StrongEps.Jker ρ ε p
            * Work.FM.L12dens Work.Spaces.K
                (fun z θ => F (Work.FTS.StrongEps.zShift z p.1)
                  (Work.FTS.StrongEps.thShift θ p.2)) s else 0)
          = Work.FTS.StrongEps.Jker ρ ε p * Work.FM.L12dens Work.Spaces.K
              (fun z θ => F (Work.FTS.StrongEps.zShift z p.1)
                (Work.FTS.StrongEps.thShift θ p.2)) s
      split_ifs with h
      · rfl
      · exact absurd hs h
    exact h1.trans (h2.trans h3)

end Work.FTS_LocDatum3a
end
end
