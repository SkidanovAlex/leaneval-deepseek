import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Topology.UniformSpace.Uniformizable
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Defs
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Pieces2.conv_joint_integrable
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Pieces2.conv_pair_integrable
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Pieces2.kernel_exp_moment_le
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Pieces2.weight_diff_integral_le

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
