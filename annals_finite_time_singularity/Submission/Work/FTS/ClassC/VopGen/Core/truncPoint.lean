import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.ClassC.VopGen.Core.truncSetup

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS.ClassC.VopGen.Core.truncPoint` — the pointwise majorant of the truncation half

The pointwise AM–GM bound of the integrand produced by the radial integration by parts of
`Work.FTS.ClassC.VopGen.Core.truncPerN` by the majorant
`(C₀+2)·w²σ·((D_zX)² + X² + Y²)`, together with the three integrability statements derived
from it.
-/

namespace Work.FTS.ClassC.VopGen.Core

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 3200000

open Work.Spaces (HkSq HkMem HkIntegrand HkIntegrand_nonneg w Iz Iθ Dz DzIter pth pz)

local notation "Aof" => Work.FTS.EllipticEst.H2W.Aof

/-- Integrability of the majorant integrand. -/
theorem majIntegrable {α : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4) {F Ψ : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ) {C₀ : ℝ} :
    MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => (C₀ + 2) *
      ((Dz (XX Ψ) p.1 p.2) ^ 2 * (w p.1) ^ 2 * sgm α p.2
        + ((XX Ψ p.1 p.2) ^ 2 * (w p.1) ^ 2 * sgm α p.2
          + (YY Ψ p.1 p.2) ^ 2 * (w p.1) ^ 2 * sgm α p.2))) (Iz ×ˢ Iθ) := by
  have hα1 : α ≤ 1 := by linarith
  obtain ⟨_, _, prDX, _⟩ := slotFacts_pure hα1 hα hα4 h 2 (by norm_num)
  obtain ⟨_, _, prX, _⟩ := slotFacts_pure hα1 hα hα4 h 1 (by norm_num)
  obtain ⟨_, _, prY, _⟩ := slotFacts_ang hα1 hα hα4 h
  have prDX' : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ
      => (Dz (XX Ψ) p.1 p.2) ^ 2 * (w p.1) ^ 2 * sgm α p.2) (Iz ×ˢ Iθ) := by
    simpa only [XX, Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero] using prDX
  have prX' : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ
      => (XX Ψ p.1 p.2) ^ 2 * (w p.1) ^ 2 * sgm α p.2) (Iz ×ˢ Iθ) := by
    simpa only [XX, Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero] using prX
  have prY' : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ
      => (YY Ψ p.1 p.2) ^ 2 * (w p.1) ^ 2 * sgm α p.2) (Iz ×ˢ Iθ) := prY
  refine MeasureTheory.Integrable.congr ((prDX'.add (prX'.add prY')).const_mul (C₀ + 2)) ?_
  filter_upwards with p
  simp only [Pi.add_apply, smul_eq_mul]

/-- **The pointwise AM–GM bound.** -/
theorem pointwiseBound {α : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4) {F Ψ : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ) {χ : ℝ → ℝ} {C₀ : ℝ}
    (hC0 : 0 ≤ C₀)
    (hχnn : ∀ z, 0 ≤ χ z) (hχle : ∀ z, χ z ≤ 1)
    (hχbd : ∀ z, |z * χ z * deriv χ z| ≤ C₀ * χ z) :
    ∀ᵐ p ∂(volume.restrict (Iz ×ˢ Iθ)),
      ‖(w p.1) ^ 2 * (-(sgm α p.2 * ((2 * (p.1 * χ p.1 * deriv χ p.1))
            * XX Ψ p.1 p.2 + (χ p.1) ^ 2 * Dz (XX Ψ) p.1 p.2))
          - ((p.1 - 3) / (1 + p.1)) * ((χ p.1) ^ 2 * XX Ψ p.1 p.2 * sgm α p.2))
        * YY Ψ p.1 p.2‖
      ≤ (C₀ + 2) * ((Dz (XX Ψ) p.1 p.2) ^ 2 * (w p.1) ^ 2 * sgm α p.2
        + ((XX Ψ p.1 p.2) ^ 2 * (w p.1) ^ 2 * sgm α p.2
          + (YY Ψ p.1 p.2) ^ 2 * (w p.1) ^ 2 * sgm α p.2)) := by
  filter_upwards [ae_mem_Q0_prod] with p hp
  have hz : 0 < p.1 := hp.1
  have hθ : p.2 ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hp.2.1, hp.2.2⟩
  have hθI : p.2 ∈ Iθ := ⟨hθ.1.le, hθ.2.le⟩
  have hw0 : 0 ≤ (w p.1) ^ 2 := sq_nonneg _
  have hσ0 : 0 ≤ sgm α p.2 := by rw [sgm]; exact sigma_nonneg hθI
  have hσ1 : sgm α p.2 ≤ 1 := sigma_le_one hα4 hθI
  have hχ1 : χ p.1 ≤ 1 := hχle p.1
  have hχsq : (χ p.1) ^ 2 ≤ 1 := by nlinarith [hχnn p.1, hχle p.1, sq_nonneg (χ p.1)]
  have hA0 : 0 ≤ |XX Ψ p.1 p.2| := abs_nonneg _
  have hD0 : 0 ≤ |Dz (XX Ψ) p.1 p.2| := abs_nonneg _
  have hb3 : |(p.1 - 3) / (1 + p.1)| ≤ 3 := by
    rw [abs_div]
    rw [abs_of_pos (by linarith : (0:ℝ) < 1 + p.1)]
    rw [div_le_iff₀ (by linarith : (0:ℝ) < 1 + p.1)]
    rw [abs_le] at *
    constructor <;> linarith [hz]
  have hdq : |2 * (p.1 * χ p.1 * deriv χ p.1)| ≤ 2 * C₀ * χ p.1 := by
    rw [abs_mul]
    rw [abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
    calc 2 * |p.1 * χ p.1 * deriv χ p.1| ≤ 2 * (C₀ * χ p.1) :=
          mul_le_mul_of_nonneg_left (hχbd p.1) (by norm_num : (0:ℝ) ≤ 2)
      _ = 2 * C₀ * χ p.1 := by ring
  have hbr : |-(sgm α p.2 * ((2 * (p.1 * χ p.1 * deriv χ p.1)) * XX Ψ p.1 p.2
        + (χ p.1) ^ 2 * Dz (XX Ψ) p.1 p.2))
      - ((p.1 - 3) / (1 + p.1)) * ((χ p.1) ^ 2 * XX Ψ p.1 p.2 * sgm α p.2)|
      ≤ sgm α p.2 * (|Dz (XX Ψ) p.1 p.2| + (2 * C₀ + 3) * |XX Ψ p.1 p.2|) := by
    have hsub : |-(sgm α p.2 * ((2 * (p.1 * χ p.1 * deriv χ p.1)) * XX Ψ p.1 p.2
          + (χ p.1) ^ 2 * Dz (XX Ψ) p.1 p.2))
        - ((p.1 - 3) / (1 + p.1)) * ((χ p.1) ^ 2 * XX Ψ p.1 p.2 * sgm α p.2)|
        ≤ |-(sgm α p.2 * ((2 * (p.1 * χ p.1 * deriv χ p.1)) * XX Ψ p.1 p.2
          + (χ p.1) ^ 2 * Dz (XX Ψ) p.1 p.2))|
          + |((p.1 - 3) / (1 + p.1)) * ((χ p.1) ^ 2 * XX Ψ p.1 p.2 * sgm α p.2)| := by
      have hh := abs_add_le
        (-(sgm α p.2 * ((2 * (p.1 * χ p.1 * deriv χ p.1)) * XX Ψ p.1 p.2
          + (χ p.1) ^ 2 * Dz (XX Ψ) p.1 p.2)))
        (-(((p.1 - 3) / (1 + p.1)) * ((χ p.1) ^ 2 * XX Ψ p.1 p.2 * sgm α p.2)))
      simpa only [sub_eq_add_neg, abs_neg] using hh
    have ha : |-(sgm α p.2 * ((2 * (p.1 * χ p.1 * deriv χ p.1)) * XX Ψ p.1 p.2
          + (χ p.1) ^ 2 * Dz (XX Ψ) p.1 p.2))|
        ≤ sgm α p.2 * (2 * C₀ * χ p.1 * |XX Ψ p.1 p.2|
          + (χ p.1) ^ 2 * |Dz (XX Ψ) p.1 p.2|) := by
      have e0 : |-(sgm α p.2 * ((2 * (p.1 * χ p.1 * deriv χ p.1)) * XX Ψ p.1 p.2
            + (χ p.1) ^ 2 * Dz (XX Ψ) p.1 p.2))|
          = sgm α p.2 * |(2 * (p.1 * χ p.1 * deriv χ p.1)) * XX Ψ p.1 p.2
            + (χ p.1) ^ 2 * Dz (XX Ψ) p.1 p.2| := by
        rw [abs_neg]
        rw [abs_mul]
        rw [abs_of_nonneg hσ0]
      rw [e0]
      refine mul_le_mul_of_nonneg_left ?_ hσ0
      have e1 : |(2 * (p.1 * χ p.1 * deriv χ p.1)) * XX Ψ p.1 p.2|
          = |2 * (p.1 * χ p.1 * deriv χ p.1)| * |XX Ψ p.1 p.2| := by
        rw [abs_mul]
      have e2 : |(χ p.1) ^ 2 * Dz (XX Ψ) p.1 p.2|
          = (χ p.1) ^ 2 * |Dz (XX Ψ) p.1 p.2| := by
        rw [abs_mul]
        rw [abs_of_nonneg (sq_nonneg (χ p.1))]
      calc |(2 * (p.1 * χ p.1 * deriv χ p.1)) * XX Ψ p.1 p.2
            + (χ p.1) ^ 2 * Dz (XX Ψ) p.1 p.2|
          ≤ |(2 * (p.1 * χ p.1 * deriv χ p.1)) * XX Ψ p.1 p.2|
            + |(χ p.1) ^ 2 * Dz (XX Ψ) p.1 p.2| := abs_add_le _ _
        _ = |2 * (p.1 * χ p.1 * deriv χ p.1)| * |XX Ψ p.1 p.2|
            + (χ p.1) ^ 2 * |Dz (XX Ψ) p.1 p.2| := by rw [e1, e2]
        _ ≤ 2 * C₀ * χ p.1 * |XX Ψ p.1 p.2|
            + (χ p.1) ^ 2 * |Dz (XX Ψ) p.1 p.2| := by
            refine add_le_add ?_ le_rfl
            exact mul_le_mul_of_nonneg_right hdq hA0
    have hb : |((p.1 - 3) / (1 + p.1)) * ((χ p.1) ^ 2 * XX Ψ p.1 p.2
          * sgm α p.2)|
        ≤ 3 * ((χ p.1) ^ 2 * |XX Ψ p.1 p.2| * sgm α p.2) := by
      have e1 : |((p.1 - 3) / (1 + p.1)) * ((χ p.1) ^ 2 * XX Ψ p.1 p.2 * sgm α p.2)|
          = |(p.1 - 3) / (1 + p.1)| * |(χ p.1) ^ 2 * XX Ψ p.1 p.2 * sgm α p.2| := by
        rw [abs_mul]
      have e2 : |(χ p.1) ^ 2 * XX Ψ p.1 p.2 * sgm α p.2|
          = (χ p.1) ^ 2 * |XX Ψ p.1 p.2| * sgm α p.2 := by
        rw [abs_mul]
        rw [abs_mul]
        rw [abs_of_nonneg (sq_nonneg (χ p.1))]
        rw [abs_of_nonneg hσ0]
      rw [e1, e2]
      exact mul_le_mul_of_nonneg_right hb3
        (mul_nonneg (mul_nonneg (sq_nonneg _) (abs_nonneg _)) hσ0)
    have hkey : sgm α p.2 * (2 * C₀ * χ p.1 * |XX Ψ p.1 p.2|
          + (χ p.1) ^ 2 * |Dz (XX Ψ) p.1 p.2|)
        + 3 * ((χ p.1) ^ 2 * |XX Ψ p.1 p.2| * sgm α p.2)
        ≤ sgm α p.2 * (|Dz (XX Ψ) p.1 p.2| + (2 * C₀ + 3) * |XX Ψ p.1 p.2|) := by
      have f1 : (χ p.1) ^ 2 * |Dz (XX Ψ) p.1 p.2| ≤ |Dz (XX Ψ) p.1 p.2| :=
        mul_le_of_le_one_left hD0 hχsq
      have f2 : 2 * C₀ * χ p.1 * |XX Ψ p.1 p.2| ≤ 2 * C₀ * |XX Ψ p.1 p.2| := by
        have h2 : 2 * C₀ * χ p.1 ≤ 2 * C₀ := by nlinarith
        calc 2 * C₀ * χ p.1 * |XX Ψ p.1 p.2|
              = (2 * C₀ * χ p.1) * |XX Ψ p.1 p.2| := by ring
          _ ≤ (2 * C₀) * |XX Ψ p.1 p.2| := mul_le_mul_of_nonneg_right h2 hA0
      have f3 : 3 * ((χ p.1) ^ 2 * |XX Ψ p.1 p.2|) ≤ 3 * |XX Ψ p.1 p.2| := by
        have h3 : (χ p.1) ^ 2 * |XX Ψ p.1 p.2| ≤ |XX Ψ p.1 p.2| :=
          mul_le_of_le_one_left hA0 hχsq
        linarith
      have g1 := mul_le_mul_of_nonneg_left f1 hσ0
      have g2 := mul_le_mul_of_nonneg_left f2 hσ0
      nlinarith [g1, g2, f3, hσ0]
    exact (hsub.trans (add_le_add ha hb)).trans hkey
  have hAM : sgm α p.2 * ((|Dz (XX Ψ) p.1 p.2| + (2 * C₀ + 3) * |XX Ψ p.1 p.2|)
        * |YY Ψ p.1 p.2|)
      ≤ sgm α p.2 * ((C₀ + 2) * ((Dz (XX Ψ) p.1 p.2) ^ 2 + (XX Ψ p.1 p.2) ^ 2
          + (YY Ψ p.1 p.2) ^ 2)) := by
    refine mul_le_mul_of_nonneg_left ?_ hσ0
    nlinarith [hD0, hA0, abs_nonneg (YY Ψ p.1 p.2), sq_abs (Dz (XX Ψ) p.1 p.2),
      sq_abs (XX Ψ p.1 p.2), sq_abs (YY Ψ p.1 p.2), hC0,
      sq_nonneg (|Dz (XX Ψ) p.1 p.2| - |YY Ψ p.1 p.2|),
      sq_nonneg (|XX Ψ p.1 p.2| - |YY Ψ p.1 p.2|)]
  have e0 : ‖(w p.1) ^ 2 * (-(sgm α p.2 * ((2 * (p.1 * χ p.1 * deriv χ p.1))
          * XX Ψ p.1 p.2 + (χ p.1) ^ 2 * Dz (XX Ψ) p.1 p.2))
        - ((p.1 - 3) / (1 + p.1)) * ((χ p.1) ^ 2 * XX Ψ p.1 p.2 * sgm α p.2))
      * YY Ψ p.1 p.2‖
      = (w p.1) ^ 2 * |-(sgm α p.2 * ((2 * (p.1 * χ p.1 * deriv χ p.1))
            * XX Ψ p.1 p.2 + (χ p.1) ^ 2 * Dz (XX Ψ) p.1 p.2))
          - ((p.1 - 3) / (1 + p.1)) * ((χ p.1) ^ 2 * XX Ψ p.1 p.2 * sgm α p.2)|
        * |YY Ψ p.1 p.2| := by
    rw [Real.norm_eq_abs]
    rw [abs_mul]
    rw [abs_mul]
    rw [abs_of_nonneg hw0]
  rw [e0]
  calc (w p.1) ^ 2 * |-(sgm α p.2 * ((2 * (p.1 * χ p.1 * deriv χ p.1))
          * XX Ψ p.1 p.2 + (χ p.1) ^ 2 * Dz (XX Ψ) p.1 p.2))
        - ((p.1 - 3) / (1 + p.1)) * ((χ p.1) ^ 2 * XX Ψ p.1 p.2 * sgm α p.2)|
        * |YY Ψ p.1 p.2|
      = (w p.1) ^ 2 * (|-(sgm α p.2 * ((2 * (p.1 * χ p.1 * deriv χ p.1))
            * XX Ψ p.1 p.2 + (χ p.1) ^ 2 * Dz (XX Ψ) p.1 p.2))
          - ((p.1 - 3) / (1 + p.1)) * ((χ p.1) ^ 2 * XX Ψ p.1 p.2 * sgm α p.2)|
          * |YY Ψ p.1 p.2|) := by ring
    _ ≤ (w p.1) ^ 2 * (sgm α p.2 * ((|Dz (XX Ψ) p.1 p.2|
          + (2 * C₀ + 3) * |XX Ψ p.1 p.2|) * |YY Ψ p.1 p.2|)) := by
        refine mul_le_mul_of_nonneg_left ?_ hw0
        calc |-(sgm α p.2 * ((2 * (p.1 * χ p.1 * deriv χ p.1))
              * XX Ψ p.1 p.2 + (χ p.1) ^ 2 * Dz (XX Ψ) p.1 p.2))
            - ((p.1 - 3) / (1 + p.1)) * ((χ p.1) ^ 2 * XX Ψ p.1 p.2 * sgm α p.2)|
            * |YY Ψ p.1 p.2|
          ≤ (sgm α p.2 * (|Dz (XX Ψ) p.1 p.2| + (2 * C₀ + 3) * |XX Ψ p.1 p.2|))
            * |YY Ψ p.1 p.2| := mul_le_mul_of_nonneg_right hbr (abs_nonneg _)
          _ = sgm α p.2 * ((|Dz (XX Ψ) p.1 p.2| + (2 * C₀ + 3) * |XX Ψ p.1 p.2|)
              * |YY Ψ p.1 p.2|) := by ring
    _ ≤ (w p.1) ^ 2 * (sgm α p.2 * ((C₀ + 2) * ((Dz (XX Ψ) p.1 p.2) ^ 2
          + (XX Ψ p.1 p.2) ^ 2 + (YY Ψ p.1 p.2) ^ 2))) :=
        mul_le_mul_of_nonneg_left hAM hw0
    _ = (C₀ + 2) * ((Dz (XX Ψ) p.1 p.2) ^ 2 * (w p.1) ^ 2 * sgm α p.2
          + ((XX Ψ p.1 p.2) ^ 2 * (w p.1) ^ 2 * sgm α p.2
            + (YY Ψ p.1 p.2) ^ 2 * (w p.1) ^ 2 * sgm α p.2)) := by ring

/-- Integrability of the expanded (derivative-free) integration-by-parts integrand. -/
theorem expIntegrable {α : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4) {F Ψ : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ) {χ : ℝ → ℝ} {C₀ : ℝ}
    (hC0 : 0 ≤ C₀) (hχcd : ContDiff ℝ Work.Stability.smoothOrder χ)
    (hχnn : ∀ z, 0 ≤ χ z) (hχle : ∀ z, χ z ≤ 1)
    (hχbd : ∀ z, |z * χ z * deriv χ z| ≤ C₀ * χ z) :
    MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => (w p.1) ^ 2
      * (-(sgm α p.2 * ((2 * (p.1 * χ p.1 * deriv χ p.1)) * XX Ψ p.1 p.2
          + (χ p.1) ^ 2 * Dz (XX Ψ) p.1 p.2))
        - ((p.1 - 3) / (1 + p.1)) * ((χ p.1) ^ 2 * XX Ψ p.1 p.2 * sgm α p.2))
      * YY Ψ p.1 p.2) (Iz ×ˢ Iθ) := by
  refine MeasureTheory.Integrable.mono' (majIntegrable hα hα4 h) ?_
    (pointwiseBound hα hα4 h hC0 hχnn hχle hχbd)
  have hXX : Work.FTS.EllipticEst.SmoothOpen (XX Ψ) :=
    (Work.FTS.EllipticEst.Prop.aofSmoothOpen
      (Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth)).Dz
  have hYY : Work.FTS.EllipticEst.SmoothOpen (YY Ψ) :=
    (Work.FTS.EllipticEst.Prop.aofSmoothOpen
      (Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth)).pth.pth
  have hwc : ContinuousOn (fun p : ℝ × ℝ => (w p.1) ^ 2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    Work.FTS.ClassC.aslotAux.BslOpPth.continuousOn_w_sq_Q0
  have hm1 : ContinuousOn (fun p : ℝ × ℝ => Dz (XX Ψ) p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := smoothOpen_continuousOn hXX.Dz
  have hm2 : ContinuousOn (fun p : ℝ × ℝ => XX Ψ p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := smoothOpen_continuousOn hXX
  have hm3 : ContinuousOn (fun p : ℝ × ℝ => YY Ψ p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := smoothOpen_continuousOn hYY
  have hχc : ContinuousOn (fun p : ℝ × ℝ => χ p.1)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    hχcd.continuous.comp_continuousOn continuousOn_fst
  have hχc' : ContinuousOn (fun p : ℝ × ℝ => deriv χ p.1)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    (hχcd.continuous_deriv (by simp)).comp_continuousOn continuousOn_fst
  have hσc : ContinuousOn (fun p : ℝ × ℝ => sgm α p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := continuousOn_sgm_Q0 α
  have hbc : ContinuousOn (fun p : ℝ × ℝ => (p.1 - 3) / (1 + p.1))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    refine ContinuousOn.div (continuousOn_fst.sub continuousOn_const)
      (continuousOn_const.add continuousOn_fst) (fun p hp => by
        have : (0:ℝ) < p.1 := hp.1
        linarith)
  have hcont : ContinuousOn (fun p : ℝ × ℝ => (w p.1) ^ 2
      * (-(sgm α p.2 * ((2 * (p.1 * χ p.1 * deriv χ p.1)) * XX Ψ p.1 p.2
          + (χ p.1) ^ 2 * Dz (XX Ψ) p.1 p.2))
        - ((p.1 - 3) / (1 + p.1)) * ((χ p.1) ^ 2 * XX Ψ p.1 p.2 * sgm α p.2))
      * YY Ψ p.1 p.2) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    have h1 : ContinuousOn (fun p : ℝ × ℝ => 2 * (p.1 * χ p.1 * deriv χ p.1))
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
      continuousOn_const.mul ((continuousOn_fst.mul hχc).mul hχc')
    exact (hwc.mul (((hσc.mul ((h1.mul hm2).add (hχc.pow 2 |>.mul hm1))).neg).sub
      (hbc.mul ((hχc.pow 2 |>.mul hm2).mul hσc)))).mul hm3
  have h6 := Work.Spaces.aesm_of_continuousOn_Qd _ hcont
  rwa [prod_restrict_eq_rect] at h6

/-- Integrability of the integration-by-parts integrand in its `deriv` form. -/
theorem derivFormIntegrable {α : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4) {F Ψ : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ) {χ : ℝ → ℝ} {C₀ : ℝ}
    (hC0 : 0 ≤ C₀)
    (hχcd : ContDiff ℝ Work.Stability.smoothOrder χ)
    (hχnn : ∀ z, 0 ≤ χ z) (hχle : ∀ z, χ z ≤ 1)
    (hχbd : ∀ z, |z * χ z * deriv χ z| ≤ C₀ * χ z) :
    MeasureTheory.IntegrableOn
      (fun p : ℝ × ℝ => (w p.1) ^ 2 * (-(p.1 * deriv (fun z' =>
            (χ z') ^ 2 * XX Ψ z' p.2 * sgm α p.2) p.1)
          - ((p.1 - 3) / (1 + p.1)) * ((χ p.1) ^ 2 * XX Ψ p.1 p.2 * sgm α p.2))
        * YY Ψ p.1 p.2) (Iz ×ˢ Iθ) := by
  have hXX : Work.FTS.EllipticEst.SmoothOpen (XX Ψ) :=
    (Work.FTS.EllipticEst.Prop.aofSmoothOpen
      (Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth)).Dz
  refine MeasureTheory.Integrable.congr
    (expIntegrable hα hα4 h hC0 hχcd hχnn hχle hχbd) ?_
  filter_upwards [ae_mem_Q0_prod] with p hp
  rw [deriv_chi_sq_mul_sgm hXX (hχcd.differentiable (by simp)) hp.2 hp.1]
  simp only [Dz, pz]

end

end Work.FTS.ClassC.VopGen.Core
