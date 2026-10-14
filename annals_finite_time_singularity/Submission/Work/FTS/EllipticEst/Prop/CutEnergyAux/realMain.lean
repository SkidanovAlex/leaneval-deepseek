import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Order.Group.Lattice
import Submission.Work.FTS.EllipticEst.Prop.CutEnergyAux.basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Prop.CutEnergyAux

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 3200000

local notation "Iθ" => Work.Spaces.Iθ
local notation "Iz" => Work.Spaces.Iz
local notation "sg" => Work.FTS.EllipticEst.sEta

/-- A.e. strong measurability of the angular mass profile of `u`. -/
theorem aesm_P2 (α : ℝ) (u G : ℝ → ℝ → ℝ)
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) :
    AEStronglyMeasurable (fun z => ∫ θ in Iθ, (u z θ) ^ 2)
      (MeasureTheory.volume.restrict Iz) :=
  aesm_massProfile h.smooth

/-- The truncation-error integrand of the `φ''`-piece is integrable. -/
theorem integrableOn_truncErr_E1 (α : ℝ) (u G : ℝ → ℝ → ℝ)
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) (φ : ℝ → ℝ)
    (hC1 : ∃ C : ℝ, ∀ z : ℝ, |deriv φ z| * z ≤ C)
    (hC2 : ∃ C : ℝ, ∀ z : ℝ, |deriv (deriv φ) z| * z ^ 2 ≤ C)
    (hP : MeasureTheory.IntegrableOn (fun z => (Work.Spaces.w z) ^ 2
      * (∫ θ in Iθ, (u z θ) ^ 2)) Iz) :
    MeasureTheory.IntegrableOn (fun z => (2 * |deriv φ z|
        * |deriv (fun x : ℝ => x ^ 2 * (Work.Spaces.w x) ^ 2) z|
        + |deriv (deriv φ) z| * (z ^ 2 * (Work.Spaces.w z) ^ 2))
      * (∫ θ in Iθ, (u z θ) ^ 2)) Iz := by
  obtain ⟨C₁, hC₁⟩ := hC1
  obtain ⟨C₂, hC₂⟩ := hC2
  have hP2nn : ∀ z : ℝ, 0 ≤ ∫ θ in Iθ, (u z θ) ^ 2 :=
    fun z => integral_nonneg fun θ => sq_nonneg _
  have haesm : AEStronglyMeasurable (fun z => (2 * |deriv φ z|
        * |deriv (fun x : ℝ => x ^ 2 * (Work.Spaces.w x) ^ 2) z|
        + |deriv (deriv φ) z| * (z ^ 2 * (Work.Spaces.w z) ^ 2))
      * (∫ θ in Iθ, (u z θ) ^ 2)) (MeasureTheory.volume.restrict Iz) := by
    have hA : AEStronglyMeasurable (fun z => 2 * |deriv φ z|
        * |deriv (fun x : ℝ => x ^ 2 * (Work.Spaces.w x) ^ 2) z|)
        (MeasureTheory.volume.restrict Iz) :=
      (((measurable_deriv φ).abs.const_mul 2).aestronglyMeasurable).mul
        ((measurable_deriv (fun x : ℝ => x ^ 2 * (Work.Spaces.w x) ^ 2)).abs.aestronglyMeasurable)
    have hB : AEStronglyMeasurable (fun z => |deriv (deriv φ) z|
        * (z ^ 2 * (Work.Spaces.w z) ^ 2)) (MeasureTheory.volume.restrict Iz) :=
      ((measurable_deriv (deriv φ)).abs.aestronglyMeasurable).mul
        (((measurable_id.pow_const 2).mul
          Work.FTS.EllipticEst.Honest.measurable_wSq).aestronglyMeasurable)
    exact (hA.add hB).mul (aesm_P2 α u G h)
  refine (hP.const_mul (max (4 * C₁ + C₂) 0)).mono' haesm ?_
  filter_upwards [ae_pos_Iz] with z hz
  have hW2' := Work.FTS.EllipticEst.Honest.deriv_zsqwSq_abs_le z hz
  have hC₁z : |deriv φ z| * z ≤ C₁ := hC₁ z
  have hC₂z : |deriv (deriv φ) z| * z ^ 2 ≤ C₂ := hC₂ z
  have hw2 : 0 ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
  have hcoef : (2 * |deriv φ z| * |deriv (fun x : ℝ => x ^ 2 * (Work.Spaces.w x) ^ 2) z|
      + |deriv (deriv φ) z| * (z ^ 2 * (Work.Spaces.w z) ^ 2))
      ≤ max (4 * C₁ + C₂) 0 * (Work.Spaces.w z) ^ 2 := by
    have h1 : 2 * |deriv φ z| * |deriv (fun x : ℝ => x ^ 2 * (Work.Spaces.w x) ^ 2) z|
        ≤ 4 * (|deriv φ z| * z) * (Work.Spaces.w z) ^ 2 := by
      calc 2 * |deriv φ z| * |deriv (fun x : ℝ => x ^ 2 * (Work.Spaces.w x) ^ 2) z|
          ≤ 2 * |deriv φ z| * (2 * z * (Work.Spaces.w z) ^ 2) :=
            mul_le_mul_of_nonneg_left hW2' (by positivity)
        _ = 4 * (|deriv φ z| * z) * (Work.Spaces.w z) ^ 2 := by ring
    have h2 : |deriv (deriv φ) z| * (z ^ 2 * (Work.Spaces.w z) ^ 2)
        ≤ C₂ * (Work.Spaces.w z) ^ 2 := by
      calc |deriv (deriv φ) z| * (z ^ 2 * (Work.Spaces.w z) ^ 2)
          = (|deriv (deriv φ) z| * z ^ 2) * (Work.Spaces.w z) ^ 2 := by ring
        _ ≤ C₂ * (Work.Spaces.w z) ^ 2 := mul_le_mul_of_nonneg_right hC₂z hw2
    have h3 : 4 * (|deriv φ z| * z) * (Work.Spaces.w z) ^ 2
        ≤ 4 * C₁ * (Work.Spaces.w z) ^ 2 :=
      mul_le_mul_of_nonneg_right (by linarith) hw2
    have h4 : (4 * C₁ + C₂) * (Work.Spaces.w z) ^ 2
        ≤ max (4 * C₁ + C₂) 0 * (Work.Spaces.w z) ^ 2 :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) hw2
    linarith
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc (2 * |deriv φ z| * |deriv (fun x : ℝ => x ^ 2 * (Work.Spaces.w x) ^ 2) z|
        + |deriv (deriv φ) z| * (z ^ 2 * (Work.Spaces.w z) ^ 2))
      * (∫ θ in Iθ, (u z θ) ^ 2)
      ≤ (max (4 * C₁ + C₂) 0 * (Work.Spaces.w z) ^ 2)
        * (∫ θ in Iθ, (u z θ) ^ 2) :=
        mul_le_mul_of_nonneg_right hcoef (hP2nn z)
    _ = max (4 * C₁ + C₂) 0 * ((Work.Spaces.w z) ^ 2
        * (∫ θ in Iθ, (u z θ) ^ 2)) := by ring

/-- The truncation-error integrand of the `φ'`-piece is integrable. -/
theorem integrableOn_truncErr_E2 (α : ℝ) (u G : ℝ → ℝ → ℝ)
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) (φ : ℝ → ℝ)
    (hC1 : ∃ C : ℝ, ∀ z : ℝ, |deriv φ z| * z ≤ C)
    (hP : MeasureTheory.IntegrableOn (fun z => (Work.Spaces.w z) ^ 2
      * (∫ θ in Iθ, (u z θ) ^ 2)) Iz) :
    MeasureTheory.IntegrableOn (fun z => |deriv φ z| * (z * (Work.Spaces.w z) ^ 2)
      * (∫ θ in Iθ, (u z θ) ^ 2)) Iz := by
  obtain ⟨C, hC⟩ := hC1
  have hP2nn : ∀ z : ℝ, 0 ≤ ∫ θ in Iθ, (u z θ) ^ 2 :=
    fun z => integral_nonneg fun θ => sq_nonneg _
  have haesm : AEStronglyMeasurable (fun z => |deriv φ z| * (z * (Work.Spaces.w z) ^ 2)
      * (∫ θ in Iθ, (u z θ) ^ 2)) (MeasureTheory.volume.restrict Iz) :=
    (((measurable_deriv φ).abs.aestronglyMeasurable).mul
      ((measurable_id.mul Work.FTS.EllipticEst.Honest.measurable_wSq).aestronglyMeasurable)).mul
      (aesm_P2 α u G h)
  refine (hP.const_mul (max C 0)).mono' haesm ?_
  filter_upwards [ae_pos_Iz] with z hz
  have hCz : |deriv φ z| * z ≤ C := hC z
  have hCmax : |deriv φ z| * z ≤ max C 0 := le_trans hCz (le_max_left _ _)
  have hw2 : 0 ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc |deriv φ z| * (z * (Work.Spaces.w z) ^ 2) * (∫ θ in Iθ, (u z θ) ^ 2)
      = (|deriv φ z| * z) * ((Work.Spaces.w z) ^ 2
          * (∫ θ in Iθ, (u z θ) ^ 2)) := by ring
    _ ≤ max C 0 * ((Work.Spaces.w z) ^ 2 * (∫ θ in Iθ, (u z θ) ^ 2)) :=
        mul_le_mul_of_nonneg_right hCmax (mul_nonneg hw2 (hP2nn z))

/-- The truncated mass `∫_z φw²∫_θ u²` is integrable as soon as the untruncated mass is and
`0 ≤ φ ≤ 1`. -/
theorem integrableOn_phi_wSq_P2 {φ P : ℝ → ℝ} (hφm : Measurable φ)
    (hφ0 : ∀ z : ℝ, 0 ≤ φ z) (hφ1 : ∀ z : ℝ, φ z ≤ 1) (hP0 : ∀ z : ℝ, 0 ≤ P z)
    (hPaesm : AEStronglyMeasurable P (MeasureTheory.volume.restrict Iz))
    (hP : MeasureTheory.IntegrableOn (fun z => (Work.Spaces.w z) ^ 2 * P z) Iz) :
    MeasureTheory.IntegrableOn (fun z => φ z * (Work.Spaces.w z) ^ 2 * P z) Iz := by
  have haesm : AEStronglyMeasurable (fun z => φ z * (Work.Spaces.w z) ^ 2 * P z)
      (MeasureTheory.volume.restrict Iz) :=
    ((hφm.mul Work.FTS.EllipticEst.Honest.measurable_wSq).aestronglyMeasurable).mul hPaesm
  refine hP.mono' haesm ?_
  filter_upwards with z
  have hw2 : 0 ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
  have hg0 : 0 ≤ (Work.Spaces.w z) ^ 2 * P z := mul_nonneg hw2 (hP0 z)
  have h1 : φ z * (Work.Spaces.w z) ^ 2 * P z ≤ (Work.Spaces.w z) ^ 2 * P z := by
    calc φ z * (Work.Spaces.w z) ^ 2 * P z
        = φ z * ((Work.Spaces.w z) ^ 2 * P z) := by ring
      _ ≤ 1 * ((Work.Spaces.w z) ^ 2 * P z) := mul_le_mul_of_nonneg_right (hφ1 z) hg0
      _ = (Work.Spaces.w z) ^ 2 * P z := one_mul _
  rw [Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (mul_nonneg (hφ0 z) hw2) (hP0 z))]
  exact h1

/-- The source AM–GM, truncated: `∫_z φw²∫_θ G·u ≤ ½∫_z φw²∫_θ G² + ½∫_z φw²∫_θ u²`. -/
theorem trunc_A_le (α : ℝ) (u G : ℝ → ℝ → ℝ)
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) {φ : ℝ → ℝ}
    (hφ0 : ∀ z : ℝ, 0 ≤ φ z)
    (hPc : MeasureTheory.IntegrableOn (fun z => φ z * (Work.Spaces.w z) ^ 2
      * (∫ θ in Iθ, (u z θ) ^ 2)) Iz)
    (hS : MeasureTheory.IntegrableOn (fun z => φ z * (Work.Spaces.w z) ^ 2
      * (∫ θ in Iθ, (G z θ) ^ 2)) Iz) :
    (∫ z in Iz, φ z * (Work.Spaces.w z) ^ 2 * (∫ θ in Iθ, G z θ * u z θ))
      ≤ (1 / 2) * (∫ z in Iz, φ z * (Work.Spaces.w z) ^ 2
          * (∫ θ in Iθ, (G z θ) ^ 2))
        + (1 / 2) * (∫ z in Iz, φ z * (Work.Spaces.w z) ^ 2
          * (∫ θ in Iθ, (u z θ) ^ 2)) := by
  have hgint : MeasureTheory.IntegrableOn (fun z => (1 / 2) * (φ z * (Work.Spaces.w z) ^ 2
      * (∫ θ in Iθ, (G z θ) ^ 2))
      + (1 / 2) * (φ z * (Work.Spaces.w z) ^ 2
        * (∫ θ in Iθ, (u z θ) ^ 2))) Iz :=
    (hS.const_mul (1 / 2)).add (hPc.const_mul (1 / 2))
  have hg0 : 0 ≤ᵐ[MeasureTheory.volume.restrict Iz]
      (fun z => (1 / 2) * (φ z * (Work.Spaces.w z) ^ 2 * (∫ θ in Iθ, (G z θ) ^ 2))
        + (1 / 2) * (φ z * (Work.Spaces.w z) ^ 2 * (∫ θ in Iθ, (u z θ) ^ 2))) :=
    Filter.Eventually.of_forall fun z => by
      have h1 : 0 ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
      have h2 : 0 ≤ ∫ θ in Iθ, (G z θ) ^ 2 := integral_nonneg fun θ => sq_nonneg _
      have h3 : 0 ≤ ∫ θ in Iθ, (u z θ) ^ 2 := integral_nonneg fun θ => sq_nonneg _
      have h4 : 0 ≤ φ z * (Work.Spaces.w z) ^ 2 * (∫ θ in Iθ, (G z θ) ^ 2) :=
        mul_nonneg (mul_nonneg (hφ0 z) h1) h2
      have h5 : 0 ≤ φ z * (Work.Spaces.w z) ^ 2 * (∫ θ in Iθ, (u z θ) ^ 2) :=
        mul_nonneg (mul_nonneg (hφ0 z) h1) h3
      first | simp only [Pi.zero_apply] | skip
      linarith
  have hle : (fun z => φ z * (Work.Spaces.w z) ^ 2 * (∫ θ in Iθ, G z θ * u z θ))
      ≤ᵐ[MeasureTheory.volume.restrict Iz]
      (fun z => (1 / 2) * (φ z * (Work.Spaces.w z) ^ 2 * (∫ θ in Iθ, (G z θ) ^ 2))
        + (1 / 2) * (φ z * (Work.Spaces.w z) ^ 2 * (∫ θ in Iθ, (u z θ) ^ 2))) := by
    filter_upwards [ae_pos_Iz] with z hz
    have hamgm := ae_slice_amgm α u G h (z := z) hz
    have hw : 0 ≤ φ z * (Work.Spaces.w z) ^ 2 := mul_nonneg (hφ0 z) (sq_nonneg _)
    calc φ z * (Work.Spaces.w z) ^ 2 * (∫ θ in Iθ, G z θ * u z θ)
        = (φ z * (Work.Spaces.w z) ^ 2) * (∫ θ in Iθ, G z θ * u z θ) := by ring
      _ ≤ (φ z * (Work.Spaces.w z) ^ 2)
            * ((1 / 2) * (∫ θ in Iθ, (G z θ) ^ 2)
              + (1 / 2) * (∫ θ in Iθ, (u z θ) ^ 2)) :=
          mul_le_mul_of_nonneg_left hamgm hw
      _ = (1 / 2) * (φ z * (Work.Spaces.w z) ^ 2 * (∫ θ in Iθ, (G z θ) ^ 2))
          + (1 / 2) * (φ z * (Work.Spaces.w z) ^ 2
            * (∫ θ in Iθ, (u z θ) ^ 2)) := by ring
  have hmain := Work.FTS.EllipticEst.Honest.setIntegral_le_of_ae_le_of_nonneg hle hg0 hgint
  rw [integral_add (hS.const_mul (1 / 2)) (hPc.const_mul (1 / 2)),
    integral_const_mul, integral_const_mul] at hmain
  exact hmain

/-- The second-order truncation term obeys the pointwise weight bound
`(φw²z²)'' ≤ 2|φ'||(z²w²)'| + |φ''|z²w² + 6φw²`. -/
theorem trunc_B2_le (φ P : ℝ → ℝ) (hφsm : ContDiff ℝ 2 φ) (hφ0 : ∀ z : ℝ, 0 ≤ φ z)
    (hP0 : ∀ z : ℝ, 0 ≤ P z)
    (hE1 : MeasureTheory.IntegrableOn (fun z => (2 * |deriv φ z|
        * |deriv (fun x : ℝ => x ^ 2 * (Work.Spaces.w x) ^ 2) z|
        + |deriv (deriv φ) z| * (z ^ 2 * (Work.Spaces.w z) ^ 2)) * P z) Iz)
    (hPc : MeasureTheory.IntegrableOn (fun z => φ z * (Work.Spaces.w z) ^ 2 * P z) Iz) :
    (∫ z in Iz,
        deriv (deriv (fun z => φ z * (Work.Spaces.w z) ^ 2 * z ^ 2)) z * P z)
      ≤ (∫ z in Iz, (2 * |deriv φ z|
          * |deriv (fun x : ℝ => x ^ 2 * (Work.Spaces.w x) ^ 2) z|
          + |deriv (deriv φ) z| * (z ^ 2 * (Work.Spaces.w z) ^ 2)) * P z)
        + 6 * (∫ z in Iz, φ z * (Work.Spaces.w z) ^ 2 * P z) := by
  have hgint : MeasureTheory.IntegrableOn (fun z => ((2 * |deriv φ z|
        * |deriv (fun x : ℝ => x ^ 2 * (Work.Spaces.w x) ^ 2) z|
        + |deriv (deriv φ) z| * (z ^ 2 * (Work.Spaces.w z) ^ 2)) * P z)
      + 6 * (φ z * (Work.Spaces.w z) ^ 2 * P z)) Iz :=
    hE1.add (hPc.const_mul 6)
  have hg0 : 0 ≤ᵐ[MeasureTheory.volume.restrict Iz]
      (fun z => ((2 * |deriv φ z|
        * |deriv (fun x : ℝ => x ^ 2 * (Work.Spaces.w x) ^ 2) z|
        + |deriv (deriv φ) z| * (z ^ 2 * (Work.Spaces.w z) ^ 2)) * P z)
      + 6 * (φ z * (Work.Spaces.w z) ^ 2 * P z)) :=
    Filter.Eventually.of_forall fun z => by
      have h1 : 0 ≤ P z := hP0 z
      have h2 : 0 ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
      have h3 : 0 ≤ 2 * |deriv φ z|
          * |deriv (fun x : ℝ => x ^ 2 * (Work.Spaces.w x) ^ 2) z|
          + |deriv (deriv φ) z| * (z ^ 2 * (Work.Spaces.w z) ^ 2) :=
        add_nonneg (mul_nonneg (by positivity) (abs_nonneg _))
          (mul_nonneg (abs_nonneg _) (mul_nonneg (sq_nonneg _) h2))
      have h4 : 0 ≤ (2 * |deriv φ z|
          * |deriv (fun x : ℝ => x ^ 2 * (Work.Spaces.w x) ^ 2) z|
          + |deriv (deriv φ) z| * (z ^ 2 * (Work.Spaces.w z) ^ 2)) * P z := mul_nonneg h3 h1
      have h5 : 0 ≤ φ z * (Work.Spaces.w z) ^ 2 * P z :=
        mul_nonneg (mul_nonneg (hφ0 z) h2) h1
      first | simp only [Pi.zero_apply] | skip
      linarith
  have hle : (fun z => deriv (deriv (fun z => φ z * (Work.Spaces.w z) ^ 2 * z ^ 2)) z * P z)
      ≤ᵐ[MeasureTheory.volume.restrict Iz]
      (fun z => ((2 * |deriv φ z|
          * |deriv (fun x : ℝ => x ^ 2 * (Work.Spaces.w x) ^ 2) z|
          + |deriv (deriv φ) z| * (z ^ 2 * (Work.Spaces.w z) ^ 2)) * P z)
        + 6 * (φ z * (Work.Spaces.w z) ^ 2 * P z)) := by
    filter_upwards [ae_pos_Iz] with z hz
    have hderiv := truncW2_deriv φ hφsm hz
    have hsum := truncW2_le φ hφsm hφ0 hz
    have hPz := hP0 z
    calc deriv (deriv (fun z => φ z * (Work.Spaces.w z) ^ 2 * z ^ 2)) z * P z
        ≤ ((2 * |deriv φ z| * |deriv (fun x : ℝ => x ^ 2 * (Work.Spaces.w x) ^ 2) z|
          + |deriv (deriv φ) z| * (z ^ 2 * (Work.Spaces.w z) ^ 2))
          + 6 * (φ z * (Work.Spaces.w z) ^ 2)) * P z :=
          mul_le_mul_of_nonneg_right hsum hPz
      _ = ((2 * |deriv φ z| * |deriv (fun x : ℝ => x ^ 2 * (Work.Spaces.w x) ^ 2) z|
          + |deriv (deriv φ) z| * (z ^ 2 * (Work.Spaces.w z) ^ 2)) * P z)
        + 6 * (φ z * (Work.Spaces.w z) ^ 2 * P z) := by ring
  have hmain := Work.FTS.EllipticEst.Honest.setIntegral_le_of_ae_le_of_nonneg hle hg0 hgint
  rw [integral_add hE1 (hPc.const_mul 6), integral_const_mul] at hmain
  exact hmain

/-- The first-order truncation term obeys the pointwise weight bound
`-(φw²z)' ≤ |φ'|(zw²) + 3φw²`. -/
theorem trunc_B1_le (φ P : ℝ → ℝ) (hφsm : ContDiff ℝ 2 φ) (hφ0 : ∀ z : ℝ, 0 ≤ φ z)
    (hP0 : ∀ z : ℝ, 0 ≤ P z)
    (hE2 : MeasureTheory.IntegrableOn (fun z => |deriv φ z| * (z * (Work.Spaces.w z) ^ 2)
      * P z) Iz)
    (hPc : MeasureTheory.IntegrableOn (fun z => φ z * (Work.Spaces.w z) ^ 2 * P z) Iz) :
    -(∫ z in Iz, deriv (fun z => φ z * (Work.Spaces.w z) ^ 2 * z) z * P z)
      ≤ (∫ z in Iz, |deriv φ z| * (z * (Work.Spaces.w z) ^ 2) * P z)
        + 3 * (∫ z in Iz, φ z * (Work.Spaces.w z) ^ 2 * P z) := by
  have hgint : MeasureTheory.IntegrableOn (fun z => (|deriv φ z| * (z * (Work.Spaces.w z) ^ 2)
      * P z) + 3 * (φ z * (Work.Spaces.w z) ^ 2 * P z)) Iz :=
    hE2.add (hPc.const_mul 3)
  have hg0 : 0 ≤ᵐ[MeasureTheory.volume.restrict Iz]
      (fun z => (|deriv φ z| * (z * (Work.Spaces.w z) ^ 2) * P z)
        + 3 * (φ z * (Work.Spaces.w z) ^ 2 * P z)) := by
    filter_upwards [ae_pos_Iz] with z hz
    have h1 : 0 ≤ P z := hP0 z
    have h2 : 0 ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
    have h3 : 0 ≤ z * (Work.Spaces.w z) ^ 2 := mul_nonneg (le_of_lt hz) h2
    have h4 : 0 ≤ |deriv φ z| * (z * (Work.Spaces.w z) ^ 2) * P z :=
      mul_nonneg (mul_nonneg (abs_nonneg _) h3) h1
    have h5 : 0 ≤ φ z * (Work.Spaces.w z) ^ 2 * P z :=
      mul_nonneg (mul_nonneg (hφ0 z) h2) h1
    first | simp only [Pi.zero_apply] | skip
    linarith
  have hle : ∀ᵐ z ∂(MeasureTheory.volume.restrict Iz),
      -((|deriv φ z| * (z * (Work.Spaces.w z) ^ 2) * P z)
        + 3 * (φ z * (Work.Spaces.w z) ^ 2 * P z))
      ≤ deriv (fun z => φ z * (Work.Spaces.w z) ^ 2 * z) z * P z := by
    filter_upwards [ae_pos_Iz] with z hz
    have hsum := truncW1_le φ hφsm hφ0 hz
    have hPz := hP0 z
    have hnn : 0 ≤ P z := hPz
    calc -((|deriv φ z| * (z * (Work.Spaces.w z) ^ 2) * P z)
          + 3 * (φ z * (Work.Spaces.w z) ^ 2 * P z))
        = -((|deriv φ z| * (z * (Work.Spaces.w z) ^ 2)
            + 3 * (φ z * (Work.Spaces.w z) ^ 2)) * P z) := by ring
      _ = (-(|deriv φ z| * (z * (Work.Spaces.w z) ^ 2)
            + 3 * (φ z * (Work.Spaces.w z) ^ 2))) * P z := by ring
      _ ≤ deriv (fun z => φ z * (Work.Spaces.w z) ^ 2 * z) z * P z := by
          refine mul_le_mul_of_nonneg_right ?_ hnn
          linarith [hsum]
  have hmain := Work.FTS.EllipticEst.Honest.neg_setIntegral_le_of_ae_le hle hg0 hgint
  rw [integral_add hE2 (hPc.const_mul 3), integral_const_mul] at hmain
  exact hmain

end Work.FTS.EllipticEst.Prop.CutEnergyAux
