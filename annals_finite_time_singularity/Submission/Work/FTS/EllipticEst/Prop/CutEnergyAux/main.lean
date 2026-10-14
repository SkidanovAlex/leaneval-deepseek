import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.Prop.CutEnergyAux.assembly

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

/-- **The real-variable truncated energy inequality.**  Given the truncated energy identity
`hid`, the a.e. angular self-form inequality `hSL`, the finiteness of the untruncated mass `hP`,
of the radial energy slot `hX`, of the source slot `hSs` and of the absolute `Lzero`-pairing
`hLabs`, together with the two bounds `hC1`, `hC2` on the cut-off derivatives, the truncated
`w²`-weighted energy inequality holds with the explicit error term. -/
theorem aeCutEnergy_real (α : ℝ) (u G : ℝ → ℝ → ℝ)
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) (φ : ℝ → ℝ)
    (hφsm : ContDiff ℝ 2 φ) (hφ0 : ∀ z : ℝ, 0 ≤ φ z) (hφ1 : ∀ z : ℝ, φ z ≤ 1)
    (hC1 : ∃ C : ℝ, ∀ z : ℝ, |deriv φ z| * z ≤ C)
    (hC2 : ∃ C : ℝ, ∀ z : ℝ, |deriv (deriv φ) z| * z ^ 2 ≤ C)
    (hSL : ∀ᵐ z ∂(MeasureTheory.volume.restrict Iz),
      (∫ θ in Iθ, (Work.Spaces.pth u z θ) ^ 2) ≤
        (∫ θ in Iθ, Work.Elliptic.Lzero u z θ * u z θ) + 6 * (∫ θ in Iθ, (u z θ) ^ 2))
    (hSLnn : ∀ᵐ z ∂(MeasureTheory.volume.restrict Iz),
      0 ≤ (∫ θ in Iθ, Work.Elliptic.Lzero u z θ * u z θ) + 6 * (∫ θ in Iθ, (u z θ) ^ 2))
    (hP : MeasureTheory.IntegrableOn (fun z => (Work.Spaces.w z) ^ 2
      * (∫ θ in Iθ, (u z θ) ^ 2)) Iz)
    (hX : MeasureTheory.IntegrableOn (fun z => φ z * (Work.Spaces.w z) ^ 2 * z ^ 2
      * (∫ θ in Iθ, (Work.Spaces.pz u z θ) ^ 2)) Iz)
    (hSs : MeasureTheory.IntegrableOn (fun z => φ z * (Work.Spaces.w z) ^ 2
      * (∫ θ in Iθ, (G z θ) ^ 2 * sg θ)) Iz)
    (hLabs : MeasureTheory.IntegrableOn (fun z => φ z * (Work.Spaces.w z) ^ 2
      * (∫ θ in Iθ, |Work.Elliptic.Lzero u z θ * u z θ|)) Iz)
    (hid : (∫ z in Iz, φ z * (Work.Spaces.w z) ^ 2
          * (∫ θ in Iθ, Work.Elliptic.bslOp α u z θ * u z θ))
        = α ^ 2 * (∫ z in Iz, φ z * (Work.Spaces.w z) ^ 2
              * (∫ θ in Iθ, (z * Work.Spaces.pz u z θ) ^ 2))
          + (∫ z in Iz, φ z * (Work.Spaces.w z) ^ 2
              * (∫ θ in Iθ, Work.Elliptic.Lzero u z θ * u z θ))
          - (α ^ 2 / 2) * (∫ z in Iz,
              deriv (deriv (fun z => φ z * (Work.Spaces.w z) ^ 2 * z ^ 2)) z
                * (∫ θ in Iθ, (u z θ) ^ 2))
          + (α * (5 + α) / 2) * (∫ z in Iz,
              deriv (fun z => φ z * (Work.Spaces.w z) ^ 2 * z) z
                * (∫ θ in Iθ, (u z θ) ^ 2))) :
    α ^ 2 * (∫ z in Iz, φ z * (Work.Spaces.w z) ^ 2 * z ^ 2
          * (∫ θ in Iθ, (Work.Spaces.pz u z θ) ^ 2))
      + (∫ z in Iz, φ z * (Work.Spaces.w z) ^ 2
          * (∫ θ in Iθ, (Work.Spaces.pth u z θ) ^ 2))
      ≤ (13 / 2 + 3 * α ^ 2 + (3 / 2) * α * (5 + α))
          * (∫ z in Iz, φ z * (Work.Spaces.w z) ^ 2
            * (∫ θ in Iθ, (u z θ) ^ 2))
        + (1 / 2) * (∫ z in Iz, φ z * (Work.Spaces.w z) ^ 2
            * (∫ θ in Iθ, (G z θ) ^ 2 * sg θ))
        + ((α ^ 2 / 2) * (∫ z in Iz,
              (2 * |deriv φ z| * |deriv (fun z => z ^ 2 * (Work.Spaces.w z) ^ 2) z|
                + |deriv (deriv φ) z| * (z ^ 2 * (Work.Spaces.w z) ^ 2))
                * (∫ θ in Iθ, (u z θ) ^ 2))
          + (α * (5 + α) / 2) * (∫ z in Iz,
              |deriv φ z| * (z * (Work.Spaces.w z) ^ 2)
                * (∫ θ in Iθ, (u z θ) ^ 2))) := by
  have hφm : Measurable φ := hφsm.continuous.measurable
  have hsu := smoothOpen_u α u G h
  have hP2nn : ∀ z : ℝ, 0 ≤ ∫ θ in Iθ, (u z θ) ^ 2 := fun z => integral_nonneg fun θ => sq_nonneg _
  -- ### 1. the profiles and their finiteness
  -- the truncated mass
  have hMint : MeasureTheory.IntegrableOn (fun z => φ z * (Work.Spaces.w z) ^ 2
      * (∫ θ in Iθ, (u z θ) ^ 2)) Iz :=
    integrableOn_phi_wSq_P2 hφm hφ0 hφ1 hP2nn (aesm_P2 α u G h) hP
  -- the source profile without `σ`
  have hG2aesm : AEStronglyMeasurable (fun z => ∫ θ in Iθ, (G z θ) ^ 2)
      (MeasureTheory.volume.restrict Iz) :=
    aesm_profile_of_cont ((continuousOn_G α u G h).pow 2)
  have hS2int : MeasureTheory.IntegrableOn (fun z => φ z * (Work.Spaces.w z) ^ 2
      * (∫ θ in Iθ, (G z θ) ^ 2)) Iz := by
    have haesm : AEStronglyMeasurable (fun z => φ z * (Work.Spaces.w z) ^ 2
        * (∫ θ in Iθ, (G z θ) ^ 2)) (MeasureTheory.volume.restrict Iz) :=
      ((hφm.mul Work.FTS.EllipticEst.Honest.measurable_wSq).aestronglyMeasurable).mul hG2aesm
    refine hSs.mono' haesm ?_
    filter_upwards [ae_pos_Iz] with z hz
    have hw2 : 0 ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
    have h2 : 0 ≤ ∫ θ in Iθ, (G z θ) ^ 2 := integral_nonneg fun θ => sq_nonneg _
    have hle : (∫ θ in Iθ, (G z θ) ^ 2) ≤ ∫ θ in Iθ, (G z θ) ^ 2 * sg θ :=
      slice_sq_le_sigma h.memG hz
        (Work.Spaces.aesm_slice_of_continuousOn_Qd _ ((continuousOn_G α u G h).pow 2) hz)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (mul_nonneg (hφ0 z) hw2) h2)]
    calc φ z * (Work.Spaces.w z) ^ 2 * (∫ θ in Iθ, (G z θ) ^ 2)
        = φ z * ((Work.Spaces.w z) ^ 2 * (∫ θ in Iθ, (G z θ) ^ 2)) := by ring
      _ ≤ φ z * ((Work.Spaces.w z) ^ 2 * (∫ θ in Iθ, (G z θ) ^ 2 * sg θ)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hle hw2) (hφ0 z)
      _ = φ z * (Work.Spaces.w z) ^ 2 * (∫ θ in Iθ, (G z θ) ^ 2 * sg θ) := by ring
  -- the `Lzero`-pairing profile
  have hL2aesm : AEStronglyMeasurable
      (fun z => ∫ θ in Iθ, Work.Elliptic.Lzero u z θ * u z θ)
      (MeasureTheory.volume.restrict Iz) :=
    aesm_profile_of_cont (continuousOn_Lzero_mul α u G h)
  have hLint : MeasureTheory.IntegrableOn (fun z => φ z * (Work.Spaces.w z) ^ 2
      * (∫ θ in Iθ, Work.Elliptic.Lzero u z θ * u z θ)) Iz := by
    have haesm : AEStronglyMeasurable (fun z => φ z * (Work.Spaces.w z) ^ 2
        * (∫ θ in Iθ, Work.Elliptic.Lzero u z θ * u z θ))
        (MeasureTheory.volume.restrict Iz) :=
      ((hφm.mul Work.FTS.EllipticEst.Honest.measurable_wSq).aestronglyMeasurable).mul hL2aesm
    refine hLabs.mono' haesm ?_
    filter_upwards with z
    have hw2 : 0 ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
    have hle : |∫ θ in Iθ, Work.Elliptic.Lzero u z θ * u z θ|
        ≤ ∫ θ in Iθ, |Work.Elliptic.Lzero u z θ * u z θ| :=
      MeasureTheory.abs_integral_le_integral_abs
    have h0 : 0 ≤ ∫ θ in Iθ, |Work.Elliptic.Lzero u z θ * u z θ| :=
      integral_nonneg fun θ => abs_nonneg _
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (mul_nonneg (hφ0 z) hw2)]
    exact mul_le_mul_of_nonneg_left hle (mul_nonneg (hφ0 z) hw2)
  -- the `θ`-energy profile
  have hPth2aesm : AEStronglyMeasurable (fun z => ∫ θ in Iθ, (Work.Spaces.pth u z θ) ^ 2)
      (MeasureTheory.volume.restrict Iz) :=
    aesm_profile_of_cont ((hsu.pth.forall 0).continuousOn.pow 2)
  have hBint : MeasureTheory.IntegrableOn (fun z => φ z * (Work.Spaces.w z) ^ 2
      * (∫ θ in Iθ, (Work.Spaces.pth u z θ) ^ 2)) Iz := by
    have hmaj : MeasureTheory.IntegrableOn (fun z => φ z * (Work.Spaces.w z) ^ 2
        * (∫ θ in Iθ, Work.Elliptic.Lzero u z θ * u z θ)
          + 6 * (φ z * (Work.Spaces.w z) ^ 2 * (∫ θ in Iθ, (u z θ) ^ 2))) Iz :=
      hLint.add (hMint.const_mul 6)
    have haesm : AEStronglyMeasurable (fun z => φ z * (Work.Spaces.w z) ^ 2
        * (∫ θ in Iθ, (Work.Spaces.pth u z θ) ^ 2)) (MeasureTheory.volume.restrict Iz) :=
      ((hφm.mul Work.FTS.EllipticEst.Honest.measurable_wSq).aestronglyMeasurable).mul hPth2aesm
    refine hmaj.mono' haesm ?_
    filter_upwards [hSL, hSLnn] with z hz hznn
    have hw2 : 0 ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
    have hb0 : 0 ≤ ∫ θ in Iθ, (Work.Spaces.pth u z θ) ^ 2 :=
      integral_nonneg fun θ => sq_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (mul_nonneg (hφ0 z) hw2) hb0)]
    calc φ z * (Work.Spaces.w z) ^ 2 * (∫ θ in Iθ, (Work.Spaces.pth u z θ) ^ 2)
        ≤ φ z * (Work.Spaces.w z) ^ 2
            * ((∫ θ in Iθ, Work.Elliptic.Lzero u z θ * u z θ)
              + 6 * (∫ θ in Iθ, (u z θ) ^ 2)) :=
          mul_le_mul_of_nonneg_left hz (mul_nonneg (hφ0 z) hw2)
      _ = φ z * (Work.Spaces.w z) ^ 2 * (∫ θ in Iθ, Work.Elliptic.Lzero u z θ * u z θ)
            + 6 * (φ z * (Work.Spaces.w z) ^ 2 * (∫ θ in Iθ, (u z θ) ^ 2)) := by ring
  -- ### 2. the truncation-error integrabilities
  have hE1int : MeasureTheory.IntegrableOn (fun z => (2 * |deriv φ z|
      * |deriv (fun x : ℝ => x ^ 2 * (Work.Spaces.w x) ^ 2) z|
      + |deriv (deriv φ) z| * (z ^ 2 * (Work.Spaces.w z) ^ 2))
      * (∫ θ in Iθ, (u z θ) ^ 2)) Iz :=
    integrableOn_truncErr_E1 α u G h φ hC1 hC2 hP
  have hE2int : MeasureTheory.IntegrableOn (fun z => |deriv φ z|
      * (z * (Work.Spaces.w z) ^ 2) * (∫ θ in Iθ, (u z θ) ^ 2)) Iz :=
    integrableOn_truncErr_E2 α u G h φ hC1 hP
  -- ### 3. the four comparisons
  have hBL : (∫ z in Iz, φ z * (Work.Spaces.w z) ^ 2
        * (∫ θ in Iθ, (Work.Spaces.pth u z θ) ^ 2))
      ≤ (∫ z in Iz, φ z * (Work.Spaces.w z) ^ 2
          * (∫ θ in Iθ, Work.Elliptic.Lzero u z θ * u z θ))
        + 6 * (∫ z in Iz, φ z * (Work.Spaces.w z) ^ 2
          * (∫ θ in Iθ, (u z θ) ^ 2)) := by
    have hmaj : MeasureTheory.IntegrableOn (fun z => φ z * (Work.Spaces.w z) ^ 2
        * (∫ θ in Iθ, Work.Elliptic.Lzero u z θ * u z θ)
          + 6 * (φ z * (Work.Spaces.w z) ^ 2 * (∫ θ in Iθ, (u z θ) ^ 2))) Iz :=
      hLint.add (hMint.const_mul 6)
    have hle : (fun z => φ z * (Work.Spaces.w z) ^ 2
          * (∫ θ in Iθ, (Work.Spaces.pth u z θ) ^ 2))
        ≤ᵐ[MeasureTheory.volume.restrict Iz]
        (fun z => φ z * (Work.Spaces.w z) ^ 2
          * (∫ θ in Iθ, Work.Elliptic.Lzero u z θ * u z θ)
            + 6 * (φ z * (Work.Spaces.w z) ^ 2 * (∫ θ in Iθ, (u z θ) ^ 2))) := by
      filter_upwards [hSL] with z hz
      have hw2 : 0 ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
      calc φ z * (Work.Spaces.w z) ^ 2 * (∫ θ in Iθ, (Work.Spaces.pth u z θ) ^ 2)
          ≤ φ z * (Work.Spaces.w z) ^ 2
              * ((∫ θ in Iθ, Work.Elliptic.Lzero u z θ * u z θ)
                + 6 * (∫ θ in Iθ, (u z θ) ^ 2)) :=
            mul_le_mul_of_nonneg_left hz (mul_nonneg (hφ0 z) hw2)
        _ = φ z * (Work.Spaces.w z) ^ 2 * (∫ θ in Iθ, Work.Elliptic.Lzero u z θ * u z θ)
              + 6 * (φ z * (Work.Spaces.w z) ^ 2 * (∫ θ in Iθ, (u z θ) ^ 2)) := by ring
    have hmain := integral_mono_ae hBint hmaj hle
    rw [integral_add hLint (hMint.const_mul 6), integral_const_mul] at hmain
    exact hmain
  have hGu : (∫ z in Iz, φ z * (Work.Spaces.w z) ^ 2 * (∫ θ in Iθ, G z θ * u z θ))
      ≤ (1 / 2) * (∫ z in Iz, φ z * (Work.Spaces.w z) ^ 2
          * (∫ θ in Iθ, (G z θ) ^ 2))
        + (1 / 2) * (∫ z in Iz, φ z * (Work.Spaces.w z) ^ 2
          * (∫ θ in Iθ, (u z θ) ^ 2)) :=
    trunc_A_le α u G h hφ0 hMint hS2int
  have hGas : (∫ z in Iz, φ z * (Work.Spaces.w z) ^ 2 * (∫ θ in Iθ, (G z θ) ^ 2))
      ≤ (∫ z in Iz, φ z * (Work.Spaces.w z) ^ 2
          * (∫ θ in Iθ, (G z θ) ^ 2 * sg θ)) := by
    refine Work.FTS.EllipticEst.Honest.setIntegral_le_of_ae_le_of_nonneg ?_ ?_ hSs
    · filter_upwards [ae_pos_Iz] with z hz
      have hw2 : 0 ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
      have hle : (∫ θ in Iθ, (G z θ) ^ 2) ≤ ∫ θ in Iθ, (G z θ) ^ 2 * sg θ :=
        slice_sq_le_sigma h.memG hz
          (Work.Spaces.aesm_slice_of_continuousOn_Qd _ ((continuousOn_G α u G h).pow 2) hz)
      calc φ z * (Work.Spaces.w z) ^ 2 * (∫ θ in Iθ, (G z θ) ^ 2)
          = φ z * ((Work.Spaces.w z) ^ 2 * (∫ θ in Iθ, (G z θ) ^ 2)) := by ring
        _ ≤ φ z * ((Work.Spaces.w z) ^ 2 * (∫ θ in Iθ, (G z θ) ^ 2 * sg θ)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hle hw2) (hφ0 z)
        _ = φ z * (Work.Spaces.w z) ^ 2 * (∫ θ in Iθ, (G z θ) ^ 2 * sg θ) := by ring
    · filter_upwards with z
      refine mul_nonneg (mul_nonneg (hφ0 z) (sq_nonneg _)) ?_
      refine MeasureTheory.integral_nonneg_of_ae ?_
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
      exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg
        (Work.FTS.EllipticEst.Honest.sin_two_nonneg_of_mem_Iθ hθ) _)
  have hB2 := trunc_B2_le φ (fun z => ∫ θ in Iθ, (u z θ) ^ 2) hφsm hφ0 hP2nn hE1int hMint
  have hB1 := trunc_B1_le φ (fun z => ∫ θ in Iθ, (u z θ) ^ 2) hφsm hφ0 hP2nn hE2int hMint
  -- ### 4. rewriting the left-hand side of the identity along `bslOp α u = G`
  have hAconv : (∫ z in Iz, φ z * (Work.Spaces.w z) ^ 2
        * (∫ θ in Iθ, (z * Work.Spaces.pz u z θ) ^ 2))
      = ∫ z in Iz, φ z * (Work.Spaces.w z) ^ 2 * z ^ 2
          * (∫ θ in Iθ, (Work.Spaces.pz u z θ) ^ 2) := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    show φ z * (Work.Spaces.w z) ^ 2 * (∫ θ in Iθ, (z * Work.Spaces.pz u z θ) ^ 2)
      = φ z * (Work.Spaces.w z) ^ 2 * z ^ 2 * (∫ θ in Iθ, (Work.Spaces.pz u z θ) ^ 2)
    have hinner : (∫ θ in Iθ, (z * Work.Spaces.pz u z θ) ^ 2)
        = z ^ 2 * (∫ θ in Iθ, (Work.Spaces.pz u z θ) ^ 2) := by
      rw [show (fun θ => (z * Work.Spaces.pz u z θ) ^ 2)
          = fun θ => z ^ 2 * (Work.Spaces.pz u z θ) ^ 2 from by funext θ; ring]
      rw [integral_const_mul]
    rw [hinner]; ring
  have hLHSG : (∫ z in Iz, φ z * (Work.Spaces.w z) ^ 2
        * (∫ θ in Iθ, Work.Elliptic.bslOp α u z θ * u z θ))
      = ∫ z in Iz, φ z * (Work.Spaces.w z) ^ 2 * (∫ θ in Iθ, G z θ * u z θ) := by
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [ae_pos_Iz] with z hz
    show φ z * (Work.Spaces.w z) ^ 2
        * (∫ θ in Iθ, Work.Elliptic.bslOp α u z θ * u z θ)
      = φ z * (Work.Spaces.w z) ^ 2 * (∫ θ in Iθ, G z θ * u z θ)
    congr 1
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [ae_Ioo_Iθ] with θ hθ
    rw [h.eq z hz θ hθ.1 hθ.2]
  rw [hLHSG] at hid
  -- ### 5. the arithmetic
  have hα2 : (0:ℝ) ≤ α ^ 2 / 2 := by positivity
  have hα5 : (0:ℝ) ≤ α * (5 + α) / 2 := by nlinarith [h.hα]
  have hGas2 : (1 / 2) * (∫ z in Iz, φ z * (Work.Spaces.w z) ^ 2
        * (∫ θ in Iθ, (G z θ) ^ 2))
      ≤ (1 / 2) * (∫ z in Iz, φ z * (Work.Spaces.w z) ^ 2
        * (∫ θ in Iθ, (G z θ) ^ 2 * sg θ)) :=
    mul_le_mul_of_nonneg_left hGas (by norm_num)
  have hE2b := mul_le_mul_of_nonneg_left hB2 hα2
  have hE1b := mul_le_mul_of_nonneg_left hB1 hα5
  nlinarith [hid, hAconv, hGu, hGas2, hE2b, hE1b, hBL]

end Work.FTS.EllipticEst.Prop.CutEnergyAux
