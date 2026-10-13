/-
Copyright: work module for the Elgindi finite-time singularity project.

# The truncated `w²`-energy inequality in the a.e. class: the final assembly

This module proves the `Prop` `Work.FTS.EllipticEst.Cores.Pieces.AeGradRho.AeCutEnergyProp`, i.e.
the truncated `w²`-weighted energy inequality of Step 1 of Elgindi's `prop:H2` in the
almost-everywhere class `AeData`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllipticEst.Prop.CutEnergyAux.profiles
import Submission.Work.FTS.EllipticEst.Cores.Pieces.AeGradRho.AeCutEnergyClean

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

local notation "Iθ" => Work.Spaces.Iθ
local notation "Iz" => Work.Spaces.Iz
local notation "sg" => Work.FTS.EllipticEst.sEta

namespace Work.FTS.EllipticEst.Prop.CutEnergyAux

set_option autoImplicit false
set_option maxHeartbeats 3200000

/-- The `Lzero`-pairing profile is integrable (from its absolute version). -/
theorem integrableOn_Lprof (α : ℝ) (u G : ℝ → ℝ → ℝ)
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) (φ : ℝ → ℝ) (hφm : Measurable φ)
    (hφ0 : ∀ z : ℝ, 0 ≤ φ z)
    (hLabs : MeasureTheory.IntegrableOn (fun z => φ z * (Work.Spaces.w z) ^ 2
      * (∫ θ in Iθ, |Work.Elliptic.Lzero u z θ * u z θ|)) Iz) :
    MeasureTheory.IntegrableOn (fun z => φ z * (Work.Spaces.w z) ^ 2
      * (∫ θ in Iθ, Work.Elliptic.Lzero u z θ * u z θ)) Iz := by
  have haesm : AEStronglyMeasurable (fun z => φ z * (Work.Spaces.w z) ^ 2
      * (∫ θ in Iθ, Work.Elliptic.Lzero u z θ * u z θ))
      (MeasureTheory.volume.restrict Iz) :=
    ((hφm.mul Work.FTS.EllipticEst.Honest.measurable_wSq).aestronglyMeasurable).mul
      (aesm_profile_of_cont (continuousOn_Lzero_mul α u G h))
  refine hLabs.mono' haesm ?_
  filter_upwards with z
  have hw2 : 0 ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
  have hle : |∫ θ in Iθ, Work.Elliptic.Lzero u z θ * u z θ|
      ≤ ∫ θ in Iθ, |Work.Elliptic.Lzero u z θ * u z θ| :=
    MeasureTheory.abs_integral_le_integral_abs
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (mul_nonneg (hφ0 z) hw2)]
  exact mul_le_mul_of_nonneg_left hle (mul_nonneg (hφ0 z) hw2)

/-- The `θ`-energy profile is integrable (from the angular slice estimate
`∫_θ (∂_θu·w)² ≤ (π/2)²∫_θ HkIntegrand α 0 (∂_θθu)`). -/
theorem integrableOn_pthProf (α : ℝ) (u G : ℝ → ℝ → ℝ)
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) (φ : ℝ → ℝ) (hφm : Measurable φ)
    (hφ0 : ∀ z : ℝ, 0 ≤ φ z) (hφ1 : ∀ z : ℝ, φ z ≤ 1)
    (hC : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      ContinuousOn (fun θ => u z θ) (Set.Icc 0 (Real.pi / 2))) :
    MeasureTheory.IntegrableOn (fun z => φ z * (Work.Spaces.w z) ^ 2
      * (∫ θ in Iθ, (Work.Spaces.pth u z θ) ^ 2)) Iz := by
  obtain ⟨hint, -⟩ := Work.FTS.EllipticEst.Honest.hksq_eq_w2_sliceIntegral h.memAng2
  have hIoi : MeasureTheory.volume.restrict Iz
      = MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)) :=
    MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := 0)).symm
  have hbound := Work.FTS.EllipticEst.H2W.Ae.aeData_ang_slice_bound α u G h hC
  rw [← hIoi] at hbound
  have haesm : AEStronglyMeasurable (fun z => φ z * (Work.Spaces.w z) ^ 2
      * (∫ θ in Iθ, (Work.Spaces.pth u z θ) ^ 2)) (MeasureTheory.volume.restrict Iz) :=
    ((hφm.mul Work.FTS.EllipticEst.Honest.measurable_wSq).aestronglyMeasurable).mul
      (aesm_profile_of_cont ((smoothOpen_u α u G h).pth.forall 0 |>.continuousOn.pow 2))
  refine (hint.const_mul ((Real.pi / 2) ^ 2)).mono' haesm ?_
  filter_upwards [hbound, ae_pos_Iz] with z hz hzpos
  have h1 : (∫ θ in Iθ, (Work.Spaces.pth u z θ * Work.Spaces.w z) ^ 2)
      = Work.Spaces.w z ^ 2 * (∫ θ in Iθ, (Work.Spaces.pth u z θ) ^ 2) := by
    rw [show (fun θ => (Work.Spaces.pth u z θ * Work.Spaces.w z) ^ 2)
        = fun θ => Work.Spaces.w z ^ 2 * (Work.Spaces.pth u z θ) ^ 2 from by
      funext θ; ring]
    rw [integral_const_mul]
  have h2 : (∫ θ in Iθ, Work.Spaces.HkIntegrand α 0 (Work.Spaces.pthIter 2 u) z θ)
      = Work.Spaces.w z ^ 2 * (∫ θ in Iθ, (Work.Spaces.pthIter 2 u z θ) ^ 2 * sg θ) := by
    rw [← integral_const_mul]
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
    exact hkIntegrand_zero_eq' α (Work.Spaces.pthIter 2 u) hθ
  have h4 : 0 ≤ ∫ θ in Iθ, (Work.Spaces.pth u z θ) ^ 2 :=
    integral_nonneg fun θ => sq_nonneg _
  have hw2 : 0 ≤ Work.Spaces.w z ^ 2 := sq_nonneg _
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (mul_nonneg (hφ0 z) hw2) h4)]
  calc φ z * (Work.Spaces.w z) ^ 2 * (∫ θ in Iθ, (Work.Spaces.pth u z θ) ^ 2)
      = φ z * ((Work.Spaces.w z) ^ 2 * (∫ θ in Iθ, (Work.Spaces.pth u z θ) ^ 2)) := by ring
    _ ≤ 1 * ((Work.Spaces.w z) ^ 2 * (∫ θ in Iθ, (Work.Spaces.pth u z θ) ^ 2)) :=
        mul_le_mul_of_nonneg_right (hφ1 z) (mul_nonneg hw2 h4)
    _ = (Work.Spaces.w z) ^ 2 * (∫ θ in Iθ, (Work.Spaces.pth u z θ) ^ 2) := one_mul _
    _ = (∫ θ in Iθ, (Work.Spaces.pth u z θ * Work.Spaces.w z) ^ 2) := h1.symm
    _ ≤ (Real.pi / 2) ^ 2 * (∫ θ in Iθ, Work.Spaces.HkIntegrand α 0
          (Work.Spaces.pthIter 2 u) z θ) := hz
    _ = (Real.pi / 2) ^ 2 * (Work.Spaces.w z ^ 2
          * (∫ θ in Iθ, (Work.Spaces.pthIter 2 u z θ) ^ 2 * sg θ)) := by rw [h2]

/-- The `∫⁻`-to-Bochner conversion, with the nonnegativity of the inner integrand required only
a.e. on the angular interval (the source slot `G²σ` is nonnegative only there). -/
theorem lintegralConv_ae (W : ℝ → ℝ) (f : ℝ → ℝ → ℝ) (hW : ∀ z : ℝ, 0 ≤ W z)
    (hf : ∀ z : ℝ, ∀ᵐ θ ∂(MeasureTheory.volume.restrict Iθ), 0 ≤ f z θ)
    (hslice : ∀ᵐ z ∂(MeasureTheory.volume.restrict Iz),
      MeasureTheory.IntegrableOn (fun θ => f z θ) Iθ)
    (hout : MeasureTheory.IntegrableOn
      (fun z => W z * (∫ θ in Iθ, f z θ)) Iz) :
    (∫⁻ z in Iz, ENNReal.ofReal (W z) * (∫⁻ θ in Iθ, ENNReal.ofReal (f z θ)))
      = ENNReal.ofReal (∫ z in Iz, W z * (∫ θ in Iθ, f z θ)) := by
  have hsl' : (fun z => ENNReal.ofReal (∫ θ in Iθ, f z θ))
      =ᵐ[MeasureTheory.volume.restrict Iz]
      (fun z => ∫⁻ θ in Iθ, ENNReal.ofReal (f z θ)) :=
    hslice.mono fun z hz =>
      MeasureTheory.ofReal_integral_eq_lintegral_ofReal hz (hf z)
  have h1 : (∫⁻ z in Iz, ENNReal.ofReal (W z) * (∫⁻ θ in Iθ, ENNReal.ofReal (f z θ)))
      = ∫⁻ z in Iz, ENNReal.ofReal (W z) * ENNReal.ofReal (∫ θ in Iθ, f z θ) :=
    MeasureTheory.lintegral_congr_ae (hsl'.symm.mono fun z hz =>
      congrArg (fun t => ENNReal.ofReal (W z) * t) hz)
  have h2 : (∫⁻ z in Iz, ENNReal.ofReal (W z) * ENNReal.ofReal (∫ θ in Iθ, f z θ))
      = ∫⁻ z in Iz, ENNReal.ofReal (W z * ∫ θ in Iθ, f z θ) :=
    MeasureTheory.lintegral_congr fun z => (ENNReal.ofReal_mul (hW z)).symm
  rw [h1, h2]
  exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hout
    (Filter.Eventually.of_forall fun z => mul_nonneg (hW z)
      (MeasureTheory.integral_nonneg_of_ae (hf z)))).symm

end Work.FTS.EllipticEst.Prop.CutEnergyAux

namespace Work.FTS.EllipticEst.Prop.CutEnergyAux

/-- **The truncated `w²`-energy inequality in the almost-everywhere class** (Elgindi, Annals 194
(2021), Step 1 of `prop:H2`). -/
theorem aeCutEnergyProp_holds (α : ℝ) (u G : ℝ → ℝ → ℝ) :
    Work.FTS.EllipticEst.Cores.Pieces.AeGradRho.AeCutEnergyProp α u G := by
  intro h hL0 hLπ φ hφsm hcpt hφ0 hφnn hφ1 hφδ hM
  -- ## 1. the a.e. slice facts
  have hC := ae_continuousOn_slice α u G h hL0 hLπ
  have hφm : Measurable φ := hφsm.continuous.measurable
  have hsl := ae_slice_ineq α u G h hC
  have hSL : ∀ᵐ z ∂(MeasureTheory.volume.restrict Iz),
      (∫ θ in Iθ, (Work.Spaces.pth u z θ) ^ 2)
        ≤ (∫ θ in Iθ, Work.Elliptic.Lzero u z θ * u z θ) + 6 * (∫ θ in Iθ, (u z θ) ^ 2) :=
    hsl.mono fun z hz => hz.1
  have hSLnn : ∀ᵐ z ∂(MeasureTheory.volume.restrict Iz),
      0 ≤ (∫ θ in Iθ, Work.Elliptic.Lzero u z θ * u z θ) + 6 * (∫ θ in Iθ, (u z θ) ^ 2) :=
    hsl.mono fun z hz => hz.2
  -- ## 2. the finiteness of the profiles
  have hP := integrableOn_mass_unt α u G h
  have hX := integrableOn_radialProf α u G h φ hφm hφnn hφ1
  have hSs := integrableOn_srcProf α u G h φ hφm hφnn hφ1
  have hLabs := lzeroProfInt α u G h φ hφm hφnn hφ1
  have hLint := integrableOn_Lprof α u G h φ hφm hφnn hLabs
  have hBint := integrableOn_pthProf α u G h φ hφm hφnn hφ1 hC
  have hMint : MeasureTheory.IntegrableOn (fun z => φ z * (Work.Spaces.w z) ^ 2
      * (∫ θ in Iθ, (u z θ) ^ 2)) Iz :=
    integrableOn_phi_wSq_P2 hφm hφnn hφ1 (fun z => integral_nonneg fun θ => sq_nonneg _)
      (aesm_P2 α u G h) hP
  obtain ⟨hC1, hC2⟩ := deriv_mul_bdd φ hφsm hφδ hcpt
  -- ## 3. the truncated energy identity
  have hslice := Work.FTS.EllipticEst.AeS1.aeSliceConds α u G h hC
  have hε : ∃ ε : ℝ, 0 < ε ∧ ∀ z ∈ Set.Icc 0 ε, φ z = 0 := by
    obtain ⟨δ, hδpos, hδ0⟩ := hφδ
    exact ⟨δ, hδpos, fun z hz => hδ0 z hz.2⟩
  have hid := Work.FTS.EllipticEst.H2W.AeW.aeTruncWHon α u G h (fun n => h.smooth n)
    (Work.FTS.EllipticEst.Dispatch.hkMem_uM α u G h)
    (Work.FTS.EllipticEst.Dispatch.hkMem_gradUD α u G h) φ hφsm hcpt hε hslice
  -- ## 4. the real-variable inequality
  have hreal := aeCutEnergy_real α u G h φ hφsm hφnn hφ1 hC1 hC2 hSL hSLnn hP hX hSs hLabs hid
  -- ## 5. the a.e. angular square integrabilities
  have hIoi : MeasureTheory.volume.restrict Iz
      = MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)) :=
    MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := 0)).symm
  have hpzSq : ∀ᵐ z ∂(MeasureTheory.volume.restrict Iz),
      MeasureTheory.IntegrableOn (fun θ => (Work.Spaces.pz u z θ) ^ 2) Iθ := by
    rw [hIoi]
    exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi
      (fun z hz => (sliceFacts α u G h z hz).2.2.2.2.2.2.1)
  have huSq : ∀ᵐ z ∂(MeasureTheory.volume.restrict Iz),
      MeasureTheory.IntegrableOn (fun θ => (u z θ) ^ 2) Iθ := by
    rw [hIoi]
    exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi
      (fun z hz => (sliceFacts α u G h z hz).2.2.2.2.2.1)
  have hGSig : ∀ᵐ z ∂(MeasureTheory.volume.restrict Iz),
      MeasureTheory.IntegrableOn (fun θ => (G z θ) ^ 2 * sg θ) Iθ := by
    rw [hIoi]
    exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi
      (fun z hz => (sliceFacts α u G h z hz).2.2.2.2.2.2.2.2.2.1)
  have hpthSq := ae_slice_pth_sq_finite α u G h hC
  have hsg : ∀ z : ℝ, ∀ᵐ θ ∂(MeasureTheory.volume.restrict Iθ), 0 ≤ sg θ := fun z =>
    (ae_Ioo_Iθ).mono fun θ hθ => le_trans zero_le_one
      (Work.FTS.EllipticEst.Honest.one_le_sEta hθ)
  -- ## 6. the Bochner profiles
  set Aℝ := ∫ z in Iz, φ z * (Work.Spaces.w z) ^ 2 * z ^ 2
      * (∫ θ in Iθ, (Work.Spaces.pz u z θ) ^ 2) with hAℝ
  set Bℝ := ∫ z in Iz, φ z * (Work.Spaces.w z) ^ 2
      * (∫ θ in Iθ, (Work.Spaces.pth u z θ) ^ 2) with hBℝ
  set Mℝ := ∫ z in Iz, φ z * (Work.Spaces.w z) ^ 2
      * (∫ θ in Iθ, (u z θ) ^ 2) with hMℝ
  set Fℝ := ∫ z in Iz, φ z * (Work.Spaces.w z) ^ 2
      * (∫ θ in Iθ, (G z θ) ^ 2 * sg θ) with hFℝ
  set Err := (α ^ 2 / 2) * (∫ z in Iz, (2 * |deriv φ z|
        * |deriv (fun z => z ^ 2 * (Work.Spaces.w z) ^ 2) z|
        + |deriv (deriv φ) z| * (z ^ 2 * (Work.Spaces.w z) ^ 2))
        * (∫ θ in Iθ, (u z θ) ^ 2))
      + (α * (5 + α) / 2) * (∫ z in Iz, |deriv φ z| * (z * (Work.Spaces.w z) ^ 2)
        * (∫ θ in Iθ, (u z θ) ^ 2)) with hErr
  -- ## 7. the `∫⁻`-to-Bochner conversions
  have hconvA : (∫⁻ z in Iz, ENNReal.ofReal (φ z * (Work.Spaces.w z) ^ 2 * z ^ 2)
        * (∫⁻ θ in Iθ, ENNReal.ofReal ((Work.Spaces.pz u z θ) ^ 2)))
      = ENNReal.ofReal Aℝ := by
    rw [hAℝ]
    exact lintegralConv_ae (fun z => φ z * (Work.Spaces.w z) ^ 2 * z ^ 2)
      (fun z θ => (Work.Spaces.pz u z θ) ^ 2)
      (fun z => mul_nonneg (mul_nonneg (hφnn z) (sq_nonneg _)) (sq_nonneg _))
      (fun z => Filter.Eventually.of_forall fun θ => sq_nonneg _) hpzSq hX
  have hconvB : (∫⁻ z in Iz, ENNReal.ofReal (φ z * (Work.Spaces.w z) ^ 2)
        * (∫⁻ θ in Iθ, ENNReal.ofReal ((Work.Spaces.pth u z θ) ^ 2)))
      = ENNReal.ofReal Bℝ := by
    rw [hBℝ]
    exact lintegralConv_ae (fun z => φ z * (Work.Spaces.w z) ^ 2)
      (fun z θ => (Work.Spaces.pth u z θ) ^ 2)
      (fun z => mul_nonneg (hφnn z) (sq_nonneg _))
      (fun z => Filter.Eventually.of_forall fun θ => sq_nonneg _) hpthSq hBint
  have hconvM : (∫⁻ z in Iz, ENNReal.ofReal (φ z * (Work.Spaces.w z) ^ 2)
        * (∫⁻ θ in Iθ, ENNReal.ofReal ((u z θ) ^ 2)))
      = ENNReal.ofReal Mℝ := by
    rw [hMℝ]
    exact lintegralConv_ae (fun z => φ z * (Work.Spaces.w z) ^ 2)
      (fun z θ => (u z θ) ^ 2)
      (fun z => mul_nonneg (hφnn z) (sq_nonneg _))
      (fun z => Filter.Eventually.of_forall fun θ => sq_nonneg _) huSq hMint
  have hconvF : (∫⁻ z in Iz, ENNReal.ofReal (φ z * (Work.Spaces.w z) ^ 2)
        * (∫⁻ θ in Iθ, ENNReal.ofReal ((G z θ) ^ 2 * sg θ)))
      = ENNReal.ofReal Fℝ := by
    rw [hFℝ]
    exact lintegralConv_ae (fun z => φ z * (Work.Spaces.w z) ^ 2)
      (fun z θ => (G z θ) ^ 2 * sg θ)
      (fun z => mul_nonneg (hφnn z) (sq_nonneg _))
      (fun z => (hsg z).mono fun θ hθ => mul_nonneg (sq_nonneg _) hθ) hGSig hSs
  -- ## 8. the nonnegativity facts
  have hA0 : 0 ≤ Aℝ := integral_nonneg fun z => mul_nonneg (mul_nonneg (mul_nonneg (hφnn z)
    (sq_nonneg _)) (sq_nonneg _)) (integral_nonneg fun θ => sq_nonneg _)
  have hB0 : 0 ≤ Bℝ := integral_nonneg fun z => mul_nonneg (mul_nonneg (hφnn z)
    (sq_nonneg _)) (integral_nonneg fun θ => sq_nonneg _)
  have hM0 : 0 ≤ Mℝ := integral_nonneg fun z => mul_nonneg (mul_nonneg (hφnn z)
    (sq_nonneg _)) (integral_nonneg fun θ => sq_nonneg _)
  have hF0 : 0 ≤ Fℝ := integral_nonneg fun z => mul_nonneg (mul_nonneg (hφnn z)
    (sq_nonneg _)) (MeasureTheory.integral_nonneg_of_ae (by
      filter_upwards [ae_Ioo_Iθ] with θ hθ
      exact mul_nonneg (sq_nonneg _) (le_trans zero_le_one
        (Work.FTS.EllipticEst.Honest.one_le_sEta hθ))))
  have hK0 : 0 ≤ 13 / 2 + (3 * α ^ 2 + (3 / 2) * α * (5 + α)) := by
    nlinarith [h.hα]
  have hErrA0 : 0 ≤ (∫ z in Iz, (2 * |deriv φ z|
      * |deriv (fun z => z ^ 2 * (Work.Spaces.w z) ^ 2) z|
      + |deriv (deriv φ) z| * (z ^ 2 * (Work.Spaces.w z) ^ 2))
      * (∫ θ in Iθ, (u z θ) ^ 2)) :=
    MeasureTheory.setIntegral_nonneg measurableSet_Ici fun z hz =>
      mul_nonneg (add_nonneg (mul_nonneg (by positivity) (abs_nonneg _))
        (mul_nonneg (abs_nonneg _) (mul_nonneg (sq_nonneg _) (sq_nonneg _))))
        (integral_nonneg fun θ => sq_nonneg _)
  have hErrB0 : 0 ≤ (∫ z in Iz, |deriv φ z| * (z * (Work.Spaces.w z) ^ 2)
      * (∫ θ in Iθ, (u z θ) ^ 2)) :=
    MeasureTheory.setIntegral_nonneg measurableSet_Ici fun z hz =>
      mul_nonneg (mul_nonneg (abs_nonneg _) (mul_nonneg hz (sq_nonneg _)))
        (integral_nonneg fun θ => sq_nonneg _)
  have hErr0 : 0 ≤ Err := by
    rw [hErr]
    exact add_nonneg (mul_nonneg (by positivity) hErrA0)
      (mul_nonneg (by nlinarith [h.hα]) hErrB0)
  -- ## 9. the final transfer
  have hreal' : α ^ 2 * Aℝ + Bℝ ≤ (13 / 2 + (3 * α ^ 2 + (3 / 2) * α * (5 + α))) * Mℝ
      + (1 / 2) * Fℝ + Err := by
    rw [hErr]
    have h0 := hreal
    rw [show (13 / 2 + 3 * α ^ 2 + (3 / 2) * α * (5 + α))
        = (13 / 2 + (3 * α ^ 2 + (3 / 2) * α * (5 + α))) from by ring] at h0
    linarith [h0]
  have hLHS : ENNReal.ofReal (α ^ 2)
        * (∫⁻ z in Iz, ENNReal.ofReal (φ z * (Work.Spaces.w z) ^ 2 * z ^ 2)
            * (∫⁻ θ in Iθ, ENNReal.ofReal ((Work.Spaces.pz u z θ) ^ 2)))
      + (∫⁻ z in Iz, ENNReal.ofReal (φ z * (Work.Spaces.w z) ^ 2)
          * (∫⁻ θ in Iθ, ENNReal.ofReal ((Work.Spaces.pth u z θ) ^ 2)))
      = ENNReal.ofReal (α ^ 2 * Aℝ + Bℝ) := by
    rw [hconvA, hconvB, ← ENNReal.ofReal_mul (sq_nonneg α),
      ← ENNReal.ofReal_add (mul_nonneg (sq_nonneg α) hA0) hB0]
  have e1 : ENNReal.ofReal (13 / 2 + (3 * α ^ 2 + (3 / 2) * α * (5 + α)))
        * (∫⁻ z in Iz, ENNReal.ofReal (φ z * (Work.Spaces.w z) ^ 2)
          * (∫⁻ θ in Iθ, ENNReal.ofReal ((u z θ) ^ 2)))
      = ENNReal.ofReal ((13 / 2 + (3 * α ^ 2 + (3 / 2) * α * (5 + α))) * Mℝ) := by
    rw [hconvM, ← ENNReal.ofReal_mul hK0]
  have e2 : ENNReal.ofReal (1 / 2)
        * (∫⁻ z in Iz, ENNReal.ofReal (φ z * (Work.Spaces.w z) ^ 2)
          * (∫⁻ θ in Iθ, ENNReal.ofReal ((G z θ) ^ 2 * sg θ)))
      = ENNReal.ofReal ((1 / 2) * Fℝ) := by
    rw [hconvF, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  have e3 : ENNReal.ofReal ((α ^ 2 / 2) * (∫ z in Iz, (2 * |deriv φ z|
          * |deriv (fun z => z ^ 2 * (Work.Spaces.w z) ^ 2) z|
          + |deriv (deriv φ) z| * (z ^ 2 * (Work.Spaces.w z) ^ 2))
          * (∫ θ in Iθ, (u z θ) ^ 2))
        + (α * (5 + α) / 2) * (∫ z in Iz, |deriv φ z| * (z * (Work.Spaces.w z) ^ 2)
          * (∫ θ in Iθ, (u z θ) ^ 2)))
      = ENNReal.ofReal Err := by
    rw [← hErr]
  have hRHS : ENNReal.ofReal (13 / 2 + (3 * α ^ 2 + (3 / 2) * α * (5 + α)))
        * (∫⁻ z in Iz, ENNReal.ofReal (φ z * (Work.Spaces.w z) ^ 2)
          * (∫⁻ θ in Iθ, ENNReal.ofReal ((u z θ) ^ 2)))
      + ENNReal.ofReal (1 / 2)
        * (∫⁻ z in Iz, ENNReal.ofReal (φ z * (Work.Spaces.w z) ^ 2)
          * (∫⁻ θ in Iθ, ENNReal.ofReal ((G z θ) ^ 2 * sg θ)))
      + ENNReal.ofReal Err
      = ENNReal.ofReal ((13 / 2 + (3 * α ^ 2 + (3 / 2) * α * (5 + α))) * Mℝ
          + (1 / 2) * Fℝ + Err) := by
    rw [← e3, e1, e2,
      ENNReal.ofReal_add (add_nonneg (mul_nonneg hK0 hM0)
        (mul_nonneg (by norm_num) hF0)) hErr0,
      ENNReal.ofReal_add (mul_nonneg hK0 hM0) (mul_nonneg (by norm_num) hF0)]
  calc ENNReal.ofReal (α ^ 2)
        * (∫⁻ z in Iz, ENNReal.ofReal (φ z * (Work.Spaces.w z) ^ 2 * z ^ 2)
            * (∫⁻ θ in Iθ, ENNReal.ofReal ((Work.Spaces.pz u z θ) ^ 2)))
      + (∫⁻ z in Iz, ENNReal.ofReal (φ z * (Work.Spaces.w z) ^ 2)
          * (∫⁻ θ in Iθ, ENNReal.ofReal ((Work.Spaces.pth u z θ) ^ 2)))
      = ENNReal.ofReal (α ^ 2 * Aℝ + Bℝ) := hLHS
    _ ≤ ENNReal.ofReal ((13 / 2 + (3 * α ^ 2 + (3 / 2) * α * (5 + α))) * Mℝ
          + (1 / 2) * Fℝ + Err) := ENNReal.ofReal_le_ofReal hreal'
    _ = ENNReal.ofReal (13 / 2 + (3 * α ^ 2 + (3 / 2) * α * (5 + α)))
          * (∫⁻ z in Iz, ENNReal.ofReal (φ z * (Work.Spaces.w z) ^ 2)
            * (∫⁻ θ in Iθ, ENNReal.ofReal ((u z θ) ^ 2)))
        + ENNReal.ofReal (1 / 2)
          * (∫⁻ z in Iz, ENNReal.ofReal (φ z * (Work.Spaces.w z) ^ 2)
            * (∫⁻ θ in Iθ, ENNReal.ofReal ((G z θ) ^ 2 * sg θ)))
        + ENNReal.ofReal Err := hRHS.symm

end Work.FTS.EllipticEst.Prop.CutEnergyAux
