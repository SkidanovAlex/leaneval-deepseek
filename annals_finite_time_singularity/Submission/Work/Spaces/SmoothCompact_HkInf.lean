/-
Copyright: work module for the Elgindi finite-time singularity project.

# Smooth, compactly supported functions lie in `ℋ^k ∩ 𝒲^{l,∞}`

T. M. Elgindi, *Finite-time singularity formation for `C^{1,α}` solutions to the
incompressible Euler equations on `ℝ³`*, Annals of Math. 194 (3) 2021.

A function which is smooth on a neighbourhood of the closed quadrant, compactly
supported, vanishing on the angular boundary and vanishing to second order in `z`
at `z = 0` belongs to `ℋ^k` and to `𝒲^{l,∞}` for all `k`, `l`, with finite norms.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.HkAux
import Submission.Work.Spaces.CurrySmooth
import Submission.Work.Spaces.mixed_comm
import Submission.Work.Spaces.WlInf_terms
import Submission.Work.Spaces.pth_integral
import Submission.Work.Spaces.HardyZ
import Submission.Work.Spaces.BoxBounds
import Submission.Work.Spaces.SinMinBounds
import Submission.Work.Spaces.SupportZ
import Submission.Work.Spaces.SmoothCompact_Aux
import Submission.Work.Spaces.SmoothCompact_HkMem

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Spaces

set_option autoImplicit false

/-- Membership in `ℋ^k` of a smooth compactly supported function. -/
theorem HkSq_le_of_bound (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) (R M : ℝ)
    (hR : 0 ≤ R) (hMnn : 0 ≤ M)
    (hf_gt : ∀ z θ : ℝ, R < z → f z θ = 0)
    (hbound : ∀ z ∈ Iz, ∀ θ ∈ Iθ, HkIntegrand α k f z θ ≤ M) :
    HkSq α k f ≤ M * (π / 2) * (R + 1) := by
  set g : ℝ → ℝ := (Set.Icc 0 R).indicator (fun _ => M * (π / 2)) with hg
  have hinner_le : ∀ z ∈ Iz, (∫ θ in Iθ, HkIntegrand α k f z θ) ≤ M * (π / 2) := by
    intro z hz
    have hz0le : (0 : ℝ) ≤ z := hz
    by_cases hzR : z ≤ R
    · calc (∫ θ in Iθ, HkIntegrand α k f z θ)
          ≤ |∫ θ in Iθ, HkIntegrand α k f z θ| := le_abs_self _
        _ = ‖∫ θ in Iθ, HkIntegrand α k f z θ‖ := (Real.norm_eq_abs _).symm
        _ ≤ M * (π / 2) := by
            rw [← volume_real_Iθ]
            refine norm_setIntegral_le_of_norm_le_const volume_Iθ_lt_top fun θ hθ => ?_
            rw [Real.norm_eq_abs]
            exact abs_le.mpr ⟨by linarith [HkIntegrand_nonneg α k f z θ, hMnn],
              hbound z hz θ hθ⟩
    · rw [show (fun θ => HkIntegrand α k f z θ) = fun _ => (0 : ℝ) from
        funext fun θ => HkIntegrand_eq_zero_of_gt α k f R z θ hf_gt (not_le.mp hzR)]
      simp only [integral_zero]
      exact mul_nonneg hMnn (by linarith [Real.pi_pos])
  have hgint : Integrable g (volume.restrict Iz) := by
    rw [hg]
    refine (MeasureTheory.integrable_indicator_iff measurableSet_Icc).mpr ?_
    have hfin : (volume.restrict Iz) (Set.Icc 0 R) ≠ ⊤ := by
      rw [Measure.restrict_apply measurableSet_Icc]
      have h1 : volume (Set.Icc 0 R ∩ Iz) ≤ volume (Set.Icc 0 R) :=
        measure_mono Set.inter_subset_left
      have h2 : volume (Set.Icc 0 R) < ⊤ := by
        rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top
      exact ne_of_lt (lt_of_le_of_lt h1 h2)
    exact MeasureTheory.integrableOn_const hfin
  have hle : (fun z => ∫ θ in Iθ, HkIntegrand α k f z θ) ≤ᵐ[volume.restrict Iz] g := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
    by_cases hzR : z ≤ R
    · rw [hg, Set.indicator_of_mem (show z ∈ Set.Icc 0 R from ⟨hz, hzR⟩)]
      exact hinner_le z hz
    · rw [hg, Set.indicator_of_notMem (by
        intro hmem
        exact absurd hmem.2 hzR)]
      rw [show (fun θ => HkIntegrand α k f z θ) = fun _ => (0 : ℝ) from
        funext fun θ => HkIntegrand_eq_zero_of_gt α k f R z θ hf_gt (not_le.mp hzR)]
      simp
  have hmain := MeasureTheory.integral_mono_of_nonneg
    (Eventually.of_forall fun z => integral_nonneg fun θ => HkIntegrand_nonneg α k f z θ) hgint hle
  have hgval : ∫ z, g z ∂(volume.restrict Iz) ≤ M * (π / 2) * (R + 1) := by
    rw [hg, MeasureTheory.integral_indicator measurableSet_Icc, MeasureTheory.setIntegral_const]
    rw [smul_eq_mul]
    have hmeas : (volume.restrict Iz).real (Set.Icc 0 R) ≤ R + 1 := by
      rw [MeasureTheory.measureReal_def, Measure.restrict_apply measurableSet_Icc]
      have hset : Set.Icc 0 R ∩ Iz = Set.Icc 0 R := by
        ext x
        constructor
        · intro hx; exact hx.1
        · intro hx; exact ⟨hx, hx.1⟩
      rw [hset, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]
      linarith
    have hMpi : 0 ≤ M * (π / 2) := mul_nonneg hMnn (by linarith [Real.pi_pos])
    nlinarith [hmeas, hMpi]
  rw [HkSq]
  exact le_trans hmain hgval

/-- A smooth compactly supported function belongs to `ℋ^k ∩ 𝒲^{l,∞}` and both norms
are finite. -/
theorem SmoothCompact_HkInf (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (k l : ℕ) (f : ℝ → ℝ → ℝ)
    (hsm : Work.Spaces.SmoothNbhd f) (hcomp : HasCompactSupport (Function.uncurry f))
    (hvan : Work.Spaces.VanishTheta f)
    (hz0 : ∀ θ ∈ Work.Spaces.Iθ, f 0 θ = 0 ∧ Work.Spaces.pz f 0 θ = 0) :
    Work.Spaces.HkMem α k f ∧ Work.Spaces.WlInfMem α l f ∧
      ∃ M : ℝ, Work.Spaces.HkSq α k f ≤ M ∧ Work.Spaces.WlInf α l f ≤ M := by
  obtain ⟨R, hR, hf_gt, -, -, -⟩ := SupportZ f hcomp
  obtain ⟨M, hMnn, hM⟩ := HkIntegrand_bound α hα hα1 k f R hR hsm hf_gt hvan hz0
  have hHk : HkMem α k f := HkMemSmoothCompact α hα hα1 k f R hR hsm hf_gt hvan hz0
  have hW := WlInfSmoothCompact α hα hα1 l f R hR hsm hf_gt hvan
  have hWnn : 0 ≤ WlInf α l f := by
    rw [WlInf]
    exact add_nonneg (wlZSum_nonneg α l f hW.1) (wlThSum_nonneg α l f hW.1)
  have hMpos : 0 ≤ M * (π / 2) * (R + 1) :=
    mul_nonneg (mul_nonneg hMnn (by linarith [Real.pi_pos])) (by linarith)
  refine ⟨hHk, hW.1, M * (π / 2) * (R + 1) + WlInf α l f, ?_, ?_⟩
  · exact le_trans (HkSq_le_of_bound α k f R M hR hMnn hf_gt hM) (le_add_of_nonneg_right hWnn)
  · exact le_add_of_nonneg_left hMpos

end Work.Spaces
