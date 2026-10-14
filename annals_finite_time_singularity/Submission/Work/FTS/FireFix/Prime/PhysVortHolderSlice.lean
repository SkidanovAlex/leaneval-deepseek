import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.MetricSpace.Holder
import Submission.Work.FTS.FireFix.Prime.profFullHolder
import Submission.Work.FTS.H2.hard_sq_prod_z
import Submission.Work.FTS.LocDataExt.Zfar5
import Submission.Work.FTS.RegPkgGal.R7d.chain_rule_along_curve
import Submission.Work.FTS.RegPkgGal.RVocab
import Submission.Work.FTS.StrongEps.EComparison.SlotsZeroSliceInt
import Submission.Work.FTS.StrongGlobal.Transfer
import Submission.Work.FTS_MuLipC.RowN.FaSlice
import Submission.Work.R1G.DecayInZ_gA
import Submission.Work.R1G.vecResid_eq_scalar_smul
import Submission.Work.SolutionDelivery.DatumEuler
import Submission.Work.SolutionDelivery.DatumOdd

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FiniteTimeSingularity Set Gradient Matrix Filter Topology MeasureTheory
open scoped Topology Matrix NNReal ENNReal

set_option autoImplicit false

namespace Work.FTS.FireFix.Prime

open Work.FTS.Regularity Work.FTS.RegPkgGal

/-! ## 5. The target: the physical vorticity slices are `α`-Hölder, uniformly on `[0,S]` -/

theorem physVort_holder_slice {α S : ℝ} {A B : ℝ → ℝ} {g : ℝ → ℝ → ℝ → ℝ}
    (h : Work.FTS.RegPkgGal.RegPkg' α S A B g) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ τ ∈ Set.Icc 0 S, ∀ x y : Work.FTS.Regularity.R3,
      ‖Work.FTS.Regularity.physVort α A B g x τ - Work.FTS.Regularity.physVort α A B g y τ‖
        ≤ C * ‖x - y‖ ^ α := by
  have hα : 0 < α := h.hα
  have hα13 : α ≤ 1 / 3 := h.hα13
  have hα1 : α ≤ 1 := by linarith
  obtain ⟨Cv, hCv0, hvan⟩ := h.hvan
  obtain ⟨Ng, hJet⟩ := h.hg
  have hLg : 0 ≤ Ng := hJet.1
  obtain ⟨K, hK0, htay⟩ := h.htay
  obtain ⟨a₀, a₁, ha₀, hab⟩ := h.hAb
  obtain ⟨b₀, b₁, hb₀, hbb⟩ := h.hBb
  obtain ⟨Cω, hCω⟩ := Work.ConstructionInstance.holder_omegaStar (β := α) hα hα1
  set CωS := omegaSHolderConst α Cv Ng Ng K Cω with hCωS
  have hslice : ∀ τ ∈ Set.Icc 0 S, HolderWith CωS (⟨α, hα.le⟩ : NNReal)
      (Work.ConstructionInstance.omegaS (3 * α) (gSlice g τ)) := by
    intro τ hτ
    exact omegaS_holder_dev hα hα13 hCv0 hLg hLg hK0 (h.hvt τ hτ)
      (fun θ hθ => h.hquad0 τ hτ θ hθ)
      (fun z θ hz hθ => hvan τ hτ z θ hz hθ)
      (fun z z' θ hz hz' hθ => hJet.zmod hz hz' hθ hτ)
      (fun z θ θ' hz hθ hθ' => hJet.thmod hz hθ hθ' hτ)
      (fun z θ hz hz2 hθ => (htay τ hτ θ hθ).1 z hz hz2)
      (fun z z' θ hz hz2 hz' hz'2 hθ => (htay τ hτ θ hθ).2.1 z z' hz hz2 hz' hz'2)
      (fun z θ θ' hz hz2 hθ hθ' => (htay τ hτ θ hθ).2.2 z hz hz2 θ' hθ')
      (fun θ hθ z hz hz1 => by
        have h1 := (htay τ hτ θ hθ).1 z hz (le_trans hz1 (by norm_num))
        have h2 : z ^ 2 ≤ z := by nlinarith
        exact le_trans h1 (mul_le_mul_of_nonneg_left h2 hK0))
      hCω
  set bmax : ℝ := (b₀⁻¹) ^ (1 / (3 * α)) with hbmax
  have hbmaxnn : 0 ≤ bmax := Real.rpow_nonneg (inv_nonneg.mpr hb₀.le) _
  refine ⟨a₀⁻¹ * (CωS : ℝ) * bmax ^ α, ?_, ?_⟩
  · have h1 : 0 ≤ a₀⁻¹ := inv_nonneg.mpr ha₀.le
    have h2 : 0 ≤ (CωS : ℝ) := CωS.coe_nonneg
    exact mul_nonneg (mul_nonneg h1 h2) (Real.rpow_nonneg hbmaxnn _)
  · intro τ hτ x y
    have hAτ : a₀ ≤ A τ := (hab τ hτ).1
    have hApos : 0 < A τ := lt_of_lt_of_le ha₀ hAτ
    have hBτ : b₀ ≤ B τ := (hbb τ hτ).1
    have hBpos : 0 < B τ := lt_of_lt_of_le hb₀ hBτ
    set b : ℝ := (B τ)⁻¹ ^ (1 / (3 * α)) with hb
    have hbpos : 0 < b := Real.rpow_pos_of_pos (inv_pos.mpr hBpos) _
    have hbp : b ^ (3 * α) = (B τ)⁻¹ := by
      rw [hb, ← Real.rpow_mul (inv_nonneg.mpr hBpos.le) (1 / (3 * α)) (3 * α),
        div_mul_cancel₀ 1 (by positivity : (3:ℝ) * α ≠ 0), Real.rpow_one]
    have hble : b ≤ bmax :=
      Real.rpow_le_rpow (inv_nonneg.mpr hBpos.le)
        ((inv_le_inv₀ hBpos hb₀).mpr hBτ) (by positivity)
    have hid : ∀ z : R3, Work.ConstructionInstance.omegaSz (3 * α) (gSlice g τ)
        (Work.Cyl.rho z ^ (3 * α) / B τ) z
        = Work.ConstructionInstance.omegaS (3 * α) (gSlice g τ) (b • z) := by
      intro z
      have hzb : Work.Cyl.rho (b • z) ^ (3 * α) = Work.Cyl.rho z ^ (3 * α) / B τ := by
        rw [rho_smul_dev hbpos.le z, Real.mul_rpow hbpos.le (Work.Cyl.rho_nonneg z), hbp,
          div_eq_mul_inv, mul_comm]
      rw [Work.ConstructionInstance.omegaS_apply', Work.ConstructionInstance.omegaSz_apply,
        theta_smul_dev hbpos z, eTheta_smul_dev hbpos z, hzb]
    have hH := (hslice τ hτ).dist_le (b • x) (b • y)
    rw [dist_eq_norm, dist_eq_norm] at hH
    have hH' : ‖Work.ConstructionInstance.omegaS (3 * α) (gSlice g τ) (b • x)
        - Work.ConstructionInstance.omegaS (3 * α) (gSlice g τ) (b • y)‖
        ≤ (CωS : ℝ) * ‖b • x - b • y‖ ^ α := hH
    have hbxy : ‖b • x - b • y‖ = b * ‖x - y‖ := by
      rw [← smul_sub, norm_smul, Real.norm_of_nonneg hbpos.le]
    rw [hbxy, Real.mul_rpow hbpos.le (norm_nonneg (x - y))] at hH'
    have hbα : b ^ α ≤ bmax ^ α := Real.rpow_le_rpow hbpos.le hble hα.le
    have hCt : 0 ≤ ‖x - y‖ ^ α := Real.rpow_nonneg (norm_nonneg _) _
    have hcore : (CωS : ℝ) * b ^ α * ‖x - y‖ ^ α ≤ (CωS : ℝ) * bmax ^ α * ‖x - y‖ ^ α := by
      have h1 : (CωS : ℝ) * b ^ α ≤ (CωS : ℝ) * bmax ^ α :=
        mul_le_mul_of_nonneg_left hbα CωS.coe_nonneg
      exact mul_le_mul_of_nonneg_right h1 hCt
    have hinv : (A τ)⁻¹ ≤ a₀⁻¹ := (inv_le_inv₀ hApos ha₀).mpr hAτ
    have hAi : 0 ≤ (A τ)⁻¹ := inv_nonneg.mpr hApos.le
    calc ‖Work.FTS.Regularity.physVort α A B g x τ
            - Work.FTS.Regularity.physVort α A B g y τ‖
        = ‖(A τ)⁻¹ • (Work.ConstructionInstance.omegaSz (3 * α) (gSlice g τ)
              (Work.Cyl.rho x ^ (3 * α) / B τ) x)
            - (A τ)⁻¹ • (Work.ConstructionInstance.omegaSz (3 * α) (gSlice g τ)
              (Work.Cyl.rho y ^ (3 * α) / B τ) y)‖ := by
            rw [Work.FTS.Regularity.physVort_apply, Work.FTS.Regularity.physVort_apply,
              Work.FTS.Regularity.pExp_eq]
      _ = ‖(A τ)⁻¹ • (Work.ConstructionInstance.omegaSz (3 * α) (gSlice g τ)
              (Work.Cyl.rho x ^ (3 * α) / B τ) x
            - Work.ConstructionInstance.omegaSz (3 * α) (gSlice g τ)
              (Work.Cyl.rho y ^ (3 * α) / B τ) y)‖ := by
            rw [smul_sub]
      _ = |(A τ)⁻¹| * ‖Work.ConstructionInstance.omegaSz (3 * α) (gSlice g τ)
              (Work.Cyl.rho x ^ (3 * α) / B τ) x
            - Work.ConstructionInstance.omegaSz (3 * α) (gSlice g τ)
              (Work.Cyl.rho y ^ (3 * α) / B τ) y‖ := by
            rw [norm_smul, Real.norm_eq_abs]
      _ = (A τ)⁻¹ * ‖Work.ConstructionInstance.omegaSz (3 * α) (gSlice g τ)
              (Work.Cyl.rho x ^ (3 * α) / B τ) x
            - Work.ConstructionInstance.omegaSz (3 * α) (gSlice g τ)
              (Work.Cyl.rho y ^ (3 * α) / B τ) y‖ := by
            rw [abs_of_nonneg hAi]
      _ = (A τ)⁻¹ * ‖Work.ConstructionInstance.omegaS (3 * α) (gSlice g τ) (b • x)
            - Work.ConstructionInstance.omegaS (3 * α) (gSlice g τ) (b • y)‖ := by
            rw [hid x, hid y]
      _ ≤ (A τ)⁻¹ * ((CωS : ℝ) * b ^ α * ‖x - y‖ ^ α) := by
            apply mul_le_mul_of_nonneg_left _ hAi
            calc ‖Work.ConstructionInstance.omegaS (3 * α) (gSlice g τ) (b • x)
                  - Work.ConstructionInstance.omegaS (3 * α) (gSlice g τ) (b • y)‖
                ≤ (CωS : ℝ) * (b ^ α * ‖x - y‖ ^ α) := hH'
              _ = (CωS : ℝ) * b ^ α * ‖x - y‖ ^ α := by ring
      _ ≤ a₀⁻¹ * ((CωS : ℝ) * bmax ^ α * ‖x - y‖ ^ α) := by
            have hc0 : 0 ≤ (CωS : ℝ) * b ^ α * ‖x - y‖ ^ α :=
              mul_nonneg (mul_nonneg CωS.coe_nonneg (Real.rpow_nonneg hbpos.le _)) hCt
            exact mul_le_mul hinv hcore hc0 (inv_nonneg.mpr ha₀.le)
      _ = a₀⁻¹ * (CωS : ℝ) * bmax ^ α * ‖x - y‖ ^ α := by ring



end Work.FTS.FireFix.Prime