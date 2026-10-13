import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.RegExportIface.Defs
import Submission.Work.FTS_RegExport.THL.holder_of_deriv_sin_bound
import Submission.Work.Spaces.WlInf_terms
import Submission.Work.FTS.PhiStar.CoreAux.fields_smooth

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.THL

open MeasureTheory Set

theorem vopStar_theta_holder {αG Cs : ℝ} (hαG : 0 < αG) (hαG1 : αG ≤ 1)
    {Φs : Work.FTS.Galerkin.Fn} (hStar : Work.FTS.Final.StarPkgo2 αG Cs Φs) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℝ, 0 < z →
      ∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi / 2), ∀ θ' ∈ Set.Ioo (0:ℝ) (Real.pi / 2),
      |Work.Construction.Vop (Work.Construction.PhiTil αG (Work.Construction.Fstar αG) Φs) z θ
        - Work.Construction.Vop
            (Work.Construction.PhiTil αG (Work.Construction.Fstar αG) Φs) z θ'|
        ≤ C * |θ - θ'| ^ (αG / 5) := by
  set g : ℝ → ℝ → ℝ := Work.Construction.PhiTil αG (Work.Construction.Fstar αG) Φs with hg
  set f : ℝ → ℝ → ℝ := Work.Construction.Vop g with hf
  have hmem : Work.Spaces.WlInfMem αG 4 f := by
    rw [hf, hg]
    exact hStar.VW.1
  have hle : Work.Spaces.WlInf αG 4 f ≤ Cs * αG := by
    rw [hf, hg]
    exact hStar.VW.2
  have hsm : Work.FTS.EllipticEst.SmoothOpen f := by
    rw [hf, hg]
    exact (Work.FTS.PhiStar.CoreAux.fields_smooth hαG hαG1 hStar.smooth).2.2.1
  have hWnn : 0 ≤ Work.Spaces.WlInf αG 4 f := by
    rw [Work.Spaces.WlInf]
    exact add_nonneg (Work.Spaces.wlZSum_nonneg αG 4 f hmem)
      (Work.Spaces.wlThSum_nonneg αG 4 f hmem)
  have hCnn : 0 ≤ Cs * αG := le_trans hWnn hle
  have hp : 0 < αG / 5 := by linarith
  have hp1 : αG / 5 ≤ 1 := by linarith
  refine ⟨2 * (Real.pi / 4) ^ (1 - αG / 5) / (αG / 5) * (2 * (Cs * αG)), ?_, ?_⟩
  · have h1 : 0 ≤ (Real.pi / 4) ^ (1 - αG / 5) :=
      Real.rpow_nonneg (by linarith [Real.pi_pos]) _
    exact mul_nonneg (div_nonneg (mul_nonneg (by norm_num) h1) hp.le) (by linarith)
  · intro z hz θ hθ θ' hθ'
    have hs : ∀ x ∈ Set.Ioo (0:ℝ) (Real.pi / 2), 0 < Real.sin (2 * x) := by
      intro x hx
      exact Real.sin_pos_of_pos_of_lt_pi (by linarith [hx.1])
        (by linarith [Real.pi_pos, hx.2])
    have hderiv : ∀ x ∈ Set.Ioo (0:ℝ) (Real.pi / 2),
        HasDerivAt (fun θ' => f z θ') (Work.Spaces.pth f z x) x := by
      intro x hx
      have hc0 : ContDiffOn ℝ Work.Stability.smoothOrder (fun θ' => f z θ')
          (Set.Ioo (0:ℝ) (Real.pi / 2)) := hsm.curry_θ hz
      have hc : ContDiffOn ℝ 1 (fun θ' => f z θ') (Set.Ioo (0:ℝ) (Real.pi / 2)) :=
        hc0.of_le (WithTop.coe_le_coe.mpr le_top)
      have hd1 : DifferentiableOn ℝ (fun θ' => f z θ') (Set.Ioo (0:ℝ) (Real.pi / 2)) :=
        hc.differentiableOn one_ne_zero
      have hdiff : DifferentiableAt ℝ (fun θ' => f z θ') x :=
        hd1.differentiableAt (isOpen_Ioo.mem_nhds hx)
      simpa only [Work.Spaces.pth] using hdiff.hasDerivAt
    have hb : ∀ x ∈ Set.Ioo (0:ℝ) (Real.pi / 2),
        |Work.Spaces.pth f z x| ≤ (2 * (Cs * αG)) * Real.sin (2 * x) ^ (αG / 5 - 1) := by
      intro x hx
      have hsx : 0 < Real.sin (2 * x) := hs x hx
      have hxIθ : x ∈ Work.Spaces.Iθ := ⟨le_of_lt hx.1, le_of_lt hx.2⟩
      have hzIz : z ∈ Work.Spaces.Iz := le_of_lt hz
      have hD := Work.Spaces.pz_Dth_sup_bound αG hαG 4 f hmem 1 0 le_rfl (by norm_num)
        z x hzIz hxIθ
      simp only [Work.Spaces.pzIter_zero, Work.Spaces.DthIter_succ, Work.Spaces.DthIter_zero,
        pow_zero, div_one] at hD
      have hsnn : 0 ≤ Real.sin (2 * x) :=
        Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hx.1]) (by linarith [Real.pi_pos, hx.2])
      have hpos : 0 ≤ (αG + Real.sin (2 * x)) * Real.sin (2 * x) ^ (αG / 5) :=
        mul_nonneg (by linarith) (Real.rpow_nonneg hsx.le _)
      have h1 : |Work.Spaces.Dth f z x|
          ≤ (Cs * αG) * ((αG + Real.sin (2 * x)) * Real.sin (2 * x) ^ (αG / 5)) :=
        hD.trans (mul_le_mul_of_nonneg_right hle hpos)
      have h2 : αG + Real.sin (2 * x) ≤ 2 := by
        have := Real.sin_le_one (2 * x); linarith
      have hsin2nn : 0 ≤ Real.sin (2 * x) ^ (αG / 5) := Real.rpow_nonneg hsx.le _
      have h3 : |Work.Spaces.Dth f z x| ≤ (2 * (Cs * αG)) * Real.sin (2 * x) ^ (αG / 5) := by
        calc |Work.Spaces.Dth f z x|
            ≤ (Cs * αG) * ((αG + Real.sin (2 * x)) * Real.sin (2 * x) ^ (αG / 5)) := h1
          _ ≤ (Cs * αG) * (2 * Real.sin (2 * x) ^ (αG / 5)) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h2 hsin2nn) hCnn
          _ = (2 * (Cs * αG)) * Real.sin (2 * x) ^ (αG / 5) := by ring
      have hDth : |Work.Spaces.Dth f z x| = Real.sin (2 * x) * |Work.Spaces.pth f z x| := by
        simp only [Work.Spaces.Dth, abs_mul, abs_of_pos hsx]
      rw [hDth] at h3
      have hrp : Real.sin (2 * x) ^ (αG / 5) / Real.sin (2 * x)
          = Real.sin (2 * x) ^ (αG / 5 - 1) := by
        rw [Real.rpow_sub hsx, Real.rpow_one]
      calc |Work.Spaces.pth f z x|
          = (Real.sin (2 * x) * |Work.Spaces.pth f z x|) / Real.sin (2 * x) := by
            rw [mul_comm (Real.sin (2 * x)) (|Work.Spaces.pth f z x|),
              mul_div_cancel_right₀ (|Work.Spaces.pth f z x|) (ne_of_gt hsx)]
        _ ≤ ((2 * (Cs * αG)) * Real.sin (2 * x) ^ (αG / 5)) / Real.sin (2 * x) :=
            div_le_div_of_nonneg_right h3 hsx.le
        _ = (2 * (Cs * αG)) * (Real.sin (2 * x) ^ (αG / 5) / Real.sin (2 * x)) := by ring
        _ = (2 * (Cs * αG)) * Real.sin (2 * x) ^ (αG / 5 - 1) := by rw [hrp]
    exact holder_of_deriv_sin_bound hp hp1 (by linarith) hderiv hb θ hθ θ' hθ'

end Work.FTS_RegExport.THL
