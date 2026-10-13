import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS_RegExport.RXT.Sys.slot_tau_cont_alpha

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.THL

open scoped Real Topology
open Set Filter

open Work.FTS.Galerkin (Fn Fam slice)

/-!
# `cs7_rop_split` — the additive split of the `ℛ`-slot of the modulated residual

On the open quadrant the modulated residual `Φ̃_τ = v2_PhiT α Φs E g τ` splits as the star residual
`Φ̃_* = PhiTs (pExp α) Φs` plus the perturbation residual `PhiTil (slice g τ) (E (slice g τ))`
(`v2_phiTil_split`), and `Rop` is additive on `C¹` pieces (`v2_rop_add_at`).  This is the
`Rop`-half of the clean split; it is what `cs7_theta_holder` (A6) consumes. -/

theorem cs7_rop_split {α C₀ Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hEL3 : Work.FTS.FinalV2.EllLimOK3 (Work.FTS.Regularity.pExp α) E)
    (hStar : Work.FTS.Final.StarPkgo2 (Work.FTS.Regularity.pExp α) Cs Φs)
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g) :
    ∀ τ : ℝ, 0 ≤ τ → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Construction.Rop (Work.FTS.Regularity.pExp α)
          (Work.FTS_RegExport.RXT.v2_PhiT α Φs E g τ) z θ
        = Work.Construction.Rop (Work.FTS.Regularity.pExp α)
            (Work.FTS.VocabO2.PhiTs (Work.FTS.Regularity.pExp α) Φs) z θ
          + Work.Construction.Rop (Work.FTS.Regularity.pExp α)
            (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α)
              (Work.FTS.Galerkin.slice g τ) (E (Work.FTS.Galerkin.slice g τ))) z θ := by
  intro τ hτ z θ hz hθ hθ2
  have hαG : 0 < Work.FTS.Regularity.pExp α := Work.FTS.Regularity.pExp_pos hα
  have hαG1 : Work.FTS.Regularity.pExp α ≤ 1 := Work.FTS.Regularity.pExp_le_one hα13
  -- the star half is `C^∞` on the open quadrant, hence `C¹`
  have hStar3 : ContDiffOn ℝ 3 (Function.uncurry (Work.FTS_RegExport.RXT.v2_PhiStar α Φs))
      Work.FTS.EllipticEst.Q0 :=
    (Work.FTS.PhiStar.CoreAux.fields_smooth hαG hαG1 hStar.smooth).1.of_le
      (by simp [Work.Stability.smoothOrder])
  have hStar1 : ContDiffOn ℝ 1 (Function.uncurry (Work.FTS_RegExport.RXT.v2_PhiStar α Φs))
      Work.FTS.EllipticEst.Q0 := hStar3.of_le (by norm_num)
  -- the Θ-part of the modulated stream function
  have hTheta3 : ContDiffOn ℝ 3 (Function.uncurry
      (Work.Construction.Theta (Work.FTS.Regularity.pExp α)
        (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
          (Work.FTS.RegExportIface.RXT.GR α g) τ))) Work.FTS.EllipticEst.Q0 := by
    refine Work.FTS_RegExport.RXT.velPert_contDiffOn_Theta (α := Work.FTS.Regularity.pExp α) ?_
    refine Work.FTS_RegExport.RXT.contDiffOn_three_L12 ?_
    obtain ⟨C, _hC0, hCb⟩ := Work.FTS_RegExport.RXT.Ftau_bounds
      (Φs := Φs) (E := E) hα hα13 hOK τ hτ
    exact Work.FTS_RegExport.RXT.contDiffOn_two_integral_Itheta (φ := Work.Spaces.K)
      Work.FTS_RegExport.RXT.v2_continuousOn_K_Iθ
      (Work.FTS_RegExport.RXT.contDiffOn_Ftau_Q0 (Φs := Φs) (E := E) hα hα13 hOK τ hτ)
      (fun z₁ θ₁ hz₁ hθ₁ hθ₁2 => ⟨(hCb z₁ θ₁ hz₁ hθ₁ hθ₁2).1,
        (hCb z₁ θ₁ hz₁ hθ₁ hθ₁2).2.1, (hCb z₁ θ₁ hz₁ hθ₁ hθ₁2).2.2⟩)
  have hFull3 : ContDiffOn ℝ 3 (Function.uncurry (Work.FTS_RegExport.RXT.v2_PhiT α Φs E g τ))
      Work.FTS.EllipticEst.Q0 :=
    (Work.FTS_RegExport.RXT.contDiffOn_slice_PhiR_Q0 (α := α) (C₀ := C₀) (Cs := Cs)
      hEL3 hStar hOK τ hτ).sub hTheta3
  -- the perturbation residual, as the difference of the two
  have hPert3 : ContDiffOn ℝ 3 (Function.uncurry (Work.FTS_RegExport.RXT.v2_PhiPert α E g τ))
      Work.FTS.EllipticEst.Q0 := by
    refine (hFull3.sub hStar3).congr ?_
    intro p hp
    obtain ⟨z₁, θ₁⟩ := p
    simp only [Function.uncurry]
    linarith [Work.FTS_RegExport.RXT.v2_phiTil_split (C₀ := C₀) hα hα13 hOK hτ z₁ θ₁ hp]
  have hPert1 : ContDiffOn ℝ 1 (Function.uncurry (Work.FTS_RegExport.RXT.v2_PhiPert α E g τ))
      Work.FTS.EllipticEst.Q0 := hPert3.of_le (by norm_num)
  -- the pointwise split, as an `AgreeOnQ`
  have hsplitFun : Work.FTS_RegExport.RXR5.AgreeOnQ (Work.FTS_RegExport.RXT.v2_PhiT α Φs E g τ)
      (Work.FTS_RegExport.RXT.v2_PhiStar α Φs + Work.FTS_RegExport.RXT.v2_PhiPert α E g τ) :=
    fun z₁ θ₁ hz₁ hθ₁ hθ₁2 => Work.FTS_RegExport.RXT.v2_phiTil_split (C₀ := C₀) hα hα13 hOK hτ
      z₁ θ₁ (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz₁, hθ₁, hθ₁2⟩)
  rw [Work.FTS_RegExport.RXR5.Rop_congr_of_agreeOnQ
    (α := Work.FTS.Regularity.pExp α) (h := hsplitFun) hz hθ hθ2]
  exact Work.FTS_RegExport.RXT.v2_rop_add_at hStar1 hPert1 ⟨hz, hθ, hθ2⟩

end Work.FTS_RegExport.THL
