import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKaux.Standing
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKaux.L12Calc
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKaux.FKDeriv

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_RegExport.RXT.Sys.L12FKaux

/-- **Uniform bound of `L₁₂` on a fake-time horizon.**

`L₁₂` is a *limit* (`L12_tendsto`) of the `L₁₂` of the approximating profiles
`F(n) = F_* + slice (gn n) τ`, and each approximant obeys the elementary bound
`abs_L12_Fstar_add_le` with the constant `Cw = Cd · (C₀ · (pExp α)²)`, where `Cd` is the constant
of the interior weighted `L^∞`–`ℋ⁴` trade-off `RXA1w.abs_mixed_le_HkNorm_C4_w_proved`: the
reference part of the profile contributes `2·pExp α`, the perturbation part `3(π/2)·Cw·3`.
Neither constant depends on `τ` (only the class-`C` membership and the `ℋ⁴`-smallness
`Xn (slice (gn n) τ) ≤ C₀·(pExp α)²`, both uniform on `[0,T]`, are used), so the bound transfers
to the limit along `n → ∞`.  (This is the third clause of `L12FK_family_jets`, isolated.)

The same argument is used elsewhere in the workspace (`L12FK_family_jets`), where the third clause
of the conclusion is exactly this estimate. -/
theorem L12_limit_bound {α C₀ : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn}
    {g : Work.FTS.Galerkin.Fam}
    (hA : Work.FTS.FinalV2.LimApprox (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    (T : ℝ) (hT : 0 < T) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ z : ℝ, 0 < z →
      |Work.Construction.L12 (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
        (Work.FTS.RegExportIface.RXT.GR α g) τ) z| ≤ C := by
  obtain ⟨gn, B, L, hC, hLip, hjet, hmu⟩ := hA T hT
  have hβ : 0 < Work.FTS.Regularity.pExp α := Work.FTS.Regularity.pExp_pos hα
  have hβ1 : Work.FTS.Regularity.pExp α ≤ 1 := Work.FTS.Regularity.pExp_le_one hα13
  obtain ⟨Cd, hCd0, hCd⟩ := Work.FTS_RegExport.RXA1w.abs_mixed_le_HkNorm_C4_w_proved hβ hβ1
  have hmem0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) T := ⟨le_rfl, hT.le⟩
  have hC0β : 0 ≤ C₀ * (Work.FTS.Regularity.pExp α) ^ 2 :=
    le_trans (Work.Spaces.HkNorm_nonneg (Work.FTS.Regularity.pExp α) 4
        (Work.FTS.Galerkin.slice (gn 0) 0)) (hC 0 0 hmem0).2.1
  refine ⟨2 * Work.FTS.Regularity.pExp α
      + 3 * (Real.pi / 2) * (Cd * (C₀ * (Work.FTS.Regularity.pExp α) ^ 2)) * 3, ?_, ?_⟩
  · have h1 : 0 ≤ Cd * (C₀ * (Work.FTS.Regularity.pExp α) ^ 2) := mul_nonneg hCd0 hC0β
    nlinarith [hβ, h1, Real.pi_pos]
  · intro τ hτ z hz
    -- the standing slot bound of the approximants, uniform in `n`
    have hbd : ∀ (n : ℕ) (k : ℕ), k ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        |Work.Spaces.DzIter k (Work.FTS.Galerkin.slice (gn n) τ) z θ|
          ≤ (Cd * (C₀ * (Work.FTS.Regularity.pExp α) ^ 2))
            * Work.FTS_RegExport.RXT.Sys.L12FKaux.SW z := by
      intro n k hk z θ hz' h0 h1
      have hcl := (hC n τ hτ).1
      have h1' := hCd _ (hcl.reg.forall 4) (Work.FTS.ClassC.classC_hkMem_four hcl)
        (Work.FTS.ClassC.bdryTraces_mono (by norm_num) hcl.tr) k 0 (by omega) z θ hz' h0 h1
      rw [Work.Spaces.mixed_zero_right] at h1'
      have h2 : Work.Spaces.HkNorm (Work.FTS.Regularity.pExp α) 4
          (Work.FTS.Galerkin.slice (gn n) τ)
          ≤ C₀ * (Work.FTS.Regularity.pExp α) ^ 2 := (hC n τ hτ).2.1
      calc |Work.Spaces.DzIter k (Work.FTS.Galerkin.slice (gn n) τ) z θ|
          ≤ Cd * Work.FTS_RegExport.RXT.Sys.L12FKaux.SW z
              * Work.Spaces.HkNorm (Work.FTS.Regularity.pExp α) 4
                (Work.FTS.Galerkin.slice (gn n) τ) := h1'
        _ ≤ Cd * Work.FTS_RegExport.RXT.Sys.L12FKaux.SW z
              * (C₀ * (Work.FTS.Regularity.pExp α) ^ 2) :=
            mul_le_mul_of_nonneg_left h2
              (mul_nonneg hCd0 (Work.FTS_RegExport.RXT.Sys.L12FKaux.SW_nonneg hz'.le))
        _ = (Cd * (C₀ * (Work.FTS.Regularity.pExp α) ^ 2))
              * Work.FTS_RegExport.RXT.Sys.L12FKaux.SW z := by ring
    -- pointwise convergence of the slices to those of the limit family `GR α g`
    have hconv : ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
        Filter.Tendsto (fun n => Work.FTS.Galerkin.slice (gn n) τ z θ) Filter.atTop
          (nhds (Work.FTS.Galerkin.slice (Work.FTS.RegExportIface.RXT.GR α g) τ z θ)) := by
      intro z θ hzθ
      have h := hjet τ hτ 0 0 (by norm_num) z θ hzθ
      have hGR := Work.FTS_RegExport.RXT.ftau_GR_of_quad (α := α) (g := g) hτ.1 hzθ.1
        hzθ.2.1.le hzθ.2.2.le
      simpa only [Work.Spaces.mixed_zero_right, Work.Spaces.DzIter_zero,
        Work.FTS.Galerkin.slice_apply, hGR] using h
    -- pass to the limit in `L₁₂`
    have htend := Work.FTS_RegExport.RXT.Sys.L12FKaux.L12_tendsto
      (β := Work.FTS.Regularity.pExp α) hβ hβ1 (mul_nonneg hCd0 hC0β)
      (fun n => (hC n τ hτ).1.reg.forall 4) hbd hconv hz
    refine le_of_tendsto htend.abs (Filter.Eventually.of_forall fun n => ?_)
    exact Work.FTS_RegExport.RXT.Sys.L12FKaux.abs_L12_Fstar_add_le
      (β := Work.FTS.Regularity.pExp α) hβ hβ1 (mul_nonneg hCd0 hC0β)
      ((hC n τ hτ).1.reg.forall 4) (Work.FTS.ClassC.classC_hkMem_four (hC n τ hτ).1)
      (fun k hk => hbd n k hk) hz

end Work.FTS_RegExport.RXT.Sys.L12FKaux

end
