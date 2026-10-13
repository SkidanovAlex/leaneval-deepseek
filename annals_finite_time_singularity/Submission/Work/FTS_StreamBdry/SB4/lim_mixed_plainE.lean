import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS_RegExport.RXA1w.abs_mixed_le_HkNorm_C4_w_proved
import Submission.Work.FTS.FinalV2.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_StreamBdry.SB4

theorem lim_mixed_plainE {αG C₀ : ℝ} (hα : 0 < αG) (hα1 : αG ≤ 1)
    {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn}
    {g : Work.FTS.Galerkin.Fam}
    (hA : Work.FTS.FinalV2.LimApprox αG C₀ Φs E g) (T : ℝ) (hT : 0 < T) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ b a : ℕ, a + b ≤ 2 →
      ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        |Work.Spaces.mixed b a (Work.FTS.Galerkin.slice g τ) z θ|
          ≤ C * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2) := by
  -- the interior trade-off: `|mixed b a f| ≤ Cw · z^{3/2}/(1+z)² · |f|_{ℋ⁴}`
  obtain ⟨Cw, hCw0, hCw⟩ :=
    Work.FTS_RegExport.RXA1w.abs_mixed_le_HkNorm_C4_w_proved hα hα1
  -- the `LimApprox` clause at the horizon `T`
  obtain ⟨gn, B, L, hC, -, hjet, -⟩ := hA T hT
  have hT0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) T := ⟨le_rfl, hT.le⟩
  have hX0 : 0 ≤ Work.FTS.Nonlin.Xn αG (Work.FTS.Galerkin.slice (gn 0) 0) :=
    Work.Spaces.HkNorm_nonneg αG 4 _
  have hC0sq : 0 ≤ C₀ * αG ^ 2 := le_trans hX0 (hC 0 0 hT0).2.1
  refine ⟨Cw * (C₀ * αG ^ 2), mul_nonneg hCw0 hC0sq, ?_⟩
  intro τ hτ b a hab z θ hz hθ0 hθ1
  have hw0 : 0 ≤ z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2 :=
    div_nonneg (Real.rpow_nonneg hz.le _) (by positivity)
  -- the existential constant of the approximating sequence is uniform in `n`
  have hbound : ∀ n : ℕ,
      |Work.Spaces.mixed b a (Work.FTS.Galerkin.slice (gn n) τ) z θ|
        ≤ Cw * (C₀ * αG ^ 2) * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2) := by
    intro n
    have hcls : Work.FTS.ClassC.ClassC αG (Work.FTS.Galerkin.slice (gn n) τ) := (hC n τ hτ).1
    have h4 : ContDiffOn ℝ 4 (Function.uncurry (Work.FTS.Galerkin.slice (gn n) τ))
        Work.FTS.EllipticEst.Q0 :=
      (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp hcls.reg 4
    have hmem : Work.Spaces.HkMem αG 4 (Work.FTS.Galerkin.slice (gn n) τ) :=
      Work.FTS.OpenPkg.HkMem_mono_open hcls.reg 4 (by norm_num) hcls.mem
    have htr : Work.FTS.Nonlin.BdryTraces αG 4 (Work.FTS.Galerkin.slice (gn n) τ) :=
      Work.FTS.ClassC.bdryTraces_mono (by norm_num) hcls.tr
    have h1 := hCw _ h4 hmem htr b a hab z θ hz hθ0 hθ1
    have h2 : Work.Spaces.HkNorm αG 4 (Work.FTS.Galerkin.slice (gn n) τ) ≤ C₀ * αG ^ 2 :=
      (hC n τ hτ).2.1
    calc |Work.Spaces.mixed b a (Work.FTS.Galerkin.slice (gn n) τ) z θ|
        ≤ Cw * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2)
            * Work.Spaces.HkNorm αG 4 (Work.FTS.Galerkin.slice (gn n) τ) := h1
      _ ≤ Cw * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2) * (C₀ * αG ^ 2) :=
          mul_le_mul_of_nonneg_left h2 (mul_nonneg hCw0 hw0)
      _ = Cw * (C₀ * αG ^ 2) * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2) := by ring
  have hzθ : (z, θ) ∈ Work.Construction.Qd := ⟨hz, hθ0, hθ1⟩
  exact le_of_tendsto ((hjet τ hτ b a (by omega) z θ hzθ).abs)
    (Filter.Eventually.of_forall hbound)

end Work.FTS_StreamBdry.SB4
