import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.FinalV2.Defs
import Submission.Work.FTS_RegExport.RXA1w.abs_mixed_le_HkNorm_C4_w_proved
import Submission.Work.FTS_RegExport.RXR1.classC_sub_hyp
import Submission.Work.FTS.RegExportIface.RXT.Leaves

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Topology

namespace Work.FTS_RegExport.RXT.Sys

/-- **RX-T weighted τ-modulus of the slice.**  The approximating families of `LimApprox` are
uniformly `τ`-Lipschitz for the `ℋ⁴`-norm, and the weighted interior `L^∞`–`ℋ⁴` trade-off
`abs_mixed_le_HkNorm_C4_w_proved` turns that into the pointwise weighted modulus
`z^{3/2}/(1+z)²`; the pointwise jet convergence on `Qd` passes the bound to the limit. -/
theorem slice_tau_modulus_weighted2 {α C₀ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn}
    {g : Work.FTS.Galerkin.Fam}
    (hA : Work.FTS.FinalV2.LimApprox α C₀ Φs E g) (T : ℝ) (hT : 0 < T) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ τ' ∈ Set.Icc (0 : ℝ) T,
      ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        |Work.FTS.Galerkin.slice g τ z θ - Work.FTS.Galerkin.slice g τ' z θ|
          ≤ L * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2) * |τ - τ'| := by
  obtain ⟨C, hC0, hC⟩ := Work.FTS_RegExport.RXA1w.abs_mixed_le_HkNorm_C4_w_proved hα hα1
  obtain ⟨gn, B, L, hclass, hlip, hconv, -⟩ := hA T hT
  refine ⟨C * max L 0, mul_nonneg hC0 (le_max_right L 0), ?_⟩
  intro τ hτ τ' hτ' z θ hz hθ hθ'
  have hQ : (z, θ) ∈ Work.Construction.Qd := ⟨hz, hθ, hθ'⟩
  have hkey : ∀ n : ℕ,
      |Work.FTS.Galerkin.slice (gn n) τ z θ - Work.FTS.Galerkin.slice (gn n) τ' z θ|
        ≤ C * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2) * (max L 0 * |τ - τ'|) := by
    intro n
    have hfτ : Work.FTS.ClassC.ClassC α (Work.FTS.Galerkin.slice (gn n) τ) :=
      (hclass n τ hτ).1
    have hfτ' : Work.FTS.ClassC.ClassC α (Work.FTS.Galerkin.slice (gn n) τ') :=
      (hclass n τ' hτ').1
    obtain ⟨hsm, hm, hb⟩ := Work.FTS_RegExport.RXR1.classC_sub_hyp hfτ hfτ'
    have h4 : ContDiffOn ℝ 4
        (Function.uncurry
          (Work.FTS.Galerkin.slice (gn n) τ - Work.FTS.Galerkin.slice (gn n) τ'))
        Work.FTS.EllipticEst.Q0 := Work.FTS.EllipticEst.SmoothOpen.forall hsm 4
    have h := hC _ h4 hm hb 0 0 (by norm_num) z θ hz hθ hθ'
    have hHk : Work.Spaces.HkNorm α 4
        (Work.FTS.Galerkin.slice (gn n) τ - Work.FTS.Galerkin.slice (gn n) τ')
        ≤ max L 0 * |τ - τ'| := by
      have h1 := hlip n τ hτ τ' hτ'
      have h2 : L * |τ - τ'| ≤ max L 0 * |τ - τ'| :=
        mul_le_mul_of_nonneg_right (le_max_left L 0) (abs_nonneg _)
      linarith
    calc |Work.FTS.Galerkin.slice (gn n) τ z θ - Work.FTS.Galerkin.slice (gn n) τ' z θ|
        = |Work.Spaces.mixed 0 0
            (Work.FTS.Galerkin.slice (gn n) τ - Work.FTS.Galerkin.slice (gn n) τ')
            z θ| := by simp
      _ ≤ C * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2) * Work.Spaces.HkNorm α 4
            (Work.FTS.Galerkin.slice (gn n) τ - Work.FTS.Galerkin.slice (gn n) τ') := h
      _ ≤ C * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2) * (max L 0 * |τ - τ'|) := by
          apply mul_le_mul_of_nonneg_left hHk
          exact mul_nonneg hC0 (div_nonneg (Real.rpow_nonneg hz.le _) (by positivity))
  have htend : Filter.Tendsto (fun n : ℕ =>
      |Work.FTS.Galerkin.slice (gn n) τ z θ - Work.FTS.Galerkin.slice (gn n) τ' z θ|)
      Filter.atTop (𝓝 |Work.FTS.Galerkin.slice g τ z θ - Work.FTS.Galerkin.slice g τ' z θ|) := by
    have h1 := hconv τ hτ 0 0 (by norm_num) z θ hQ
    have h2 := hconv τ' hτ' 0 0 (by norm_num) z θ hQ
    have h3 := h1.sub h2
    simpa using h3.abs
  have hfin := le_of_tendsto' htend hkey
  calc |Work.FTS.Galerkin.slice g τ z θ - Work.FTS.Galerkin.slice g τ' z θ|
      ≤ C * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2) * (max L 0 * |τ - τ'|) := hfin
    _ = C * max L 0 * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2) * |τ - τ'| := by ring

end Work.FTS_RegExport.RXT.Sys
