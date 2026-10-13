import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKaux.Standing

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.RXT.Sys.L12FKaux

open Work.FTS.Galerkin (Fn Fam slice)

theorem app_diff_w {α T L : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    {gn : ℕ → Work.FTS.Galerkin.Fam}
    (hcl : ∀ (n : ℕ) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) T →
      Work.FTS.ClassC.ClassC α (Work.FTS.Galerkin.slice (gn n) τ))
    (hlip : ∀ (n : ℕ) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) T → ∀ (τ' : ℝ), τ' ∈ Set.Icc (0 : ℝ) T →
      Work.Spaces.HkNorm α 4 (Work.FTS.Galerkin.slice (gn n) τ
        - Work.FTS.Galerkin.slice (gn n) τ') ≤ L * |τ - τ'|) :
    ∃ Cw : ℝ, 0 ≤ Cw ∧ ∀ (n : ℕ) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) T → ∀ (τ' : ℝ),
      τ' ∈ Set.Icc (0 : ℝ) T → ∀ b a : ℕ, a + b ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ →
      θ < Real.pi / 2 →
      |Work.Spaces.mixed b a (Work.FTS.Galerkin.slice (gn n) τ) z θ
        - Work.Spaces.mixed b a (Work.FTS.Galerkin.slice (gn n) τ') z θ|
        ≤ Cw * SW z * |τ - τ'| := by
  -- The `Standing.app_diff_le` estimate, restricted to `τ, τ' ∈ [0,T]`, with the constant
  -- `max L 0` so that no sign hypothesis on `L` is needed: the weighted interior `L^∞`–`ℋ⁴`
  -- trade-off applied to the difference slot, whose `ℋ⁴`-norm is controlled by `hlip`.
  obtain ⟨C, hC0, hC⟩ := Work.FTS_RegExport.RXA1w.abs_mixed_le_HkNorm_C4_w_proved hα hα1
  refine ⟨C * max L 0, mul_nonneg hC0 (le_max_right L 0), ?_⟩
  intro n τ hτ τ' hτ' b a hab z θ hz hθ0 hθ1
  have hcls := hcl n τ hτ
  have hcls' := hcl n τ' hτ'
  obtain ⟨hsm, hm, hb⟩ := Work.FTS_RegExport.RXR1.classC_sub_hyp hcls hcls'
  have h4 : ContDiffOn ℝ 4
      (Function.uncurry (fun z θ => slice (gn n) τ z θ - slice (gn n) τ' z θ))
      Work.FTS.EllipticEst.Q0 := hsm.forall 4
  have h1 := hC _ h4 hm hb b a hab z θ hz hθ0 hθ1
  have hsub := Work.FTS.EllipticEst.TTSlot11Aux.mixed_sub_open hcls.reg hcls'.reg b a
    z θ hz hθ0 hθ1
  have hHk : Work.Spaces.HkNorm α 4
      (fun z θ => slice (gn n) τ z θ - slice (gn n) τ' z θ) ≤ L * |τ - τ'| :=
    hlip n τ hτ τ' hτ'
  have hHk' : Work.Spaces.HkNorm α 4
      (fun z θ => slice (gn n) τ z θ - slice (gn n) τ' z θ)
      ≤ max L 0 * |τ - τ'| :=
    le_trans hHk (mul_le_mul_of_nonneg_right (le_max_left L 0) (abs_nonneg _))
  have h3 : 0 ≤ C * SW z := mul_nonneg hC0 (SW_nonneg hz.le)
  have h5 : |Work.Spaces.mixed b a (slice (gn n) τ) z θ
      - Work.Spaces.mixed b a (slice (gn n) τ') z θ|
      = |Work.Spaces.mixed b a
          (fun z θ => slice (gn n) τ z θ - slice (gn n) τ' z θ) z θ| := by rw [hsub]
  rw [h5]
  calc |Work.Spaces.mixed b a
        (fun z θ => slice (gn n) τ z θ - slice (gn n) τ' z θ) z θ|
      ≤ C * SW z * Work.Spaces.HkNorm α 4
          (fun z θ => slice (gn n) τ z θ - slice (gn n) τ' z θ) := h1
    _ ≤ C * SW z * (max L 0 * |τ - τ'|) := mul_le_mul_of_nonneg_left hHk' h3
    _ = C * max L 0 * SW z * |τ - τ'| := by ring

end Work.FTS_RegExport.RXT.Sys.L12FKaux
