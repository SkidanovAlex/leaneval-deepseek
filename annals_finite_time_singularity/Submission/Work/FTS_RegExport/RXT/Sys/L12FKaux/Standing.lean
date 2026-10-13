import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.FinalV2.Defs
import Submission.Work.FTS.RegExportIface.RXT.Leaves
import Submission.Work.FTS_RegExport.RXA1w.abs_mixed_le_HkNorm_C4_w_proved
import Submission.Work.FTS_RegExport.RXA2w.lim_mixed_weighted_proved
import Submission.Work.FTS_RegExport.RXR1.classC_sub_hyp
import Submission.Work.FTS_RegExport.RXT.L12Iter.Basic
import Submission.Work.FTS.StrongEps.SupPort.classC_mixed_sup_le
import Submission.Work.FTS.EllipticEst.TT.Slot11.ZsqAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `L12FKaux.Standing` — the standing bounds for the limit family and its approximants

For a family `g` with `LimApprox β C₀ Φs E g` (and `β = pExp α`), the approximating families
`gn` of the clause are class-`C` with uniformly bounded `ℋ⁴`-norm and `ℋ⁴`-Lipschitz in the fake
time.  Feeding those three facts into the interior weighted `L^∞`–`ℋ⁴` trade-off
(`RXA1w.abs_mixed_le_HkNorm_C4_w_proved`) gives the weighted slot bounds
`|D_z^bD_θ^a (slice (gn n) τ)| ≤ C · z^{3/2}/(1+z)²` and the weighted τ-modulus
`|D_z^bD_θ^a(slice (gn n) τ) − D_z^bD_θ^a(slice (gn n) τ')| ≤ C·z^{3/2}/(1+z)²·|τ−τ'|`
for `a + b ≤ 2`, which are the hypotheses of the `L₁₂`-calculus of `RXT.L12Iter`.

Everything here is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_RegExport.RXT.Sys.L12FKaux

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false

/-- The radial weight `z^{3/2}/(1+z)²` of the standing bound. -/
abbrev SW (z : ℝ) : ℝ := z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2

theorem SW_nonneg {z : ℝ} (hz : 0 ≤ z) : 0 ≤ SW z :=
  Work.FTS_RegExport.RXT.L12Iter.Rwt_nonneg hz

/-- **Weighted slot bounds for the approximants.** -/
theorem app_slot_le {α C₀ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    {gn : ℕ → Fam}
    (hcl : ∀ (n : ℕ) (τ : ℝ), Work.FTS.ClassC.ClassC α (slice (gn n) τ))
    (hXn : ∀ (n : ℕ) (τ : ℝ), Work.FTS.Nonlin.Xn α (slice (gn n) τ) ≤ C₀ * α ^ 2) :
    ∃ Cw : ℝ, 0 ≤ Cw ∧ ∀ (n : ℕ) (τ : ℝ) (b a : ℕ), a + b ≤ 2 →
      ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        |Work.Spaces.mixed b a (slice (gn n) τ) z θ| ≤ Cw * SW z := by
  obtain ⟨C, hC0, hC⟩ := Work.FTS_RegExport.RXA1w.abs_mixed_le_HkNorm_C4_w_proved hα hα1
  have hsq : 0 ≤ C₀ * α ^ 2 :=
    le_trans (Work.Spaces.HkNorm_nonneg α 4 (slice (gn 0) 0)) (hXn 0 0)
  refine ⟨C * (C₀ * α ^ 2), mul_nonneg hC0 hsq, ?_⟩
  intro n τ b a hab z θ hz hθ0 hθ1
  have hcls := hcl n τ
  have h4 : ContDiffOn ℝ 4 (Function.uncurry (slice (gn n) τ)) Work.FTS.EllipticEst.Q0 :=
    hcls.reg.forall 4
  have hmem : Work.Spaces.HkMem α 4 (slice (gn n) τ) :=
    Work.FTS.ClassC.classC_hkMem_four hcls
  have htr : Work.FTS.Nonlin.BdryTraces α 4 (slice (gn n) τ) :=
    Work.FTS.ClassC.bdryTraces_mono (by norm_num) hcls.tr
  have h1 := hC _ h4 hmem htr b a hab z θ hz hθ0 hθ1
  have h2 : Work.Spaces.HkNorm α 4 (slice (gn n) τ) ≤ C₀ * α ^ 2 := hXn n τ
  have h3 : 0 ≤ C * SW z := mul_nonneg hC0 (SW_nonneg hz.le)
  calc |Work.Spaces.mixed b a (slice (gn n) τ) z θ|
      ≤ C * SW z * Work.Spaces.HkNorm α 4 (slice (gn n) τ) := h1
    _ ≤ C * SW z * (C₀ * α ^ 2) := mul_le_mul_of_nonneg_left h2 h3
    _ = C * (C₀ * α ^ 2) * SW z := by ring

/-- **Weighted τ-modulus of the approximants.** -/
theorem app_diff_le {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    {gn : ℕ → Fam} {L : ℝ} (hL0 : 0 ≤ L)
    (hcl : ∀ (n : ℕ) (τ : ℝ), Work.FTS.ClassC.ClassC α (slice (gn n) τ))
    (hlip : ∀ (n : ℕ) (τ τ' : ℝ),
      Work.Spaces.HkNorm α 4 (slice (gn n) τ - slice (gn n) τ') ≤ L * |τ - τ'|) :
    ∃ Cw : ℝ, 0 ≤ Cw ∧ ∀ (n : ℕ) (τ τ' : ℝ) (b a : ℕ), a + b ≤ 2 →
      ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        |Work.Spaces.mixed b a (slice (gn n) τ) z θ
            - Work.Spaces.mixed b a (slice (gn n) τ') z θ|
          ≤ Cw * SW z * |τ - τ'| := by
  obtain ⟨C, hC0, hC⟩ := Work.FTS_RegExport.RXA1w.abs_mixed_le_HkNorm_C4_w_proved hα hα1
  refine ⟨C * L, mul_nonneg hC0 hL0, ?_⟩
  intro n τ τ' b a hab z θ hz hθ0 hθ1
  have hcls := hcl n τ
  have hcls' := hcl n τ'
  obtain ⟨hsm, hm, hb⟩ := Work.FTS_RegExport.RXR1.classC_sub_hyp hcls hcls'
  have h4 : ContDiffOn ℝ 4
      (Function.uncurry (fun z θ => slice (gn n) τ z θ - slice (gn n) τ' z θ))
      Work.FTS.EllipticEst.Q0 := hsm.forall 4
  have h1 := hC _ h4 hm hb b a hab z θ hz hθ0 hθ1
  have hsub := Work.FTS.EllipticEst.TTSlot11Aux.mixed_sub_open hcls.reg hcls'.reg b a
    z θ hz hθ0 hθ1
  have hHk : Work.Spaces.HkNorm α 4
      (fun z θ => slice (gn n) τ z θ - slice (gn n) τ' z θ) ≤ L * |τ - τ'| := hlip n τ τ'
  have h2 : 0 ≤ L * |τ - τ'| := mul_nonneg hL0 (abs_nonneg _)
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
    _ ≤ C * SW z * (L * |τ - τ'|) := mul_le_mul_of_nonneg_left hHk h3
    _ = C * L * SW z * |τ - τ'| := by ring

/-- **Uniform τ-modulus of the approximants** (the `L^∞`-form, no `z`-weight). -/
theorem app_diff_unif {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    {gn : ℕ → Fam} {L : ℝ}
    (hcl : ∀ (n : ℕ) (τ : ℝ), Work.FTS.ClassC.ClassC α (slice (gn n) τ))
    (hlip : ∀ (n : ℕ) (τ τ' : ℝ),
      Work.Spaces.HkNorm α 4 (slice (gn n) τ - slice (gn n) τ') ≤ L * |τ - τ'|) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (n : ℕ) (τ τ' : ℝ) (z θ : ℝ), (z, θ) ∈ Work.Construction.Qd →
      |slice (gn n) τ z θ - slice (gn n) τ' z θ| ≤ K * |τ - τ'| := by
  have hγ1 : 0 < Work.Spaces.gam α - 1 := by rw [Work.Spaces.gam_sub_one]; linarith
  refine ⟨10 / Real.sqrt (Work.Spaces.gam α - 1) * max L 0,
    mul_nonneg (div_nonneg (by norm_num) (Real.sqrt_nonneg _)) (le_max_right L 0), ?_⟩
  intro n τ τ' z θ hQd
  have hsub : Work.FTS.ClassC.ClassC α
      (fun z θ => slice (gn n) τ z θ - slice (gn n) τ' z θ) :=
    Work.FTS.StrongEps.EComparison.classC_sub (hcl n τ) (hcl n τ')
  have h1 := Work.FTS.StrongEps.SupPort.classC_mixed_sup_le hα hα1 hsub 0 0 (by norm_num) hQd
  have h2 : Work.FTS.Nonlin.Xn α
      (fun z θ => slice (gn n) τ z θ - slice (gn n) τ' z θ) ≤ L * |τ - τ'| := hlip n τ τ'
  have h2' : Work.FTS.Nonlin.Xn α
      (fun z θ => slice (gn n) τ z θ - slice (gn n) τ' z θ) ≤ max L 0 * |τ - τ'| := by
    refine le_trans h2 (mul_le_mul_of_nonneg_right (le_max_left L 0) (abs_nonneg _))
  have h3 : 0 ≤ 10 / Real.sqrt (Work.Spaces.gam α - 1) :=
    div_nonneg (by norm_num) (Real.sqrt_nonneg _)
  have h4 : |Work.Spaces.mixed 0 0
      (fun z θ => slice (gn n) τ z θ - slice (gn n) τ' z θ) z θ| ≤
      10 / Real.sqrt (Work.Spaces.gam α - 1) * (max L 0 * |τ - τ'|) :=
    le_trans h1 (mul_le_mul_of_nonneg_left h2' h3)
  have h5 : Work.Spaces.mixed 0 0
      (fun z θ => slice (gn n) τ z θ - slice (gn n) τ' z θ) z θ
      = slice (gn n) τ z θ - slice (gn n) τ' z θ := rfl
  rw [h5] at h4
  calc |slice (gn n) τ z θ - slice (gn n) τ' z θ|
      ≤ 10 / Real.sqrt (Work.Spaces.gam α - 1) * (max L 0 * |τ - τ'|) := h4
    _ = 10 / Real.sqrt (Work.Spaces.gam α - 1) * max L 0 * |τ - τ'| := by ring


/-- `|K(θ)| ≤ 3`. -/
theorem abs_K_le_three (θ : ℝ) : |Work.Spaces.K θ| ≤ 3 :=
  Work.FTS_RegExport.RXT.L12Iter.abs_Ktheta_le_three θ

end Work.FTS_RegExport.RXT.Sys.L12FKaux
