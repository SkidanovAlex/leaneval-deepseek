import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.Nonlinear.Pieces.Ctx
import Submission.Work.FTS.Nonlinear.Pieces.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.Nonlinear.Pieces.RNP

set_option linter.unusedVariables false

/-- **Row 8 of the design table** (Elgindi §8, tex 1450): the `ℋ⁴`-norm of
`N₁^{gg} = 2ℛ(Φ̃_g)·g`.

`ℛ(Φ̃_g)` is an `ℋ⁴`-function of norm `≤ Ce·X` with `X = |g|_{ℋ⁴}` (`EllPkgG.R`), so the
product rule `N4Norm.prod` (with its loss `√10·α^{-1/2}`) applied to `ℛ(Φ̃_g)` and `g`
(`GalClass α g` gives `RegQ α 4 g` by `galClass_regQ4`) bounds the product by
`Ci·α^{-1/2}·(Ce X)·X`; the factor `2` in front of `N₁^{gg}` is pulled out by
`Xn_const_mul`.  The constant is `K = 2·Ci·max Ce 1` (positive independently of the sign of
`Ce`). -/
theorem row8 {α₂ Ci Ct Ce Cs : ℝ} (hN : Work.FTS.Nonlin.N4Norm Ci α₂) :
    ∃ K : ℝ, 0 < K ∧ ∀ {α : ℝ} {g Φs Φg : Work.FTS.Galerkin.Fn},
      Work.FTS.Nonlin.GalClass α g → Work.FTS.Nonlin.StarPkg α Cs Φs →
      Work.FTS.Nonlin.EllPkgG α Ce g Φg → 0 < α → α ≤ 1 → α ≤ α₂ →
      Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N1gg α g Φg)
        ≤ K * (α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 2) := by
  obtain ⟨hCi, hα₂pos⟩ := hN.pos
  have hmax : 0 < max Ce 1 := lt_of_lt_of_le zero_lt_one (le_max_right Ce 1)
  refine ⟨2 * Ci * max Ce 1, by positivity, ?_⟩
  intro α g Φs Φg hgal hstar hell hα hα1 hαα₂
  have hg4 : Work.FTS.Nonlin.RegQ α 4 g := Work.FTS.Nonlin.galClass_regQ4 hgal
  have hαIoc : α ∈ Set.Ioc 0 α₂ := ⟨hα, hαα₂⟩
  have hRreg : Work.FTS.Nonlin.RegQ α 4
      (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTg α g Φg)) := hell.R.1
  have hRB : Work.FTS.Nonlin.Xn α (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTg α g Φg))
      ≤ Ce * Work.FTS.Nonlin.Xn α g := hell.R.2
  have hprod := (hN.prod α hαIoc (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTg α g Φg)) g
    hRreg hg4).2
  have hXg : 0 ≤ Work.FTS.Nonlin.Xn α g := Work.Spaces.HkNorm_nonneg α 4 g
  have hXR : 0 ≤ Work.FTS.Nonlin.Xn α
      (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTg α g Φg)) :=
    Work.Spaces.HkNorm_nonneg α 4 _
  have hA : 0 ≤ α ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hα.le _
  have heq : Work.FTS.Nonlin.N1gg α g Φg = fun z θ =>
      2 * (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTg α g Φg) z θ * g z θ) := by
    funext z θ
    simp only [Work.FTS.Nonlin.N1gg]
    ring
  have hstep1 : Ci * α ^ (-(1 / 2 : ℝ))
        * Work.FTS.Nonlin.Xn α (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTg α g Φg))
        * Work.FTS.Nonlin.Xn α g
      ≤ Ci * α ^ (-(1 / 2 : ℝ)) * (Ce * Work.FTS.Nonlin.Xn α g)
        * Work.FTS.Nonlin.Xn α g := by
    have hp : 0 ≤ Ci * α ^ (-(1 / 2 : ℝ)) := mul_nonneg hCi.le hA
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hRB hp) hXg
  have hstep2 : Ci * α ^ (-(1 / 2 : ℝ)) * (Ce * Work.FTS.Nonlin.Xn α g)
        * Work.FTS.Nonlin.Xn α g
      ≤ Ci * α ^ (-(1 / 2 : ℝ)) * (max Ce 1 * Work.FTS.Nonlin.Xn α g)
        * Work.FTS.Nonlin.Xn α g := by
    have hp : 0 ≤ Ci * α ^ (-(1 / 2 : ℝ)) := mul_nonneg hCi.le hA
    have h1 : Ce * Work.FTS.Nonlin.Xn α g ≤ max Ce 1 * Work.FTS.Nonlin.Xn α g :=
      mul_le_mul_of_nonneg_right (le_max_left Ce 1) hXg
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hp) hXg
  have heqe : Ci * α ^ (-(1 / 2 : ℝ)) * (max Ce 1 * Work.FTS.Nonlin.Xn α g)
        * Work.FTS.Nonlin.Xn α g
      = Ci * max Ce 1 * (α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 2) := by ring
  rw [heq, Work.FTS.Nonlinear.Pieces.RowsN0Aux.Xn_const_mul]
  rw [abs_of_pos (by norm_num : (0:ℝ) < 2)]
  linarith [hprod, hstep1, hstep2, heqe.le, heqe.ge]

end Work.FTS.Nonlinear.Pieces.RNP
