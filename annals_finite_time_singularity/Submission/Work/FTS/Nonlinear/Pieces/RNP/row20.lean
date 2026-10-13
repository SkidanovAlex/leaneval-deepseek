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

/-- **Row 20 of the design table** (Elgindi §8): the `ℋ⁴`-pairing of
`N₄^{gg} = -(1/2) sin(2θ) FK(g) ∂_θ g = -(1/2) FK(g) D_θ g` with `g`.

The coefficient `FK g = ∫_θ K(θ) g(z,θ) dθ` depends on `z` alone.  The norm-level interface
`N4Norm.fkH` (its zero-mode hypothesis `L₁₂ g 0 = 0` is the `l12` field of `GalClass α g`)
gives `FK g ∈ ℋ⁴` with `|FK g|_{ℋ⁴} ≤ Ci·X`, `X = |g|_{ℋ⁴}`, and the transport estimate
`N4Extra.t1` (the slot with `D_θ` and an *arbitrary* coefficient) then bounds the pairing by

`Ct·α^{-1/2}·|(1/2)FK g|_{ℋ⁴}·X² ≤ (Ct·Ci/2)·α^{-1/2}X³`,

using `Xn_const_mul` for the factor `1/2`.  Hence the constant `K = Ct·Ci/2 + 1`. -/
theorem row20 (IP : ℝ → Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn → ℝ)
    {α₂ Ci Ct Ce Cs : ℝ} (hN : Work.FTS.Nonlin.N4Norm Ci α₂)
    (hE : Work.FTS.Nonlin.N4Extra IP α₂ Ct) :
    ∃ K : ℝ, 0 < K ∧ ∀ {α : ℝ} {g Φs Φg : Work.FTS.Galerkin.Fn},
      Work.FTS.Nonlin.GalClass α g → Work.FTS.Nonlin.StarPkg α Cs Φs →
      Work.FTS.Nonlin.EllPkgG α Ce g Φg → 0 < α → α ≤ 1 → α ≤ α₂ →
      |IP α (Work.FTS.Nonlin.N4gg α g) g|
        ≤ K * (α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 3) := by
  obtain ⟨hCi, -⟩ := hN.pos
  have hCt0 : 0 < Ct := hE.pos.1
  refine ⟨Ct * Ci / 2 + 1, by positivity, ?_⟩
  intro α g Φs Φg hgal hstar hell hα hα1 hαα₂
  have hIoc : α ∈ Set.Ioc 0 α₂ := ⟨hα, hαα₂⟩
  have hreg : Work.FTS.Nonlin.RegQ α 4 g := Work.FTS.Nonlin.galClass_regQ4 hgal
  have hX0 : 0 ≤ Work.FTS.Nonlin.Xn α g := Work.Spaces.HkNorm_nonneg α 4 g
  have hrp : 0 ≤ α ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hα.le _
  -- `FK g` is a radial `ℋ⁴`-function, controlled by the `ℋ⁴`-norm of `g` (its zero mode
  -- vanishes by `GalClass.l12`)
  have hfk : Work.FTS.Nonlin.Xn α (fun z _ => Work.Construction.FK g z)
      ≤ Ci * Work.FTS.Nonlin.Xn α g := (hN.fkH α hIoc g hreg hgal.l12).2
  -- the transport estimate in the `D_θ`-slot, with the (radial) coefficient `-(1/2)FK g`
  have ht1 := hE.t1 α hIoc (fun z θ => -(1 / 2) * Work.Construction.FK g z) g hreg
  -- the `ℋ⁴`-norm of the coefficient
  have hcoef : Work.FTS.Nonlin.Xn α (fun z θ => -(1 / 2) * Work.Construction.FK g z)
      ≤ (1 / 2) * (Ci * Work.FTS.Nonlin.Xn α g) := by
    rw [Work.FTS.Nonlinear.Pieces.RowsN0Aux.Xn_const_mul]
    rw [show |-(1 / 2 : ℝ)| = (1 / 2) by norm_num]
    exact mul_le_mul_of_nonneg_left hfk (by norm_num)
  have hstep : |IP α (fun z θ => -(1 / 2) * Work.Construction.FK g z
        * Work.Spaces.Dth g z θ) g|
      ≤ (Ct * Ci / 2 + 1) * (α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 3) := by
    refine ht1.trans ?_
    have h1 : Ct * α ^ (-(1 / 2 : ℝ))
          * Work.FTS.Nonlin.Xn α (fun z θ => -(1 / 2) * Work.Construction.FK g z)
          * Work.FTS.Nonlin.Xn α g ^ 2
        ≤ Ct * α ^ (-(1 / 2 : ℝ)) * ((1 / 2) * (Ci * Work.FTS.Nonlin.Xn α g))
          * Work.FTS.Nonlin.Xn α g ^ 2 :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hcoef (mul_nonneg hCt0.le hrp)) (pow_nonneg hX0 2)
    refine h1.trans ?_
    have harith : Ct * α ^ (-(1 / 2 : ℝ)) * ((1 / 2) * (Ci * Work.FTS.Nonlin.Xn α g))
          * Work.FTS.Nonlin.Xn α g ^ 2
        = (Ct * Ci / 2) * (α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 3) := by ring
    rw [harith]
    exact mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg hrp (pow_nonneg hX0 3))
  -- `N₄^{gg}` is exactly the function of the transport estimate
  rw [show Work.FTS.Nonlin.N4gg α g = fun z θ => (-(1 / 2)) * Work.Construction.FK g z
      * Work.Spaces.Dth g z θ from rfl]
  exact hstep

end Work.FTS.Nonlinear.Pieces.RNP
