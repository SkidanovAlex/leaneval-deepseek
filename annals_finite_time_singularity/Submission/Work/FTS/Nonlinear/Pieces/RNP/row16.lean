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

/-- **Row 16 of the design table** (`|(N₃^{gg}, g)| ≤ C√α X³`, Elgindi §8, tex 1484):
`N₃^{gg} = -2α V(Φ̃_g)·D_z g`, so the pairing is the `D_z`-transport estimate `N4Extra.t2`
applied with the coefficient `f = V(Φ̃_g)`:

`|IP α (N₃^{gg}) g| = 2α·|IP α (V(Φ̃_g)·D_z g) g| ≤ 2α·Ct·α^{-1/2}·|V(Φ̃_g)|_{ℋ⁴}·X²`,

and `|V(Φ̃_g)|_{ℋ⁴} ≤ Ce·X` is the `V`-clause of `EllPkgG α Ce g Φg`.  Since
`α·α^{-1/2} = √α` for `α > 0`, the bound is `2·Ct·Ce·√α·X³`; the sign of `Ce` is absorbed by
replacing it with `max Ce 1`. -/
theorem row16 (IP : ℝ → Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn → ℝ)
    {α₂ Ci Ct Ce Cs : ℝ} (hN : Work.FTS.Nonlin.N4Norm Ci α₂)
    (hE : Work.FTS.Nonlin.N4Extra IP α₂ Ct) :
    ∃ K : ℝ, 0 < K ∧ ∀ {α : ℝ} {g Φs Φg : Work.FTS.Galerkin.Fn},
      Work.FTS.Nonlin.GalClass α g → Work.FTS.Nonlin.StarPkg α Cs Φs →
      Work.FTS.Nonlin.EllPkgG α Ce g Φg → 0 < α → α ≤ 1 → α ≤ α₂ →
      |IP α (Work.FTS.Nonlin.N3gg α g Φg) g|
        ≤ K * (Real.sqrt α * Work.FTS.Nonlin.Xn α g ^ 3) := by
  have hCt0 : 0 < Ct := hE.pos.1
  have hMpos : 0 < max Ce 1 := lt_of_lt_of_le zero_lt_one (le_max_right Ce 1)
  refine ⟨2 * Ct * max Ce 1, by positivity, ?_⟩
  intro α g Φs Φg hgal hstar hell hα hα1 hαα₂
  have hIoc : α ∈ Set.Ioc 0 α₂ := ⟨hα, hαα₂⟩
  have hreg4 : Work.FTS.Nonlin.RegQ α 4 g := Work.FTS.Nonlin.galClass_regQ4 hgal
  have hX0 : 0 ≤ Work.FTS.Nonlin.Xn α g := Work.Spaces.HkNorm_nonneg α 4 g
  have hA0 : 0 ≤ α ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hα.le _
  -- the elliptic package bounds the coefficient `V(Φ̃_g)` by `Ce·X`
  have hVB : Work.FTS.Nonlin.Xn α (Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α g Φg))
      ≤ Ce * Work.FTS.Nonlin.Xn α g := hell.V.2
  -- the `D_z`-transport estimate
  have ht2 := hE.t2 α hIoc (Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α g Φg)) g hreg4
  have hb : |IP α (fun z θ => Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α g Φg) z θ
        * Work.Spaces.Dz g z θ) g|
      ≤ Ct * α ^ (-(1 / 2 : ℝ))
        * (max Ce 1 * Work.FTS.Nonlin.Xn α g) * Work.FTS.Nonlin.Xn α g ^ 2 := by
    refine ht2.trans ?_
    have h1 : Work.FTS.Nonlin.Xn α (Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α g Φg))
        ≤ max Ce 1 * Work.FTS.Nonlin.Xn α g :=
      hVB.trans (mul_le_mul_of_nonneg_right (le_max_left Ce 1) hX0)
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left h1 (mul_nonneg hCt0.le hA0)) (pow_nonneg hX0 2)
  -- `N₃^{gg}` is `−2α` times the coefficient `V(Φ̃_g)·D_z g`
  have hN3 : Work.FTS.Nonlin.N3gg α g Φg
      = fun z θ => (-2 * α) * ((fun z θ =>
          Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α g Φg) z θ
            * Work.Spaces.Dz g z θ) z θ) := by
    funext z θ
    simp only [Work.FTS.Nonlin.N3gg]
    ring
  have hIPeq : IP α (Work.FTS.Nonlin.N3gg α g Φg) g
      = (-2 * α) * IP α (fun z θ => Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α g Φg) z θ
          * Work.Spaces.Dz g z θ) g := by
    rw [hN3]
    exact hE.smul α hIoc (-2 * α) _ g hreg4
  have habs : |(-2 : ℝ) * α| = 2 * α := by
    rw [abs_of_neg (by linarith)]
    ring
  rw [hIPeq, abs_mul, habs]
  have hstep : 2 * α * |IP α (fun z θ =>
        Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α g Φg) z θ
          * Work.Spaces.Dz g z θ) g|
      ≤ 2 * α * (Ct * α ^ (-(1 / 2 : ℝ))
        * (max Ce 1 * Work.FTS.Nonlin.Xn α g) * Work.FTS.Nonlin.Xn α g ^ 2) :=
    mul_le_mul_of_nonneg_left hb (by positivity)
  refine hstep.trans ?_
  have hsqrt : Real.sqrt α = α * α ^ (-(1 / 2 : ℝ)) := by
    rw [Real.sqrt_eq_rpow]
    have h := Real.rpow_add hα (1 : ℝ) (-(1 / 2 : ℝ))
    rw [Real.rpow_one, show (1 : ℝ) + -(1 / 2) = 1 / 2 by norm_num] at h
    exact h
  rw [hsqrt]
  exact le_of_eq (by ring)

end Work.FTS.Nonlinear.Pieces.RNP
