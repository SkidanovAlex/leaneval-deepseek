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

/-- **Row 18 of the design table** (`|(N₃^{*g}, g)| ≤ C α^{3/2} X²`, Elgindi §8, tex 1484):
`N₃^{*g} = -2α V(Φ̃_*)·D_z g`, so the pairing is the `𝒲^{4,∞}`-transport estimate
`N4Extra.t3` applied with the coefficient `f = V(Φ̃_*)`, whose `𝒲^{4,∞}`-norm is `≤ Cs·α` by
the `V`-clause of `StarPkg α Cs Φs`:

`|IP α (N₃^{*g}) g| = 2α·|IP α (V(Φ̃_*)·D_z g) g| ≤ 2α·Ct·α^{-1/2}·|V(Φ̃_*)|_{𝒲^{4,∞}}·X²`,

and `α·α^{-1/2}·α = α^{3/2}`, giving `2·Ct·Cs·α^{3/2}X²`.  The sign of `Cs` is absorbed by
replacing it with `max Cs 1`. -/
theorem row18 (IP : ℝ → Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn → ℝ)
    {α₂ Ci Ct Ce Cs : ℝ} (hN : Work.FTS.Nonlin.N4Norm Ci α₂)
    (hE : Work.FTS.Nonlin.N4Extra IP α₂ Ct) :
    ∃ K : ℝ, 0 < K ∧ ∀ {α : ℝ} {g Φs Φg : Work.FTS.Galerkin.Fn},
      Work.FTS.Nonlin.GalClass α g → Work.FTS.Nonlin.StarPkg α Cs Φs →
      Work.FTS.Nonlin.EllPkgG α Ce g Φg → 0 < α → α ≤ 1 → α ≤ α₂ →
      |IP α (Work.FTS.Nonlin.N3sg α Φs g) g|
        ≤ K * (α ^ (3 / 2 : ℝ) * Work.FTS.Nonlin.Xn α g ^ 2) := by
  have hCt0 : 0 < Ct := hE.pos.1
  have hCs1 : (0 : ℝ) < max Cs 1 := lt_of_lt_of_le zero_lt_one (le_max_right Cs 1)
  refine ⟨2 * Ct * max Cs 1, mul_pos (mul_pos two_pos hCt0) hCs1, ?_⟩
  intro α g Φs Φg hgal hstar hell hα hα1 hαα₂
  have hIoc : α ∈ Set.Ioc 0 α₂ := ⟨hα, hαα₂⟩
  have hreg4 : Work.FTS.Nonlin.RegQ α 4 g := Work.FTS.Nonlin.galClass_regQ4 hgal
  have hX0 : 0 ≤ Work.FTS.Nonlin.Xn α g := Work.Spaces.HkNorm_nonneg α 4 g
  have hA0 : 0 ≤ α ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hα.le _
  -- the `V`-clause of `StarPkg` bounds the coefficient in `𝒲^{4,∞}` by `Cs·α`
  have hM : Work.Spaces.WlInf α 4 (Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs))
      ≤ max Cs 1 * α :=
    hstar.V.2.trans (mul_le_mul_of_nonneg_right (le_max_left Cs 1) hα.le)
  -- the `𝒲^{4,∞}`-transport estimate `t3`
  have hb : |IP α (fun z θ => Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs) z θ
        * Work.Spaces.Dz g z θ) g|
      ≤ Ct * α ^ (-(1 / 2 : ℝ))
        * (max Cs 1 * α) * Work.FTS.Nonlin.Xn α g ^ 2 := by
    refine (hE.t3 α hIoc (Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs)) g
      hstar.V.1 hreg4).trans ?_
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hM (mul_nonneg hCt0.le hA0)) (pow_nonneg hX0 2)
  -- `N₃^{*g}` is `−2α` times the coefficient `V(Φ̃_*)·D_z g`
  have hN3 : Work.FTS.Nonlin.N3sg α Φs g
      = fun z θ => (-2 * α) * ((fun z θ =>
          Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs) z θ
            * Work.Spaces.Dz g z θ) z θ) := by
    funext z θ
    simp only [Work.FTS.Nonlin.N3sg]
    ring
  have hIPeq : IP α (Work.FTS.Nonlin.N3sg α Φs g) g
      = (-2 * α) * IP α (fun z θ => Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs) z θ
          * Work.Spaces.Dz g z θ) g := by
    rw [hN3]
    exact hE.smul α hIoc (-2 * α) _ g hreg4
  have habs : |(-2 : ℝ) * α| = 2 * α := by
    rw [abs_of_neg (by linarith)]
    ring
  rw [hIPeq, abs_mul, habs]
  refine (mul_le_mul_of_nonneg_left hb (by positivity)).trans ?_
  -- `α·α^{-1/2}·α = α^{3/2}`
  have h32 : α ^ (3 / 2 : ℝ) = α * α ^ (-(1 / 2 : ℝ)) * α := by
    have h1 := Real.rpow_add hα (1 : ℝ) (1 / 2 : ℝ)
    rw [show (1 : ℝ) + 1 / 2 = 3 / 2 by norm_num, Real.rpow_one] at h1
    have h2 := Real.rpow_add hα (1 : ℝ) (-(1 / 2 : ℝ))
    rw [show (1 : ℝ) + -(1 / 2) = 1 / 2 by norm_num, Real.rpow_one] at h2
    rw [h1, h2]
    ring
  rw [h32]
  generalize hq : α ^ (-(1 / 2 : ℝ)) = q
  exact le_of_eq (by ring)

end Work.FTS.Nonlinear.Pieces.RNP
