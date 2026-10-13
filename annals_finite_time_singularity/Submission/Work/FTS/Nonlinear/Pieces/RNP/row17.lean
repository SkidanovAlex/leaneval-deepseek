import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.Nonlinear.Pieces.Ctx
import Submission.Work.FTS.Nonlinear.Pieces.Basic
import Submission.Work.FTS.LocData.SmoothQuad_Fstar

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.Nonlinear.Pieces.RNP

set_option linter.unusedVariables false

/-- **Row 17 of the design table** (Elgindi §8): the `ℋ⁴`-norm of
`N₃^{gs} = -2α V(Φ̃_g)·D_z F_*`.

`V(Φ̃_g)` is an `ℋ⁴`-function of norm `≤ Ce·X` (`EllPkgG.V`), while `D_z F_*` is a *radial*
profile in `𝒲^{4,∞}` with norm `≤ Cα` (`DzFstar_W`), so the mixed product rule `N4Norm.wprod`
(multiplication by a `𝒲^{4,∞}` function, with the loss `α^{-1/2}`) applied to the two factors
gives
`|V(Φ̃_g)·D_zF_*|_{ℋ⁴} ≤ Ci·α^{-1/2}·(Cα)·(Ce X)`;
the prefactor `2α` of `N₃^{gs}` (pulled out by `Xn_const_mul`) turns `α·α^{-1/2}·α` into
`α^{3/2}`, which is exactly the exponent of the stated bound.  As in the neighbouring rows the
sign of `Ce` is absorbed by `max Ce 1` and the hypothesis `StarPkg α Cs Φs` is not needed. -/
theorem row17 {α₂ Ci Ct Ce Cs : ℝ} (hN : Work.FTS.Nonlin.N4Norm Ci α₂) :
    ∃ K : ℝ, 0 < K ∧ ∀ {α : ℝ} {g Φs Φg : Work.FTS.Galerkin.Fn},
      Work.FTS.Nonlin.GalClass α g → Work.FTS.Nonlin.StarPkg α Cs Φs →
      Work.FTS.Nonlin.EllPkgG α Ce g Φg → 0 < α → α ≤ 1 → α ≤ α₂ →
      Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N3gs α g Φg)
        ≤ K * (α ^ (3 / 2 : ℝ) * Work.FTS.Nonlin.Xn α g) := by
  obtain ⟨hCi, hα₂pos⟩ := hN.pos
  obtain ⟨CF, hCF, hDzF⟩ := Work.FTS.Nonlin.DzFstar_W
  have hmax : 0 < max Ce 1 := lt_of_lt_of_le zero_lt_one (le_max_right Ce 1)
  refine ⟨2 * Ci * (CF + 1) * max Ce 1 + 1, by positivity, ?_⟩
  intro α g Φs Φg hgal hstar hell hα hα1 hαα₂
  have hIoc : α ∈ Set.Ioc 0 α₂ := ⟨hα, hαα₂⟩
  -- nonnegativity bookkeeping
  have hXg : 0 ≤ Work.FTS.Nonlin.Xn α g := Work.Spaces.HkNorm_nonneg α 4 g
  have hA : 0 ≤ α ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hα.le _
  -- the `𝒲^{4,∞}`-factor `D_z F_*`, with norm `≤ C α`
  obtain ⟨hDzWmem, hDzWle⟩ := hDzF α hα hα1
  have hDzsmooth : Work.FTS.LocData.SmoothQuad
      (Work.Spaces.Dz (Work.Construction.Fstar α)) :=
    Work.FTS.LocData.SmoothQuad.DzIter (Work.FTS.LocData.SmoothQuad_Fstar α) 1
  have hW' : Work.Spaces.WlInf α 4 (Work.Spaces.Dz (Work.Construction.Fstar α))
      ≤ (CF + 1) * α :=
    le_trans hDzWle (mul_le_mul_of_nonneg_right (by linarith) hα.le)
  -- the `ℋ⁴`-factor `V(Φ̃_g)`, with norm `≤ Ce X`
  have hVreg : Work.FTS.Nonlin.RegQ α 4
      (Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α g Φg)) := hell.V.1
  have hVB : Work.FTS.Nonlin.Xn α
      (Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α g Φg)) ≤ Ce * Work.FTS.Nonlin.Xn α g :=
    hell.V.2
  have hV' : Work.FTS.Nonlin.Xn α
      (Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α g Φg))
      ≤ max Ce 1 * Work.FTS.Nonlin.Xn α g :=
    le_trans hVB (mul_le_mul_of_nonneg_right (le_max_left Ce 1) hXg)
  -- the mixed product rule
  have hprod := (hN.wprod α hIoc (Work.Spaces.Dz (Work.Construction.Fstar α))
    (Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α g Φg)) hDzsmooth hDzWmem hVreg).2
  have hbound : Work.FTS.Nonlin.Xn α (fun z θ =>
        Work.Spaces.Dz (Work.Construction.Fstar α) z θ
          * Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α g Φg) z θ)
      ≤ Ci * α ^ (-(1 / 2 : ℝ)) * ((CF + 1) * α)
        * (max Ce 1 * Work.FTS.Nonlin.Xn α g) := by
    refine hprod.trans ?_
    refine mul_le_mul ?_ hV' (Work.Spaces.HkNorm_nonneg α 4 _) ?_
    · exact mul_le_mul_of_nonneg_left hW' (mul_nonneg hCi.le hA)
    · exact mul_nonneg (mul_nonneg hCi.le hA) (mul_nonneg (by linarith) hα.le)
  -- `N₃^{gs}` is `(-2α)` times that product
  have hN3 : Work.FTS.Nonlin.N3gs α g Φg = fun z θ => (-2 * α) *
      (Work.Spaces.Dz (Work.Construction.Fstar α) z θ
        * Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α g Φg) z θ) := by
    funext z θ
    simp only [Work.FTS.Nonlin.N3gs]
    ring
  have hXeq : Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N3gs α g Φg)
      = 2 * α * Work.FTS.Nonlin.Xn α (fun z θ =>
          Work.Spaces.Dz (Work.Construction.Fstar α) z θ
            * Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α g Φg) z θ) := by
    rw [hN3, Work.FTS.Nonlinear.Pieces.RowsN0Aux.Xn_const_mul α (-2 * α)
      (fun z θ => Work.Spaces.Dz (Work.Construction.Fstar α) z θ
        * Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α g Φg) z θ),
      abs_of_neg (by linarith : (-2 : ℝ) * α < 0)]
    ring
  rw [hXeq]
  refine le_trans (mul_le_mul_of_nonneg_left hbound (by linarith)) ?_
  -- `α · α^{-1/2} · α = α^{3/2}`
  have hpow : α * α ^ (-(1 / 2 : ℝ)) * α = α ^ (3 / 2 : ℝ) := by
    have hz : α * α ^ (-(1 / 2 : ℝ)) = Real.sqrt α := by
      rw [Real.sqrt_eq_rpow]
      have h := Real.rpow_add hα (1 : ℝ) (-(1 / 2))
      rw [Real.rpow_one, show (1 : ℝ) + -(1 / 2) = 1 / 2 by norm_num] at h
      exact h.symm
    have h32 : α ^ (3 / 2 : ℝ) = α * Real.sqrt α := by
      rw [show (3 / 2 : ℝ) = 1 + (1 / 2 : ℝ) by norm_num, Real.rpow_add hα 1 (1 / 2),
        Real.rpow_one, Real.sqrt_eq_rpow]
    rw [h32, hz]; ring
  have harith : 2 * α * (Ci * α ^ (-(1 / 2 : ℝ)) * ((CF + 1) * α)
        * (max Ce 1 * Work.FTS.Nonlin.Xn α g))
      = 2 * Ci * (CF + 1) * max Ce 1 * (α ^ (3 / 2 : ℝ) * Work.FTS.Nonlin.Xn α g) := by
    rw [← hpow]
    ring
  rw [harith]
  refine mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) ?_
  exact mul_nonneg (Real.rpow_nonneg hα.le _) hXg

end Work.FTS.Nonlinear.Pieces.RNP
