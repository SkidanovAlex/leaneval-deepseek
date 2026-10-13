import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.StrongEps.E4R3.N4C.Defs
import Submission.Work.FTS.NonlinRows.NRow5
import Submission.Work.FTS.NonlinRows.NRow1_7Aux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

-- Uniform-in-`Cs`, `Ce` restatement of `Work.FTS.StrongEps.E4R3.N4C.HonRows.n0row5`.
-- The two binders `Cs`, `Ce` are moved from the theorem's argument list into the inner
-- `forall`, so that the constant `K` does not depend on them (the target `rowsN0T`
-- quantifies `{Cs Ce}` *after* the `exists K`).  The proof script is unchanged.

namespace Work.FTS.StrongEps.E4R3.N4C.HonRowsU

open Work.FTS.Galerkin (Fn)

set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-- Row 5 of the §8 table in the **honest** (open-quadrant) class: the `ℋ⁴`-honesty and the
`ℋ⁴`-norm bound of `N₀₅ᵃ = -c2m(θ)·L₁₂(g)(z)·D_zF_*`.  The proof is the exact honest
transcription of `Work.FTS.NonlinRows.NRow5`: the `𝒲^{4,∞}`-factor `D_zF_*` (norm `≤ Cα`,
`Work.FTS.Nonlin.DzFstar_W`) is priced by the `wprod` clause of `N4Norm'`, and the coefficient
`c2m·L₁₂(g)` is handled by `angmul_field` (`c2m` is bounded, its `D_θ`-iterates vanish like
`sin 2θ`, and `L₁₂(g)` is honest with norm `≤ Ci·Xn α g` by `N4Norm'.l12H`). -/
theorem n0row5u (IP : ℝ → Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn → ℝ)
    {α₂ Ci Ct : ℝ} (hN : Work.FTS.OpenPkg.N4Norm' Ci α₂)
    (hE : Work.FTS.StrongEps.E4R3.N4C.N4ExtraH IP α₂ Ct) :
    ∃ K : ℝ, 0 < K ∧ ∀ {Cs Ce α : ℝ} {g Φs Φg : Work.FTS.Galerkin.Fn},
      0 < α → α ≤ 1 → α ≤ α₂ →
      Work.FTS.EllipticEst.SmoothOpen g → Work.Spaces.HkMem α 4 g →
      Work.Spaces.HkMem α 5 g → Work.Construction.L12 g 0 = 0 →
      Work.Spaces.DecayAll 4 g →
      Work.FTS.VocabO2.StarPkgo2 α Cs Φs → Work.FTS.VocabO.EllPkgGo α Ce g Φg →
      Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N05aF α g) ∧
        Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N05aF α g)
          ≤ K * (Real.sqrt α * Work.FTS.Nonlin.Xn α g) := by
  obtain ⟨hCi, _⟩ := hN.pos
  obtain ⟨_, _⟩ := hE.pos
  obtain ⟨Cdz, hCdz, hDzF⟩ := Work.FTS.Nonlin.DzFstar_W
  obtain ⟨Ca, hCa, hang⟩ := Work.FTS.OpenPkg.angmul_field
  refine ⟨Ci * Ci * (Cdz + 1) * (Ca * 1000) + 1, by positivity, ?_⟩
  intro Cs Ce α g Φs Φg hα hα1 hαα₂ hgsm hgm4 hgm5 hL12zero hdec hstar hell
  have hXg : 0 ≤ Work.FTS.Nonlin.Xn α g := Work.Spaces.HkNorm_nonneg α 4 g
  have hIoc : α ∈ Set.Ioc 0 α₂ := ⟨hα, hαα₂⟩
  have hQo4g : Work.FTS.VocabO.HQo α 4 g := ⟨hgsm, hgm4⟩
  -- ---------------------------------------------------------------------
  -- the radial factor `L₁₂(g)`: smoothness, honesty, norm bound
  -- ---------------------------------------------------------------------
  have hLsm : Work.FTS.EllipticEst.SmoothOpen (fun z (_ : ℝ) => Work.Construction.L12 g z) :=
    Work.FTS.NonlinRows.smoothOpen_L12_radial hα hell.smooth hell.V.1.1
  obtain ⟨hLmem, hLle⟩ := hN.l12H α hIoc g hQo4g hL12zero
  -- ---------------------------------------------------------------------
  -- the fixed profile: `D_zF_*` is `SmoothOpen` and `𝒲^{4,∞}` with norm `≤ Cdz·α`
  -- ---------------------------------------------------------------------
  have hFsm : Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Fstar α) :=
    Work.FTS.OpenPkg.smoothOpen_of_smoothQuad (Work.FTS.LocData.SmoothQuad_Fstar α)
  have hDzFsm : Work.FTS.EllipticEst.SmoothOpen
      (Work.Spaces.Dz (Work.Construction.Fstar α)) := hFsm.Dz
  obtain ⟨hDzFmem, hDzFle⟩ := hDzF α hα hα1
  have hDzFle' : Work.Spaces.WlInf α 4 (Work.Spaces.Dz (Work.Construction.Fstar α))
      ≤ (Cdz + 1) * α :=
    le_trans hDzFle (mul_le_mul_of_nonneg_right (by linarith) hα.le)
  -- ---------------------------------------------------------------------
  -- the coefficient `coef = c2m·L₁₂(g)`: `HQo α 4` with `Xn ≤ Ca·1000·Ci·Xn g`
  -- ---------------------------------------------------------------------
  set coef : Fn := fun z θ => Work.Construction.c2m θ * Work.Construction.L12 g z with hcoef
  have hcoefSm : Work.FTS.EllipticEst.SmoothOpen coef := by
    rw [hcoef]
    exact Work.FTS.NonlinRows.smoothOpen_c2m_L12 hα hell.smooth hell.V.1.1
  have hangc := hang α hα hα1 (fun θ => Work.Construction.c2m θ)
    (fun z (_ : ℝ) => Work.Construction.L12 g z) 1000 Work.FTS.NonlinRows.smoothOpen_c2m
    (fun θ hθ => le_trans (Work.FTS.Nonlinear.Pieces.abs_c2m_le_two hθ) (by norm_num))
    (fun i hi hi4 θ hθ => Work.FTS.NonlinRows.DthIter_c2m_le_sin i hi hi4 hθ) hLsm hLmem
  have hcoefHk : Work.Spaces.HkMem α 4 coef := by
    rw [hcoef]
    exact hangc.1
  have hcoefXn : Work.FTS.Nonlin.Xn α coef
      ≤ (Ca * 1000) * (Ci * Work.FTS.Nonlin.Xn α g) := by
    rw [hcoef]
    refine hangc.2.trans ?_
    exact mul_le_mul_of_nonneg_left hLle (by positivity)
  have hQo : Work.FTS.VocabO.HQo α 4 coef := ⟨hcoefSm, hcoefHk⟩
  -- ---------------------------------------------------------------------
  -- the `𝒲^{4,∞}`-product rule
  -- ---------------------------------------------------------------------
  have hprod := hN.wprod α hIoc (Work.Spaces.Dz (Work.Construction.Fstar α)) coef
    hDzFsm hDzFmem hQo
  -- ---------------------------------------------------------------------
  -- `N₀₅ᵃ` is `-` the product
  -- ---------------------------------------------------------------------
  have heq : Work.FTS.Nonlin.N05aF α g
      = -(fun z θ => Work.Spaces.Dz (Work.Construction.Fstar α) z θ * coef z θ) := by
    funext z θ
    simp only [Work.FTS.Nonlin.N05aF, Work.Construction.N05a, hcoef, Pi.neg_apply]
    ring
  constructor
  · rw [heq]
    exact Work.FTS.NonlinRows.HkMem_neg' α 4 hprod.1
  · -- the norm bound
    have hXnprod : Work.FTS.Nonlin.Xn α
          (fun z θ => Work.Spaces.Dz (Work.Construction.Fstar α) z θ * coef z θ)
        ≤ Ci * α ^ (-(1 / 2 : ℝ)) * ((Cdz + 1) * α)
            * ((Ca * 1000) * (Ci * Work.FTS.Nonlin.Xn α g)) := by
      refine hprod.2.trans ?_
      refine mul_le_mul ?_ hcoefXn (Work.Spaces.HkNorm_nonneg α 4 coef) ?_
      · exact mul_le_mul_of_nonneg_left hDzFle'
          (mul_nonneg hCi.le (Real.rpow_nonneg hα.le _))
      · exact mul_nonneg (mul_nonneg hCi.le (Real.rpow_nonneg hα.le _))
          (mul_nonneg (by linarith : (0 : ℝ) ≤ Cdz + 1) hα.le)
    have hsqrt : α ^ (-(1 / 2 : ℝ)) * α = Real.sqrt α := by
      rw [Real.sqrt_eq_rpow]
      have h := Real.rpow_add hα (-(1 / 2 : ℝ)) (1 : ℝ)
      rw [Real.rpow_one, show -(1 / 2 : ℝ) + 1 = 1 / 2 by norm_num] at h
      exact h.symm
    have hkey : Ci * α ^ (-(1 / 2 : ℝ)) * ((Cdz + 1) * α)
          * ((Ca * 1000) * (Ci * Work.FTS.Nonlin.Xn α g))
        = (Ci * Ci * (Cdz + 1) * (Ca * 1000)) * (Real.sqrt α * Work.FTS.Nonlin.Xn α g) := by
      rw [show Ci * α ^ (-(1 / 2 : ℝ)) * ((Cdz + 1) * α)
            * ((Ca * 1000) * (Ci * Work.FTS.Nonlin.Xn α g))
          = (Ci * Ci * (Cdz + 1) * (Ca * 1000)) * (α ^ (-(1 / 2 : ℝ)) * α)
              * Work.FTS.Nonlin.Xn α g from by ring, hsqrt]
      ring
    have hS : 0 ≤ Real.sqrt α * Work.FTS.Nonlin.Xn α g :=
      mul_nonneg (Real.sqrt_nonneg α) hXg
    calc Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N05aF α g)
        = Work.FTS.Nonlin.Xn α
            (fun z θ => Work.Spaces.Dz (Work.Construction.Fstar α) z θ * coef z θ) := by
          rw [heq]
          exact Work.FTS.EllipticEst.HkNorm_neg α 4
            (fun z θ => Work.Spaces.Dz (Work.Construction.Fstar α) z θ * coef z θ)
      _ ≤ Ci * α ^ (-(1 / 2 : ℝ)) * ((Cdz + 1) * α)
            * ((Ca * 1000) * (Ci * Work.FTS.Nonlin.Xn α g)) := hXnprod
      _ = (Ci * Ci * (Cdz + 1) * (Ca * 1000)) * (Real.sqrt α * Work.FTS.Nonlin.Xn α g) := hkey
      _ ≤ (Ci * Ci * (Cdz + 1) * (Ca * 1000) + 1)
            * (Real.sqrt α * Work.FTS.Nonlin.Xn α g) :=
          mul_le_mul_of_nonneg_right (by linarith) hS

end Work.FTS.StrongEps.E4R3.N4C.HonRowsU
