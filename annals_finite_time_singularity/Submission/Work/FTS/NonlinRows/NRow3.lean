import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.NonlinRows.Defs
import Submission.Work.FTS.OpenPkg.Defs
import Submission.Work.FTS.OpenPkg.Basic
import Submission.Work.FTS.Nonlinear.Pieces.rowsN0Q
import Submission.Work.FTS.NonlinRows.NRow1_7Aux
import Submission.Work.FTS.Nonlinear.FstarPkgAll
import Submission.Work.FTS.LocData.SmoothQuad_Fstar
import Submission.Work.FTS.LocData.HkMem_const_mul

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.NonlinRows

set_option linter.unusedVariables false

/-- **Row 3 of the §8 table, in the open-quadrant (primed) vocabulary**: the `ℋ⁴`-honesty and the
bound of the piece `N₀₄ᵃ = (3/(2α))·sin(2θ)·L₁₂(g)·∂_θF_*`.

The piece factorises *exactly* as a product of the concrete `𝒲^{4,∞}`-function `D_θF_*` and the
radial coefficient `(3/(2α))·L₁₂(g)`:
`N₀₄ᵃ = D_θF_* · ((3/(2α))·L₁₂(g))`.  Hence the `𝒲^{4,∞}`-product rule `N4Norm'.wprod` applies
to it (the coefficient `D_θF_*` is *not* in `ℋ⁴`, so the honest `prod` clause is unavailable, and
it *is* in `𝒲^{4,∞}`: `Work.FTS.Nonlin.DthFstar_W`).  The exponents combine as

  `α^{-1/2} · |D_θF_*|_{𝒲^{4,∞}} · |(3/(2α))L₁₂(g)|_{ℋ⁴} ≤ α^{-1/2}·(Cα²)·(3/(2α))·Ci·X = O(√α·X)`,

which is exactly the rate of the row.  (The extra `α` in `|D_θF_*|_{𝒲^{4,∞}} ≤ Cα²` over
`|F_*|_{𝒲^{4,∞}} ≤ Cα` comes from the `D_θ`-differentiation of `Γ = (sinθcos²θ)^{α/3}`; it is
what makes the `α^{-1}` of the coefficient harmless.) -/
theorem NRow3 (IP : ℝ → Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn → ℝ) {α₂ Ci Ct Ce Cs : ℝ}
    (hN : Work.FTS.OpenPkg.N4Norm' Ci α₂) (hE : Work.FTS.OpenPkg.N4Extra' IP α₂ Ct) :
    ∃ K : ℝ, 0 < K ∧ ∀ {α : ℝ} {g Φs Φg : Work.FTS.Galerkin.Fn},
      Work.FTS.NonlinRows.Ctx α₂ Ci Ct Ce Cs α g Φs Φg →
      Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N04aF α g) ∧
        Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N04aF α g)
          ≤ K * (Real.sqrt α * Work.FTS.Nonlin.Xn α g) := by
  obtain ⟨hCi, _⟩ := hN.pos
  obtain ⟨CF, hCF, hF⟩ := Work.FTS.Nonlin.DthFstar_W
  refine ⟨(3 / 2) * CF * Ci ^ 2 + 1, by positivity, ?_⟩
  intro α g Φs Φg hctx
  have hα : 0 < α := hctx.hα
  have hα1 : α ≤ 1 := hctx.hα1
  have hαα₂ : α ≤ α₂ := hctx.hαα₂
  have hgal : Work.FTS.Nonlin.GalClass α g := hctx.hg
  have hell : Work.FTS.VocabO.EllPkgGo α Ce g Φg := hctx.hell
  have hIoc : α ∈ Set.Ioc 0 α₂ := ⟨hα, hαα₂⟩
  have hXg : 0 ≤ Work.FTS.Nonlin.Xn α g := Work.Spaces.HkNorm_nonneg α 4 g
  have hreg4 : Work.FTS.Nonlin.RegQ α 4 g := Work.FTS.Nonlin.galClass_regQ4 hgal
  -- `D_θF_*` is `C^∞` on the open quadrant and in `𝒲^{4,∞}` with norm `≤ CF·α²`
  have hFsm : Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Fstar α) :=
    Work.FTS.OpenPkg.smoothOpen_of_smoothQuad (Work.FTS.LocData.SmoothQuad_Fstar α)
  have hDthSm : Work.FTS.EllipticEst.SmoothOpen
      (Work.Spaces.Dth (Work.Construction.Fstar α)) := hFsm.Dth
  obtain ⟨hDthMem, hDthLe⟩ := hF α hα hα1
  -- the radial coefficient `(3/(2α))·L₁₂(g)`
  have hL12sm : Work.FTS.EllipticEst.SmoothOpen (fun z _ => Work.Construction.L12 g z) :=
    smoothOpen_L12_radial hα hell.smooth hell.V.1.1
  have hL12 := hN.l12H α hIoc g (Work.FTS.OpenPkg.HQo_of_RegQ hreg4) hgal.l12
  have hc0 : (0 : ℝ) < 3 / (2 * α) := by positivity
  have hcoefSm : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (3 / (2 * α)) * Work.Construction.L12 g z) :=
    smoothOpen_const_mul (3 / (2 * α)) hL12sm
  have hcoefMem : Work.Spaces.HkMem α 4
      (fun z θ => (3 / (2 * α)) * Work.Construction.L12 g z) :=
    Work.FTS.LocData.HkMem_const_mul α 4 (3 / (2 * α)) hL12.1
  have hcoefXn : Work.FTS.Nonlin.Xn α (fun z θ => (3 / (2 * α)) * Work.Construction.L12 g z)
      ≤ (3 / (2 * α)) * (Ci * Work.FTS.Nonlin.Xn α g) := by
    rw [Work.FTS.Nonlinear.Pieces.RowsN0Aux.Xn_const_mul, abs_of_nonneg hc0.le]
    exact mul_le_mul_of_nonneg_left hL12.2 hc0.le
  -- the `𝒲^{4,∞}`-product rule on `D_θF_* · ((3/(2α))L₁₂(g))`
  have hprod := hN.wprod α hIoc (Work.Spaces.Dth (Work.Construction.Fstar α))
    (fun z θ => (3 / (2 * α)) * Work.Construction.L12 g z)
    hDthSm hDthMem ⟨hcoefSm, hcoefMem⟩
  -- the exact factorisation of the piece
  have hid : Work.FTS.Nonlin.N04aF α g = fun z θ =>
      Work.Spaces.Dth (Work.Construction.Fstar α) z θ
        * ((3 / (2 * α)) * Work.Construction.L12 g z) := by
    funext z θ
    simp only [Work.FTS.Nonlin.N04aF, Work.Construction.N04a, Work.Spaces.Dth,
      Work.Spaces.pth, Work.Construction.s2]
    ring
  rw [hid]
  refine ⟨hprod.1, ?_⟩
  -- the chain of bounds
  have hXcf : 0 ≤ Work.FTS.Nonlin.Xn α
      (fun z θ => (3 / (2 * α)) * Work.Construction.L12 g z) :=
    Work.Spaces.HkNorm_nonneg α 4 _
  have hk : (0 : ℝ) ≤ Ci * α ^ (-(1 / 2 : ℝ)) :=
    mul_nonneg hCi.le (Real.rpow_nonneg hα.le _)
  have hstep1 : Ci * α ^ (-(1 / 2 : ℝ))
        * Work.Spaces.WlInf α 4 (Work.Spaces.Dth (Work.Construction.Fstar α))
        * Work.FTS.Nonlin.Xn α (fun z θ => (3 / (2 * α)) * Work.Construction.L12 g z)
      ≤ Ci * α ^ (-(1 / 2 : ℝ)) * (CF * α ^ 2)
        * Work.FTS.Nonlin.Xn α (fun z θ => (3 / (2 * α)) * Work.Construction.L12 g z) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hDthLe hk) hXcf
  have hstep2 : Ci * α ^ (-(1 / 2 : ℝ)) * (CF * α ^ 2)
        * Work.FTS.Nonlin.Xn α (fun z θ => (3 / (2 * α)) * Work.Construction.L12 g z)
      ≤ Ci * α ^ (-(1 / 2 : ℝ)) * (CF * α ^ 2)
        * ((3 / (2 * α)) * (Ci * Work.FTS.Nonlin.Xn α g)) :=
    mul_le_mul_of_nonneg_left hcoefXn
      (mul_nonneg hk (mul_nonneg hCF.le (pow_nonneg hα.le 2)))
  -- the `α`-bookkeeping
  have hαpow : α ^ (-(1 / 2 : ℝ)) * α ^ (((2 : ℕ) : ℝ)) * α ^ (-(1 : ℝ)) = Real.sqrt α := by
    have h1 : α ^ (((2 : ℕ) : ℝ)) * α ^ (-(1 : ℝ)) = α := by
      rw [← Real.rpow_add hα,
        show (((2 : ℕ) : ℝ) + (-(1 : ℝ))) = 1 by norm_num, Real.rpow_one]
    have h2 : α ^ (-(1 / 2 : ℝ)) * α = Real.sqrt α := by
      have h := Real.rpow_add hα (-(1 / 2 : ℝ)) (1 : ℝ)
      rw [show -(1 / 2 : ℝ) + 1 = (1 / 2 : ℝ) by norm_num, Real.rpow_one] at h
      rw [Real.sqrt_eq_rpow, ← h]
    rw [show α ^ (-(1 / 2 : ℝ)) * α ^ (((2 : ℕ) : ℝ)) * α ^ (-(1 : ℝ))
          = α ^ (-(1 / 2 : ℝ)) * (α ^ (((2 : ℕ) : ℝ)) * α ^ (-(1 : ℝ))) from by ring,
      h1, h2]
  have hkey : Ci * α ^ (-(1 / 2 : ℝ)) * (CF * α ^ 2)
        * ((3 / (2 * α)) * (Ci * Work.FTS.Nonlin.Xn α g))
      = ((3 / 2) * CF * Ci ^ 2) * (Real.sqrt α * Work.FTS.Nonlin.Xn α g) := by
    rw [show (3 : ℝ) / (2 * α) = (3 / 2) * α ^ (-(1 : ℝ)) by
      rw [Real.rpow_neg_one]; field_simp]
    rw [show Ci * α ^ (-(1 / 2 : ℝ)) * (CF * α ^ 2)
          * (((3 / 2) * α ^ (-(1 : ℝ))) * (Ci * Work.FTS.Nonlin.Xn α g))
        = ((3 / 2) * CF * Ci ^ 2)
            * (α ^ (-(1 / 2 : ℝ)) * α ^ (((2 : ℕ) : ℝ)) * α ^ (-(1 : ℝ)))
            * Work.FTS.Nonlin.Xn α g from by rw [Real.rpow_natCast]; ring]
    rw [hαpow]
    ring
  have hS : 0 ≤ Real.sqrt α * Work.FTS.Nonlin.Xn α g :=
    mul_nonneg (Real.sqrt_nonneg α) hXg
  calc Work.FTS.Nonlin.Xn α (fun z θ => Work.Spaces.Dth (Work.Construction.Fstar α) z θ
          * ((3 / (2 * α)) * Work.Construction.L12 g z))
      ≤ Ci * α ^ (-(1 / 2 : ℝ)) * (CF * α ^ 2)
          * ((3 / (2 * α)) * (Ci * Work.FTS.Nonlin.Xn α g)) :=
        hprod.2.trans (hstep1.trans hstep2)
    _ = ((3 / 2) * CF * Ci ^ 2) * (Real.sqrt α * Work.FTS.Nonlin.Xn α g) := hkey
    _ ≤ ((3 / 2) * CF * Ci ^ 2 + 1) * (Real.sqrt α * Work.FTS.Nonlin.Xn α g) :=
        mul_le_mul_of_nonneg_right (by linarith) hS

end Work.FTS.NonlinRows
