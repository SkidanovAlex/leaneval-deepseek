/-
# Row 12 of the §8 table, in the open-quadrant (primed) vocabulary

Elgindi §8 (tex 1450): the piece `N₂^{gg} = -2·U(Φ̃_g)·∂_θ g` comes with the
`ℋ⁴`-honesty of `N₂^{gg}` and the pairing bound `|⟨N₂^{gg}, g⟩| ≤ C α^{-1/2} X³`.

The proof has three parts.

* **The honest representative.**  `N₂^{gg}` is *not* of the shape of an `IP`-clause: the
  transport clause `t1` pairs `f · D_θ g` (`D_θ = sin(2θ)∂_θ`), and the `ℋ⁴`-product rule
  `prod` multiplies two `ℋ⁴`-functions.  Both apply to
  `coef · D_θ g` with `coef = -2·U(Φ̃_g)/sin 2θ` — which is exactly `EllPkgGo.U`
  (`HQo α 4 coef`, `Xn α coef ≤ 2·Ce·Xn α g`) times `D_θ g` (`HQo α 4 (D_θ g)`, because
  `D_θ g` is `ℋ⁴` as soon as `g ∈ RegQ α 5`, `HkMem_dth_of_RegQ_ge`).
  The two functions `N₂^{gg}` and `coef · D_θ g` agree on `(0,∞) × [0,π/2]`:
  on the open angle interval because `sin 2θ ≠ 0` there, and on the two boundary lines
  `θ = 0, π/2` because `U(Φ̃_g)` vanishes there (`EllPkgGo.vanishU`), both sides being
  `0`.  Hence the honesty transfers along `HkMem_congr_Ioi`, and the `IP`-value transfers
  along `N4Extra'.congr` (which only sees the open quadrant).
* **The bound.**  `t1` applied to `coef` and `g` gives
  `|⟨coef·D_θ g, g⟩| ≤ Ct α^{-1/2} Xn α coef · Xn α g²`, and the homogeneity
  `Xn_const_mul` of the norm turns `Xn α coef` into `2·Xn α (U/sin 2θ) ≤ 2·max Ce 1·Xn α g`.
  The exponents combine to `α^{-1/2} X³`.
* `hN` is used only through `prod`.

Nothing here uses `Φs` or the star package (`Cs`); the row is an `EllPkgGo`-only row.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.NonlinRows.Defs
import Submission.Work.FTS.OpenPkg.Defs
import Submission.Work.FTS.OpenPkg.Basic
import Submission.Work.FTS.LocData.HkMem_const_mul
import Submission.Work.Coercivity.HkMem_congr_Ioi
import Submission.Work.FTS.CoercivityFix.E2Bound.HkMem_dth_of_RegQ_ge
import Submission.Work.FTS.LocDataExt.Monotone
import Submission.Work.FTS.Nonlinear.Pieces.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.NonlinRows

open scoped Real

open Work.FTS.Galerkin (Fn)

set_option linter.unusedVariables false

/-- `SmoothOpen` is stable under multiplication by a scalar (the `SmoothOpen`-analogue of
`ContDiffOn.const_smul`). -/
private theorem smoothOpen_const_mul {F : ℝ → ℝ → ℝ} (c : ℝ)
    (h : Work.FTS.EllipticEst.SmoothOpen F) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => c * F z θ) :=
  h.const_smul c

/-- **Row 12 of the §8 table, in the open-quadrant (primed) vocabulary** (Elgindi §8, tex 1450):
the `ℋ⁴`-honesty and the pairing bound of the piece `N₂^{gg} = -2·U(Φ̃_g)·∂_θg`.

The rate is `α^{-1/2}X³`, with `K = 2·Ct·max Ce 1 + 1`; the constant is independent of `α`,
of the data and of the truncation. -/
theorem NRow12 (IP : ℝ → Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn → ℝ) {α₂ Ci Ct Ce Cs : ℝ}
    (hN : Work.FTS.OpenPkg.N4Norm' Ci α₂) (hE : Work.FTS.OpenPkg.N4Extra' IP α₂ Ct) :
    ∃ K : ℝ, 0 < K ∧ ∀ {α : ℝ} {g Φs Φg : Work.FTS.Galerkin.Fn},
      Work.FTS.NonlinRows.Ctx α₂ Ci Ct Ce Cs α g Φs Φg →
      Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N2gg α g Φg) ∧
        |IP α (Work.FTS.Nonlin.N2gg α g Φg) g|
          ≤ K * (α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 3) := by
  obtain ⟨hCt, _hα₂⟩ := hE.pos
  have hmax : 0 < max Ce 1 := lt_of_lt_of_le zero_lt_one (le_max_right Ce 1)
  refine ⟨2 * Ct * max Ce 1 + 1, ?_, ?_⟩
  · have : 0 < 2 * Ct * max Ce 1 := mul_pos (mul_pos (by norm_num) hCt) hmax
    linarith
  · intro α g Φs Φg hctx
    have hα : 0 < α := hctx.hα
    have hαα₂ : α ≤ α₂ := hctx.hαα₂
    have hgal : Work.FTS.Nonlin.GalClass α g := hctx.hg
    have hell : Work.FTS.VocabO.EllPkgGo α Ce g Φg := hctx.hell
    have hIoc : α ∈ Set.Ioc 0 α₂ := ⟨hα, hαα₂⟩
    have hreg4 : Work.FTS.Nonlin.RegQ α 4 g := Work.FTS.Nonlin.galClass_regQ4 hgal
    have hreg6 : Work.FTS.Nonlin.RegQ α 6 g := hgal.reg
    have hreg5 : Work.FTS.Nonlin.RegQ α 5 g :=
      Work.FTS.LocDataExt.RegQ_mono (by norm_num) hreg6
    have hSmG : Work.FTS.EllipticEst.SmoothOpen g :=
      Work.FTS.OpenPkg.smoothOpen_of_smoothQuad hreg6.1
    -- the coefficient `coef = -2·U(Φ̃_g)/sin 2θ` of the transport clause `t1`
    set coef : Fn := fun z θ => -2 * (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTg α g Φg)
      z θ / Work.Construction.s2 θ) with hcoef
    have hcoefHQo : Work.FTS.VocabO.HQo α 4 coef := by
      refine ⟨?_, ?_⟩
      · rw [hcoef]
        exact smoothOpen_const_mul (-2) hell.U.1.1
      · rw [hcoef]
        exact Work.FTS.LocData.HkMem_const_mul α 4 (-2) hell.U.1.2
    -- `D_θ g` is `ℋ⁴`, since `D_θ` lowers the order of the regular class by one
    have hDthHQo : Work.FTS.VocabO.HQo α 4 (Work.Spaces.Dth g) :=
      ⟨hSmG.Dth,
        Work.FTS.CoercivityFix.E2Bound.HkMem_dth_of_RegQ_ge α 4 (by linarith) hreg5⟩
    -- the honest product `coef · D_θ g`, by the `ℋ⁴`-product rule
    have hprod := hN.prod α hIoc coef (Work.Spaces.Dth g) hcoefHQo hDthHQo
    -- the two functions agree on `(0,∞) × [0,π/2]`
    have hpt : ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Work.Spaces.Iθ,
        (fun z θ => coef z θ * Work.Spaces.Dth g z θ) z θ
          = Work.FTS.Nonlin.N2gg α g Φg z θ := by
      intro z _hz θ hθ
      have hv1 : Work.Construction.Uop α (Work.Construction.PhiTil α g Φg) z 0 = 0 :=
        hell.vanishU.1 z
      have hv2 : Work.Construction.Uop α (Work.Construction.PhiTil α g Φg) z (π / 2) = 0 :=
        hell.vanishU.2 z
      have hsin : Real.sin (2 * (π / 2)) = 0 := by
        rw [show 2 * (π / 2) = Real.pi by ring, Real.sin_pi]
      simp only [hcoef, Work.FTS.Nonlin.N2gg, Work.FTS.Nonlin.PhiTg, Work.Spaces.Dth,
        Work.Spaces.pth, Work.Construction.s2_eq]
      rcases eq_or_lt_of_le hθ.1 with h0 | hpos
      · -- `θ = 0`: both sides are `0`
        subst h0
        simp [hv1]
      · rcases eq_or_lt_of_le hθ.2 with hpi | hlt
        · -- `θ = π/2`: both sides are `0`
          subst hpi
          simp [hv2, hsin]
        · -- interior: cancel `sin 2θ`
          have hs : Real.sin (2 * θ) ≠ 0 :=
            ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith))
          field_simp
    -- the `ℋ⁴`-honesty of `N₂^{gg}`, transferred from the honest product
    have hmemN2 : Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N2gg α g Φg) :=
      Work.Coercivity.HkMem_congr_Ioi α 4 hprod.1 hpt
    -- `IP` only depends on the values on the open quadrant
    have hIPeq : IP α (Work.FTS.Nonlin.N2gg α g Φg) g
        = IP α (fun z θ => coef z θ * Work.Spaces.Dth g z θ) g := by
      refine hE.congr α hIoc _ _ g hmemN2 hprod.1 hreg4 ?_
      intro z θ hQd
      exact (hpt z hQd.1 θ ⟨le_of_lt hQd.2.1, le_of_lt hQd.2.2⟩).symm
    refine ⟨hmemN2, ?_⟩
    rw [hIPeq]
    -- the transport clause `t1`
    have ht1 := hE.t1 α hIoc coef g hcoefHQo hreg4
    have hXg : 0 ≤ Work.FTS.Nonlin.Xn α g := Work.Spaces.HkNorm_nonneg α 4 g
    have hrp : 0 ≤ α ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hα.le _
    -- the norm of the coefficient
    have hXnCoef : Work.FTS.Nonlin.Xn α coef
        = 2 * Work.FTS.Nonlin.Xn α (fun z θ => Work.Construction.Uop α
            (Work.FTS.Nonlin.PhiTg α g Φg) z θ / Work.Construction.s2 θ) := by
      rw [hcoef, Work.FTS.Nonlinear.Pieces.RowsN0Aux.Xn_const_mul]
      norm_num
    have hXc : Work.FTS.Nonlin.Xn α coef ≤ 2 * (max Ce 1 * Work.FTS.Nonlin.Xn α g) := by
      rw [hXnCoef]
      have hU2 : Work.FTS.Nonlin.Xn α (fun z θ => Work.Construction.Uop α
          (Work.FTS.Nonlin.PhiTg α g Φg) z θ / Work.Construction.s2 θ)
          ≤ Ce * Work.FTS.Nonlin.Xn α g := hell.U.2
      have hmaxle : Ce * Work.FTS.Nonlin.Xn α g ≤ max Ce 1 * Work.FTS.Nonlin.Xn α g :=
        mul_le_mul_of_nonneg_right (le_max_left Ce 1) hXg
      linarith [hU2, hmaxle]
    have hkey : Ct * α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α coef
          * Work.FTS.Nonlin.Xn α g ^ 2
        ≤ (2 * Ct * max Ce 1 + 1)
          * (α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 3) := by
      have h1 : Ct * α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α coef
            * Work.FTS.Nonlin.Xn α g ^ 2
          ≤ Ct * α ^ (-(1 / 2 : ℝ))
            * (2 * (max Ce 1 * Work.FTS.Nonlin.Xn α g)) * Work.FTS.Nonlin.Xn α g ^ 2 :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hXc (mul_nonneg hCt.le hrp)) (pow_nonneg hXg 2)
      refine le_trans h1 ?_
      have h2 : 0 ≤ α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 3 :=
        mul_nonneg hrp (pow_nonneg hXg 3)
      calc Ct * α ^ (-(1 / 2 : ℝ)) * (2 * (max Ce 1 * Work.FTS.Nonlin.Xn α g))
            * Work.FTS.Nonlin.Xn α g ^ 2
          = 2 * Ct * max Ce 1 * (α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 3) := by ring
        _ ≤ (2 * Ct * max Ce 1 + 1)
              * (α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 3) :=
            mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) h2
    exact le_trans ht1 hkey

end Work.FTS.NonlinRows
