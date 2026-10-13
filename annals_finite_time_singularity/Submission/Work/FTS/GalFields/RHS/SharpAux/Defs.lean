/-
# `SharpAux/Defs` — the twenty terms of the pointwise difference of `N`

This file fixes the *vocabulary* of the difference `N α (F_*+g) (Φ_s+EllSol g) - N α (F_*+g')
(Φ_s+EllSol g')` along a Galerkin difference `h = g - g'`, together with two product rules
(the `ℋ⁴`-product and the `𝒲^{4,∞}`-product) in the exact shape consumed by the term bounds of
`SharpAux/` and by the assembly in `RHS/sharp_N_diff`.

The algebraic identity proved in `SharpAux/Core` is

`N g - N g' = TRA + TRB + TRC + TRD + TUA + TUB + TUC + TUD + TVA + TVB + TVC + TVD
                 + TDA + TDB + TDC + TDD + TEA + TEB + TEC + TED`   (on the open quadrant `Qd`),

coming from the telescoping `P(g) - P(g') = P(g')(h) + P(Δ)(g)` of each of the five summands of
`N`, where `Δ = PhiTil α h (EllSol h)` is the difference of the two straightened stream
functions and `h = g - g'`.

The `𝒲^{4,∞}`-priced first factors are `StarH α Φs = ((z+1)/z) Rop α (PhiTs α Φs)`,
`UsPhi α Φs = Uop α (PhiTs α Φs)/s2`, `Vstar α Φs = Vop (PhiTs α Φs)`, `Fstar α`,
`DthFstar α`, `DzFstar α` and `hKerA α = FK (Fstar α) = α·hKer`; the honest (`HQo α 4`) factors
are the `g`, `g'`, `h`-derived atoms of the terms.

Everything here is a definition or an elementary norm product rule; nothing is proved about the
identity itself.  All declarations are `sorry`-free.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.GalFields.Defs
import Submission.Work.FTS.GalFields.RHS.HkSum
import Submission.Work.FTS.GalFields.Norm.Basic
import Submission.Work.FTS.OpenPkg.Defs
import Submission.Work.FTS.OpenPkg.Basic
import Submission.Work.FTS.VocabO2
import Submission.Work.FTS.Nonlinear.Open.Main
import Submission.Work.Spaces.GammaW_Prelim

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.GalFields.RHS.Sharp

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The two `g`-free atoms -/

/-- The star coefficient in the weighted form the `𝒲^{4,∞}`-package prices:
`StarH α Φs = ((z+1)/z)·Rop α (PhiTil α (F_*) Φs)`. -/
def StarH (α : ℝ) (Φs : Fn) : Fn :=
  fun z θ => (z + 1) / z * Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) z θ

/-- The flat angular coefficient `U(Φ̃_*)/sin(2θ)` of the star node. -/
def UsPhi (α : ℝ) (Φs : Fn) : Fn :=
  fun z θ => Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z θ / Work.Construction.s2 θ

/-- The star coefficient `V(Φ̃_*)`. -/
def Vstar (α : ℝ) (Φs : Fn) : Fn :=
  Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs)

/-- `FK (F_*) = 2α·hKer`: the angular moment of the background profile, written in the radial
form which `RNP.hKerConstWlInf` prices (`FK (F_*) z = 2α·hKer z`, see `FstarPkg.FK_Fstar`). -/
def Fkstar (α : ℝ) : Fn := fun z _ => 2 * α * Work.Spaces.hKer z

/-- The `∂_θ`-derivative `D_θF_* = sin(2θ) ∂_θF_*` of the background profile. -/
def DthFstar (α : ℝ) : Fn := Work.Spaces.Dth (Work.Construction.Fstar α)

/-- The `D_z`-derivative of the background profile. -/
def DzFstar (α : ℝ) : Fn := Work.Spaces.Dz (Work.Construction.Fstar α)

/-- The radial factor `z/(1+z)` (multiplying the difference in the `StarH`-terms). -/
def pfac (z : ℝ) : ℝ := z / (1 + z)

/-- `sin²θ`. -/
def sinSq (θ : ℝ) : ℝ := Real.sin θ ^ 2

/-! ## The straightened stream functions of `g` and of the difference -/

/-- `Φ̃_g = PhiTil α g (EllSol g)`: the straightened stream function of the `g`-node. -/
def Zgof (α : ℝ) (EllSol : Fn → Fn) (g : Fn) : Fn :=
  Work.Construction.PhiTil α g (EllSol g)

/-- `Δ = PhiTil α h (EllSol h)`: the straightened stream function of the difference. -/
def Dof (α : ℝ) (EllSol : Fn → Fn) (h : Fn) : Fn :=
  Work.Construction.PhiTil α h (EllSol h)

/-! ## The twenty terms -/

/-- `2·Rop(Φ̃_*)·h` in the weighted form `2·StarH·((z/(1+z))h)`. -/
def TRA (α : ℝ) (Φs h : Fn) : Fn :=
  fun z θ => 2 * (StarH α Φs z θ * (pfac z * h z θ))

/-- `2·Rop(Φ̃_{g'})·h`. -/
def TRB (α : ℝ) (EllSol : Fn → Fn) (g' h : Fn) : Fn :=
  fun z θ => 2 * (Work.Construction.Rop α (Zgof α EllSol g') z θ * h z θ)

/-- `2·Rop(Δ)·F_*`. -/
def TRC (α : ℝ) (EllSol : Fn → Fn) (h : Fn) : Fn :=
  fun z θ => 2 * (Work.Construction.Fstar α z θ * Work.Construction.Rop α (Dof α EllSol h) z θ)

/-- `2·Rop(Δ)·g`. -/
def TRD (α : ℝ) (EllSol : Fn → Fn) (g h : Fn) : Fn :=
  fun z θ => 2 * (Work.Construction.Rop α (Dof α EllSol h) z θ * g z θ)

/-- `-2·(U(Φ̃_*)/s2)·D_θh`. -/
def TUA (α : ℝ) (Φs h : Fn) : Fn :=
  fun z θ => (-2) * (UsPhi α Φs z θ * Work.Spaces.Dth h z θ)

/-- `-2·(U(Φ̃_{g'})/s2)·D_θh`. -/
def TUB (α : ℝ) (EllSol : Fn → Fn) (g' h : Fn) : Fn :=
  fun z θ => (-2) * ((Work.Construction.Uop α (Zgof α EllSol g') z θ / Work.Construction.s2 θ)
    * Work.Spaces.Dth h z θ)

/-- `-2·(U(Δ)/s2)·D_θF_*`. -/
def TUC (α : ℝ) (EllSol : Fn → Fn) (h : Fn) : Fn :=
  fun z θ => (-2) * (DthFstar α z θ
    * (Work.Construction.Uop α (Dof α EllSol h) z θ / Work.Construction.s2 θ))

/-- `-2·(U(Δ)/s2)·D_θg`. -/
def TUD (α : ℝ) (EllSol : Fn → Fn) (g h : Fn) : Fn :=
  fun z θ => (-2) * ((Work.Construction.Uop α (Dof α EllSol h) z θ / Work.Construction.s2 θ)
    * Work.Spaces.Dth g z θ)

/-- `-2α·V(Φ̃_*)·D_zh`. -/
def TVA (α : ℝ) (Φs h : Fn) : Fn :=
  fun z θ => (-(2 * α)) * (Vstar α Φs z θ * Work.Spaces.Dz h z θ)

/-- `-2α·V(Φ̃_{g'})·D_zh`. -/
def TVB (α : ℝ) (EllSol : Fn → Fn) (g' h : Fn) : Fn :=
  fun z θ => (-(2 * α)) * (Work.Construction.Vop (Zgof α EllSol g') z θ
    * Work.Spaces.Dz h z θ)

/-- `-2α·V(Δ)·D_zF_*`. -/
def TVC (α : ℝ) (EllSol : Fn → Fn) (h : Fn) : Fn :=
  fun z θ => (-(2 * α)) * (DzFstar α z θ * Work.Construction.Vop (Dof α EllSol h) z θ)

/-- `-2α·V(Δ)·D_zg`. -/
def TVD (α : ℝ) (EllSol : Fn → Fn) (g h : Fn) : Fn :=
  fun z θ => (-(2 * α)) * (Work.Construction.Vop (Dof α EllSol h) z θ
    * Work.Spaces.Dz g z θ)

/-- `-(1/2)·FK(F_*)·D_θh`. -/
def TDA (α : ℝ) (h : Fn) : Fn :=
  fun z θ => (-(1 / 2)) * (Fkstar α z θ * Work.Spaces.Dth h z θ)

/-- `-(1/2)·FK(g')·D_θh`. -/
def TDB (α : ℝ) (g' h : Fn) : Fn :=
  fun z θ => (-(1 / 2)) * (Work.Construction.FK g' z * Work.Spaces.Dth h z θ)

/-- `-(1/2)·FK(h)·D_θF_*`. -/
def TDC (α : ℝ) (h : Fn) : Fn :=
  fun z θ => (-(1 / 2)) * (DthFstar α z θ * Work.Construction.FK h z)

/-- `-(1/2)·FK(h)·D_θg`. -/
def TDD (α : ℝ) (g h : Fn) : Fn :=
  fun z θ => (-(1 / 2)) * (Work.Construction.FK h z * Work.Spaces.Dth g z θ)

/-- `-FK(F_*)·(sin²θ·h)`. -/
def TEA (α : ℝ) (h : Fn) : Fn :=
  fun z θ => (-1) * (Fkstar α z θ * (sinSq θ * h z θ))

/-- `-(sin²θ·FK(g'))·h`. -/
def TEB (α : ℝ) (g' h : Fn) : Fn :=
  fun z θ => (-1) * ((sinSq θ * Work.Construction.FK g' z) * h z θ)

/-- `-F_*·(sin²θ·FK(h))`. -/
def TEC (α : ℝ) (h : Fn) : Fn :=
  fun z θ => (-1) * (Work.Construction.Fstar α z θ
    * (sinSq θ * Work.Construction.FK h z))

/-- `-(sin²θ·FK(h))·g`. -/
def TED (α : ℝ) (g h : Fn) : Fn :=
  fun z θ => (-1) * ((sinSq θ * Work.Construction.FK h z) * g z θ)

/-! ## Two product rules in normal form -/

/-- **The `ℋ⁴`-product rule in normal form**: if `f` carries `(1+|g|_{ℋ⁵}+|g'|_{ℋ⁵})` and `u`
carries `|h|_{ℋ⁵}`, then the product is honest in `ℋ⁴` with a norm bounded by
`Ci·α^{-1/2}·A·B·(1+|g|_{ℋ⁵}+|g'|_{ℋ⁵})·|h|_{ℋ⁵}`. -/
theorem Xn_mul_honest {α α₂ Ci : ℝ} (hN : Work.FTS.OpenPkg.N4Norm' Ci α₂) (hα : 0 < α)
    (hαα₂ : α ≤ α₂) {f u g g' h : Fn} (hfS : Work.FTS.EllipticEst.SmoothOpen f)
    (huS : Work.FTS.EllipticEst.SmoothOpen u) (hf : Work.Spaces.HkMem α 4 f)
    (hu : Work.Spaces.HkMem α 4 u) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hfX : Work.FTS.Nonlin.Xn α f ≤ A * (1 + Work.FTS.GalFields.Xn5 α g
      + Work.FTS.GalFields.Xn5 α g'))
    (huX : Work.FTS.Nonlin.Xn α u ≤ B * Work.FTS.GalFields.Xn5 α h) :
    Work.Spaces.HkMem α 4 (fun z θ => f z θ * u z θ) ∧
      Work.FTS.Nonlin.Xn α (fun z θ => f z θ * u z θ)
        ≤ Ci * α ^ (-(1 / 2 : ℝ)) * A * B
          * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
          * Work.FTS.GalFields.Xn5 α h := by
  have hprod := hN.prod α ⟨hα, hαα₂⟩ f u ⟨hfS, hf⟩ ⟨huS, hu⟩
  refine ⟨hprod.1, le_trans hprod.2 ?_⟩
  have hXf : 0 ≤ Work.FTS.Nonlin.Xn α f := Work.Spaces.HkNorm_nonneg α 4 f
  have hXu : 0 ≤ Work.FTS.Nonlin.Xn α u := Work.Spaces.HkNorm_nonneg α 4 u
  have hY0 : 0 ≤ Work.FTS.GalFields.Xn5 α g := Work.Spaces.HkNorm_nonneg α 5 g
  have hY0' : 0 ≤ Work.FTS.GalFields.Xn5 α g' := Work.Spaces.HkNorm_nonneg α 5 g'
  have hYh : 0 ≤ Work.FTS.GalFields.Xn5 α h := Work.Spaces.HkNorm_nonneg α 5 h
  have h1 : (1 : ℝ) ≤ 1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g' := by
    linarith
  have hS : (0 : ℝ) ≤ 1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g' :=
    le_trans zero_le_one h1
  calc Ci * α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α f * Work.FTS.Nonlin.Xn α u
      ≤ Ci * α ^ (-(1 / 2 : ℝ)) * (A * (1 + Work.FTS.GalFields.Xn5 α g
            + Work.FTS.GalFields.Xn5 α g')) * (B * Work.FTS.GalFields.Xn5 α h) := by
        have hc : 0 ≤ Ci * α ^ (-(1 / 2 : ℝ)) :=
          mul_nonneg hN.pos.1.le (Real.rpow_nonneg hα.le _)
        exact mul_le_mul (mul_le_mul_of_nonneg_left hfX hc) huX hXu
          (mul_nonneg hc (mul_nonneg hA hS))
    _ = Ci * α ^ (-(1 / 2 : ℝ)) * A * B
          * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
          * Work.FTS.GalFields.Xn5 α h := by ring

/-- **The `𝒲^{4,∞}`-product rule in normal form**: a coefficient `f` priced by
`|f|_{𝒲^{4,∞}} ≤ Cw`, times an honest `ℋ⁴`-function `u` carrying `B·|h|_{ℋ⁵}`. -/
theorem Xn_mul_wlInf {α α₂ Ci : ℝ} (hN : Work.FTS.OpenPkg.N4Norm' Ci α₂) (hα : 0 < α)
    (hαα₂ : α ≤ α₂) {f u h : Fn} (hfS : Work.FTS.EllipticEst.SmoothOpen f)
    (hfm : Work.Spaces.WlInfMem α 4 f) (huS : Work.FTS.EllipticEst.SmoothOpen u)
    (hu : Work.Spaces.HkMem α 4 u) {Cw B : ℝ} (hCw : Work.Spaces.WlInf α 4 f ≤ Cw)
    (huX : Work.FTS.Nonlin.Xn α u ≤ B * Work.FTS.GalFields.Xn5 α h) :
    Work.Spaces.HkMem α 4 (fun z θ => f z θ * u z θ) ∧
      Work.FTS.Nonlin.Xn α (fun z θ => f z θ * u z θ)
        ≤ Ci * α ^ (-(1 / 2 : ℝ)) * Cw * B * Work.FTS.GalFields.Xn5 α h := by
  have hprod := hN.wprod α ⟨hα, hαα₂⟩ f u hfS hfm ⟨huS, hu⟩
  refine ⟨hprod.1, le_trans hprod.2 ?_⟩
  have hW : 0 ≤ Work.Spaces.WlInf α 4 f := Work.Spaces.WlInf_nonneg α 4 f hfm
  have hCw0 : 0 ≤ Cw := le_trans hW hCw
  have hXu : 0 ≤ Work.FTS.Nonlin.Xn α u := Work.Spaces.HkNorm_nonneg α 4 u
  have hYh : 0 ≤ Work.FTS.GalFields.Xn5 α h := Work.Spaces.HkNorm_nonneg α 5 h
  have hc : 0 ≤ Ci * α ^ (-(1 / 2 : ℝ)) :=
    mul_nonneg hN.pos.1.le (Real.rpow_nonneg hα.le _)
  have h2 : Work.Spaces.WlInf α 4 f * Work.FTS.Nonlin.Xn α u
      ≤ Cw * (B * Work.FTS.GalFields.Xn5 α h) :=
    mul_le_mul hCw huX hXu hCw0
  calc Ci * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.WlInf α 4 f * Work.FTS.Nonlin.Xn α u
      = (Ci * α ^ (-(1 / 2 : ℝ))) * (Work.Spaces.WlInf α 4 f * Work.FTS.Nonlin.Xn α u) := by
        ring
    _ ≤ (Ci * α ^ (-(1 / 2 : ℝ))) * (Cw * (B * Work.FTS.GalFields.Xn5 α h)) :=
        mul_le_mul_of_nonneg_left h2 hc
    _ = Ci * α ^ (-(1 / 2 : ℝ)) * Cw * B * Work.FTS.GalFields.Xn5 α h := by ring

end Work.FTS.GalFields.RHS.Sharp
