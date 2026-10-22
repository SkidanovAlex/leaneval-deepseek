import Mathlib
import Submission.Work.ANALYTIC.CechPt.DualCechBridge
import Submission.Work.ANALYTIC.CechPt.DdZfAux
import Submission.Work.ANALYTIC.CechPt.gamma_phiT
import Submission.Work.ANALYTIC.CechPt.lamHat_lamInf_zz
import Submission.Work.ANALYTIC.CechPt.toPointEquiv_lcDisc_span_zz

/-!
# Compatibility of the bridge with the augmentation of the dual Čech complex

The bridge `sdBridge T : sd (ℤ[T]) ≅ C(T,ℤ)_disc` of `DualCechBridge.lean` identifies the single
dual of the free module on a light profinite set `T` with the discrete group of locally constant
`ℤ`-valued functions on `T`.  This module proves the one compatibility with the *augmentation*
that the contraction of the dual Čech complex needs:

`rho ≫ (sdBridge C_0).hom = (𝟙 ≅ C(C_0,ℤ)_disc) (1 ↦ 1)  ,`

i.e. the augmentation `rho` (the "constant function `1`") is sent by the bridge to the generator
`1 ↦ 1` of `C(C_0,ℤ)_disc`.

The computation is that of `sdBridge_rho.lean`: the two sides are morphisms `𝟙 ⟶ Cdisc C_0`, the
functor `toPointEquiv : (𝟙 ⟶ Y) ≃ Y(∗)` is injective, and both sides have image the constant
function `1` — the left one by `gamma_phiT_aux` (the bridge evaluates a section `phiOf (zf T) lam`
to `lamHat T lam`, and `rho = phiOf (zf (cechTerm 0)) (lamInf (cechTerm 0))` with
`lamHat T (lamInf T) = 1`), the right one by `toPointEquiv_lcDisc_span_zz`.
-/

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed
open _root_.LightCondensed _root_.LightCondensed.Solid

noncomputable section

namespace Work.ANALYTIC.CechPt

/-- **Compatibility of the bridge with the augmentation.**  The augmentation `rho` of the dual
Čech complex (the constant function `1`) corresponds, under the bridge, to the generator
`1 ↦ 1` of the discrete group of locally constant functions. -/
theorem sdBridgeRho :
    rho ≫ (sdBridge (cechTerm 0)).hom
      = lcDiscIntIso.inv ≫
        (LightCondMod.LocallyConstant.functor ℤ).map
          (ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ (LocallyConstant ↥(cechTerm 0) ℤ)
            (1 : LocallyConstant ↥(cechTerm 0) ℤ))) := by
  have hrho : rho = phiOf (zf (cechTerm 0)) (lamInf (cechTerm 0)) := rfl
  have hsd : sdBridge (cechTerm 0) = phiT (cechTerm 0) := rfl
  apply (Work.ATOM.toPointEquiv (Work.ANALYTIC.Cdisc (cechTerm 0))).injective
  rw [hrho, hsd, gamma_phiT_aux]
  rw [lamHat_lamInf_zz]
  exact (toPointEquiv_lcDisc_span_zz (cechTerm 0)).symm

end Work.ANALYTIC.CechPt
