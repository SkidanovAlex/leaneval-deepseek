import Mathlib.RepresentationTheory.Coinduced
import Mathlib.RingTheory.Henselian
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RepresentationTheory.Rep.Iso
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass
import Submission.Work.SSGRoute.PT.e1a_beta_can
import Submission.Work.SSGRoute.PT.e1a_localComparison_bricks
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END
set_option maxHeartbeats 1000000

namespace Work.SSGRoute.ExtChain

open CategoryTheory SSGRoute.PTExt
open scoped TensorProduct

-- The `extLoc`/`extToIdeles`/`unitsK` terms below are equal to the `Rep.resFunctor`-spelled ones
-- only up to unfolding `Rep.res`/`freeCoverSES`/`ShortComplex.map` (the same situation as in
-- `NK/HassePrinciple/locUnits_compatible.lean` and in `PT/e1a_localComparison_bricks.lean`).
set_option backward.isDefEq.respectTransparency false

-- in module `Submission.Work.SSGRoute.ExtChain.extLoc_extToIdeles_e1aSyzShift_eq_zero_imp`,
-- namespace `Work.SSGRoute.ExtChain`; context: `open CategoryTheory SSGRoute.PTExt`, `open scoped TensorProduct`
/-- **The converse of `SSGStage.extLoc_extToIdeles_e1aSyzShift_eq_zero`.**  For `z ∈ Ext¹_{Gal(K/k)}(R, Kˣ)`
with `R = ker (freeCover N)` the canonical syzygy of `N`, the vanishing of the `q`-component of the
idèle localisation of `y = e1aSyzShift N z` is *equivalent* to the vanishing of the localised
degree-one class `(extRes_{D_q} z) ∘ mk₀ (unitsToLocalUnits)`.

The `⟸` direction is proved (`SSGStage.extLoc_extToIdeles_e1aSyzShift_eq_zero`); this is the
`⟹` direction, which the "himg" half of the chain–localisation comparison needs in order to read
the hypothesis `extToIdeles y = 0` as `z_w = 0`.  Route: `extLoc_extToIdeles_eq` followed by
`e1aShiftEquiv_extRes` exhibits `extLoc_q (extToIdeles (e1aSyzShift N z))` as the image of
`(extRes_{D_q} z) ∘ mk₀ (unitsToLocalUnits)` under the *localised* syzygy shift
`x ↦ ((freeCoverSES N).map (Rep.resFunctor (decompK q).subtype)).extClass.comp x _`, which is
injective (`ExtChain.bijective_extClass_precomp`, the same brick that proves
`e1aShiftEquiv_extRes`; `ExtChain/ext_shift_natural_res.lean`). -/
theorem extLoc_extToIdeles_e1aSyzShift_eq_zero_imp {k : Type} [Field k] [NumberField k]
    {Ω : Type} [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField K]
    (N : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) [Finite N.V]
    (q : NK.GlobalCFT.Place K)
    (z : CategoryTheory.Abelian.Ext.{0}
        (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover N)) (SSGRoute.PTExt.unitsK k K) 1) :
    SSGRoute.PTExt.extLoc (k := k) q
        (SSGRoute.PTExt.extToIdeles (k := k)
          (Work.SSGRoute.ExtChain.e1aSyzShift (k := k) (K := K) N z)) = 0 →
      (SSGRoute.PTExt.extRes (SSGRoute.PTExt.decompK (k := k) q).subtype z).comp
        (CategoryTheory.Abelian.Ext.mk₀ (NK.HassePrinciple.unitsToLocalUnits k K q))
        (add_zero 1) = 0 := by
  intro h
  haveI hproj : CategoryTheory.Projective (Work.SSGRoute.freeCoverSES N).X₂ :=
    Rep.free_projective (k := SSGRoute.PTExt.Coeff) (G := K ≃ₐ[k] K) (α := N.V)
  -- `extLoc_q ∘ extToIdeles` is "restrict to `D_q` and apply `Kˣ → K_qˣ`".
  rw [Work.SSGRoute.SSGStage.extLoc_extToIdeles_eq (k := k) (K := ↥K) q
    (Work.SSGRoute.ExtChain.e1aSyzShift (k := k) (K := K) N z)] at h
  -- the syzygy shift commutes with restriction, so this is the localised syzygy shift applied to
  -- the degree-one class `(extRes_{D_q} z) ∘ mk₀ (unitsToLocalUnits)`.
  rw [Work.SSGRoute.ExtChain.e1aSyzShift,
    Work.SSGRoute.SSGStage.e1aShiftEquiv_extRes (SSGRoute.PTExt.decompK (k := k) q)
      (Work.SSGRoute.freeCoverSES N) (Work.SSGRoute.freeCoverSES_shortExact N)
      (SSGRoute.PTExt.unitsK k K) 1 (le_refl 1) z] at h
  -- reassociate so that the degree-one class becomes the argument of the connecting map.
  rw [CategoryTheory.Abelian.Ext.comp_assoc_of_third_deg_zero] at h
  haveI hprojD : CategoryTheory.Projective
      ((Work.SSGRoute.freeCoverSES N).map
        (Rep.resFunctor (k := SSGRoute.PTExt.Coeff)
          (SSGRoute.PTExt.decompK (k := k) q).subtype)).X₂ :=
    Functor.projective_obj
      (Rep.resFunctor (k := SSGRoute.PTExt.Coeff)
        (SSGRoute.PTExt.decompK (k := k) q).subtype)
      (Work.SSGRoute.freeCoverSES N).X₂
  have hSD : ((Work.SSGRoute.freeCoverSES N).map
      (Rep.resFunctor (k := SSGRoute.PTExt.Coeff)
        (SSGRoute.PTExt.decompK (k := k) q).subtype)).ShortExact :=
    (Work.SSGRoute.freeCoverSES_shortExact N).map_of_exact
      (Rep.resFunctor (k := SSGRoute.PTExt.Coeff)
        (SSGRoute.PTExt.decompK (k := k) q).subtype)
  -- The localised syzygy shift is injective.
  have hbij := Work.SSGRoute.ExtChain.bijective_extClass_precomp hSD
    (SSGRoute.PTExt.localUnitsK (k := k) q) (le_refl 1) (by omega : 1 + 1 = 1 + 1)
  have hpre : (hSD.extClass.precomp (SSGRoute.PTExt.localUnitsK (k := k) q)
      (by omega : 1 + 1 = 1 + 1))
        ((SSGRoute.PTExt.extRes (SSGRoute.PTExt.decompK (k := k) q).subtype z).comp
          (CategoryTheory.Abelian.Ext.mk₀ (NK.HassePrinciple.unitsToLocalUnits k K q))
          (add_zero 1)) = 0 := h
  exact hbij.1 (by rw [hpre, map_zero])

end Work.SSGRoute.ExtChain
