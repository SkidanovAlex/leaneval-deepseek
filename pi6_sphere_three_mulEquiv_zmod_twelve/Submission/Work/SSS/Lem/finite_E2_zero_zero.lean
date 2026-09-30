import Mathlib
import Submission.Work.SSS.baseRowDefs
import Submission.Work.SSS.LESFacts
import Submission.Work.SSS.Lem.mono_homologyMap_zero
import Submission.Work.SSS.Lem.E2_zero_zero_quot

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SSS.Lem

open CategoryTheory CategoryTheory.Limits

-- ℤ-modules carry two definitionally distinct `Module ℤ` structures (the structural one, and the
-- canonical one coming from the additive group structure); disable the canonical one so that the
-- layout of subtypes and quotients agrees with the structural instance.
attribute [-instance] AddCommGroup.toIntModule

theorem finite_E2_zero_zero {C : ChainComplex (ModuleCat ℤ) ℕ} (ξ : Work.SSS.Filtration C)
    (hH : Module.Finite ℤ (C.homology 0)) :
    Module.Finite ℤ (Work.SSS.E2 ξ 0 0) := by
  -- the inclusion `F_0 ⊆ C` factors as `F_0 ⊆ F_1 ⊆ C`
  have hfac : Work.SSS.incF ξ.F 0 ≫ ξ.incl 1 = ξ.incl 0 := ξ.compat (Nat.zero_le 1)
  have hcomp : HomologicalComplex.homologyMap (ξ.incl 0) 0 =
      HomologicalComplex.homologyMap (Work.SSS.incF ξ.F 0) 0 ≫
        HomologicalComplex.homologyMap (ξ.incl 1) 0 := by
    rw [← hfac, HomologicalComplex.homologyMap_comp]
  -- saturation in degree `1`: the inclusion `F_1 ⊆ C` is injective on `H_0`
  have hsat : IsIso ((ξ.incl 1).f 1) := ξ.sat 1
  have hmon : Mono (ξ.incl 1) := ξ.mono_incl 1
  have hmono : Mono (HomologicalComplex.homologyMap (ξ.incl 1) 0) :=
    mono_homologyMap_zero (ξ.incl 1) inferInstance inferInstance
  have hinj : Function.Injective (HomologicalComplex.homologyMap (ξ.incl 1) 0).hom :=
    (ModuleCat.mono_iff_injective _).mp hmono
  -- hence `ker ψ = ker φ`
  have hker : LinearMap.ker (HomologicalComplex.homologyMap (ξ.incl 0) 0).hom =
      LinearMap.ker (HomologicalComplex.homologyMap (Work.SSS.incF ξ.F 0) 0).hom := by
    rw [hcomp, ModuleCat.hom_comp, LinearMap.ker_comp, LinearMap.ker_eq_bot.mpr hinj,
      Submodule.comap_bot]
  -- `↥(E1 ξ 0 0) ⧸ ker φ` is a submodule of the finitely generated `H_0(C)`
  have hrange : Module.Finite ℤ
      ↥(LinearMap.range (HomologicalComplex.homologyMap (ξ.incl 0) 0).hom) := by
    refine Module.Finite.iff_fg.mpr (Submodule.FG.of_le
      (S := LinearMap.range (HomologicalComplex.homologyMap (ξ.incl 0) 0).hom)
      (T := ⊤) ?_ le_top)
    exact hH.fg_top
  have hquot : Module.Finite ℤ (↥(Work.SSS.E1 ξ 0 0) ⧸
      (LinearMap.ker (HomologicalComplex.homologyMap (ξ.incl 0) 0).hom)) :=
    (Module.Finite.equiv_iff
      (LinearMap.quotKerEquivRange (HomologicalComplex.homologyMap (ξ.incl 0) 0).hom).symm).mp
      hrange
  have hfin : Module.Finite ℤ (↥(Work.SSS.E1 ξ 0 0) ⧸
      (LinearMap.ker (HomologicalComplex.homologyMap (Work.SSS.incF ξ.F 0) 0).hom)) :=
    (Module.Finite.equiv_iff (Submodule.quotEquivOfEq _ _ hker)).mp hquot
  -- `E2 ξ 0 0` is that quotient
  obtain ⟨e⟩ := E2_zero_zero_quot ξ
  exact (Module.Finite.equiv_iff e.symm).mp hfin

end Work.SSS.Lem
