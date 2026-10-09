import Mathlib
import Submission.Work.SSGRoute.PTDefs
import Submission.Work.SSGRoute.E9c.TransportDefs
import Submission.Work.SSGRoute.e7comega_defs
import Submission.Work.SSGRoute.localUnitsMap_exists
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.PT

open CategoryTheory SSGRoute.PTExt

/-- **The archimedean local units map is injective.**  For a tower `k ⊆ K ⊆ L` of number fields with
`K/k`, `L/k` finite Galois, an infinite place `w` of `K` and a place `u | w` of `L`, the local units
map `localUnitsMap k ↥K ↥L w u hu : res f K_wˣ ⟶ L_uˣ` is injective on carriers.

Short route (both reviewers confirmed): every element of the source carrier is `Additive.ofMul y`,
so by `Work.SSGRoute.localUnitsMap_spec` it suffices to know that
`NK.GlobalCFT.Place.localAlgebraMapUnits u w hu` is injective — which is the already-proved
`NK.GlobalCFT.Inclusion.globalCFT_localAlgebraMapUnits_injective` (arbitrary `LiesOver`, no
archimedean hypothesis). Hence a few lines: `intro a b hab`, write both as `ofMul`, rewrite with the
spec, and conclude with `Units.ext`/`Additive.ofMul.inj`. -/
theorem localUnitsMap_injective {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] {K L : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
    [NumberField ↥K] [FiniteDimensional k L] [IsGalois k L] [NumberField ↥L]
    [Algebra ↥K ↥L] [IsScalarTower k ↥K ↥L] [IsScalarTower ↥K ↥L Ω]
    (w : NK.GlobalCFT.Place ↥K)
    (hw : ∀ q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K),
      w ≠ NK.GlobalCFT.Place.ofFinite q)
    (u : NK.GlobalCFT.Place ↥L) (hu : NK.GlobalCFT.Place.LiesOver u w) :
    Function.Injective (fun a => (Work.SSGRoute.localUnitsMap k ↥K ↥L w u hu).hom a) := by
  intro a b hab
  -- Write `a` and `b`, elements of the source carrier `K_wˣ`, as `Additive.ofMul` of a unit.
  have ha : (Additive.ofMul (Additive.toMul a) :
      ↑(Rep.res (decompKRestrict k ↥K ↥L w u hu) (localUnitsK (k := k) w))) = a :=
    ofMul_toMul _
  have hb : (Additive.ofMul (Additive.toMul b) :
      ↑(Rep.res (decompKRestrict k ↥K ↥L w u hu) (localUnitsK (k := k) w))) = b :=
    ofMul_toMul _
  -- Rewrite `hab` with the computation rule `localUnitsMap_spec`.
  have key : Additive.ofMul (NK.GlobalCFT.Place.localAlgebraMapUnits u w hu (Additive.toMul a))
      = Additive.ofMul
        (NK.GlobalCFT.Place.localAlgebraMapUnits u w hu (Additive.toMul b)) :=
    (Work.SSGRoute.localUnitsMap_spec k ↥K ↥L w u hu (Additive.toMul a)).symm.trans
      (((congrArg (fun x => (Work.SSGRoute.localUnitsMap k ↥K ↥L w u hu).hom x) ha).trans
        (hab.trans
          (congrArg (fun x => (Work.SSGRoute.localUnitsMap k ↥K ↥L w u hu).hom x) hb.symm))).trans
        (Work.SSGRoute.localUnitsMap_spec k ↥K ↥L w u hu (Additive.toMul b)))
  -- The local algebra map on unit groups is injective.
  have hxy : Additive.toMul a = Additive.toMul b :=
    NK.GlobalCFT.Inclusion.globalCFT_localAlgebraMapUnits_injective hu
      (Additive.ofMul.injective key)
  exact ha.symm.trans ((congrArg Additive.ofMul hxy).trans hb)

end Work.SSGRoute.PT
