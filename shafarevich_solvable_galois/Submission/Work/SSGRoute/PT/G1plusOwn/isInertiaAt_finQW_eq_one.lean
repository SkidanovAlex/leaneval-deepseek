import Mathlib
import Submission.Work.SSGRoute.PT.levelPair_unramified_eq_zero
import Submission.Work.SSGRoute.inertiaSub_image_eq_levelInertia
import Submission.Work.SSGRoute.primeOfLevel_mem_iff_k
import Submission.Work.SSGRoute.PT.G1plusOwn.levelFree
import Submission.Work.SSGRoute.InertiaDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.PT.G1plusOwn

open scoped Pointwise

/-- **`finQW L A hA` is the prime of `𝓞 L` below `A`, i.e. it is `Work.SSGRoute.levelPrime`.**

Both are `HeightOneSpectrum`s of `𝓞 ↥L` whose maximal ideal is characterised by
`y ∈ P ↔ A.valuation ((y : ↥L) : Ω) < 1` (`PT.finQW_spec`, `primeOfLevel_mem_iff_k`), so
`IsDedekindDomain.HeightOneSpectrum.ext` finishes. -/
theorem finQW_eq_levelPrime_galois
    (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (L : IntermediateField k Ω) [FiniteDimensional k L] [IsGalois k L]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) :
    Work.SSGRoute.PT.finQW L A hA = Work.SSGRoute.levelPrime k Ω A hA L := by
  haveI hSep : IsSepClosure k Ω := IsSepClosure.of_isAlgClosure_of_perfectField k Ω
  haveI : NumberField ↥L := NumberField.of_module_finite k ↥L
  have hA' : A.comap (algebraMap k Ω) ≠ ⊤ := hA
  ext x
  rw [Work.SSGRoute.PT.finQW_spec L A hA x,
    Work.SSGRoute.primeOfLevel_mem_iff_k k Ω A hA L x]
  simp only [IsScalarTower.algebraMap_apply (NumberField.RingOfIntegers ↥L) ↥L Ω]
  rfl

/-- **The inertia at the level prime of a level unramified over `k` is trivial.**

`k` a number field, `Ω` an algebraic closure, `L ≤ Ω` a finite Galois level over `k` which is
unramified at the finite place `A` of `Ω` (`hI : I_A ≤ L.fixingSubgroup`), `finQW L A hA` the prime
of `𝓞 L` below `A`.  Then every `σ ∈ Gal(L/k)` acting trivially on the residue field at that prime
is `1`.

Route: `Work.SSGRoute.PT.isInertiaAt_iff_mem_inertia_local` turns `IsInertiaAt` into membership in
`Ideal.inertia (↥L ≃ₐ[k] ↥L) (finQW L A hA).asIdeal`; `Work.SSGRoute.PT.finQW_spec` and
`Work.SSGRoute.primeOfLevel_mem_iff_k` show `finQW L A hA = levelPrime k Ω A hA L` (both
`HeightOneSpectrum`s of `𝓞 ↥L` with the same `asIdeal`, characterised by
`y ∈ P ↔ A.valuation ((y : ↥L) : Ω) < 1`; use `IsDedekindDomain.HeightOneSpectrum.ext`); and
`Work.SSGRoute.inertiaSub_image_eq_levelInertia` identifies that inertia with
`(inertiaSub k Ω A).map (AlgEquiv.restrictNormalHom L)` (`levelInertiaOf` is that ideal inertia by
`rfl`).  So `σ = AlgEquiv.restrictNormalHom L ι` for some `ι ∈ I_A ≤ L.fixingSubgroup
= ker (AlgEquiv.restrictNormalHom L)` (`IntermediateField.restrictNormalHom_ker`), whence `σ = 1`. -/
theorem isInertiaAt_finQW_eq_one
    (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (L : IntermediateField k Ω) [FiniteDimensional k L] [IsGalois k L]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (hI : Work.SSGRoute.inertiaSub k Ω A ≤ L.fixingSubgroup)
    (σ : ↥L ≃ₐ[k] ↥L)
    (hσ : SSGRoute.PTExt.IsInertiaAt (Work.SSGRoute.PT.finQW L A hA) σ) : σ = 1 := by
  haveI : Normal k L := IsGalois.to_normal
  haveI : NumberField ↥L := NumberField.of_module_finite k ↥L
  -- The image of `I_A` in `Gal(L/k)` is trivial, because `I_A` fixes `L` pointwise.
  have hbot : (Work.SSGRoute.inertiaSub k Ω A).map (AlgEquiv.restrictNormalHom L) = ⊥ := by
    rw [Subgroup.map_eq_bot_iff]
    intro x hx
    have hx' : x ∈ L.fixingSubgroup := hI hx
    rwa [← IntermediateField.restrictNormalHom_ker] at hx'
  -- Hence the level inertia (the ideal inertia at `levelPrime`) is trivial.
  have himg : Ideal.inertia (↥L ≃ₐ[k] ↥L)
      (Work.SSGRoute.levelPrime k Ω A hA L).asIdeal = ⊥ := by
    have h2 := Work.SSGRoute.inertiaSub_image_eq_levelInertia k Ω A hA L
    rw [hbot] at h2
    exact h2.symm
  -- `IsInertiaAt` at `finQW` is membership in that inertia.
  have hmem : σ ∈ Ideal.inertia (↥L ≃ₐ[k] ↥L)
      (Work.SSGRoute.PT.finQW L A hA).asIdeal :=
    (Work.SSGRoute.PT.isInertiaAt_iff_mem_inertia_local
      (Work.SSGRoute.PT.finQW L A hA) σ).mp hσ
  rw [finQW_eq_levelPrime_galois k Ω L A hA, himg] at hmem
  simpa using hmem

end Work.SSGRoute.PT.G1plusOwn
