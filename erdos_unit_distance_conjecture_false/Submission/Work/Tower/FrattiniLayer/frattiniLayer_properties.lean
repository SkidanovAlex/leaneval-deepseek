import Mathlib
import Submission.Work.Tower.FrattiniLayer.Basic
import Submission.Work.Tower.FrattiniLayer.isUnramifiedOver_of_algEquiv
import Submission.Work.Tower.TowerCut.isUnramifiedExtensionForallPrimes_iSup

/-!
# Properties of the Frattini layer

For a number field `F` and a field `Ω/F` whose set `cubicUnramifiedSet F Ω` of cubic everywhere
unramified Galois extensions of `F` is *finite*, the Frattini layer
`frattiniLayer F Ω = ⨆ M ∈ cubicUnramifiedSet F Ω, M` is a finite, Galois, everywhere unramified
extension of `F`.

The three components of the proof:

* **Finiteness.** `frattiniLayer F Ω` is the supremum of a finite family of finite-dimensional
  extensions, hence finite-dimensional by `IntermediateField.finiteDimensional_iSup_of_finite`
  (the instance even covers the empty index set).
* **Galois.** Each factor is Galois, and a compositum of normal (resp. separable) extensions is
  normal (resp. separable) by `IntermediateField.normal_iSup` / `IntermediateField.isSeparable_iSup`.
* **Unramifiedness.** In the nonempty case, unramifiedness passes to finite composita
  (`Work.Tower.TowerCut.isUnramifiedExtensionForallPrimes_iSup`, transported to `IsUnramifiedOver`
  by the interface `isUnramifiedOver_iff_forallPrimes`); the empty case is the trivial extension
  `F/F`, transported to `↥⊥ ≃ₐ[F] F`.
-/

open NumberField

namespace Work.Tower.FrattiniLayer

/-- **Unramifiedness of the trivial extension**: the identity `𝓞 F → 𝓞 F` is unramified at every
prime.  (`IsUnramifiedAt R q` is `FormallyUnramified R (Localization.AtPrime q)`, and localizations
are formally unramified.) -/
theorem isUnramifiedAt_self {F : Type*} [Field F] [NumberField F] (𝔓 : Ideal (𝓞 F)) [𝔓.IsPrime] :
    Algebra.IsUnramifiedAt (𝓞 F) 𝔓 := inferInstance

/-- `IsUnramifiedOver F F` holds: `F/F` is unramified at every finite prime. -/
theorem isUnramifiedOver_self {F : Type*} [Field F] [NumberField F] :
    Work.Tower.FrattiniLayer.IsUnramifiedOver F F :=
  fun 𝔓 => isUnramifiedAt_self 𝔓

set_option linter.style.haveILetI false in
theorem frattiniLayer_properties {F Ω : Type*} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    (hS : (Work.Tower.FrattiniLayer.cubicUnramifiedSet F Ω).Finite) :
    Module.Finite F ↥(Work.Tower.FrattiniLayer.frattiniLayer F Ω) ∧
    IsGalois F ↥(Work.Tower.FrattiniLayer.frattiniLayer F Ω) ∧
    Work.Tower.FrattiniLayer.IsUnramifiedOver F ↥(Work.Tower.FrattiniLayer.frattiniLayer F Ω) := by
  classical
  -- The index set of the defining supremum is finite.
  haveI : Finite ↥(Work.Tower.FrattiniLayer.cubicUnramifiedSet F Ω) :=
    Set.finite_coe_iff.mpr hS
  -- Every factor is finite-dimensional, Galois, unramified and a number field.
  haveI hfin : ∀ M : ↥(Work.Tower.FrattiniLayer.cubicUnramifiedSet F Ω),
      FiniteDimensional F ↥(M : IntermediateField F Ω) :=
    fun M => FiniteDimensional.of_finrank_pos (by have h := M.2.1; rw [h]; norm_num)
  haveI hgal : ∀ M : ↥(Work.Tower.FrattiniLayer.cubicUnramifiedSet F Ω),
      IsGalois F ↥(M : IntermediateField F Ω) := fun M => M.2.2.1
  haveI hnorm : ∀ M : ↥(Work.Tower.FrattiniLayer.cubicUnramifiedSet F Ω),
      Normal F ↥(M : IntermediateField F Ω) := fun M => (hgal M).to_normal
  haveI hsep : ∀ M : ↥(Work.Tower.FrattiniLayer.cubicUnramifiedSet F Ω),
      Algebra.IsSeparable F ↥(M : IntermediateField F Ω) := fun M => (hgal M).to_isSeparable
  haveI hunr : ∀ M : ↥(Work.Tower.FrattiniLayer.cubicUnramifiedSet F Ω),
      Work.Tower.FrattiniLayer.IsUnramifiedOver F ↥(M : IntermediateField F Ω) :=
    fun M => M.2.2.2
  haveI hnf : ∀ M : ↥(Work.Tower.FrattiniLayer.cubicUnramifiedSet F Ω),
      NumberField ↥(M : IntermediateField F Ω) :=
    fun M => NumberField.of_module_finite F ↥(M : IntermediateField F Ω)
  refine ⟨?_, ?_, ?_⟩
  · -- finiteness: a finite supremum of finite-dimensional extensions is finite-dimensional
    rw [Work.Tower.FrattiniLayer.frattiniLayer]
    infer_instance
  · -- Galois: a supremum of normal, separable extensions is normal and separable
    rw [Work.Tower.FrattiniLayer.frattiniLayer]
    exact IsGalois.mk
  · -- unramifiedness
    rw [Work.Tower.FrattiniLayer.frattiniLayer]
    by_cases hne : Nonempty ↥(Work.Tower.FrattiniLayer.cubicUnramifiedSet F Ω)
    · -- nonempty index set: apply the finite-compositum theorem
      haveI : Nonempty ↥(Work.Tower.FrattiniLayer.cubicUnramifiedSet F Ω) := hne
      haveI : NumberField ↥(⨆ M : ↥(Work.Tower.FrattiniLayer.cubicUnramifiedSet F Ω),
          (M : IntermediateField F Ω)) := NumberField.of_module_finite F _
      rw [Work.Tower.FrattiniLayer.isUnramifiedOver_iff_forallPrimes]
      refine Work.Tower.TowerCut.isUnramifiedExtensionForallPrimes_iSup
        (fun M : ↥(Work.Tower.FrattiniLayer.cubicUnramifiedSet F Ω) =>
          (M : IntermediateField F Ω)) ?_
      intro M
      exact (Work.Tower.FrattiniLayer.isUnramifiedOver_iff_forallPrimes (F := F)
        (L := ↥(M : IntermediateField F Ω))).mp (hunr M)
    · -- empty index set: the layer is `⊥ ≅ F`, and `F/F` is unramified
      haveI : IsEmpty ↥(Work.Tower.FrattiniLayer.cubicUnramifiedSet F Ω) :=
        not_nonempty_iff.mp hne
      rw [iSup_of_empty]
      exact Work.Tower.FrattiniLayer.isUnramifiedOver_of_algEquiv
        (IntermediateField.botEquiv F Ω).symm (isUnramifiedOver_self (F := F))

end Work.Tower.FrattiniLayer
