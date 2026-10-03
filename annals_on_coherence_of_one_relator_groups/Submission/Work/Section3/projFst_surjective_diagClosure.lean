import Mathlib
import Submission.Work.ORHughesFree.Section3.DiagClosureDefs
import Submission.Work.ORHughesFree.Epic.starRegularClosure_eq_top
import Submission.Work.ORHughesFree.StarRegular.starRegularClosure_le
import Submission.Work.ORHughesFree.StarRegular.starRegularClosure_isStarRegular
import Submission.Work.Section3.UniverseStenstrom.epicSurjectiveU

set_option autoImplicit false

universe u

namespace Work.Section3

open Work.ORHughesFree

/-- A product of `∗`-regular rings is `∗`-regular: weak inverses are taken componentwise and
properness of the involution is checked componentwise. -/
theorem isStarRegular_prod_diagClosure {U₁ U₂ : Type u} [Ring U₁] [StarRing U₁]
    [Work.ORHughesFree.IsStarRegular U₁] [Ring U₂] [StarRing U₂]
    [Work.ORHughesFree.IsStarRegular U₂] : Work.ORHughesFree.IsStarRegular (U₁ × U₂) where
  vonNeumannRegular := ⟨fun x => by
    obtain ⟨y₁, hy₁⟩ := (inferInstance : VonNeumannRegularRing U₁).exists_mul_inverse x.1
    obtain ⟨y₂, hy₂⟩ := (inferInstance : VonNeumannRegularRing U₂).exists_mul_inverse x.2
    exact ⟨(y₁, y₂), by ext <;> simp [hy₁, hy₂]⟩⟩
  proper := fun x hx => by
    have h1 : star x.1 * x.1 = 0 := by simpa using congrArg Prod.fst hx
    have h2 : star x.2 * x.2 = 0 := by simpa using congrArg Prod.snd hx
    exact Prod.ext ((inferInstance : Work.ORHughesFree.IsStarRegular U₁).proper x.1 h1)
      ((inferInstance : Work.ORHughesFree.IsStarRegular U₂).proper x.2 h2)

/-- The first projection `T →+* U₁` of the `∗`-regular closure `T` of the diagonal is surjective
whenever `φ₁` is epic: `projFst` is epic (its composite with the corestricted diagonal `toClosure`
is `φ₁`) and its source is von Neumann regular, being `∗`-regular; an epic homomorphism out of a
von Neumann regular ring is surjective (Stenström XI.1.4 / Gardner). -/
theorem projFst_surjective_diagClosure {R U₁ U₂ : Type u} [Ring R] [StarRing R]
    [Ring U₁] [StarRing U₁] [Work.ORHughesFree.IsStarRegular U₁]
    [Ring U₂] [StarRing U₂] [Work.ORHughesFree.IsStarRegular U₂]
    (φ₁ : R →+* U₁) (φ₂ : R →+* U₂) (h₁ : ∀ x : R, φ₁ (star x) = star (φ₁ x))
    (h₂ : ∀ x : R, φ₂ (star x) = star (φ₂ x)) (hep : Work.ORHughesFree.IsEpic φ₁) :
    Function.Surjective (Work.ORHughesFree.Section3.projFst φ₁ φ₂ h₁ h₂) := by
  -- `U₁ × U₂` is `∗`-regular, hence so is the `∗`-regular closure `T` of the diagonal.
  haveI hprod : IsStarRegular (U₁ × U₂) := isStarRegular_prod_diagClosure
  haveI : IsStarRegular ↥(Work.ORHughesFree.Section3.diagClosure φ₁ φ₂ h₁ h₂) :=
    Work.ORHughesFree.StarRegular.starRegularClosure_isStarRegular
      (Work.ORHughesFree.Section3.diagStarSubring φ₁ φ₂ h₁ h₂)
  haveI : VonNeumannRegularRing ↥(Work.ORHughesFree.Section3.diagClosure φ₁ φ₂ h₁ h₂) :=
    inferInstance
  -- `projFst ∘ toClosure = φ₁`, an epic homomorphism, so `projFst` is epic.
  have hcomp : (Work.ORHughesFree.Section3.projFst φ₁ φ₂ h₁ h₂).comp
        (Work.ORHughesFree.Section3.toClosure φ₁ φ₂ h₁ h₂) = φ₁ :=
    RingHom.ext fun r => by
      simp [Work.ORHughesFree.Section3.projFst_toClosure]
  have hepic : Work.ORHughesFree.IsEpic (Work.ORHughesFree.Section3.projFst φ₁ φ₂ h₁ h₂) :=
    Work.ORHughesFree.IsEpic.of_comp
      (f := Work.ORHughesFree.Section3.toClosure φ₁ φ₂ h₁ h₂)
      (g := Work.ORHughesFree.Section3.projFst φ₁ φ₂ h₁ h₂)
      (hcomp.symm ▸ hep)
  -- An epic homomorphism out of a von Neumann regular ring is surjective.
  exact Work.Section3.UniverseStenstrom.surjective_of_isEpic_vnRegularU
    (Work.ORHughesFree.Section3.projFst φ₁ φ₂ h₁ h₂) hepic

end Work.Section3
