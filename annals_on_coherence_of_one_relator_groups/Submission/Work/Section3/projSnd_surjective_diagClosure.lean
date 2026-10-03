import Mathlib
import Submission.Work.ORHughesFree.Section3.DiagClosureDefs
import Submission.Work.ORHughesFree.StarRegular.starRegularClosure_isStarRegular
import Submission.Work.Section3.epicSurjectiveUniverse

set_option autoImplicit false

universe u

namespace Work.Section3

open Work.ORHughesFree

/-!
# Surjectivity of the second projection of the diagonal `∗`-regular closure

Given a `∗`-ring `R`, two `∗`-regular rings `U₁`, `U₂` and `∗`-homomorphisms `φᵢ : R →+* Uᵢ`,
let `T ⊆ U₁ × U₂` be the `∗`-regular closure of the diagonal `Δ = {(φ₁ r, φ₂ r)}`.  We show
that the second projection `projSnd : T →+* U₂` is surjective as soon as `φ₂` is epic.

The argument is short once the two structural facts are in place:

* `projSnd` is *epic*: its composition with the corestricted diagonal `toClosure : R →+* T` is
  `φ₂`, which is epic, so `projSnd` is epic by `IsEpic.of_comp`;
* `T` is von Neumann regular, being `∗`-regular (`starRegularClosure_isStarRegular`: the
  `∗`-regular closure of a `∗`-subring of the `∗`-regular ring `U₁ × U₂` is `∗`-regular, and
  `U₁ × U₂` is `∗`-regular because `IsStarRegular` is checked componentwise).

Then an epic homomorphism out of a von Neumann regular ring is surjective
(`stenstromVnRegularU`, the universe-general form of Stenström XI.1.4 / Gardner).

This is the argument of [JZLA20, §2.3, Proposition 2.7] (cited there as [Ste, Proposition
XI.1.4]); it is the ingredient of the uniqueness of epic `∗`-regular envelopes
([JZLA20, Theorem 2.9]) that shows that the two projections of the diagonal closure are
surjective.
-/

/-- A product of `∗`-regular rings is `∗`-regular: weak inverses are taken componentwise and
properness of the involution is checked componentwise. -/
instance instIsStarRegularProd {U₁ U₂ : Type u} [Ring U₁] [StarRing U₁] [Ring U₂]
    [StarRing U₂] [IsStarRegular U₁] [IsStarRegular U₂] : IsStarRegular (U₁ × U₂) where
  vonNeumannRegular := ⟨fun x => by
    obtain ⟨y₁, hy₁⟩ := (inferInstance : VonNeumannRegularRing U₁).exists_mul_inverse x.1
    obtain ⟨y₂, hy₂⟩ := (inferInstance : VonNeumannRegularRing U₂).exists_mul_inverse x.2
    exact ⟨(y₁, y₂), by ext <;> simp [hy₁, hy₂]⟩⟩
  proper := fun x hx => by
    ext
    · exact (IsStarRegular.proper (R := U₁)) x.1 (by simpa using congrArg Prod.fst hx)
    · exact (IsStarRegular.proper (R := U₂)) x.2 (by simpa using congrArg Prod.snd hx)

theorem projSnd_surjective_diagClosure {R U₁ U₂ : Type u} [Ring R] [StarRing R]
    [Ring U₁] [StarRing U₁] [Work.ORHughesFree.IsStarRegular U₁]
    [Ring U₂] [StarRing U₂] [Work.ORHughesFree.IsStarRegular U₂]
    (φ₁ : R →+* U₁) (φ₂ : R →+* U₂) (h₁ : ∀ x : R, φ₁ (star x) = star (φ₁ x))
    (h₂ : ∀ x : R, φ₂ (star x) = star (φ₂ x)) (hep : Work.ORHughesFree.IsEpic φ₂) :
    Function.Surjective (Work.ORHughesFree.Section3.projSnd φ₁ φ₂ h₁ h₂) := by
  -- The ambient ring `U₁ × U₂` is `∗`-regular, componentwise.
  haveI hprod : IsStarRegular (U₁ × U₂) := instIsStarRegularProd
  -- The `∗`-regular closure `T` of the diagonal is `∗`-regular, hence von Neumann regular.
  haveI hT : IsStarRegular ↥(Work.ORHughesFree.Section3.diagClosure φ₁ φ₂ h₁ h₂) :=
    Work.ORHughesFree.StarRegular.starRegularClosure_isStarRegular
      (Work.ORHughesFree.Section3.diagStarSubring φ₁ φ₂ h₁ h₂)
  haveI : VonNeumannRegularRing ↥(Work.ORHughesFree.Section3.diagClosure φ₁ φ₂ h₁ h₂) :=
    inferInstance
  -- `projSnd ∘ toClosure = φ₂`, an epic homomorphism; hence `projSnd` is epic.
  have hcomp : (Work.ORHughesFree.Section3.projSnd φ₁ φ₂ h₁ h₂).comp
        (Work.ORHughesFree.Section3.toClosure φ₁ φ₂ h₁ h₂) = φ₂ :=
    RingHom.ext fun r => by
      rw [RingHom.comp_apply, Work.ORHughesFree.Section3.projSnd_toClosure]
  have hepic : Work.ORHughesFree.IsEpic (Work.ORHughesFree.Section3.projSnd φ₁ φ₂ h₁ h₂) :=
    Work.ORHughesFree.IsEpic.of_comp
      (f := Work.ORHughesFree.Section3.toClosure φ₁ φ₂ h₁ h₂)
      (g := Work.ORHughesFree.Section3.projSnd φ₁ φ₂ h₁ h₂)
      (hcomp.symm ▸ hep)
  -- An epic homomorphism out of a von Neumann regular ring is surjective.
  exact Work.Section3.EpicSurjectiveUniverse.stenstromVnRegularU _ hepic

end Work.Section3
