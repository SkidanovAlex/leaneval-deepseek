/-
# The diagonal `∗`-subring of `U₁ × U₂` and its `∗`-regular closure

Setup for the uniqueness of epic `∗`-regular envelopes ([JZLA20, Theorem 2.9] = [Ja17base,
Theorem 6.3]): given a `∗`-ring `R`, two `∗`-regular rings `U₁`, `U₂` and `∗`-homomorphisms
`φᵢ : R →+* Uᵢ`, form the *diagonal* homomorphism

`diagHom φ₁ φ₂ : R →+* U₁ × U₂`, `r ↦ (φ₁ r, φ₂ r)`,

whose image `Δ` is a `∗`-subring of `U₁ × U₂` (this is where the star-compatibility of `φ₁, φ₂`
is used), and the `∗`-regular closure `T := starRegularClosure Δ` of `Δ` inside `U₁ × U₂`.

This file only contains the definitions; the properties of `T` used by the uniqueness proof are
the subject of separate lemmas.
-/
import Mathlib
import Submission.Work.ORHughesFree.Epic
import Submission.Work.ORHughesFree.StarRegular

set_option autoImplicit false

universe u

namespace Work.ORHughesFree.Section3

open Work.ORHughesFree

variable {R : Type u} [Ring R] [StarRing R]
variable {U₁ : Type u} [Ring U₁] [StarRing U₁] {U₂ : Type u} [Ring U₂] [StarRing U₂]

/-- The diagonal homomorphism `r ↦ (φ₁ r, φ₂ r)` into the product. -/
def diagHom (φ₁ : R →+* U₁) (φ₂ : R →+* U₂) : R →+* U₁ × U₂ where
  toFun r := (φ₁ r, φ₂ r)
  map_one' := by simp
  map_mul' a b := by simp
  map_zero' := by simp
  map_add' a b := by simp

@[simp]
theorem diagHom_apply (φ₁ : R →+* U₁) (φ₂ : R →+* U₂) (r : R) :
    diagHom φ₁ φ₂ r = (φ₁ r, φ₂ r) := rfl

theorem star_diagHom (φ₁ : R →+* U₁) (φ₂ : R →+* U₂)
    (h₁ : ∀ x : R, φ₁ (star x) = star (φ₁ x)) (h₂ : ∀ x : R, φ₂ (star x) = star (φ₂ x))
    (r : R) : star (diagHom φ₁ φ₂ r) = diagHom φ₁ φ₂ (star r) := by
  rw [diagHom_apply, diagHom_apply, h₁ r, h₂ r]
  rfl

/-- The image of the diagonal homomorphism, as a `∗`-subring of the product.  The star-closure
uses that `φ₁, φ₂` are `∗`-homomorphisms. -/
def diagStarSubring (φ₁ : R →+* U₁) (φ₂ : R →+* U₂)
    (h₁ : ∀ x : R, φ₁ (star x) = star (φ₁ x)) (h₂ : ∀ x : R, φ₂ (star x) = star (φ₂ x)) :
    StarSubring (U₁ × U₂) where
  toSubring := (diagHom φ₁ φ₂).range
  star_mem' := by
    rintro x ⟨r, hr⟩
    refine ⟨star r, ?_⟩
    rw [← hr]
    exact (star_diagHom φ₁ φ₂ h₁ h₂ r).symm

theorem mem_diagStarSubring_iff (φ₁ : R →+* U₁) (φ₂ : R →+* U₂)
    (h₁ : ∀ x : R, φ₁ (star x) = star (φ₁ x)) (h₂ : ∀ x : R, φ₂ (star x) = star (φ₂ x))
    {x : U₁ × U₂} :
    x ∈ (diagStarSubring φ₁ φ₂ h₁ h₂ : Set (U₁ × U₂)) ↔ ∃ r : R, (φ₁ r, φ₂ r) = x := by
  constructor
  · rintro ⟨r, hr⟩
    exact ⟨r, hr⟩
  · rintro ⟨r, hr⟩
    exact ⟨r, hr⟩

/-- The `∗`-regular closure of the diagonal `∗`-subring inside `U₁ × U₂`. -/
noncomputable def diagClosure (φ₁ : R →+* U₁) (φ₂ : R →+* U₂)
    (h₁ : ∀ x : R, φ₁ (star x) = star (φ₁ x)) (h₂ : ∀ x : R, φ₂ (star x) = star (φ₂ x)) :
    StarSubring (U₁ × U₂) :=
  starRegularClosure (diagStarSubring φ₁ φ₂ h₁ h₂)

/-- The first projection `T →+* U₁` of the closure ring. -/
noncomputable def projFst (φ₁ : R →+* U₁) (φ₂ : R →+* U₂)
    (h₁ : ∀ x : R, φ₁ (star x) = star (φ₁ x)) (h₂ : ∀ x : R, φ₂ (star x) = star (φ₂ x)) :
    ↥(diagClosure φ₁ φ₂ h₁ h₂) →+* U₁ :=
  (RingHom.fst U₁ U₂).comp (Subring.subtype (diagClosure φ₁ φ₂ h₁ h₂).toSubring)

/-- The second projection `T →+* U₂` of the closure ring. -/
noncomputable def projSnd (φ₁ : R →+* U₁) (φ₂ : R →+* U₂)
    (h₁ : ∀ x : R, φ₁ (star x) = star (φ₁ x)) (h₂ : ∀ x : R, φ₂ (star x) = star (φ₂ x)) :
    ↥(diagClosure φ₁ φ₂ h₁ h₂) →+* U₂ :=
  (RingHom.snd U₁ U₂).comp (Subring.subtype (diagClosure φ₁ φ₂ h₁ h₂).toSubring)

@[simp]
theorem projFst_apply (φ₁ : R →+* U₁) (φ₂ : R →+* U₂)
    (h₁ : ∀ x : R, φ₁ (star x) = star (φ₁ x)) (h₂ : ∀ x : R, φ₂ (star x) = star (φ₂ x))
    (t : ↥(diagClosure φ₁ φ₂ h₁ h₂)) :
    projFst φ₁ φ₂ h₁ h₂ t = (t : U₁ × U₂).1 := rfl

@[simp]
theorem projSnd_apply (φ₁ : R →+* U₁) (φ₂ : R →+* U₂)
    (h₁ : ∀ x : R, φ₁ (star x) = star (φ₁ x)) (h₂ : ∀ x : R, φ₂ (star x) = star (φ₂ x))
    (t : ↥(diagClosure φ₁ φ₂ h₁ h₂)) :
    projSnd φ₁ φ₂ h₁ h₂ t = (t : U₁ × U₂).2 := rfl

/-- The diagonal map, corestricted to the closure ring. -/
noncomputable def toClosure (φ₁ : R →+* U₁) (φ₂ : R →+* U₂)
    (h₁ : ∀ x : R, φ₁ (star x) = star (φ₁ x)) (h₂ : ∀ x : R, φ₂ (star x) = star (φ₂ x)) :
    R →+* ↥(diagClosure φ₁ φ₂ h₁ h₂) :=
  (diagHom φ₁ φ₂).codRestrict (diagClosure φ₁ φ₂ h₁ h₂).toSubring
    (fun r => Work.ORHughesFree.subset_starRegularClosure (diagStarSubring φ₁ φ₂ h₁ h₂)
      (show diagHom φ₁ φ₂ r ∈ (diagStarSubring φ₁ φ₂ h₁ h₂ : Set (U₁ × U₂)) from ⟨r, rfl⟩))

@[simp]
theorem toClosure_apply (φ₁ : R →+* U₁) (φ₂ : R →+* U₂)
    (h₁ : ∀ x : R, φ₁ (star x) = star (φ₁ x)) (h₂ : ∀ x : R, φ₂ (star x) = star (φ₂ x))
    (r : R) :
    ((toClosure φ₁ φ₂ h₁ h₂ r : ↥(diagClosure φ₁ φ₂ h₁ h₂)) : U₁ × U₂) =
      diagHom φ₁ φ₂ r := rfl

/-- The two projections of the diagonal are `φ₁` and `φ₂`. -/
@[simp]
theorem projFst_toClosure (φ₁ : R →+* U₁) (φ₂ : R →+* U₂)
    (h₁ : ∀ x : R, φ₁ (star x) = star (φ₁ x)) (h₂ : ∀ x : R, φ₂ (star x) = star (φ₂ x))
    (r : R) : projFst φ₁ φ₂ h₁ h₂ (toClosure φ₁ φ₂ h₁ h₂ r) = φ₁ r := rfl

@[simp]
theorem projSnd_toClosure (φ₁ : R →+* U₁) (φ₂ : R →+* U₂)
    (h₁ : ∀ x : R, φ₁ (star x) = star (φ₁ x)) (h₂ : ∀ x : R, φ₂ (star x) = star (φ₂ x))
    (r : R) : projSnd φ₁ φ₂ h₁ h₂ (toClosure φ₁ φ₂ h₁ h₂ r) = φ₂ r := rfl

/-- The corestricted diagonal is a `∗`-homomorphism. -/
theorem toClosure_star (φ₁ : R →+* U₁) (φ₂ : R →+* U₂)
    (h₁ : ∀ x : R, φ₁ (star x) = star (φ₁ x)) (h₂ : ∀ x : R, φ₂ (star x) = star (φ₂ x))
    (x : R) : toClosure φ₁ φ₂ h₁ h₂ (star x) = star (toClosure φ₁ φ₂ h₁ h₂ x) := by
  apply Subtype.ext
  show (diagHom φ₁ φ₂ (star x) : U₁ × U₂) = star (diagHom φ₁ φ₂ x : U₁ × U₂)
  rw [diagHom_apply, diagHom_apply, h₁ x, h₂ x]
  rfl

end Work.ORHughesFree.Section3
