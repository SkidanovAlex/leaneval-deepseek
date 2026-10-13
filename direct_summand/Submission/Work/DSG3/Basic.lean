import Mathlib
import Submission.Work.DSMap.Map

/-!
# DSG3 — the multisection reduction (area G3 of the `direct_summand` proof map)

This module holds the vocabulary shared by the area: the generic point of `Spec A` for a
domain `A`, taken as a point of the scheme `Spec A`.

The frozen statement of the area is `DSMap.area_G3_multisection` (in
`Submission/Work/DSMap/Map.lean`); the proved version is
`DSMap.area_G3_multisection_proved` in `Submission/Work/DSG3/Main.lean`.

## Main definitions

* `DSMap.genericPointOfSpec A` — the generic point of `Spec A` for a domain `A`.

## Main results (in this file)

* `DSMap.closure_singleton_genericPointOfSpec` — it is a generic point (`closure = ⊤`).
* `DSMap.mem_basicOpen_genericPointOfSpec` — it lies in `D(g)` iff `g ≠ 0`.
* `DSMap.range_imageι_fromSpecResidueField` — the scheme-theoretic image of
  `Spec κ(x) ⟶ X` has underlying set `closure {x}`.
-/

open CategoryTheory AlgebraicGeometry

universe u v w

namespace DSMap

section GenericPoint

variable (A : Type u) [CommRing A] [IsDomain A]

/-- The generic point of `Spec A` for a domain `A`: the point defined by the zero ideal. -/
noncomputable def genericPointOfSpec : Spec (.of A) := genericPoint (Spec (.of A))

lemma genericPointOfSpec_eq_bot :
    (genericPointOfSpec A : PrimeSpectrum A) = (⊥ : PrimeSpectrum A) := by
  rw [genericPointOfSpec, genericPoint_eq_bot_of_affine]

lemma genericPointOfSpec_asIdeal : (genericPointOfSpec A : PrimeSpectrum A).asIdeal = ⊥ := by
  rw [genericPointOfSpec_eq_bot A]
  rfl

@[simp]
lemma closure_singleton_genericPointOfSpec :
    closure ({genericPointOfSpec A} : Set (Spec (.of A))) = ⊤ := by
  rw [genericPointOfSpec, genericPoint_closure]
  rfl

lemma isGenericPoint_genericPointOfSpec :
    IsGenericPoint (genericPointOfSpec A) (⊤ : Set (Spec (.of A))) :=
  closure_singleton_genericPointOfSpec A

set_option backward.isDefEq.respectTransparency false in
/-- The generic point lies in a basic open `D(g)` exactly when `g ≠ 0`. -/
lemma mem_basicOpen_genericPointOfSpec {g : A} :
    genericPointOfSpec A ∈ (PrimeSpectrum.basicOpen g : (Spec (.of A)).Opens) ↔ g ≠ 0 := by
  rw [PrimeSpectrum.mem_basicOpen, genericPointOfSpec_asIdeal A]
  simp

end GenericPoint
section ImageResidue

variable {X Y : Scheme.{u}}

/-- The underlying set of the scheme-theoretic image of `X.fromSpecResidueField x`
is the closure of `{x}`. -/
lemma range_imageι_fromSpecResidueField (x : X) :
    Set.range (X.fromSpecResidueField x).imageι = closure ({x} : Set X) := by
  rw [Scheme.IdealSheafData.range_subschemeι, Scheme.Hom.support_ker,
    Scheme.range_fromSpecResidueField]

set_option backward.isDefEq.respectTransparency false in
/-- `IsFinite` restricts to smaller opens of the target. -/
lemma isFinite_morphismRestrict_of_le (f : X ⟶ Y) {U V : Y.Opens} (h : V ≤ U)
    (hf : IsFinite (f ∣_ U)) : IsFinite (f ∣_ V) := by
  have h1 : IsFinite ((f ∣_ U) ∣_ (U.ι ⁻¹ᵁ V)) := inferInstance
  have h2 : IsFinite (f ∣_ (U.ι ''ᵁ (U.ι ⁻¹ᵁ V))) :=
    (MorphismProperty.arrow_mk_iso_iff @IsFinite (morphismRestrictRestrict f U (U.ι ⁻¹ᵁ V))).mp h1
  have h3 : U.ι ''ᵁ (U.ι ⁻¹ᵁ V) = V := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι, inf_eq_right.mpr h]
  rw [h3] at h2
  exact h2

end ImageResidue

section GenericHelpers

variable {A : Type u} [CommRing A] [IsDomain A]

set_option backward.isDefEq.respectTransparency false in
/-- Around the generic point of `Spec A` (`A` a domain), every neighbourhood contains a basic
open `D(g)` with `g ≠ 0`. -/
lemma exists_ne_zero_basicOpen_subset {U : (Spec (.of A)).Opens}
    (hU : genericPointOfSpec A ∈ U) :
    ∃ g : A, g ≠ 0 ∧ (PrimeSpectrum.basicOpen g : (Spec (.of A)).Opens) ≤ U := by
  obtain ⟨U', hU'mem, hxU', hU'U⟩ :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.mp (PrimeSpectrum.isBasis_basic_opens (R := A)) hU
  obtain ⟨g, rfl⟩ := hU'mem
  exact ⟨g, (mem_basicOpen_genericPointOfSpec A).mp hxU', hU'U⟩

end GenericHelpers

end DSMap
