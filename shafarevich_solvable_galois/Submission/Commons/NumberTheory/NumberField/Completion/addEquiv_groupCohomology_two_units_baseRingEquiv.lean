import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
import Submission.Commons.RepresentationTheory.GroupCohomology.natCard_groupCohomology_res_mulEquiv
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Commons.NumberTheory.NumberField.Completion

open Additive

variable {M M' E : Type} [Field M] [Field M'] [Field E] [Algebra M E] [Algebra M' E]

/-- If `φ : M ≃+* M'` makes the `M`-algebra and `M'`-algebra structures on `E` agree, then an
`M`-algebra automorphism of `E` and an `M'`-algebra automorphism of `E` with the same underlying
ring automorphism are the same object.

Concretely, this is the monoid isomorphism `(E ≃ₐ[M] E) ≃* (E ≃ₐ[M'] E)` given by keeping the
underlying ring automorphism. -/
noncomputable def algEquivCongrRingEquiv (φ : M ≃+* M')
    (he : (algebraMap M' E).comp φ.toRingHom = algebraMap M E) :
    (E ≃ₐ[M] E) ≃* (E ≃ₐ[M'] E) where
  toFun g :=
    { g.toRingEquiv with
      commutes' := fun m' => by
        obtain ⟨m, rfl⟩ := φ.surjective m'
        have h1 : (algebraMap M' E) (φ m) = algebraMap M E m := by
          simpa using RingHom.congr_fun he m
        rw [h1]
        exact AlgEquiv.commutes g m }
  invFun g :=
    { g.toRingEquiv with
      commutes' := fun m => by
        have h1 : (algebraMap M' E) (φ m) = algebraMap M E m := by
          simpa using RingHom.congr_fun he m
        rw [← h1]
        exact AlgEquiv.commutes g (φ m) }
  left_inv g := by ext x; rfl
  right_inv g := by ext x; rfl
  map_mul' g h := by ext x; rfl

/-- The two units representations have the same underlying action, transported along
`algEquivCongrRingEquiv`. -/
lemma algEquivCongrRingEquiv_rho (φ : M ≃+* M')
    (he : (algebraMap M' E).comp φ.toRingHom = algebraMap M E)
    (g : E ≃ₐ[M] E) (u : Additive Eˣ) :
    (Rep.ofAlgebraAutOnUnits M E).ρ g u =
      (Rep.ofAlgebraAutOnUnits M' E).ρ (algEquivCongrRingEquiv φ he g) u := by
  rw [show (Rep.ofAlgebraAutOnUnits M E).ρ g u = Additive.ofMul (g • u.toMul) from rfl,
      show (Rep.ofAlgebraAutOnUnits M' E).ρ (algEquivCongrRingEquiv φ he g) u =
        Additive.ofMul ((algEquivCongrRingEquiv φ he g) • u.toMul) from rfl]
  apply Additive.ofMul.injective
  apply Units.ext
  rfl

theorem addEquiv_groupCohomology_two_units_baseRingEquiv {M M' E : Type} [Field M] [Field M']
    [Field E] [Algebra M E] [Algebra M' E]
    (φ : M ≃+* M') (he : (algebraMap M' E).comp φ.toRingHom = algebraMap M E) :
    Nonempty (groupCohomology (Rep.ofAlgebraAutOnUnits M E) 2 ≃+
      groupCohomology (Rep.ofAlgebraAutOnUnits M' E) 2) := by
  refine ⟨(groupCohomology.mapIso
    (A := Rep.ofAlgebraAutOnUnits M' E) (B := Rep.ofAlgebraAutOnUnits M E)
    (algEquivCongrRingEquiv φ he) (LinearEquiv.refl ℤ (Additive Eˣ)) ?_ 2
    ).toLinearEquiv.toAddEquiv⟩
  intro g
  apply LinearMap.ext
  intro u
  rw [LinearEquiv.refl_toLinearMap]
  exact algEquivCongrRingEquiv_rho φ he g u

end Commons.NumberTheory.NumberField.Completion