import Mathlib
import Submission.Commons.RepresentationTheory.GroupCohomology.natCard_groupCohomology_res_mulEquiv
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Commons.NumberTheory.NumberField.Completion

open CategoryTheory

/-!
# Invariance of `H²` of the units representation under a base-field-mapping algebra isomorphism

For an `F`-algebra `E`, `Rep.ofAlgebraAutOnUnits F E` is the `ℤ`-linear representation of the
automorphism group `E ≃ₐ[F] E` on the additive group `Eˣ` of units.

The main theorem of this file states that the `Nat.card` of the second group cohomology of this
representation only depends on the isomorphism class of the `F`-algebra `E`: an `F`-algebra
isomorphism `ψ : E ≃ₐ[F] E'` induces an isomorphism of representations (after transporting the
group along the conjugation isomorphism `g ↦ ψ.symm.trans (g.trans ψ)`), hence an isomorphism on
cohomology.
-/

/-- An isomorphism `e : A ≅ B'` of `k`-linear `G`-representations induces an isomorphism on group
cohomology, hence equality of `Nat.card`. -/
theorem natCard_groupCohomology_eq_of_iso {k G : Type} [CommRing k] [Group G]
    {A B' : Rep.{0,0,0} k G} (e : A ≅ B') (n : ℕ) :
    Nat.card (groupCohomology A n) = Nat.card (groupCohomology B' n) :=
  Nat.card_congr ((groupCohomology.functor k G n).mapIso e).toLinearEquiv.toEquiv

/-- **Invariance of `H²` of the units representation under a base-field-mapping algebra
isomorphism.** -/
theorem natCard_groupCohomology_two_units_topAlgEquiv {F : Type} [Field F] {E : Type} [Field E]
    {E' : Type} [Field E'] [Algebra F E] [Algebra F E'] (ψ : E ≃ₐ[F] E') :
    Nat.card (groupCohomology (Rep.ofAlgebraAutOnUnits F E) 2) =
      Nat.card (groupCohomology (Rep.ofAlgebraAutOnUnits F E') 2) := by
  -- The conjugation isomorphism `E ≃ₐ[F] E ≃* E' ≃ₐ[F] E'` induced by `ψ`.
  let e : (E ≃ₐ[F] E) ≃* (E' ≃ₐ[F] E') :=
    { toFun := fun g => ψ.symm.trans (g.trans ψ)
      invFun := fun g' => ψ.trans (g'.trans ψ.symm)
      left_inv := by intro g; ext x; simp [AlgEquiv.trans_apply]
      right_inv := by intro g'; ext x; simp [AlgEquiv.trans_apply]
      map_mul' := by intro g h; ext x; simp [AlgEquiv.trans_apply] }
  -- `ψ` induces a `MulEquiv` of unit groups.
  let u : E'ˣ ≃* Eˣ := Units.mapEquiv ψ.symm
  -- the corresponding additive (hence `ℤ`-linear) equivalence.
  let L0 : Additive (E'ˣ) ≃+ Additive (Eˣ) :=
    { toFun := fun x => Additive.ofMul (u x.toMul)
      invFun := fun y => Additive.ofMul (u.symm y.toMul)
      left_inv := by intro x; simp
      right_inv := by intro y; simp
      map_add' := by intro x y; rw [toMul_add, map_mul, ofMul_mul] }
  let L : Additive (E'ˣ) ≃ₗ[ℤ] Additive (Eˣ) :=
    L0.toLinearEquiv (fun c x => map_zsmul L0 c x)
  -- `L` intertwines the two actions up to the conjugation isomorphism `e`.
  have key : ∀ (g : E ≃ₐ[F] E) (v : E'ˣ), u ((e g) • v) = g • u v := by
    intro g v
    apply Units.ext
    show (ψ.symm : E' → E) ((e g : E' → E') (v : E')) =
      (g : E → E) ((ψ.symm : E' → E) (v : E'))
    have h1 : (e g : E' → E') (v : E') = ψ (g (ψ.symm (v : E'))) := by
      simp [e, AlgEquiv.trans_apply]
    rw [h1, AlgEquiv.symm_apply_apply]
  -- the two representations, unfolded to plain `Representation`s
  let ρ' : Representation ℤ (E ≃ₐ[F] E) (Additive (E'ˣ)) :=
    (Representation.ofMulDistribMulAction (E' ≃ₐ[F] E') E'ˣ).comp e.toMonoidHom
  let σ' : Representation ℤ (E ≃ₐ[F] E) (Additive (Eˣ)) :=
    Representation.ofMulDistribMulAction (E ≃ₐ[F] E) Eˣ
  have hcomm : ∀ g : E ≃ₐ[F] E, (L : Additive (E'ˣ) →ₗ[ℤ] Additive (Eˣ)) ∘ₗ ρ' g =
      σ' g ∘ₗ (L : Additive (E'ˣ) →ₗ[ℤ] Additive (Eˣ)) := by
    intro g
    apply LinearMap.ext
    intro x
    apply Additive.ext
    show (L0 (ρ' g x)).toMul = (σ' g (L0 x)).toMul
    rw [show ρ' g = (Representation.ofMulDistribMulAction (E' ≃ₐ[F] E') E'ˣ) (e g) from rfl,
        show σ' g = (Representation.ofMulDistribMulAction (E ≃ₐ[F] E) Eˣ) g from rfl,
        Representation.ofMulDistribMulAction_apply_apply,
        Representation.ofMulDistribMulAction_apply_apply]
    change u ((e g) • x.toMul) = g • u x.toMul
    exact key g x.toMul
  have iso : Rep.res e.toMonoidHom (Rep.ofAlgebraAutOnUnits F E') ≅ Rep.ofAlgebraAutOnUnits F E :=
    Rep.mkIso (Representation.Equiv.mk (ρ := ρ') (σ := σ') L hcomm)
  calc Nat.card (groupCohomology (Rep.ofAlgebraAutOnUnits F E) 2)
      = Nat.card (groupCohomology (Rep.res e.toMonoidHom (Rep.ofAlgebraAutOnUnits F E')) 2) :=
        (natCard_groupCohomology_eq_of_iso iso 2).symm
    _ = Nat.card (groupCohomology (Rep.ofAlgebraAutOnUnits F E') 2) :=
        Commons.RepresentationTheory.GroupCohomology.natCard_groupCohomology_res_mulEquiv
          e (Rep.ofAlgebraAutOnUnits F E') 2

end Commons.NumberTheory.NumberField.Completion
