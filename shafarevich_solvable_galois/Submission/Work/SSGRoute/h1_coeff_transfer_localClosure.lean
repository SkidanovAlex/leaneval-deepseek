import Mathlib
import Submission.Work.SSGRoute.E7aAux
import Submission.Work.SSGRoute.PTDefs
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.homRep
import Submission.Work.SSGRoute.hom_dualMod_local_units
import Submission.Work.SSGRoute.PTembedding.homRep_dualMod_units_of_isCyclotomicDual
import Submission.Work.SSGRoute.PT.H1Transfer
import Submission.Work.SSGRoute.homRep_dualMod_units_localClosure
import Submission.Work.SSGRoute.h1_equiv_of_equiv
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `H¹` seam between the local coeff-twist and the local units

The local twin of the coefficient transfer used in the E7a assembly: given the isomorphism of
`Γ`-representations `Hom_ℤ(E^∨(1), Γ_ℓˣ) ≅ E` (`homRep_dualMod_units_localClosure`,
`Γ = Gal(κ̄/k_v)`) and a `Γ`-action on `E` which agrees pointwise with the one read through the
comparison map `act : Γ →* Gal(K/k)`, continuous `H¹` transfers across it.

Proof: the isomorphism of representations gives an equivariant additive equivalence
`Φ : Hom_ℤ(E^∨(1), μ_p-structure) ≃+ E`, and `Work.SSGRoute.h1_equiv_of_equiv` turns that into an
additive equivalence of `H¹`'s.
-/

namespace Work.SSGRoute

open SSGRoute.PTExt CategoryTheory
open scoped TensorProduct

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 800000

section Helpers

variable {Γ : Type} [Group Γ]

/-- The `ρ`-action of `homRep R N` is the ambient `SMul`-action on the linear maps. -/
lemma h1ct_homRep_rho_smul (R N : Rep.{0} Coeff Γ) (γ : Γ) (φ : R.V →ₗ[Coeff] N.V) :
    @SMul.smul _ _ (homRepDistribMulAction R N).toSMul γ φ = (homRep R N).ρ γ φ := rfl

/-- The action of `Rep.res f (modRep G E)` agrees with any pointwise equal action on `E`. -/
lemma h1ct_res_modRep_rho (p : ℕ) [Fact p.Prime] {G : Type} [Group G] (f : Γ →* G)
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction G E]
    [SMulCommClass G (ZMod p) E]
    [inst : DistribMulAction Γ E]
    (hinst : ∀ (γ : Γ) (x : E), @SMul.smul _ _ inst.toSMul γ x = f γ • x) (γ : Γ) (x : E) :
    (Rep.res f (modRep G E)).ρ γ x = @SMul.smul _ _ inst.toSMul γ x := by
  rw [show (Rep.res f (modRep G E)).ρ γ x = (modRep G E).ρ (f γ) x from rfl]
  change (Rep.ofDistribMulAction Coeff G E).ρ (f γ) x = _
  rw [Rep.ofDistribMulAction_ρ_apply_apply, ← hinst]

end Helpers

theorem h1_coeff_transfer_localClosure (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k]
    [NumberField k] [Field Ω] [Algebra k Ω] [IsSepClosure k Ω] (K : IntermediateField k Ω)
    [FiniteDimensional k K] [IsGalois k K] [NumberField K] (A : ValuationSubring Ω)
    (hA : SSGRoute.IsFinPlace k A)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
    (act : (Work.SSGRoute.localClosureAt k A hA ≃ₐ[Work.SSGRoute.localFieldAt k A hA]
        Work.SSGRoute.localClosureAt k A hA) →* (K ≃ₐ[k] K))
    (ζ' : Work.SSGRoute.localClosureAt k A hA) (hζ' : IsPrimitiveRoot ζ' p)
    (hcyc : SSGRoute.IsCyclotomicDual p (T := T) act ζ')
    [inst : DistribMulAction (Work.SSGRoute.localClosureAt k A hA ≃ₐ[Work.SSGRoute.localFieldAt k A hA]
        Work.SSGRoute.localClosureAt k A hA) E]
    (hinst : ∀ (γ : Work.SSGRoute.localClosureAt k A hA ≃ₐ[Work.SSGRoute.localFieldAt k A hA]
        Work.SSGRoute.localClosureAt k A hA) (e : E),
      @SMul.smul _ _ inst.toSMul γ e = act γ • e) :
    Nonempty (Work.AbsoluteKummer.H1
        (Work.SSGRoute.localClosureAt k A hA ≃ₐ[Work.SSGRoute.localFieldAt k A hA]
          Work.SSGRoute.localClosureAt k A hA)
        ((Rep.res act (SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
            (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T)))) →ₗ[SSGRoute.PTExt.Coeff]
          (SSGRoute.PTExt.modRep
            (Work.SSGRoute.localClosureAt k A hA ≃ₐ[Work.SSGRoute.localFieldAt k A hA]
              Work.SSGRoute.localClosureAt k A hA)
            (Additive (Units (Work.SSGRoute.localClosureAt k A hA))))) ≃+
      Work.AbsoluteKummer.H1
        (Work.SSGRoute.localClosureAt k A hA ≃ₐ[Work.SSGRoute.localFieldAt k A hA]
          Work.SSGRoute.localClosureAt k A hA) E) := by
  classical
  -- the local twin of the Tate-twist cancellation, as an isomorphism of `Γ`-representations
  obtain ⟨e⟩ :=
    homRep_dualMod_units_localClosure (p := p) (k := k) (Ω := Ω) (K := K) (A := A) (hA := hA)
      (T := T) (E := E) (act := act) (ζ' := ζ') (hζ' := hζ') (hcyc := hcyc)
  -- the two representations of the local Galois group
  let X : Rep.{0} Coeff (Work.SSGRoute.localClosureAt k A hA ≃ₐ[Work.SSGRoute.localFieldAt k A hA]
      Work.SSGRoute.localClosureAt k A hA) :=
    Rep.res act (modRep (K ≃ₐ[k] K) (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T)))
  let Y : Rep.{0} Coeff (Work.SSGRoute.localClosureAt k A hA ≃ₐ[Work.SSGRoute.localFieldAt k A hA]
      Work.SSGRoute.localClosureAt k A hA) :=
    modRep (Work.SSGRoute.localClosureAt k A hA ≃ₐ[Work.SSGRoute.localFieldAt k A hA]
        Work.SSGRoute.localClosureAt k A hA)
      (Additive (Units (Work.SSGRoute.localClosureAt k A hA)))
  let Z : Rep.{0} Coeff (Work.SSGRoute.localClosureAt k A hA ≃ₐ[Work.SSGRoute.localFieldAt k A hA]
      Work.SSGRoute.localClosureAt k A hA) := Rep.res act (modRep (K ≃ₐ[k] K) E)
  -- the additive equivalence `Hom_ℤ(E^∨(1), μ_p) ≃ₗ E` underlying the twist cancellation
  let Φ : (X.V →ₗ[Coeff] Y.V) ≃+ E :=
    { toFun := fun φ => e.hom.hom φ
      invFun := fun y => e.inv.hom y
      left_inv := fun φ => Rep.inv_hom_apply (homRep X Y) Z e φ
      right_inv := fun y => Rep.hom_inv_apply (homRep X Y) Z e y
      map_add' := fun φ ψ => map_add e.hom.hom φ ψ }
  -- it is equivariant, where the target is read through the given action `inst`
  have hΦ : ∀ (γ : Work.SSGRoute.localClosureAt k A hA ≃ₐ[Work.SSGRoute.localFieldAt k A hA]
      Work.SSGRoute.localClosureAt k A hA) (φ : X.V →ₗ[Coeff] Y.V),
      Φ (@SMul.smul _ _ (homRepDistribMulAction X Y).toSMul γ φ)
        = @SMul.smul _ _ inst.toSMul γ (Φ φ) := by
    intro γ φ
    have h1 : @SMul.smul _ _ (homRepDistribMulAction X Y).toSMul γ φ = (homRep X Y).ρ γ φ :=
      h1ct_homRep_rho_smul X Y γ φ
    have h2 : e.hom.hom ((homRep X Y).ρ γ φ) = Z.ρ γ (e.hom.hom φ) :=
      Rep.hom_comm_apply e.hom γ φ
    have h3 : Z.ρ γ (e.hom.hom φ) = @SMul.smul _ _ inst.toSMul γ (e.hom.hom φ) :=
      h1ct_res_modRep_rho (Γ := Work.SSGRoute.localClosureAt k A hA ≃ₐ[Work.SSGRoute.localFieldAt k A hA]
        Work.SSGRoute.localClosureAt k A hA) p act E (fun γ x => hinst γ x) γ (e.hom.hom φ)
    exact (congrArg (fun ψ : ↑(homRep X Y) => e.hom.hom ψ) h1).trans (h2.trans h3)
  exact @h1_equiv_of_equiv
    (Work.SSGRoute.localClosureAt k A hA ≃ₐ[Work.SSGRoute.localFieldAt k A hA]
      Work.SSGRoute.localClosureAt k A hA) _ _
    (X.V →ₗ[Coeff] Y.V) E _ _ (homRepDistribMulAction X Y) inst Φ hΦ

end Work.SSGRoute
