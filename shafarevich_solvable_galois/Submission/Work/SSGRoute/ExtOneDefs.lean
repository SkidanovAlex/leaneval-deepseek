import Mathlib
import Submission.Work.SSGRoute.PTDefs
import Submission.Work.SSGRoute.homRep
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Vocabulary for the proof of `Ext¹_G(M,N) ≅ Ext¹_G(ℤ, Hom_ℤ(M,N))` (`N` divisible)

The coefficient ring is `Coeff = ULift ℤ`.  On a type with an `AddCommGroup` structure there are two
competing `ULift ℤ`-module structures that occur in the workspace: the one coming from
`AddCommGroup.toIntModule` through `ULift.module` (which is what type class search produces when the
type is already known), and the field `Rep.hV2` of a `Rep` (which is what `Rep.ρ`, `Rep.Hom` and
Mathlib's internal hom `Rep.ihom` use).  The first lemma below shows that *all* `ULift ℤ`-module
structures on an `AddCommGroup` coincide, which is what makes it possible to move between the two.

This file is `sorry`-free and provides:
* `Work.SSGRoute.subsingleton_moduleCoeff`, `Work.SSGRoute.smul_moduleCoeff_congr`;
* `Work.SSGRoute.ihomRep`, the abbreviation for the internal hom `Work.SSGRoute.homRep`
  (definitionally equal to it) with transparent body, and the basic computation rules.
-/

open CategoryTheory SSGRoute.PTExt

namespace Work.SSGRoute

noncomputable section

variable {G : Type} [Group G]

/-- **All `ULift ℤ`-module structures on an additive commutative group coincide.** -/
instance subsingleton_moduleCoeff (M : Type) [AddCommGroup M] : Subsingleton (Module Coeff M) := by
  constructor
  intro P Q
  apply Module.ext'
  intro r m
  obtain ⟨k⟩ := r
  have hP : P.smul (ULift.up k) m = k • m := by
    letI := P
    rw [← Int.cast_smul_eq_zsmul (R := ULift ℤ) k m]
    rfl
  have hQ : Q.smul (ULift.up k) m = k • m := by
    letI := Q
    rw [← Int.cast_smul_eq_zsmul (R := ULift ℤ) k m]
    rfl
  exact hP.trans hQ.symm

/-- The scalar actions of two `ULift ℤ`-module structures on the same `AddCommGroup` agree. -/
lemma smul_moduleCoeff_congr (X : Type) [AddCommGroup X] (P Q : Module Coeff X) (c : Coeff) (x : X) :
    @SMul.smul Coeff X P.toDistribMulAction.toSMul c x =
      @SMul.smul Coeff X Q.toDistribMulAction.toSMul c x := by
  rw [Subsingleton.elim P Q]

/-- The internal `Hom_ℤ(X, N)`, with transparent body: definitionally the same object as
`Work.SSGRoute.homRep X N`. -/
abbrev ihomRep (X N : Rep.{0} Coeff G) : Rep.{0} Coeff G :=
  Rep.ofDistribMulAction Coeff G (X.V →ₗ[Coeff] N.V)

lemma ihomRep_eq_homRep (X N : Rep.{0} Coeff G) : ihomRep X N = homRep X N := rfl

/-- The `ρ`-action of `homRep X N` is the scalar action of the `SMul G` instance. -/
lemma homRep_rho_eq_smul (X N : Rep.{0} Coeff G) (g : G) (ψ : X.V →ₗ[Coeff] N.V) :
    (homRep X N).ρ g ψ = g • ψ := rfl

/-- Computation rule for the action on the internal hom. -/
@[simp] lemma homRep_rho_apply (X N : Rep.{0} Coeff G) (g : G) (ψ : X.V →ₗ[Coeff] N.V) (x : X.V) :
    (show X.V →ₗ[Coeff] N.V from (homRep X N).ρ g ψ) x = N.ρ g (ψ (X.ρ g⁻¹ x)) := by
  show (g • ψ) x = _
  exact homRep_smul_apply X N g ψ x

end

end Work.SSGRoute
