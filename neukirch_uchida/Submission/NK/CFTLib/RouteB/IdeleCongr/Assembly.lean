/-
Assembly of the transport of the idèle class group, and of its Galois representation,
from a per-place transport of local fields.

Given a family `Φ` of ring isomorphisms `L_v ≃+* L'_{φ v}` (compatible with the
embeddings of `L`, preserving local units and continuous) we obtain

* `exists_classGroupCongr`: a group isomorphism `C_L ≃* C_{L'}` intertwining the
  Galois actions via `AlgEquiv.autCongr e`;
* `rep_iso_of_classGroupCongr`: the resulting isomorphism of `ℤ[Gal(L/K)]`-modules
  `Rep.res (autCongr e) (rep K L') ≅ rep K L`.
-/
import Mathlib
import Submission.NK.CFTLib.RouteB.IdeleCongr.PlaceCongr
import Submission.NK.GlobalCFT.GaloisClassGroup
import Submission.NK.GlobalCFT.Cohomology
import Mathlib.RepresentationTheory.Rep.Res

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped NumberField RestrictedProduct
open NumberField IsDedekindDomain

noncomputable section

namespace NK.CFTLib.RouteB.IdeleCongr

open NK.GlobalCFT

variable {K L L' : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Field L']
  [NumberField L'] [Algebra K L] [Algebra K L']

/-- Descent of an idèle-level transport to the idèle class groups: an isomorphism `Ψ` of the
idèle groups which maps the principal idèles onto the principal idèles and intertwines the
Galois actions induces one of the idèle class groups with the same property. -/
theorem exists_classGroupCongr (e : L ≃ₐ[K] L') (Ψ : Idele L ≃* Idele L')
    (hprin : Subgroup.map Ψ.toMonoidHom (Idele.principalSubgroup L)
      = Idele.principalSubgroup L')
    (hsmul : ∀ (σ : L ≃ₐ[K] L) (x : Idele L),
      Ψ (σ • x) = (AlgEquiv.autCongr e σ) • Ψ x) :
    ∃ Ψc : IdeleClassGroup L ≃* IdeleClassGroup L',
      ∀ (σ : L ≃ₐ[K] L) (x : IdeleClassGroup L),
        Ψc (σ • x) = (AlgEquiv.autCongr e σ) • Ψc x := by
  haveI hN : (Idele.principalSubgroup L).Normal := Subgroup.normal_of_isMulCommutative _
  haveI hN' : (Idele.principalSubgroup L').Normal := Subgroup.normal_of_isMulCommutative _
  have hprin' : Subgroup.map (Ψ : Idele L →* Idele L') (Idele.principalSubgroup L)
      = Idele.principalSubgroup L' := hprin
  refine ⟨QuotientGroup.congr (Idele.principalSubgroup L) (Idele.principalSubgroup L') Ψ hprin',
    ?_⟩
  intro σ x
  induction x using QuotientGroup.induction_on with
  | H y =>
    have h0 : (σ : Gal(L/K)) • (y : IdeleClassGroup L)
        = ((σ • y : Idele L) : IdeleClassGroup L) :=
      IdeleClassGroup.smul_mk σ y
    have h3 : (((AlgEquiv.autCongr e σ) • Ψ y : Idele L') : IdeleClassGroup L')
        = (AlgEquiv.autCongr e σ) • ((Ψ y : Idele L') : IdeleClassGroup L') :=
      IdeleClassGroup.smul_mk (AlgEquiv.autCongr e σ) (Ψ y)
    rw [h0, QuotientGroup.congr_mk, hsmul σ y, h3, QuotientGroup.congr_mk]

/-- The `ℤ`-linear isomorphism of the additive idèle class groups induced by a group
isomorphism `Ψ : C_L ≃* C_{L'}`, in the direction `C_{L'} → C_L`. -/
def classGroupLinearEquiv :
    IdeleClassGroup L ≃* IdeleClassGroup L' →
      Additive (IdeleClassGroup L') ≃ₗ[ℤ] Additive (IdeleClassGroup L) :=
  fun Ψ => AddEquiv.toIntLinearEquiv (MulEquiv.toAdditive Ψ.symm)

@[simp] theorem classGroupLinearEquiv_apply (Ψ : IdeleClassGroup L ≃* IdeleClassGroup L')
    (a : Additive (IdeleClassGroup L')) :
    classGroupLinearEquiv Ψ a = Additive.ofMul (Ψ.symm a.toMul) := rfl

/-- The transport of the idèle class group along `e`, when it intertwines the Galois actions,
gives an isomorphism of the associated `ℤ[Gal(L/K)]`-modules. -/
theorem rep_iso_of_classGroupCongr (e : L ≃ₐ[K] L') (Ψc : IdeleClassGroup L ≃* IdeleClassGroup L')
    (hsmul : ∀ (σ : L ≃ₐ[K] L) (x : IdeleClassGroup L),
      Ψc (σ • x) = (AlgEquiv.autCongr e σ) • Ψc x) :
    Nonempty (Rep.res (AlgEquiv.autCongr e).toMonoidHom (IdeleClassGroup.rep K L') ≅
      IdeleClassGroup.rep K L) := by
  have key : ∀ (g : L ≃ₐ[K] L) (z : IdeleClassGroup L'),
      Ψc.symm ((AlgEquiv.autCongr e g) • z) = g • Ψc.symm z := by
    intro g z
    obtain ⟨x, rfl⟩ := Ψc.surjective z
    rw [← hsmul g x, MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply]
  refine ⟨Rep.mkIso (Representation.Equiv.mk (classGroupLinearEquiv Ψc) ?_)⟩
  intro g
  ext a
  show Additive.ofMul (Ψc.symm ((AlgEquiv.autCongr e g) • (Additive.toMul a : IdeleClassGroup L')))
      = Additive.ofMul (g • Ψc.symm (Additive.toMul a : IdeleClassGroup L'))
  rw [key g (Additive.toMul a : IdeleClassGroup L')]

end NK.CFTLib.RouteB.IdeleCongr
