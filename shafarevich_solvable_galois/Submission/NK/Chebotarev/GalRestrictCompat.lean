/-
Work of the Neukirch–Uchida team: the Čebotarev density theorem.
-/
import Submission.NK.Chebotarev.Basic
import Submission.Commons.FieldTheory.Galois.isGalois_of_normal_of_charZero
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Restriction of the Galois action on rings of integers

For a tower `K ⊆ E ⊆ M` of number fields with `M/K` finite Galois and `E/K` normal, the action of
`σ : Gal(M/K)` on `𝓞 M` restricts on the subring `𝓞 E` to the action of the restriction
`σ|_E ∈ Gal(E/K)`.  This is the compatibility that makes the Frobenius elements of a tower of
number fields compatible, and it is the key input for "restriction of Frobenius along
`Gal(F/ℚ) ↠ Gal(L/ℚ)`".
-/

open scoped NumberField

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace NK.Chebotarev

variable {K M : Type*} [Field K] [Field M] [NumberField K] [NumberField M] [Algebra K M]
  [FiniteDimensional K M] [IsGalois K M]

/-- **Compatibility of `galRestrict` with restriction to an intermediate field**, evaluated in
`M`. -/
theorem algebraMap_galRestrict_restrictNormalHom (E : IntermediateField K M) [Normal K E]
    (σ : Gal(M/K)) (x : 𝓞 E) :
    algebraMap (𝓞 M) M (algebraMap (𝓞 E) (𝓞 M) ((galRestrict (𝓞 K) K ↥E (𝓞 ↥E)
        (AlgEquiv.restrictNormalHom (F := K) (K₁ := M) E σ)) x)) =
      algebraMap (𝓞 M) M (galRestrict (𝓞 K) K M (𝓞 M) σ
        (algebraMap (𝓞 E) (𝓞 M) x)) := by
  conv_lhs => rw [← IsScalarTower.algebraMap_apply (𝓞 E) (𝓞 M) M]
  conv_rhs => rw [algebraMap_galRestrict_apply]
  conv_lhs => rw [IsScalarTower.algebraMap_apply (𝓞 E) ↥E M]
  conv_lhs => rw [algebraMap_galRestrict_apply]
  conv_lhs => rw [show (AlgEquiv.restrictNormalHom (F := K) (K₁ := M) E σ) =
      σ.restrictNormal ↥E from rfl]
  conv_lhs => rw [AlgEquiv.restrictNormal_commutes]
  conv_rhs => rw [← IsScalarTower.algebraMap_apply (𝓞 E) (𝓞 M) M]
  conv_rhs => rw [IsScalarTower.algebraMap_apply (𝓞 E) ↥E M]

/-- **Compatibility of `galRestrict` with restriction to an intermediate field.**  The element of
`𝓞 M` obtained by applying the automorphism induced by `σ` to an element of `𝓞 E` only depends on
the restriction `σ|_E` of `σ` to `E`. -/
theorem galRestrict_restrictNormalHom (E : IntermediateField K M) [Normal K E]
    (σ : Gal(M/K)) (x : 𝓞 E) :
    algebraMap (𝓞 E) (𝓞 M) ((galRestrict (𝓞 K) K ↥E (𝓞 ↥E)
        (AlgEquiv.restrictNormalHom (F := K) (K₁ := M) E σ)) x) =
      galRestrict (𝓞 K) K M (𝓞 M) σ (algebraMap (𝓞 E) (𝓞 M) x) := by
  refine Subtype.ext ?_
  exact algebraMap_galRestrict_restrictNormalHom E σ x

end NK.Chebotarev
