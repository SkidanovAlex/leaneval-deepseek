import Submission.NK.Reconstruct.Reconstruction
import Submission.NeukirchUchida.Uniqueness
import Submission.NeukirchUchida.PlaceRigidity
import Submission.NK.Reconstruct.exists_sigma_of_levelPrimeIdentification
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Non-vacuity of the reconstruction's conclusion

Theorems showing that the conclusion of the reconstruction (`Conjugates σ ϕ`) and the shapes of its
named inputs are *not* vacuous:

* `NK.Reconstruct.conjugates_conjHomEquiv` — for `ϕ = conjHomEquiv hσ` the field isomorphism `σ`
  itself induces `ϕ`, so the conclusion is inhabited for every candidate `σ : K₂' ≃+* K₁'` mapping
  the embedded `K₂` onto the embedded `K₁`; consequently the `∃!` form of the reconstruction is
  consistent (`NK.Reconstruct.existsUnique_conjugates_conjHomEquiv`).
* `NK.Reconstruct.preservesDecompositionGroups_conjHomEquiv` — the group-theoretic input
  `Submission.NeukirchUchida.PreservesDecompositionGroups` is satisfied by every such `ϕ`, i.e. by
  every isomorphism of absolute Galois groups induced by a field isomorphism: input (a) of the
  reconstruction is satisfiable in the canonical example.
-/

set_option linter.unusedVariables false

namespace NK.Reconstruct

open scoped Pointwise

variable {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
  [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
  [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']

/-- **Every `MapsBase` isomorphism induces the isomorphism of absolute Galois groups given by
conjugation with itself.** -/
theorem conjugates_conjHomEquiv {σ : K₂' ≃+* K₁'}
    (hσ : Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ) :
    Submission.NeukirchUchida.Conjugates σ (Submission.NeukirchUchida.conjHomEquiv hσ) :=
  ⟨hσ, fun g => (Submission.NeukirchUchida.conj_toRingEquiv hσ g).symm⟩

/-- **The `∃!` form of the reconstruction is consistent**: for `ϕ = conjHomEquiv hσ` the inducing
field isomorphism exists and is unique. -/
theorem existsUnique_conjugates_conjHomEquiv {σ : K₂' ≃+* K₁'}
    (hσ : Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ) :
    ∃! σ' : K₂' ≃+* K₁',
      Submission.NeukirchUchida.Conjugates σ' (Submission.NeukirchUchida.conjHomEquiv hσ) :=
  ⟨σ, conjugates_conjHomEquiv hσ, fun _ hy =>
    Submission.NeukirchUchida.unique_sigma_of_centralizer_trivial
      (fun c hpres hcomm => centralizer_trivial_of_sepClosure c hpres hcomm)
      (Submission.NeukirchUchida.conjHomEquiv hσ) hy (conjugates_conjHomEquiv hσ)⟩

end NK.Reconstruct
