import Submission.NK.ReconstructField.LevelCandidate
import Submission.NK.ReconstructField.Lift
import Submission.NeukirchUchida.Conjugation
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The level-wise matching condition of CoNF XII §12.2

For a finite Galois level `L ⊆ K₁'` with image `L₂ := levelMap ϕ L`, a base-field-mapping
isomorphism `σ : K₂' ≃+* K₁'` *matches* `ϕ` at `L` if the conjugation by `σ` agrees with `ϕ`
modulo `Gal(K₂'/L₂)`:

`NK.ReconstructField.LevelMatch ϕ hϕ σ hσ L : Prop`,
`LevelMatch ϕ hϕ σ hσ L := ∀ g : Gal(K₁'/K₁), c_σ(g) * (ϕ g)⁻¹ ∈ (levelMap ϕ L).fixingSubgroup`.

This is the condition `C_L` of Neukirch's reconstruction (Neukirch, *Invent. Math.* 6 (1969);
CoNF XII §12.2): `σ` carries `L` onto `levelMap ϕ L` and induces the correspondence `ϕ` on the
finite quotient `Gal(L/K₁)`.  The conditions are monotone in `L`, and their intersection over all
finite Galois levels `L` is exactly `{σ : conjHomEquiv hσ = ϕ}` — the set whose nonemptiness is the
existence half of Neukirch–Uchida.
-/

set_option linter.unusedVariables false

namespace NK.ReconstructField

open NK.Reconstruct
open scoped Pointwise

variable {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
  [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
  [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']

/-- **The level-wise matching condition.**  A `MapsBase` isomorphism `σ : K₂' ≃+* K₁'` matches `ϕ` at
the finite Galois level `L ⊆ K₁'` if for every `g : Gal(K₁'/K₁)` the conjugate `c_σ(g)` and `ϕ g`
differ by an element of `Gal(K₂'/(levelMap ϕ L))`. -/
def LevelMatch (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (hϕ : IsHomeomorph ϕ) (σ : K₂' ≃+* K₁')
    (hσ : Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ)
    (L : IntermediateField K₁ K₁') [FiniteDimensional K₁ L] [Normal K₁ L] [NumberField ↥L]
    [FiniteDimensional K₂ (NK.Reconstruct.levelMap ϕ L)]
    [Normal K₂ (NK.Reconstruct.levelMap ϕ L)] [NumberField ↥(NK.Reconstruct.levelMap ϕ L)] :
    Prop :=
  ∀ g : Gal(K₁'/K₁),
    Submission.NeukirchUchida.conjHomEquiv hσ g * (ϕ g)⁻¹ ∈
      (NK.Reconstruct.levelMap ϕ L).fixingSubgroup

end NK.ReconstructField
