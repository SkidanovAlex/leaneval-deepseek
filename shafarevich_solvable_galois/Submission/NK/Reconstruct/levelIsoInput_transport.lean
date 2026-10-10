import Mathlib.FieldTheory.KrullTopology
import Mathlib.NumberTheory.NumberField.Basic
import Submission.NK.Reconstruct.exists_frobeniusCorrespondence_transport
import Submission.NK.ReconstructField.LevelCandidate
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Transport of the level-wise weak Neukirch–Uchida input along an isomorphism of separable closures

`NK.ReconstructField.LevelIsoInput ϕ hϕ` is the assertion that every finite level `L/K₁` of `K₁'`
is isomorphic to the corresponding level `levelMap ϕ L` of `K₂'`.  It is the single hypothesis
`hlev` of the σ-producing theorem
`NK.Reconstruct.exists_sigma_of_localCorrespondence_of_levelIso`.

The reconstruction step is carried out inside a *single* separable closure `Ω` (Shimizu's §4
compares base changes `π_{L/K}` for two base fields inside one field), which is why the level-pair
bridge of this area is stated for
`ψ : Gal(Ω/↥K₁.L) ≃* Gal(Ω/↥K₂.L)`.  This file is the (purely formal) passage back: if `ψ` is the
conjugate of `ϕ` by an isomorphism `e : K₂' ≃ₐ[K₂] Ω` of separable closures, then the level-wise
input for `ψ` implies the level-wise input for `ϕ`.

The only ingredient is `NK.Reconstruct.levelConjEquiv ϕ e ψ hψ L : ↥(levelMap ϕ L) ≃+* ↥(levelMap ψ L)`
(`Submission/Work/Reconstruct/exists_frobeniusCorrespondence_transport.lean`), the isomorphism
induced by `e` between the two corresponding levels; composing a level isomorphism for `ψ` with its
inverse gives one for `ϕ`.

## References

S. Shimizu, *On the Neukirch–Uchida theorem for small sets of primes*, arXiv:2009.10431, §4.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace NK.Reconstruct

/-- **Transport of `LevelIsoInput` along an isomorphism of separable closures.** -/
theorem levelIsoInput_transport {K₁ K₂ K₁' K₂' Ω : Type*} [Field K₁] [NumberField K₁] [Field K₂]
    [NumberField K₂] [Field K₁'] [Field K₂'] [Field Ω] [Algebra K₁ K₁'] [Algebra K₂ K₂']
    [Algebra K₂ Ω] [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂'] [IsSepClosure K₂ Ω]
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (hϕ : IsHomeomorph ϕ) (e : K₂' ≃ₐ[K₂] Ω)
    (ψ : Gal(K₁'/K₁) ≃* Gal(Ω/K₂)) (hψeq : ∀ g : Gal(K₁'/K₁), ψ g = algEquivConjHom e (ϕ g))
    (hψ : IsHomeomorph ψ) (h : NK.ReconstructField.LevelIsoInput ψ hψ) :
    NK.ReconstructField.LevelIsoInput ϕ hϕ := by
  intro L hfdL
  obtain ⟨σ⟩ := h L
  exact ⟨σ.trans (levelConjEquiv ϕ e ψ hψeq L).symm⟩

end NK.Reconstruct
