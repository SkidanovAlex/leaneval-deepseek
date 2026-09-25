import Mathlib
import Submission.Work.ShafarevichKoch.SupportedComparison

/-!
# `Work.ShafarevichKoch.continuous_restrictToEmpty`

The Shafarevich--Koch comparison `1 → H_S → G_S → G_∅ → 1`
(`SupportedComparison.lean`) is a diagram of *profinite* groups: the Galois groups
`G_S = Gal(k_S/F)` and `G_∅ = Gal(k_∅/F)` of the maximal pro-`p` extensions unramified
outside `S` resp. nowhere carry the Krull topology (`krullTopology`), and the comparison
maps must be continuous for that topology to be usable as morphisms of topological
(resp. profinite) groups -- e.g. to feed them to the continuous cohomology of
`Submission.Work.ConCohomology`.

* `continuous_autCongr` -- conjugating an automorphism by a field isomorphism is continuous
  for the Krull topologies.  This is a general fact about the Krull topology, proved
  directly from its neighbourhood basis at `1`: the preimage of the fixing subgroup of a
  finite-dimensional intermediate field `E ⊆ A₂` contains the fixing subgroup of the
  finite-dimensional field `E.map e.symm ⊆ A₁`.
* `continuous_restrictToEmpty` -- `restrictToEmpty F p S` is continuous, being the composite
  of the continuous restriction `AlgEquiv.restrictNormalHom` (Mathlib's
  `InfiniteGalois.restrictNormalHom_continuous`) with the continuous conjugation above.

Everything is pure topology of the Krull topology: no class field theory and no arithmetic
enters.
-/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

open scoped Classical
open scoped NumberField
open NumberField

noncomputable section

namespace Work.ShafarevichKoch

/-- **Conjugation by a field isomorphism is continuous for the Krull topology.**

For `e : A₁ ≃ₐ[F] A₂`, the group isomorphism
`AlgEquiv.autCongr e : Gal(A₁/F) ≃* Gal(A₂/F)`, `ψ ↦ e.symm.trans (ψ.trans e)`, is
continuous.  Indeed, a basis of neighbourhoods of `1` in `Gal(A₂/F)` is given by the fixing
subgroups `Gal(A₂/E)` of the finite-dimensional intermediate fields `E ⊆ A₂`; for such an
`E` the field `E.map e.symm ⊆ A₁` is again finite-dimensional over `F`, and
`Gal(A₁/E.map e.symm)` is mapped by `AlgEquiv.autCongr e` into `Gal(A₂/E)`, since
`e.symm x ∈ E.map e.symm` for every `x ∈ E`. -/
theorem continuous_autCongr {F A₁ A₂ : Type*} [Field F] [Field A₁] [Field A₂]
    [Algebra F A₁] [Algebra F A₂] (e : A₁ ≃ₐ[F] A₂) :
    Continuous (AlgEquiv.autCongr e) := by
  apply continuous_of_continuousAt_one _ (continuousAt_def.mpr _)
  intro s hs
  rw [map_one] at hs
  rw [krullTopology_mem_nhds_one_iff F A₂] at hs
  rw [krullTopology_mem_nhds_one_iff F A₁]
  obtain ⟨E, hE, hsub⟩ := hs
  refine ⟨E.map (e.symm : A₂ →ₐ[F] A₁), ?_, ?_⟩
  · exact LinearEquiv.finiteDimensional
      (IntermediateField.equivMap E (e.symm : A₂ →ₐ[F] A₁)).toLinearEquiv
  · intro ψ hψ
    refine hsub ((IntermediateField.mem_fixingSubgroup_iff _ _).mpr fun x hx => ?_)
    rw [AlgEquiv.autCongr_apply, AlgEquiv.trans_apply, AlgEquiv.trans_apply]
    rw [(IntermediateField.mem_fixingSubgroup_iff _ _).mp hψ (e.symm x) ⟨x, hx, rfl⟩]
    exact AlgEquiv.apply_symm_apply e x

/-- **The restriction `Gal(k_S/F) →* Gal(k_∅/F)` is continuous** for the Krull topologies.

`restrictToEmpty F p S` is, by definition, the composite of the restriction
`AlgEquiv.restrictNormalHom : Gal(k_S/F) →* Gal(k_∅ in k_S /F)` (continuous by
`InfiniteGalois.restrictNormalHom_continuous`, both fields being Galois over `F`) with the
conjugation `AlgEquiv.autCongr (kEmptyEquiv F p S)` identifying
`Gal(k_∅ in k_S /F)` with `Gal(k_∅/F)` (continuous by `continuous_autCongr`). -/
theorem continuous_restrictToEmpty (F : Type) [Field F] [NumberField F] (p : ℕ) [Fact p.Prime]
    (S : Finset ℕ) : Continuous (restrictToEmpty F p S) := by
  have hres : Continuous (AlgEquiv.restrictNormalHom (K₁ := ↥(kSupported F p S))
      ↥(kEmptyInS F p S)) :=
    InfiniteGalois.restrictNormalHom_continuous (kEmptyInS F p S)
  have hconj : Continuous ⇑((AlgEquiv.autCongr (kEmptyEquiv F p S)).toMonoidHom) :=
    continuous_autCongr (kEmptyEquiv F p S)
  exact hconj.comp hres

end Work.ShafarevichKoch
