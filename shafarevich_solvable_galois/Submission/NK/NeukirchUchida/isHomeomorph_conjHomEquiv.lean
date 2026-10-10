import Mathlib.FieldTheory.KrullTopology
import Submission.NK.NeukirchUchida.continuous_conjHom
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The conjugation isomorphism is a homeomorphism

Let `σ : K₂' ≃+* K₁'` be a ring isomorphism mapping the embedded copy of `K₂` onto the
embedded copy of `K₁` (`Submission.NeukirchUchida.MapsBase`).  Then conjugation by `σ`
defines a group isomorphism `conjHomEquiv hσ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)`
(`Submission.NeukirchUchida.Conjugation`).  The main result here is that this isomorphism is
in fact a homeomorphism for the Krull topologies, i.e. `IsHomeomorph (conjHomEquiv hσ)`.

The Krull topology on `Gal(K/K')` has as a fundamental system of neighbourhoods of the
identity the fixing subgroups `Gal(K'/E)` of the finite intermediate fields `E/K`.  The
continuity of conjugation by `σ` is `NK.NeukirchUchida.continuous_conjHom`; applying it
to `σ.symm` gives the continuity of the inverse, which is the *same* map `g ↦ σ ∘ g ∘ σ⁻¹`
read on the other side.  A bijection whose inverse is continuous is an open map
(`Equiv.continuous_symm_iff`), whence `IsHomeomorph`.
-/

namespace NK.NeukirchUchida

open Submission.NeukirchUchida

open scoped Topology

/-- **The conjugation isomorphism is a homeomorphism.**  If `σ : K₂' ≃+* K₁'` maps the
embedded copy of `K₂` onto the embedded copy of `K₁`, then the induced group isomorphism
`conjHomEquiv hσ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)` is a homeomorphism of the Krull topologies.

Continuity in one direction is `continuous_conjHom`; continuity of the inverse is the same
statement for `σ.symm` (whose conjugation map is the inverse of conjugation by `σ`), and a
bijection with continuous inverse is open. -/
theorem isHomeomorph_conjHomEquiv {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [Field K₂] [Field K₁']
    [Field K₂'] [Algebra K₁ K₁'] [Algebra K₂ K₂'] (σ : K₂' ≃+* K₁')
    (hσ : Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ) :
    IsHomeomorph (Submission.NeukirchUchida.conjHomEquiv hσ) := by
  have hcont : Continuous ⇑(Submission.NeukirchUchida.conjHomEquiv hσ) :=
    continuous_conjHom σ hσ
  have hcont_symm : Continuous ⇑((Submission.NeukirchUchida.conjHomEquiv hσ).symm) := by
    have h : ⇑((Submission.NeukirchUchida.conjHomEquiv hσ).symm) =
        ⇑(Submission.NeukirchUchida.conjHom
          (Submission.NeukirchUchida.mapsBase_symm_alg hσ)) := rfl
    rw [h]
    exact continuous_conjHom σ.symm (Submission.NeukirchUchida.mapsBase_symm_alg hσ)
  exact ⟨hcont,
    (Equiv.continuous_symm_iff (Submission.NeukirchUchida.conjHomEquiv hσ).toEquiv).mp
      hcont_symm,
    (Submission.NeukirchUchida.conjHomEquiv hσ).bijective⟩

end NK.NeukirchUchida
