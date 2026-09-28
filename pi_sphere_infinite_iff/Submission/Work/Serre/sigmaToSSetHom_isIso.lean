import Mathlib
import Submission.Work.Serre.sigmaSSetDefs
import Submission.Work.ThomBordism.sigmaSSetIso

/-!
# The singular simplicial set of a disjoint union is the coproduct

`Work.Serre.sigmaToSSetHom ι X` is the canonical comparison map
`∐ᵢ S(Xᵢ) ⟶ S(Σᵢ Xᵢ)`.  It is an isomorphism: the standard simplex `Δᵏ` is connected, so every
continuous map `Δᵏ ⟶ Σᵢ Xᵢ` lands in a single summand `Xᵢ`; equivalently, the cofan with point
`S(Σᵢ Xᵢ)` and legs `S` of the sum inclusions is colimiting.

That colimiting cofan is `Work.ThomBordism.ssetSigmaCofan`, and its colimit property is
`Work.ThomBordism.ssetSigmaCofan_isColimit`.  The general criterion
`CategoryTheory.Limits.Cofan.nonempty_isColimit_iff_isIso_sigmaDesc` converts a colimiting cofan
`c` into the statement that `Sigma.desc c.inj` is an isomorphism — and `Sigma.desc c.inj` is
exactly `sigmaToSSetHom ι X`, since the latter is defined by the universal property of the
coproduct from these very legs.
-/

open CategoryTheory CategoryTheory.Limits

namespace Work.Serre

theorem sigmaToSSetHom_isIso (ι : Type) (X : ι → Type) [∀ i, TopologicalSpace (X i)] :
    CategoryTheory.IsIso (Work.Serre.sigmaToSSetHom ι X) := by
  have h := (Cofan.nonempty_isColimit_iff_isIso_sigmaDesc
      (Work.ThomBordism.ssetSigmaCofan (fun i => TopCat.of (X i)))).mp
      ⟨Work.ThomBordism.ssetSigmaCofan_isColimit (fun i => TopCat.of (X i))⟩
  exact h

end Work.Serre
