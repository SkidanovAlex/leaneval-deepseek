import Mathlib
import Submission.Work.SSGRoute.Interfaces
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Vocabulary for the Grünwald-with-escape core (`grunwald_escape_relative`)

The statement of the design's node N2 (`Work.SSGRoute.grunwald_escape_relative`) uses the
pointwise action of `Gal(Ω/k)` on the places `ValuationSubring Ω`, whose `SMul` instance lives in
the `Pointwise` scope.  Since a delegated restatement has to elaborate in an environment in which
that scope is *not* open, the two places where the statement mentions `τ • A` are packaged here as
the predicate `gesKConj`; the statements of the files that depend on `grunwald_escape_relative` can
then be written without any scoped notation.

`gesKConj K A B` (`B` lies over the same prime of the subfield `K` as `A`) is *not* the same as
`SSGRoute.IsConjPlace k A B` (conjugacy over the base field `k`): `K`-conjugacy is the finer
relation used by the one-place-per-`K`-prime sets `T` of the Grünwald statements.
-/

namespace Work.SSGRoute

open _root_.SSGRoute
open scoped Pointwise

/-- `B` lies over the same prime of the subfield `K` as `A`: `B = τ • A` for some `τ` in the
fixing subgroup `K.fixingSubgroup` of `K`. -/
def gesKConj {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] (K : IntermediateField k Ω)
    (A B : ValuationSubring Ω) : Prop :=
  ∃ τ ∈ K.fixingSubgroup, τ • A = B

/-- The element of `Gal(Ω/↥K)` attached to an element of a local group
`decomp k A ⊓ K.fixingSubgroup`. -/
noncomputable def gesLocalToGalK {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]
    (K : IntermediateField k Ω) {A : ValuationSubring Ω}
    (σ : ↥(SSGRoute.decomp k A ⊓ K.fixingSubgroup)) : Ω ≃ₐ[↥K] Ω :=
  (IntermediateField.fixingSubgroupEquiv K)
    ⟨(σ : Ω ≃ₐ[k] Ω), (Subgroup.mem_inf.mp σ.2).2⟩

/-- The element of `Gal(Ω/↥K)` attached to an element `σ` of `K.fixingSubgroup`. -/
noncomputable def gesGalKOfFixing {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]
    (K : IntermediateField k Ω) (σ : Ω ≃ₐ[k] Ω) (hσ : σ ∈ K.fixingSubgroup) : Ω ≃ₐ[↥K] Ω :=
  (IntermediateField.fixingSubgroupEquiv K) ⟨σ, hσ⟩

end Work.SSGRoute
