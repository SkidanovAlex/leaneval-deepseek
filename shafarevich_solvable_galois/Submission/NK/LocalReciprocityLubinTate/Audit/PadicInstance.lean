import Submission.NK.LocalReciprocityLubinTate.Basic
import Submission.NK.LocalReciprocityLubinTate.Audit.isValuativeTopology_padic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The `p`-adic instantiation of the chapter's local-field conventions

Mathlib does not register `IsNonarchimedeanLocalField ℚ_[p]`: `ℚ_[p]` carries `ValuativeRel` and the
`p`-adic norm topology, but the missing link is `IsValuativeTopology ℚ_[p]`, which is supplied by
`NK.LocalReciprocityLubinTate.Audit.isValuativeTopology_padic`.  Here it is installed as an
instance, so that every definition of the chapter (`residueCard`, `principalUnits`, `higherUnits`,
`IsUniformizer`, and the Lubin–Tate tower's unit filtration) can be instantiated at `ℚ_[2]` and
`ℚ_[3]`.

This is the formal instantiation demanded by the audit of the chapter; see `Conventions.lean` for the
corresponding statements.
-/

open scoped ValuativeRel

namespace NK.LocalReciprocityLubinTate

/-- **`ℚ_[p]` is a nonarchimedean local field** in Mathlib's sense: the `p`-adic valuation topology
is the valuative topology of `mulValuation`, the field is locally compact, and the valuation is
nontrivial. -/
instance isNonarchimedeanLocalField_padic (p : ℕ) [Fact p.Prime] :
    IsNonarchimedeanLocalField ℚ_[p] where
  toIsValuativeTopology := Audit.isValuativeTopology_padic p
  toLocallyCompactSpace := inferInstance
  toIsNontrivial := inferInstance

end NK.LocalReciprocityLubinTate
