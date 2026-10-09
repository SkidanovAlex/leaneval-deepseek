import Mathlib
import Submission.NK.LocalReciprocityLubinTate.Audit.hondaReciprocity_level_one_residueCard_two
import Submission.NK.LocalReciprocityLubinTate.Audit.residueCard_padic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The level-one Honda identity at `ℚ_[2]`

The audit witness
`NK.LocalReciprocityLubinTate.Audit.hondaReciprocity_level_one_residueCard_two` is stated for
every nonarchimedean local field of residue cardinality `2`.  This file instantiates it at the
`p`-adic field `ℚ_[2]` demanded by the specification's audit duty (`p = 2`), using
`NK.LocalReciprocityLubinTate.Audit.residueCard_padic`.

## Main result

* `NK.LocalReciprocityLubinTate.Audit.hondaReciprocity_level_one_padic_two`.
-/

namespace NK.LocalReciprocityLubinTate.Audit

/-- **Honda's reciprocity law at level one, for `ℚ_[2]`**:
`N_{ℚ_[2](Λ_1)/ℚ_[2]} ℚ_[2](Λ_1)ˣ = ⟨π⟩ · U¹` for every uniformiser `π` of `ℚ_[2]`. -/
theorem hondaReciprocity_level_one_padic_two (π : ℚ_[2]ˣ)
    (hπ : NK.LocalReciprocityLubinTate.IsUniformizer ℚ_[2] (π : ℚ_[2])) :
    NK.LocalReciprocity.normGroup ℚ_[2]
        ↥(NK.LocalReciprocityLubinTate.LTLevel ℚ_[2] (π : ℚ_[2]) 2 1) =
      Subgroup.zpowers π ⊔ NK.LocalReciprocityLubinTate.higherUnits ℚ_[2] 1 :=
  hondaReciprocity_level_one_residueCard_two ℚ_[2] π hπ (residueCard_padic 2)

/-- The same at the `residueCard`-indexed level, i.e. the literal `n = 1` component of
`NK.LocalReciprocityLubinTate.HondaReciprocity (Q.adicCompletion K) π (higherUnits _) q` for the
`q = residueCard ℚ_[2]` of the boundary theorem. -/
theorem hondaReciprocity_level_one_padic_two_residueCard (π : ℚ_[2]ˣ)
    (hπ : NK.LocalReciprocityLubinTate.IsUniformizer ℚ_[2] (π : ℚ_[2])) :
    NK.LocalReciprocity.normGroup ℚ_[2]
        ↥(NK.LocalReciprocityLubinTate.LTLevel ℚ_[2] (π : ℚ_[2])
          (NK.LocalReciprocityLubinTate.residueCard ℚ_[2]) 1) =
      Subgroup.zpowers π ⊔ NK.LocalReciprocityLubinTate.higherUnits ℚ_[2] 1 := by
  rw [residueCard_padic 2]
  exact hondaReciprocity_level_one_padic_two π hπ

end NK.LocalReciprocityLubinTate.Audit
