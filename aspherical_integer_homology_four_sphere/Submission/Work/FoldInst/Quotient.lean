/-
# The space `M̄`, its topological instances, and the truncation set

`M̄` is the quotient of the two copies of the truncated 24-cell by the identification relation `~₁`.
The class atlas of `Atlas.lean` gives the Hausdorff property, and the compactness of `Q̄` propagates
to `M̄`.  The *truncation set* is the image of the union of the truncation facets; it is a closed
subset (the boundary of `M̄`, i.e. the union of the five cusped tori).
-/
import Mathlib
import Submission.Work.QuotientT2.ClassAtlasQuotient
import Submission.Work.FoldInst.Atlas
import Submission.Work.FoldInst.Qbar_geometry

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open Matrix
open scoped Matrix

namespace Work.FoldInst

instance : CompactSpace Qbar := isCompact_iff_compactSpace.mp Qbar_geometry.1

instance : CompactSpace Xbar := inferInstance

/-- **The space `M̄`**: the two truncated 24-cells glued by the side pairings. -/
abbrev Mbar := Quotient setoid

/-- The quotient map. -/
abbrev mk (x : Xbar) : Mbar := Quotient.mk setoid x

instance : T2Space Mbar := classAtlas.t2Space_quotient

instance : CompactSpace Mbar := Quotient.compactSpace

instance : T1Space Mbar := inferInstance

/-- A set is open in `M̄` iff its preimage in the two copies is open. -/
theorem isOpen_quotient_iff_preimage {U : Set Mbar} : IsOpen U ↔ IsOpen (mk ⁻¹' U) :=
  QuotientT2.isOpen_quotient_iff_preimage

/-- A set is closed in `M̄` iff its preimage in the two copies is closed. -/
theorem isClosed_quotient_iff_preimage {U : Set Mbar} : IsClosed U ↔ IsClosed (mk ⁻¹' U) :=
  QuotientT2.isClosed_quotient_iff_preimage

/-! ### The truncation set -/

/-- The union of the truncation facets, inside the two copies of `Q̄`. -/
def Xtrunc : Set Xbar := {x | ∃ w : Fin 24, truncSlack w x.2.1 = 0}

theorem isClosed_Xtrunc : IsClosed Xtrunc := by
  have h : Xtrunc = ⋃ (w : Fin 24), {x : Xbar | truncSlack w x.2.1 = 0} := by
    ext x
    simp only [Xtrunc, Set.mem_setOf_eq, Set.mem_iUnion]
  rw [h]
  exact isClosed_iUnion_of_finite fun w => isClosed_eq
    ((continuous_truncSlack w).comp
      ((continuous_subtype_val : Continuous (Subtype.val : Qbar → E4)).comp continuous_snd))
    continuous_const

/-- The truncation set is invariant under the action: a sign change permutes the truncation
constraints. -/
theorem actX_mem_Xtrunc {γ : Gg} {x : Xbar} (h : x ∈ Xtrunc) : actX γ x ∈ Xtrunc := by
  obtain ⟨w, hw⟩ := h
  refine ⟨truncPerm γ.1 w, ?_⟩
  rw [show (actX γ x).2.1 = act γ.1 x.2.1 from rfl, truncSlack_act γ.1 (truncPerm γ.1 w) x.2.1]
  rw [truncPerm_invol]
  exact hw

/-- The saturation of the truncation facets. -/
def XtruncSat : Set Xbar := {y | ∃ x ∈ Xtrunc, rel x y}

theorem Xtrunc_subset_sat : Xtrunc ⊆ XtruncSat := fun x hx => ⟨x, hx, rel_refl x⟩

theorem isClosed_XtruncSat : IsClosed XtruncSat := by
  have h : XtruncSat = Xtrunc := by
    ext y
    constructor
    · rintro ⟨x, hx, h⟩
      obtain ⟨γ, hγ, rfl⟩ := h
      exact actX_mem_Xtrunc hx
    · exact fun hy => Xtrunc_subset_sat hy
  rw [h]
  exact isClosed_Xtrunc

/-- **The truncation set** `T ⊆ M̄`: the image of the truncation facets. -/
def Tset : Set Mbar := mk '' Xtrunc

theorem isClosed_Tset : IsClosed Tset :=
  QuotientT2.ClassAtlas.isClosedMap_quotient_mk classAtlas Xtrunc isClosed_Xtrunc

theorem mem_Tset_iff {p : Mbar} : p ∈ Tset ↔ ∃ x ∈ Xtrunc, mk x = p := Iff.rfl

end Work.FoldInst
