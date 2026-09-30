/-
# The table-level certificate for `∂ ∘ ∂ = 0` on the face poset of `Q̄`

This file collects the *table-level* objects used by the (generated) chunk checks in
`QbarDdCheck.lean` and by the assembly in `QbarCW_hasDdZero.lean`:

* `dimQ i = 4 - #(qTight i)` is the dimension of the face `i` as a function of its index;
* `Sset e` is the set of faces of the facets of `e` (`⋃_{f ∈ qFacet e} qFacet f`);
* `ddTab e g = ∑_{f ∈ qFacet e} [g ∈ qFacet f] · qInc e f · qInc f g` is the coefficient of `g`
  in `∂∂e`, written purely in terms of the generated tables;
* the three propositions `FacetChk e`, `CandChk e`, `CoefChk e` that the generator
  `scripts/gen_qbar_dd_check.py` proves by `decide`, one index range at a time.
-/
import Mathlib
import Submission.Work.MbarHomology.Qbar.CW

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option maxRecDepth 100000
set_option autoImplicit false

namespace Work.MbarHomology.Qbar

open scoped BigOperators
open Work.MbarHomology

/-- The dimension of the face with index `i`, as a function of the index. -/
abbrev dimQ (i : Fin 865) : ℕ := 4 - (qTight i).card

theorem dimQ_le (i : Fin 865) : dimQ i ≤ 4 := Nat.sub_le _ _

/-- The faces of the facets of the face with index `e`. -/
def Sset (e : Fin 865) : Finset (Fin 865) := (qFacet e).biUnion (fun f => qFacet f)

/-- The coefficient of `g` in `∂∂e`, in terms of the generated tables. -/
def ddTab (e g : Fin 865) : ℤ :=
  ∑ f ∈ qFacet e, (if g ∈ qFacet f then qInc e f * qInc f g else 0)

/-- If `g` is a face of no facet of `e` then its `∂∂e`-coefficient is `0`. -/
theorem ddTab_zero_of_notMem {e g : Fin 865} (h : g ∉ Sset e) : ddTab e g = 0 := by
  rw [ddTab, Finset.sum_eq_zero]
  intro f hf
  rw [ite_eq_right (by intro hgf; exact h (Finset.mem_biUnion.mpr ⟨f, hf, hgf⟩))]

/-- Every element of `qFacet e` is a facet of `e`, with the codimension-one tight set. -/
abbrev FacetChk (e : Fin 865) : Prop :=
  ∀ f ∈ qFacet e, qTight e ⊆ qTight f ∧ (qTight f).card = (qTight e).card + 1

/-- Every face whose tight set is obtained from that of `e` by adding one constraint is in
`qFacet e`.  This is the direction of the bridge that is not automatic. -/
abbrev CandChk (e : Fin 865) : Prop := ∀ c : Fin 48, c ∉ qTight e →
    qTight (qOfCode (qCode (insert c (qTight e)))) = insert c (qTight e) →
    qOfCode (qCode (insert c (qTight e))) ∈ qFacet e

/-- `∂∂e = 0` at every face `g` occurring in the tables. -/
abbrev CoefChk (e : Fin 865) : Prop := ∀ g ∈ Sset e, ddTab e g = 0

end Work.MbarHomology.Qbar
