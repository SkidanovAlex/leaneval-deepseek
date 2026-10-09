/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# What the ramification filtration computes: the fixed-field dictionary

`Submission/Work/Ramification/Determined.lean` records, in its header, that "the maximal tamely
ramified subextension is the fixed field of `G_1`" and that the filtration determines the lower
indices `g_i`.  This file proves the *dictionary* between the filtration and the field-theoretic
quantities, which is what turns the filtration into usable data for Neukirch's *Kennzeichnung*:

* `NK.RamificationDeep.finrank_fixedField_ramificationSubgroup`:
  **the fixed field of `G_i` has degree `g_i = lowerIndex A i` over the top field `L`**, i.e.
  `[L : L^{G_i}] = g_i` — the indices of the filtration are the degrees of the fixed-field tower;
* `NK.RamificationDeep.finrank_fixedField_zero_eq_addVal`: consequently
  **`[L : L^{G_0}] = e(L/M)`**, the ramification index (the identity `#G_0 = e(L/M)` is
  `NK.RamificationAudit.lowerIndex_zero_eq_addVal_uniformizer`); so `L^{G_0}` is the *inertia
  field*, of degree `e(L/M)` over `M`, and the residual degree is `[L^{G_0} : M] = f(L/M)`;
* `NK.RamificationDeep.finrank_fixedField_one_mul_tame`:
  `[L : L^{G_0}] = [L : L^{G_1}] · [L^{G_1} : L^{G_0}]`, the decomposition of the ramification
  index into its `p`-part (`#G_1`, the wild part) and its prime-to-`p` part (`#(G_0/G_1)`, the tame
  part — the companion file proves the coprimality of the latter with `p`).

Together with `NK.RamificationDeep.ramificationSubgroup_inf_fixingSubgroup` (the compatibility of
the lower filtration with subextensions) and `NK.RamificationDeep.herbrandMultiplicativity_of_tower`
(the Herbrand formula in towers), these are the field-theoretic readings of the filtration that
steps (a) and (c) of Neukirch's proof use.
-/
import Mathlib
import Submission.NK.Ramification.Herbrand
import Submission.NK.RamificationAudit.lowerIndex_zero_eq_addVal_uniformizer
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open scoped Pointwise

namespace NK.RamificationDeep

universe u

noncomputable section

variable {K : Type*} {L : Type*} [Field K] [Field L] [Algebra K L]

/-! ## The fixed field of `G_i` has degree `g_i` -/

/-- **The fixed-field dictionary**: for any subgroup `H` of the decomposition subgroup, the fixed
field of `H` has degree `#H` over `L`.  This is Mathlib's `finrank_fixedField_eq_card` for the
image of `H` in `Gal(L/K)`, together with the invariance of the cardinality under the injective
inclusion. -/
theorem finrank_fixedField_map_subtype_eq_natCard (A : ValuationSubring L) [FiniteDimensional K L]
    (H : Subgroup (A.decompositionSubgroup K)) :
    Module.finrank ↥(IntermediateField.fixedField (H.map (A.decompositionSubgroup K).subtype)) L
      = Nat.card ↥H := by
  rw [IntermediateField.finrank_fixedField_eq_card]
  exact (Nat.card_congr
    (Subgroup.equivMapOfInjective H (A.decompositionSubgroup K).subtype
      Subtype.coe_injective).toEquiv).symm

/-- **The fixed field of the `i`-th ramification subgroup has degree `g_i` over `L`**:

  `[L : L^{G_i}] = g_i = #G_i`.

In particular the indices of the lower filtration are exactly the degrees of the fixed fields of
its members, so every statement about the `g_i` is a statement about the tower
`L = L^{G_0} ⊇ … ⊇ L^{G_i} ⊇ …` (`G_i ⊇ G_{i+1}` gives `L^{G_i} ⊆ L^{G_{i+1}}`). -/
theorem finrank_fixedField_ramificationSubgroup (A : ValuationSubring L) [FiniteDimensional K L]
    (i : ℕ) :
    Module.finrank ↥(IntermediateField.fixedField
        ((NK.Ramification.ramificationSubgroup (K := K) A i).map
          (A.decompositionSubgroup K).subtype)) L
      = NK.Ramification.lowerIndex (K := K) A i :=
  finrank_fixedField_map_subtype_eq_natCard (K := K) A
    (NK.Ramification.ramificationSubgroup (K := K) A i)

/-! ## The two corollaries are delegated

The corollaries

* `NK.RamificationDeep.finrank_fixedField_zero_eq_addVal` — `[L : L^{G_0}] = e(L/M)`: the
  inertia field has degree the ramification index;
* `NK.RamificationDeep.finrank_fixedField_one_mul_tame` and
  `NK.RamificationDeep.coprime_p_finrank_fixedField_tame` — the decomposition of the ramification
  index into its wild part `#G_1` (a `p`-power) and its tame part `#(G_0/G_1)` (prime to `p`),

are proved in the companion files `finrank_fixedField_zero_eq_addVal.lean` and
`finrank_fixedField_tame.lean` (delegated), which carry the instance bookkeeping for the towers of
intermediate fields.  Their content is the immediate combination of
`finrank_fixedField_ramificationSubgroup` above with
`NK.RamificationAudit.lowerIndex_zero_eq_addVal_uniformizer` (`#G_0 = e`) and with
`NK.RamificationDeep.coprime_natCard_quotient_zero_of_card` (`p ∤ #(G_0/G_1)`). -/

end

end NK.RamificationDeep
