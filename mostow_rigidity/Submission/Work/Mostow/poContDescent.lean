import Mathlib
import Submission.Work.Mostow.poAux

/-!
# Descending continuity of the `PO(n,1)`-action to the projectivised group

The action of `PO n 1` on the chart `E n` is defined through a chosen representative,
`g • u = actO (Quotient.out g) u`.  The point of this file is that continuity of the
matrix-level action `(A, u) ↦ actO A u` (hypothesis `h1`) *descends* to `PO n 1`
(hypothesis `h2` records that the action is well defined on the quotient).

The quotient map `O1 n → PO n 1 = O1 n ⧸ center` is an *open* quotient map
(`QuotientGroup.isOpenQuotientMap_mk`), so its product with the identity on the locally
compact chart `E n` is again an open quotient map.  A map out of a quotient is continuous
iff its composite with the quotient map is, which reduces the claim to `h1`.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory Matrix

/-- Continuity of the `PO n 1`-action on `E n` descends from continuity of the underlying
`O(n,1)`-action, the latter being provided by hypothesis `h1`. -/
theorem poContDescent (n : ℕ)
    (h1 : Continuous (fun p : O1 n × E n => actO p.1 p.2))
    (h2 : ∀ (A : O1 n) (u : E n), (A : PO n 1) • u = actO A u) :
    Continuous (fun p : PO n 1 × E n => p.1 • p.2) := by
  -- The quotient map `O1 n → PO n 1` is open; pair it with the identity on `E n`.
  have hf : IsOpenQuotientMap (Prod.map (QuotientGroup.mk : O1 n → PO n 1) (id : E n → E n)) :=
    (QuotientGroup.isOpenQuotientMap_mk).prodMap IsOpenQuotientMap.id
  -- A map out of the quotient is continuous iff its composite with the quotient map is.
  rw [← hf.continuous_comp_iff]
  -- The composite is exactly the matrix-level action, by well-definedness of the action.
  convert h1 using 1
  funext p
  exact h2 p.1 p.2

end Work.Mostow
