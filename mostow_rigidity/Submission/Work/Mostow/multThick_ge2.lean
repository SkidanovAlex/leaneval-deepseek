import Mathlib
import Submission.Mostow.GapADefs
import Submission.Work.Mostow.geomFiniteMultThick

/-! Guidance from the project lead (the requester):

# Low-dimensional copies (lead's request). The strata / Kazhdan-Margulis / geodesic-stratum chapters need the toolkit in
# every dimension k >= 1 (strata of dimension 1, 2, ... inside H^n). Your statement is the SAME Prop as an already-PROVED
# area lemma, only with a weaker dimension hypothesis:
#   multThick_ge2     <- Work.Mostow.geomFiniteMultThick (PROVED in the geomFinite tree); restate for 2 <= n.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

/-- The multiplicity-`N` thick part of a lattice is cocompact, in every dimension `n ≥ 2`.

This is the dimension-`2` (and higher) restatement of `Work.Mostow.geomFiniteMultThick`, whose
proof is the multiplicity-`N` packing/counting argument and never uses anything beyond `n ≥ 1`. -/
theorem multThick_ge2 (n : ℕ) (hn : 2 ≤ n) (hA : POActionProp n) (hI : HypIsometryProp n)
    (Γ : Subgroup (PO n 1)) (hΓ : HypLattice Γ) : MultThickProp Γ :=
  geomFiniteMultThick n (by omega) hA hI Γ hΓ

end Work.Mostow
