import Submission.Work.ConvexCells.Basic
import Submission.Work.ConvexCells.FlagPt_mem
import Submission.Work.ConvexCells.tightAt_flagPt
import Submission.Work.ConvexCells.exists_exit
import Submission.Work.ConvexCells.exists_flagPt
import Submission.Work.ConvexCells.flagPt_unique
import Submission.Work.ConvexCells.Carriers_of_Ok
import Submission.Work.ConvexCells.Carriers_of_unionClosed
import Submission.Work.ConvexCells.Carriers_of_addF

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false

/-!
# The barycentric subdivision of a polytope realizes its face lattice

Main results of the `ConvexCells` area.

* `sd_carrier` — the affine realization of the open simplex attached to a flag lies in the relative
  interior of the *largest* face of the flag;
* `sd_realization` — **the headline**: for data passing the decidable `checks`, the affine
  realization of the disjoint union of the open flag simplices is a bijection onto
  `P.Pset = {x | ∀ i, ⟪n_i,x⟫ ≤ b_i}`;
* `sd_realization_of_carriers`, `sd_realization_of_unionClosed`, `sd_realization_of_addF` — the same
  with the face-completeness hypothesis taken as a hypothesis or discharged by an auxiliary
  certificate scheme.
-/

namespace Work.ConvexCells

open scoped BigOperators

variable {d : ℕ}

/-- Face compatibility: the open simplex attached to a flag lies in the relative interior of the
largest face of that flag. -/
theorem sd_carrier (P : PolytopeData d) (h : P.checks = true) (s : P.FlagPt) :
    P.tightAt s.toE' = P.tight s.topFace :=
  tightAt_flagPt P (P.checks_sound h) s

/-- **The barycentric subdivision realizes the polytope**, in terms of the explicit
face-completeness hypothesis `Carriers`. -/
theorem sd_realization_of_carriers (P : PolytopeData d) (h : P.checks = true) (hc : P.Carriers) :
    Set.BijOn (fun s : P.FlagPt => s.toE') Set.univ P.Pset := by
  refine ⟨fun s _ => FlagPt_mem (P := P) (P.checks_sound h) s, fun s _ t _ hst => ?_,
    fun y hy => ?_⟩
  · exact flagPt_unique P (P.checks_sound h) s t hst
  · obtain ⟨s, hs⟩ := exists_flagPt P (P.checks_sound h) hc y hy
    exact ⟨s, trivial, hs⟩

/-- **The barycentric subdivision realizes the polytope.**  For data satisfying the decidable
`checks` (which include the certificates that make `Carriers` automatic, see `Carriers_of_Ok`), the
affine realization of the disjoint union of the open flag simplices is a bijection onto `P.Pset`. -/
theorem sd_realization (P : PolytopeData d) (h : P.checks = true) :
    Set.BijOn (fun s : P.FlagPt => s.toE') Set.univ P.Pset :=
  sd_realization_of_carriers P h (Carriers_of_Ok P (P.checks_sound h))

/-- `sd_realization` with `Carriers` discharged from closure of the face family under unions of
tight sets (an auxiliary scheme; see `UnionClosed`). -/
theorem sd_realization_of_unionClosed (P : PolytopeData d) (h : P.checks = true)
    (hu : P.UnionClosed) : Set.BijOn (fun s : P.FlagPt => s.toE') Set.univ P.Pset :=
  sd_realization_of_carriers P h (Carriers_of_unionClosed P (P.checks_sound h) hu)

/-- `sd_realization` with `Carriers` discharged from a certificate that every face can be enlarged by
one extra constraint. -/
theorem sd_realization_of_addF (P : PolytopeData d) (h : P.checks = true)
    (addF : Fin P.K → Fin P.m → Fin P.K)
    (hsub : ∀ f i, P.tight f ⊆ P.tight (addF f i))
    (hmem : ∀ f i, i ∈ P.tight (addF f i))
    (himp : ∀ f i (y : E d), y ∈ P.Pset → (∀ k ∈ P.tight f, inner ℝ (P.nR k) y = P.bR k) →
      inner ℝ (P.nR i) y = P.bR i →
      ∀ j ∈ P.tight (addF f i), inner ℝ (P.nR j) y = P.bR j) :
    Set.BijOn (fun s : P.FlagPt => s.toE') Set.univ P.Pset :=
  sd_realization_of_carriers P h (Carriers_of_addF P (P.checks_sound h) addF hsub hmem himp)

end Work.ConvexCells
