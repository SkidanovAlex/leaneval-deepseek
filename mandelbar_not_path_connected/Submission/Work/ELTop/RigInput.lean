/-
# ELTop discharges the input structure `Work.EL.PairSides` of the ELRig area

The ELRig area (`Submission/Work/ELRig/Defs.lean`) phrases the two-sidedness of a co-landing
pair as the structure `Work.EL.PairSides hN P` and takes it as an explicit hypothesis until
ELTop supplies it.  This file supplies it: every field of `PairSides` is one of the ELTop
lemmas about `pairSide`, `pairSideNear` and `pairSideThroughArc`.

The only additional hypothesis is the non-degeneracy `arcLen P.a P.b ≠ 0`, i.e. the two angles
of the pair are not congruent modulo `ℤ`; without it both sides are the empty set (the reference
point lies on the pair curve) and the decomposition fails.
-/
import Submission.Work.ELRig.Defs
import Submission.Work.ELTop.pairSides_decomposition
import Submission.Work.ELTop.isOpen_pairSide
import Submission.Work.ELTop.paramRay_subset_pairSide
import Submission.Work.ELTop.paramRay_subset_pairSideNear

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set
open scoped Topology

set_option linter.unusedVariables false

noncomputable section

namespace Work.ELTop

/-- **The two-sidedness of a co-landing pair**, in the form in which the ELRig area consumes it
(`Work.EL.PairSides`).  Every field is an ELTop lemma about the pair curve. -/
theorem pairSides {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ) (hJ : Work.Top.JordanForm)
    (P : Work.EL.CoPair hN) (hnd : Work.EL.arcLen P.a P.b ≠ 0) :
    Work.EL.PairSides hN P where
  isOpen_far := (isOpen_pairSide hN P).1
  isOpen_near := (isOpen_pairSide hN P).2
  disjoint := (pairSides_decomposition hN hJ P hnd).2.1
  union_eq := ((pairSides_decomposition hN hJ P hnd).1).symm
  preconnected_far := isPreconnected_connectedComponentIn
  preconnected_near := isPreconnected_connectedComponentIn
  frontier_far := (pairSides_decomposition hN hJ P hnd).2.2.1
  frontier_near := (pairSides_decomposition hN hJ P hnd).2.2.2
  paramRay_far := fun θ hθ => paramRay_subset_pairSide hN hJ P hθ
  paramRay_near := fun θ hθ => paramRay_subset_pairSideNear hN hJ P hθ

/-- The non-degeneracy needed by `pairSides`: for two real angles `a < b < a + 1` (so that the
arc from `a` to `b` is the interval `[a,b]` and is nondegenerate) the arc length is nonzero. -/
theorem arcLen_ne_zero_of_lt {a b : ℝ} (h : a < b) (h' : b < a + 1) : Work.EL.arcLen a b ≠ 0 := by
  have h1 : (0 : ℝ) < b - a := by linarith
  have h2 : b - a < 1 := by linarith
  have hfr : Int.fract (b - a) = b - a := Int.fract_eq_self.mpr ⟨le_of_lt h1, h2⟩
  rw [Work.EL.arcLen, hfr]
  exact ne_of_gt h1


end Work.ELTop
