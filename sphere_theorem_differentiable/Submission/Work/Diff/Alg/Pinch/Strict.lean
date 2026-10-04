import Mathlib
import Submission.Work.Diff.Alg.Pinch.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Strict (interior) versions of the PIC2 / Ricci-pinching cones

The Böhm–Wilking cone family is built from the *closed* cone
`Dpic p = {R | IsAlgCurv R ∧ InPIC2 R ∧ RicPinch p R}`
and its images under the linear transformations `ell a b`.  Transversal invariance of the
corresponding cones `Ccone a b p = ell a b '' Dpic p` is a statement about the *interior* of the
cone, so we record strict predicates whose sets are those (relative) interiors.

Both strict predicates are phrased as "one may move a little way into the round sphere", which is
the standard description of the interior of a convex cone with nonempty interior: since `Iso n`
satisfies `InPIC2` and `RicPinch p` (`p ≤ 1`) with a positive *margin*,
`InPIC2 (R - ε • Iso n)` for some `ε > 0` holds exactly when `R` is an interior point of the cone
`{R | InPIC2 R}`, and similarly for `RicPinch p` at any `p < 1`.
-/

namespace Work.Diff.Alg.Pinch

open Finset Submission.Diff.Alg

variable {n : ℕ}

/-- `R` lies in the interior of the cone of tensors with nonnegative complex sectional curvature:
`R` can be moved a little way in the `-Iso n` direction while remaining `InPIC2`. -/
def StrictInPIC2 (R : Curv4 n) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ InPIC2 (R - ε • Iso n)

/-- `R` satisfies the Ricci pinching `Ric ≥ (p/n)·scal` with a positive margin. -/
def StrictRicPinch (p : ℝ) (R : Curv4 n) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ RicPinch p (R - ε • Iso n)

/-- The strict (interior) version of the cone `Dpic p`. -/
def DpicS (p : ℝ) : Set (Curv4 n) :=
  {R | IsAlgCurv R ∧ StrictInPIC2 R ∧ StrictRicPinch p R}

/-- The interior of the Böhm–Wilking cone `Ccone a b p`, i.e. `ell a b` applied to `DpicS p`. -/
def CconeS (a b p : ℝ) : Set (Curv4 n) := ell a b '' DpicS (n := n) p

end Work.Diff.Alg.Pinch
