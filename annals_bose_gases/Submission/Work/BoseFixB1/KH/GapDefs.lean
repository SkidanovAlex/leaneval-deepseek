import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.SmallBoxSliding.Assembly
import Submission.Work.SmallBoxSliding.Band
import Submission.Work.SmallBoxSliding.Jensen
import Submission.Work.SmallBoxSliding.boxMass_integral_u
import Submission.Work.SmallBoxSliding.chiSmallB_continuous_joint
import Submission.Work.SmallBoxSliding.integral_chiMass_eq
import Submission.Work.SmallBoxSliding.integral_chiSmallB_sq_u
import Submission.Work.SmallBoxSliding.nBoxInd_integral_u
import Submission.Work.SmallBoxSliding.qLHSwordB_integral_u
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1.KH.GapDefs` — the sliding-box vocabulary of the gap pairing

The gap pairing (`Work.BoseFixB1.KH.gap_pairing`) bounds the `u`-integral of the small-box
excited count by the anchored box's Neumann resolvent fraction.  This module fixes the notation
it is stated in: the small box `B(u) = dlBox ℓ d u`, its true volume `boxMass ℓ d u`, its
indicator `boxInd ℓ d u`, the box mean `bMean ℓ d u f` and FS's mean-free projection
`bQ ℓ d u f = 1_{B(u)}(f − ⨍_{B(u)}f)`.

Nothing here is deep: `bMean`/`bQ` are definitions (`1/0 = 0` at the empty box, where both
sides vanish anyway).
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BoseFixB1.KH

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- The corpus's coordinate basis `Submission.BoseGases.kcStdBasis` is the standard orthonormal
basis of `EuclideanSpace ℝ (Fin 3)` (the basis in which the corpus writes the Dirichlet form of
`Work.BoseKinLoc.neuFrac`). -/
lemma kcStdBasis_eq_basisFun (k : Fin 3) :
    Submission.BoseGases.kcStdBasis k = EuclideanSpace.basisFun (Fin 3) ℝ k := by
  rw [Submission.BoseGases.kcStdBasis, EuclideanSpace.basisFun_apply]

/-- The rectangular box `∏_j [a_j, b_j]` of `ℝ³`. -/
def rectBox (a b : E3) : Set E3 := {y : E3 | ∀ j : Fin 3, a j ≤ y j ∧ y j ≤ b j}

/-- **The box mean** `⨍_{B(u)} f = |B(u)|⁻¹ ∫_{B(u)} f`, written with the indicator
(`1/0 = 0` on the empty box, where both sides vanish). -/
noncomputable def bMean (ℓ d : ℝ) (u : E3) (f : E3 → ℝ) : ℝ :=
  (1 / Work.SmallBoxSliding.boxMass ℓ d u) *
    ∫ x : E3, Work.SmallBoxSliding.boxInd ℓ d u x * f x

/-- **FS's mean-free projection** `Q_{B(u)} f = 1_{B(u)} (f − ⨍_{B(u)} f)`. -/
noncomputable def bQ (ℓ d : ℝ) (u : E3) (f : E3 → ℝ) : E3 → ℝ :=
  fun x => Work.SmallBoxSliding.boxInd ℓ d u x * (f x - bMean ℓ d u f)

@[simp] lemma bQ_apply (ℓ d : ℝ) (u : E3) (f : E3 → ℝ) (x : E3) :
    bQ ℓ d u f x = Work.SmallBoxSliding.boxInd ℓ d u x * (f x - bMean ℓ d u f) := rfl

lemma boxInd_apply (ℓ d : ℝ) (u x : E3) :
    Work.SmallBoxSliding.boxInd ℓ d u x
      = (Submission.BoseGases.dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) x := rfl

lemma boxInd_nonneg (ℓ d : ℝ) (u x : E3) :
    0 ≤ Work.SmallBoxSliding.boxInd ℓ d u x := by
  by_cases hx : x ∈ Submission.BoseGases.dlBox ℓ d u
  · simp [boxInd_apply, Set.indicator_of_mem hx]
  · simp [boxInd_apply, Set.indicator_of_notMem hx]

lemma boxInd_le_one (ℓ d : ℝ) (u x : E3) :
    Work.SmallBoxSliding.boxInd ℓ d u x ≤ 1 := by
  by_cases hx : x ∈ Submission.BoseGases.dlBox ℓ d u
  · simp [boxInd_apply, Set.indicator_of_mem hx]
  · simp [boxInd_apply, Set.indicator_of_notMem hx]

lemma boxMass_nonneg (ℓ d : ℝ) (u : E3) : 0 ≤ Work.SmallBoxSliding.boxMass ℓ d u :=
  integral_nonneg fun x => boxInd_nonneg ℓ d u x

lemma bMean_eq (ℓ d : ℝ) (u : E3) (f : E3 → ℝ) :
    bMean ℓ d u f
      = (1 / Work.SmallBoxSliding.boxMass ℓ d u) *
          ∫ x : E3, Work.SmallBoxSliding.boxInd ℓ d u x * f x := rfl

end Work.BoseFixB1.KH
