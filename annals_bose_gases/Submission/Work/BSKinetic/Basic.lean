import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BSKinetic.bigKinU_one_eq_oneBody
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BSKinetic.Basic` — elementary identifications of the sliding objects

The definitions of `Defs.lean` are designed so that the corpus's `Work.UBBInputs9` objects are
*definitionally* the `u = 0` member of the moving-box family.  This file records that, and the
two elementary support facts (the anchored window is `chiScale ℓ`, the family is indexed by
translation).
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BSKinetic

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases
open Work.UBBInputs9

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 1. The `u = 0` member of the moving-box family -/

lemma bsBox_at_zero (ℓ : ℝ) : bsBox ℓ 0 = acube ℓ := by
  unfold bsBox
  ext x
  simp

lemma bsWin_at_zero (ℓ : ℝ) : bsWin ℓ 0 = chiScale ℓ := by
  unfold bsWin
  ext x
  simp

lemma bsWin0_at_zero (ℓ : ℝ) : bsWin0 ℓ = chiScale ℓ := rfl

/-- **The `u = 0` member of the moving-box family is the anchored big-box kinetic word.**  This
is the identification that makes `Work.UBBInputs9.BSslidingKin` the `u = 0` anchor of the family
form `familyBigKin`: the RHS of the BS sliding inequality is one member of the family on its left
side. -/
theorem tBwordKinBig_eq_familyBigKin_zero (N : ℕ) (ℓ c : ℝ) (Φ : X N → ℝ) :
    Work.UBBInputs9.tBwordKinBig N ℓ c Φ = Work.UBBInputs9.tBwordKinBigU N ℓ c 0 Φ := by
  have hbox : Work.UBBInputs9.bigBox ℓ 0 = acube ℓ := by
    rw [← bsBox_eq_bigBox, bsBox_at_zero]
  have hwin : Work.UBBInputs9.chiBig ℓ 0 = chiScale ℓ := by
    funext x
    simp [Work.UBBInputs9.chiBig]
  unfold Work.UBBInputs9.tBwordKinBig Work.UBBInputs9.tBwordKinBigU
  rw [hbox, hwin]

/-- The anchored big-box kinetic word is the `u = 0` member of the family form's integrand. -/
theorem anchoredBigKin_eq_familyBigKin_zero (N : ℕ) (ℓ c : ℝ) (Φ : X N → ℝ) :
    anchoredBigKin N ℓ c Φ = Work.UBBInputs9.tBwordKinBigU N ℓ c 0 Φ :=
  tBwordKinBig_eq_familyBigKin_zero N ℓ c Φ

/-! ## 3. The `N = 1` forms, as one-body statements -/

/-- **`familyBigKin` at `N = 1` is the one-body family form.**  Combining
`bigKinU_one_eq_oneBody` with the definition of `familyBigKin`. -/
theorem familyBigKin_one_eq_familyForm {ℓ c : ℝ} (hℓ : 0 < ℓ) (Φ : X 1 → ℝ)
    (hΦ : ContDiff ℝ (⊤ : ENat) Φ) :
    familyBigKin 1 ℓ c Φ = bsFamilyForm ℓ (fsKinCoeff c) (slotFun1 Φ) := by
  unfold familyBigKin bsFamilyForm
  apply integral_congr_ae
  filter_upwards with u
  exact bigKinU_one_eq_oneBody hℓ c u Φ hΦ

/-- **`BSslidingKin` at `N = 1` is the one-body small-box inequality**: definitionally,
`oneBodySmallKin ℓ d b ε c φ ≤ bigBoxWord1 ℓ c φ`. -/
theorem bsSlidingKin_one_iff (ℓ d b ε c : ℝ) (φ : X 1 → ℝ) :
    Work.UBBInputs9.BSslidingKin 1 ℓ d b ε c φ ↔
      oneBodySmallKin ℓ d b ε c φ ≤ bigBoxWord1 ℓ c φ :=
  Iff.rfl

end Work.BSKinetic
