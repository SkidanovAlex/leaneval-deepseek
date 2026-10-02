import Mathlib
import Submission.Work.Gen.Euler
import Submission.Work.Gen.Basic
import Submission.Work.Gen.EulerDefs
import Submission.Work.Gen.EulerChernCP4
import Submission.Work.Whitney.Basic
import Submission.Work.Whitney.Cup

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

/-!
# The ring computation for `Work.Gen.EulerChern`

This module carries out, for `ℂP⁴`, the *bookkeeping* half of `Work.Gen.EulerChern`: from the
Whitney sum formula (isolated as the hypothesis `Work.Gen.WhitneyFormula`, owned by
`Submission/Work/Whitney/`) and the duality sign `Work.Gen.TautDualSign`, it computes the Chern
classes of the five-fold sum `Work.Gen.eulerTarget = (ℂ ⊗ O(1))⁵`:

  `c₂(eulerTarget) = -5 • uSq 4`,  `c₄(eulerTarget) = 10 • uFourth 4`.

Everything below is *conditional* on those two inputs; the only place they are used is the section
`Whitney` at the top (`whitney_one`, `whitney_two`, `whitney_four`) and `lineC4_two` (which uses
`TautDualSign`).
-/

open CategoryTheory
open Work.Projective

namespace Work.Gen

noncomputable section

local notation "ss" => Work.Whitney.ssB (CP 4)

/-- `↑(3 : Fin 5) = 3`. -/
theorem fin_five_three : (↑(3 : Fin 5) : ℕ) = 3 := by norm_num

/-- `↑(4 : Fin 5) = 4`. -/
theorem fin_five_four : (↑(4 : Fin 5) : ℕ) = 4 := by norm_num

/-! ## The Whitney formula in degrees 1, 2 and 4 (the isolated use of `WhitneyFormula`) -/

theorem whitney_one (hW : WhitneyFormula) {m₁ m₂ : ℕ} {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂]
    (Z₁ : VectorBundleCore ℂ (CP 4) (EuclideanSpace ℂ (Fin m₁)) ι₁)
    (Z₂ : VectorBundleCore ℂ (CP 4) (EuclideanSpace ℂ (Fin m₂)) ι₂) :
    Work.Thom.chernClass (m₁ + m₂) 1 (Work.Whitney.whitneySum Z₁ Z₂)
      = Work.Cohomology.cupH' ℤ ss 0 2 (Work.Thom.chernClass m₁ 0 Z₁)
          (Work.Thom.chernClass m₂ 1 Z₂)
        + Work.Cohomology.cupH' ℤ ss 2 0 (Work.Thom.chernClass m₁ 1 Z₁)
          (Work.Thom.chernClass m₂ 0 Z₂) := by
  rw [hW Z₁ Z₂ (j := 1), Fin.sum_univ_two]
  simp only [Fin.val_zero, Fin.val_one, Nat.sub_zero, Nat.add_zero, Nat.mul_zero]
  rw [Work.Gen.cohTransport_eq_id', Work.Gen.cohTransport_eq_id']

theorem whitney_two (hW : WhitneyFormula) {m₁ m₂ : ℕ} {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂]
    (Z₁ : VectorBundleCore ℂ (CP 4) (EuclideanSpace ℂ (Fin m₁)) ι₁)
    (Z₂ : VectorBundleCore ℂ (CP 4) (EuclideanSpace ℂ (Fin m₂)) ι₂) :
    Work.Thom.chernClass (m₁ + m₂) 2 (Work.Whitney.whitneySum Z₁ Z₂)
      = Work.Cohomology.cupH' ℤ ss 0 4 (Work.Thom.chernClass m₁ 0 Z₁)
          (Work.Thom.chernClass m₂ 2 Z₂)
        + Work.Cohomology.cupH' ℤ ss 2 2 (Work.Thom.chernClass m₁ 1 Z₁)
          (Work.Thom.chernClass m₂ 1 Z₂)
        + Work.Cohomology.cupH' ℤ ss 4 0 (Work.Thom.chernClass m₁ 2 Z₁)
          (Work.Thom.chernClass m₂ 0 Z₂) := by
  rw [hW Z₁ Z₂ (j := 2), Fin.sum_univ_three]
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, Nat.sub_zero, Nat.sub_self, Nat.add_zero,
    Nat.mul_zero]
  rw [Work.Gen.cohTransport_eq_id', Work.Gen.cohTransport_eq_id', Work.Gen.cohTransport_eq_id']

theorem whitney_four (hW : WhitneyFormula) {m₁ m₂ : ℕ} {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂]
    (Z₁ : VectorBundleCore ℂ (CP 4) (EuclideanSpace ℂ (Fin m₁)) ι₁)
    (Z₂ : VectorBundleCore ℂ (CP 4) (EuclideanSpace ℂ (Fin m₂)) ι₂) :
    Work.Thom.chernClass (m₁ + m₂) 4 (Work.Whitney.whitneySum Z₁ Z₂)
      = Work.Cohomology.cupH' ℤ ss 0 8 (Work.Thom.chernClass m₁ 0 Z₁)
          (Work.Thom.chernClass m₂ 4 Z₂)
        + Work.Cohomology.cupH' ℤ ss 2 6 (Work.Thom.chernClass m₁ 1 Z₁)
          (Work.Thom.chernClass m₂ 3 Z₂)
        + Work.Cohomology.cupH' ℤ ss 4 4 (Work.Thom.chernClass m₁ 2 Z₁)
          (Work.Thom.chernClass m₂ 2 Z₂)
        + Work.Cohomology.cupH' ℤ ss 6 2 (Work.Thom.chernClass m₁ 3 Z₁)
          (Work.Thom.chernClass m₂ 1 Z₂)
        + Work.Cohomology.cupH' ℤ ss 8 0 (Work.Thom.chernClass m₁ 4 Z₁)
          (Work.Thom.chernClass m₂ 0 Z₂) := by
  rw [hW Z₁ Z₂ (j := 4), Fin.sum_univ_five]
  rw [Work.Gen.cohTransport_eq_id', Work.Gen.cohTransport_eq_id', Work.Gen.cohTransport_eq_id',
    Work.Gen.cohTransport_eq_id', Work.Gen.cohTransport_eq_id']
  rfl

/-! ## The iterated sums `W2, W3, W4` of `lineC 4` -/

/-- Two copies of `ℂ ⊗ O(1)` over `ℂP⁴`. -/
def W2 : VectorBundleCore ℂ (CP 4) (EuclideanSpace ℂ (Fin 4)) (lineIdx × lineIdx) :=
  Work.Whitney.whitneySum (lineC 4) (lineC 4)

/-- Three copies of `ℂ ⊗ O(1)` over `ℂP⁴`. -/
def W3 : VectorBundleCore ℂ (CP 4) (EuclideanSpace ℂ (Fin 6)) (lineIdx × (lineIdx × lineIdx)) :=
  Work.Whitney.whitneySum (lineC 4) W2

/-- Four copies of `ℂ ⊗ O(1)` over `ℂP⁴`. -/
def W4 : VectorBundleCore ℂ (CP 4) (EuclideanSpace ℂ (Fin 8))
    (lineIdx × (lineIdx × (lineIdx × lineIdx))) :=
  Work.Whitney.whitneySum (lineC 4) W3

/-! ## The Chern classes of `ℂ ⊗ O(1)` -/

theorem lineC4_one (hW : WhitneyFormula) (hS : TautDualSign) :
    Work.Thom.chernClass 2 1 (lineC 4) = 0 := by
  rw [lineC, whitney_one hW (tautDual 4) (tautLine 4)]
  simp only [Work.Thom.chernClass_zero_eq_oneH]
  rw [show Work.Thom.chernClass 1 1 (tautDual 4) = uCoh 4 from rfl,
      show Work.Thom.chernClass 1 1 (tautLine 4) = -uCoh 4 from by rw [hS 4]; rfl]
  rw [Work.Cohomology.cupH'_one_left, Work.Cohomology.cupH'_one_right]
  simp

theorem lineC4_two (hW : WhitneyFormula) (hS : TautDualSign) :
    Work.Thom.chernClass 2 2 (lineC 4) = -uSq 4 := by
  rw [lineC, whitney_two hW (tautDual 4) (tautLine 4)]
  rw [Work.Thom.chernClass_eq_zero_of_lt (tautDual 4) (by norm_num : 1 < 2),
      Work.Thom.chernClass_eq_zero_of_lt (tautLine 4) (by norm_num : 1 < 2)]
  simp only [Work.Thom.chernClass_zero_eq_oneH]
  rw [show Work.Thom.chernClass 1 1 (tautDual 4) = uCoh 4 from rfl,
      show Work.Thom.chernClass 1 1 (tautLine 4) = -uCoh 4 from by rw [hS 4]; rfl]
  rw [Work.Cohomology.cupH'_zero_right, Work.Cohomology.cupH'_zero_left]
  rw [map_neg (f := Work.Cohomology.cupH' ℤ ss 2 2 (uCoh 4))]
  rw [show (Work.Cohomology.cupH' ℤ ss 2 2 (uCoh 4) (uCoh 4)) = uSq 4 from rfl]
  simp

theorem lineC4_three : Work.Thom.chernClass 2 3 (lineC 4) = 0 :=
  Work.Thom.chernClass_eq_zero_of_lt (lineC 4) (by norm_num)

theorem lineC4_four : Work.Thom.chernClass 2 4 (lineC 4) = 0 :=
  Work.Thom.chernClass_eq_zero_of_lt (lineC 4) (by norm_num)


end

end Work.Gen
