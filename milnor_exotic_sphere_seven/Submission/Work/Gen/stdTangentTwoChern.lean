import Mathlib
import Submission.Work.Gen.EulerChernCP4
import Submission.Work.Gen.eulerSequence_iso_two
import Submission.Work.Gen.C1LineTrivial
import Submission.Work.Gen.chernClass_tautLine
import Submission.Work.Thom.trivialChern
import Submission.Work.Whitney.Basic

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
# The Chern classes of the complexified tangent bundle of `ℂP²`

This module computes the four Chern classes of `Work.Gen.stdTangentC 2`, the complexified
tangent bundle of `ℂP²`, realising `c(ℂ ⊗_ℝ TℂP²) = (1 - u²)³` with `u = c₁(O(1))`:

  `c₁ = 0`,  `c₂ = -3u²`,  `c₃ = 0`,  `c₄ = 3u⁴`.

The proof is the `n = 2` instance of the computation of `Submission/Work/Gen/EulerChern.lean`
(which does `n = 4`), along the same three inputs:

* the complexified Euler sequence of `ℂP²`, `ℂ ⊗ TℂP² ⊕ ε² ≅ (ℂ ⊗ O(1))³`
  (`Work.Gen.eulerSequence_iso_two`, proved in `Submission/Work/GenTwo/`), in the shape
  `Work.Gen.stdTwoSrc ≅ Work.Gen.stdTwoTgt`;
* the **Whitney sum formula** `c_j(E ⊕ F) = Σ_{a+b=j} c_a(E) ⌣ c_b(F)`, entering exactly once,
  through the named hypothesis `hW : Work.Gen.WhitneyFormula`;
* the duality sign `c₁(O(-1)) = -c₁(O(1))` (`Work.Gen.tautDualSign`, proved unconditionally by
  `Submission/Work/Gen/chernClass_tautLine.lean`).

Everything in the file except the final theorem is a helper lemma; the only input that is not
discharged here is the Whitney sum formula, which is the reason the theorem is stated with
`hW` as a hypothesis.
-/

namespace Work.Gen

open Work.Projective

noncomputable section

local notation "ss2" => Work.Whitney.ssB (CP 2)

/-! ## The two bundles of the `ℂP²` Euler sequence, and the line bundle `ℂ ⊗ O(1)` -/

/-- The trivial complex rank-`2` bundle over `ℂP²` (the `ε²` of the Euler sequence). -/
abbrev stdTwoTriv : VectorBundleCore ℂ (CP 2) (EuclideanSpace ℂ (Fin 2)) (Fin 1) :=
  trivialVectorBundleCore ℂ (CP 2) (EuclideanSpace ℂ (Fin 2)) (Fin 1)

/-- Two copies of `ℂ ⊗ O(1)` over `ℂP²`. -/
abbrev stdTwoW2 : VectorBundleCore ℂ (CP 2) (EuclideanSpace ℂ (Fin 4))
    ((Fin 3 × Fin 3) × (Fin 3 × Fin 3)) :=
  Work.Whitney.whitneySum (lineC 2) (lineC 2)

/-- The source `ℂ ⊗_ℝ TℂP² ⊕ ε²` of the complexified Euler sequence of `ℂP²`. -/
abbrev stdTwoSrc : VectorBundleCore ℂ (CP 2) (EuclideanSpace ℂ (Fin 6)) (Fin 3 × Fin 1) :=
  Work.Whitney.whitneySum (stdTangentC 2) stdTwoTriv

/-- The target `(ℂ ⊗ O(1))³` of the complexified Euler sequence of `ℂP²`. -/
abbrev stdTwoTgt : VectorBundleCore ℂ (CP 2) (EuclideanSpace ℂ (Fin 6))
    ((Fin 3 × Fin 3) × ((Fin 3 × Fin 3) × (Fin 3 × Fin 3))) :=
  Work.Whitney.whitneySum (lineC 2) stdTwoW2

/-! ## The Whitney sum formula in degrees `1`–`4`, over `ℂP²`

These are verbatim the lemmas `Work.Gen.whitney_one`, `whitney_two`, `whitney_four` of
`Submission/Work/Gen/EulerChernAux.lean` (over `ℂP⁴`), and a new degree-`3` instance, with the base
replaced by `ℂP²`.  Each is a `Fin`-sum collapse of the single hypothesis `Work.Gen.WhitneyFormula`.
-/

/-- `3` as an element of `Fin 4` is `3`. -/
theorem stdTwo_fin4_three : (↑(3 : Fin 4) : ℕ) = 3 := rfl

/-- `4` as an element of `Fin 5` is `4`. -/
theorem stdTwo_fin5_four : (↑(4 : Fin 5) : ℕ) = 4 := rfl

/-- **Whitney formula in degree `1` over `ℂP²`.** -/
theorem stdTwo_whit_one (hW : WhitneyFormula) {m₁ m₂ : ℕ} {ι₁ ι₂ : Type} [Fintype ι₁]
    [Fintype ι₂]
    (Z₁ : VectorBundleCore ℂ (CP 2) (EuclideanSpace ℂ (Fin m₁)) ι₁)
    (Z₂ : VectorBundleCore ℂ (CP 2) (EuclideanSpace ℂ (Fin m₂)) ι₂) :
    Work.Thom.chernClass (m₁ + m₂) 1 (Work.Whitney.whitneySum Z₁ Z₂)
      = Work.Cohomology.cupH' ℤ ss2 0 2 (Work.Thom.chernClass m₁ 0 Z₁)
          (Work.Thom.chernClass m₂ 1 Z₂)
        + Work.Cohomology.cupH' ℤ ss2 2 0 (Work.Thom.chernClass m₁ 1 Z₁)
          (Work.Thom.chernClass m₂ 0 Z₂) := by
  rw [hW Z₁ Z₂ (j := 1), Fin.sum_univ_two]
  simp only [Fin.val_zero, Fin.val_one, Nat.sub_zero, Nat.add_zero, Nat.mul_zero]
  rw [Work.Gen.cohTransport_eq_id', Work.Gen.cohTransport_eq_id']

/-- **Whitney formula in degree `2` over `ℂP²`.** -/
theorem stdTwo_whit_two (hW : WhitneyFormula) {m₁ m₂ : ℕ} {ι₁ ι₂ : Type} [Fintype ι₁]
    [Fintype ι₂]
    (Z₁ : VectorBundleCore ℂ (CP 2) (EuclideanSpace ℂ (Fin m₁)) ι₁)
    (Z₂ : VectorBundleCore ℂ (CP 2) (EuclideanSpace ℂ (Fin m₂)) ι₂) :
    Work.Thom.chernClass (m₁ + m₂) 2 (Work.Whitney.whitneySum Z₁ Z₂)
      = Work.Cohomology.cupH' ℤ ss2 0 4 (Work.Thom.chernClass m₁ 0 Z₁)
          (Work.Thom.chernClass m₂ 2 Z₂)
        + Work.Cohomology.cupH' ℤ ss2 2 2 (Work.Thom.chernClass m₁ 1 Z₁)
          (Work.Thom.chernClass m₂ 1 Z₂)
        + Work.Cohomology.cupH' ℤ ss2 4 0 (Work.Thom.chernClass m₁ 2 Z₁)
          (Work.Thom.chernClass m₂ 0 Z₂) := by
  rw [hW Z₁ Z₂ (j := 2), Fin.sum_univ_three]
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, Nat.sub_zero, Nat.sub_self, Nat.add_zero,
    Nat.mul_zero]
  rw [Work.Gen.cohTransport_eq_id', Work.Gen.cohTransport_eq_id', Work.Gen.cohTransport_eq_id']

/-- **Whitney formula in degree `3` over `ℂP²`.** -/
theorem stdTwo_whit_three (hW : WhitneyFormula) {m₁ m₂ : ℕ} {ι₁ ι₂ : Type} [Fintype ι₁]
    [Fintype ι₂]
    (Z₁ : VectorBundleCore ℂ (CP 2) (EuclideanSpace ℂ (Fin m₁)) ι₁)
    (Z₂ : VectorBundleCore ℂ (CP 2) (EuclideanSpace ℂ (Fin m₂)) ι₂) :
    Work.Thom.chernClass (m₁ + m₂) 3 (Work.Whitney.whitneySum Z₁ Z₂)
      = Work.Cohomology.cupH' ℤ ss2 0 6 (Work.Thom.chernClass m₁ 0 Z₁)
          (Work.Thom.chernClass m₂ 3 Z₂)
        + Work.Cohomology.cupH' ℤ ss2 2 4 (Work.Thom.chernClass m₁ 1 Z₁)
          (Work.Thom.chernClass m₂ 2 Z₂)
        + Work.Cohomology.cupH' ℤ ss2 4 2 (Work.Thom.chernClass m₁ 2 Z₁)
          (Work.Thom.chernClass m₂ 1 Z₂)
        + Work.Cohomology.cupH' ℤ ss2 6 0 (Work.Thom.chernClass m₁ 3 Z₁)
          (Work.Thom.chernClass m₂ 0 Z₂) := by
  rw [hW Z₁ Z₂ (j := 3), Fin.sum_univ_four]
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, stdTwo_fin4_three, Nat.sub_zero, Nat.sub_self,
    Nat.add_zero, Nat.mul_zero]
  rw [Work.Gen.cohTransport_eq_id', Work.Gen.cohTransport_eq_id', Work.Gen.cohTransport_eq_id',
    Work.Gen.cohTransport_eq_id']

/-- **Whitney formula in degree `4` over `ℂP²`.** -/
theorem stdTwo_whit_four (hW : WhitneyFormula) {m₁ m₂ : ℕ} {ι₁ ι₂ : Type} [Fintype ι₁]
    [Fintype ι₂]
    (Z₁ : VectorBundleCore ℂ (CP 2) (EuclideanSpace ℂ (Fin m₁)) ι₁)
    (Z₂ : VectorBundleCore ℂ (CP 2) (EuclideanSpace ℂ (Fin m₂)) ι₂) :
    Work.Thom.chernClass (m₁ + m₂) 4 (Work.Whitney.whitneySum Z₁ Z₂)
      = Work.Cohomology.cupH' ℤ ss2 0 8 (Work.Thom.chernClass m₁ 0 Z₁)
          (Work.Thom.chernClass m₂ 4 Z₂)
        + Work.Cohomology.cupH' ℤ ss2 2 6 (Work.Thom.chernClass m₁ 1 Z₁)
          (Work.Thom.chernClass m₂ 3 Z₂)
        + Work.Cohomology.cupH' ℤ ss2 4 4 (Work.Thom.chernClass m₁ 2 Z₁)
          (Work.Thom.chernClass m₂ 2 Z₂)
        + Work.Cohomology.cupH' ℤ ss2 6 2 (Work.Thom.chernClass m₁ 3 Z₁)
          (Work.Thom.chernClass m₂ 1 Z₂)
        + Work.Cohomology.cupH' ℤ ss2 8 0 (Work.Thom.chernClass m₁ 4 Z₁)
          (Work.Thom.chernClass m₂ 0 Z₂) := by
  rw [hW Z₁ Z₂ (j := 4), Fin.sum_univ_five]
  rw [Work.Gen.cohTransport_eq_id', Work.Gen.cohTransport_eq_id', Work.Gen.cohTransport_eq_id',
    Work.Gen.cohTransport_eq_id', Work.Gen.cohTransport_eq_id']
  rfl

/-! ## The cup product in the middle degree of `ℂP²` -/

/-- The cup product of `-x` with `y` is the negative of `x ⌣ y`. -/
theorem stdTwo_cupH_neg_left (x y : (Work.Cohomology.cochainC ℤ ss2).homology 4) :
    Work.Cohomology.cupH' ℤ ss2 4 4 (-x) y = -(Work.Cohomology.cupH' ℤ ss2 4 4 x y) := by
  rw [map_neg, LinearMap.neg_apply]

/-- The cup product of `x` with `-y` is the negative of `x ⌣ y`. -/
theorem stdTwo_cupH_neg_right (x y : (Work.Cohomology.cochainC ℤ ss2).homology 4) :
    Work.Cohomology.cupH' ℤ ss2 4 4 x (-y) = -(Work.Cohomology.cupH' ℤ ss2 4 4 x y) := by
  rw [map_neg]

/-- `(-u²) ⌣ (-u²) = u⁴`. -/
theorem stdTwo_cupH_uSq_neg_neg :
    Work.Cohomology.cupH' ℤ ss2 4 4 (-(uSq 2)) (-(uSq 2)) = uFourth 2 := by
  rw [stdTwo_cupH_neg_left, stdTwo_cupH_neg_right, neg_neg]
  rfl

/-- `(-u²) ⌣ (-u² + -u²) = u⁴ + u⁴`. -/
theorem stdTwo_cupH_uSq_nn2 :
    Work.Cohomology.cupH' ℤ ss2 4 4 (-(uSq 2)) (-(uSq 2) + -(uSq 2))
      = uFourth 2 + uFourth 2 := by
  rw [map_add, stdTwo_cupH_uSq_neg_neg]

/-! ## The Chern classes of `ℂ ⊗ O(1)` over `ℂP²` -/

/-- `c₁(ℂ ⊗ O(1)) = 0` over `ℂP²`. -/
theorem stdTwo_lineC_one (hW : WhitneyFormula) :
    Work.Thom.chernClass 2 1 (lineC 2) = 0 := by
  have hS : TautDualSign := tautDualSign
  rw [lineC, stdTwo_whit_one hW (tautDual 2) (tautLine 2)]
  simp only [Work.Thom.chernClass_zero_eq_oneH]
  rw [show Work.Thom.chernClass 1 1 (tautDual 2) = uCoh 2 from rfl,
      show Work.Thom.chernClass 1 1 (tautLine 2) = -uCoh 2 from by rw [hS 2]; rfl]
  rw [Work.Cohomology.cupH'_one_left, Work.Cohomology.cupH'_one_right]
  simp

/-- `c₂(ℂ ⊗ O(1)) = -u²` over `ℂP²`. -/
theorem stdTwo_lineC_two (hW : WhitneyFormula) :
    Work.Thom.chernClass 2 2 (lineC 2) = -uSq 2 := by
  have hS : TautDualSign := tautDualSign
  rw [lineC, stdTwo_whit_two hW (tautDual 2) (tautLine 2)]
  rw [Work.Thom.chernClass_eq_zero_of_lt (tautDual 2) (by norm_num : 1 < 2),
      Work.Thom.chernClass_eq_zero_of_lt (tautLine 2) (by norm_num : 1 < 2)]
  simp only [Work.Thom.chernClass_zero_eq_oneH]
  rw [show Work.Thom.chernClass 1 1 (tautDual 2) = uCoh 2 from rfl,
      show Work.Thom.chernClass 1 1 (tautLine 2) = -uCoh 2 from by rw [hS 2]; rfl]
  rw [Work.Cohomology.cupH'_zero_right, Work.Cohomology.cupH'_zero_left]
  rw [map_neg (f := Work.Cohomology.cupH' ℤ ss2 2 2 (uCoh 2))]
  rw [show (Work.Cohomology.cupH' ℤ ss2 2 2 (uCoh 2) (uCoh 2)) = uSq 2 from rfl]
  simp

/-- `c₃(ℂ ⊗ O(1)) = 0` over `ℂP²`, for rank reasons. -/
theorem stdTwo_lineC_three : Work.Thom.chernClass 2 3 (lineC 2) = 0 :=
  Work.Thom.chernClass_eq_zero_of_lt (lineC 2) (by norm_num)

/-- `c₄(ℂ ⊗ O(1)) = 0` over `ℂP²`, for rank reasons. -/
theorem stdTwo_lineC_four : Work.Thom.chernClass 2 4 (lineC 2) = 0 :=
  Work.Thom.chernClass_eq_zero_of_lt (lineC 2) (by norm_num)

/-! ## The Chern classes of `(ℂ ⊗ O(1))²` over `ℂP²` -/

/-- `c₁((ℂ ⊗ O(1))²) = 0`. -/
theorem stdTwo_W2_one (hW : WhitneyFormula) :
    Work.Thom.chernClass 4 1 stdTwoW2 = 0 := by
  change Work.Thom.chernClass 4 1 (Work.Whitney.whitneySum (lineC 2) (lineC 2)) = 0
  rw [stdTwo_whit_one hW (lineC 2) (lineC 2)]
  simp only [Work.Thom.chernClass_zero_eq_oneH, stdTwo_lineC_one hW]
  rw [Work.Cohomology.cupH'_one_left, Work.Cohomology.cupH'_one_right]
  simp

/-- `c₂((ℂ ⊗ O(1))²) = -u² + -u²`. -/
theorem stdTwo_W2_two (hW : WhitneyFormula) :
    Work.Thom.chernClass 4 2 stdTwoW2 = -uSq 2 + -uSq 2 := by
  change Work.Thom.chernClass 4 2 (Work.Whitney.whitneySum (lineC 2) (lineC 2))
    = -uSq 2 + -uSq 2
  rw [stdTwo_whit_two hW (lineC 2) (lineC 2)]
  simp only [Work.Thom.chernClass_zero_eq_oneH, stdTwo_lineC_one hW, stdTwo_lineC_two hW,
    Work.Cohomology.cupH'_zero_left, Work.Cohomology.cupH'_zero_right,
    Work.Cohomology.cupH'_one_left, Work.Cohomology.cupH'_one_right]
  simp

/-- `c₃((ℂ ⊗ O(1))²) = 0`. -/
theorem stdTwo_W2_three (hW : WhitneyFormula) :
    Work.Thom.chernClass 4 3 stdTwoW2 = 0 := by
  change Work.Thom.chernClass 4 3 (Work.Whitney.whitneySum (lineC 2) (lineC 2)) = 0
  rw [stdTwo_whit_three hW (lineC 2) (lineC 2)]
  simp only [Work.Thom.chernClass_zero_eq_oneH, stdTwo_lineC_one hW, stdTwo_lineC_two hW,
    stdTwo_lineC_three, Work.Cohomology.cupH'_zero_left, Work.Cohomology.cupH'_zero_right,
    Work.Cohomology.cupH'_one_left, Work.Cohomology.cupH'_one_right]
  simp

/-- `c₄((ℂ ⊗ O(1))²) = u⁴`. -/
theorem stdTwo_W2_four (hW : WhitneyFormula) :
    Work.Thom.chernClass 4 4 stdTwoW2 = uFourth 2 := by
  change Work.Thom.chernClass 4 4 (Work.Whitney.whitneySum (lineC 2) (lineC 2)) = uFourth 2
  rw [stdTwo_whit_four hW (lineC 2) (lineC 2)]
  simp only [Work.Thom.chernClass_zero_eq_oneH, stdTwo_lineC_one hW, stdTwo_lineC_two hW,
    stdTwo_lineC_three, stdTwo_lineC_four, Work.Cohomology.cupH'_zero_left,
    Work.Cohomology.cupH'_zero_right, Work.Cohomology.cupH'_one_left,
    Work.Cohomology.cupH'_one_right, stdTwo_cupH_uSq_neg_neg]
  simp

/-! ## The Chern classes of the Euler-sequence target `(ℂ ⊗ O(1))³` over `ℂP²`

This is `c(T) = (1 - u²)³ = 1 - 3u² + 3u⁴ - u⁶`, truncated to the degrees that `H^*(ℂP²;ℤ)`
sees in the range `≤ 8`. -/

/-- `c₁((ℂ ⊗ O(1))³) = 0`. -/
theorem stdTwo_Tgt_one (hW : WhitneyFormula) :
    Work.Thom.chernClass 6 1 stdTwoTgt = 0 := by
  change Work.Thom.chernClass 6 1 (Work.Whitney.whitneySum (lineC 2) stdTwoW2) = 0
  rw [stdTwo_whit_one hW (lineC 2) stdTwoW2]
  simp only [Work.Thom.chernClass_zero_eq_oneH, stdTwo_lineC_one hW, stdTwo_W2_one hW,
    Work.Cohomology.cupH'_zero_left, Work.Cohomology.cupH'_zero_right,
    Work.Cohomology.cupH'_one_left, Work.Cohomology.cupH'_one_right]
  simp

/-- `c₂((ℂ ⊗ O(1))³) = -u² + -u² + -u²`. -/
theorem stdTwo_Tgt_two (hW : WhitneyFormula) :
    Work.Thom.chernClass 6 2 stdTwoTgt = -uSq 2 + -uSq 2 + -uSq 2 := by
  change Work.Thom.chernClass 6 2 (Work.Whitney.whitneySum (lineC 2) stdTwoW2)
    = -uSq 2 + -uSq 2 + -uSq 2
  rw [stdTwo_whit_two hW (lineC 2) stdTwoW2]
  simp only [Work.Thom.chernClass_zero_eq_oneH, stdTwo_lineC_one hW, stdTwo_lineC_two hW,
    stdTwo_W2_one hW, stdTwo_W2_two hW, Work.Cohomology.cupH'_zero_left,
    Work.Cohomology.cupH'_zero_right, Work.Cohomology.cupH'_one_left,
    Work.Cohomology.cupH'_one_right]
  simp

/-- `c₃((ℂ ⊗ O(1))³) = 0`. -/
theorem stdTwo_Tgt_three (hW : WhitneyFormula) :
    Work.Thom.chernClass 6 3 stdTwoTgt = 0 := by
  change Work.Thom.chernClass 6 3 (Work.Whitney.whitneySum (lineC 2) stdTwoW2) = 0
  rw [stdTwo_whit_three hW (lineC 2) stdTwoW2]
  simp only [Work.Thom.chernClass_zero_eq_oneH, stdTwo_lineC_one hW, stdTwo_lineC_two hW,
    stdTwo_lineC_three, stdTwo_W2_one hW, stdTwo_W2_two hW, stdTwo_W2_three hW,
    Work.Cohomology.cupH'_zero_left, Work.Cohomology.cupH'_zero_right,
    Work.Cohomology.cupH'_one_left, Work.Cohomology.cupH'_one_right]
  simp

/-- `c₄((ℂ ⊗ O(1))³) = u⁴ + (u⁴ + u⁴)`. -/
theorem stdTwo_Tgt_four (hW : WhitneyFormula) :
    Work.Thom.chernClass 6 4 stdTwoTgt = uFourth 2 + (uFourth 2 + uFourth 2) := by
  change Work.Thom.chernClass 6 4 (Work.Whitney.whitneySum (lineC 2) stdTwoW2)
    = uFourth 2 + (uFourth 2 + uFourth 2)
  rw [stdTwo_whit_four hW (lineC 2) stdTwoW2]
  simp only [Work.Thom.chernClass_zero_eq_oneH, stdTwo_lineC_one hW, stdTwo_lineC_two hW,
    stdTwo_lineC_three, stdTwo_lineC_four, stdTwo_W2_one hW, stdTwo_W2_two hW, stdTwo_W2_three hW,
    stdTwo_W2_four hW, Work.Cohomology.cupH'_zero_left, Work.Cohomology.cupH'_zero_right,
    Work.Cohomology.cupH'_one_left, Work.Cohomology.cupH'_one_right, stdTwo_cupH_uSq_neg_neg,
    stdTwo_cupH_uSq_nn2]
  simp

/-! ## Stability: stripping the trivial rank-`2` summand

`c_j(ℂ ⊗ TℂP² ⊕ ε²) = c_j(ℂ ⊗ TℂP²)` for `j = 1, …, 4`: the Whitney formula applied to
`Z ⊕ ε²`, using that the Chern classes of the trivial bundle vanish above degree `0`. -/

/-- **Stability in degree `1`**: `c₁` is unchanged by adding the trivial rank-`2` bundle. -/
theorem stdTwo_stab_one (hW : WhitneyFormula) :
    Work.Thom.chernClass 4 1 (stdTangentC 2) = Work.Thom.chernClass 6 1 stdTwoSrc := by
  change Work.Thom.chernClass 4 1 (stdTangentC 2)
    = Work.Thom.chernClass 6 1 (Work.Whitney.whitneySum (stdTangentC 2) stdTwoTriv)
  rw [stdTwo_whit_one hW (stdTangentC 2) stdTwoTriv]
  simp only [Work.Thom.chernClass_zero_eq_oneH,
    Work.Thom.chernClass_trivial (B := CP 2) (ι := Fin 1) (m := 2) (j := 1) (by norm_num),
    Work.Cohomology.cupH'_zero_left, Work.Cohomology.cupH'_one_left,
    Work.Cohomology.cupH'_one_right]
  simp

/-- **Stability in degree `2`**: `c₂` is unchanged by adding the trivial rank-`2` bundle. -/
theorem stdTwo_stab_two (hW : WhitneyFormula) :
    Work.Thom.chernClass 4 2 (stdTangentC 2) = Work.Thom.chernClass 6 2 stdTwoSrc := by
  change Work.Thom.chernClass 4 2 (stdTangentC 2)
    = Work.Thom.chernClass 6 2 (Work.Whitney.whitneySum (stdTangentC 2) stdTwoTriv)
  rw [stdTwo_whit_two hW (stdTangentC 2) stdTwoTriv]
  simp only [Work.Thom.chernClass_zero_eq_oneH,
    Work.Thom.chernClass_trivial (B := CP 2) (ι := Fin 1) (m := 2) (j := 1) (by norm_num),
    Work.Thom.chernClass_trivial (B := CP 2) (ι := Fin 1) (m := 2) (j := 2) (by norm_num),
    Work.Cohomology.cupH'_zero_left, Work.Cohomology.cupH'_one_left,
    Work.Cohomology.cupH'_one_right]
  simp

/-- **Stability in degree `3`**: `c₃` is unchanged by adding the trivial rank-`2` bundle. -/
theorem stdTwo_stab_three (hW : WhitneyFormula) :
    Work.Thom.chernClass 4 3 (stdTangentC 2) = Work.Thom.chernClass 6 3 stdTwoSrc := by
  change Work.Thom.chernClass 4 3 (stdTangentC 2)
    = Work.Thom.chernClass 6 3 (Work.Whitney.whitneySum (stdTangentC 2) stdTwoTriv)
  rw [stdTwo_whit_three hW (stdTangentC 2) stdTwoTriv]
  simp only [Work.Thom.chernClass_zero_eq_oneH,
    Work.Thom.chernClass_trivial (B := CP 2) (ι := Fin 1) (m := 2) (j := 1) (by norm_num),
    Work.Thom.chernClass_trivial (B := CP 2) (ι := Fin 1) (m := 2) (j := 2) (by norm_num),
    Work.Thom.chernClass_trivial (B := CP 2) (ι := Fin 1) (m := 2) (j := 3) (by norm_num),
    Work.Cohomology.cupH'_zero_left, Work.Cohomology.cupH'_one_left,
    Work.Cohomology.cupH'_one_right]
  simp

/-- **Stability in degree `4`**: `c₄` is unchanged by adding the trivial rank-`2` bundle. -/
theorem stdTwo_stab_four (hW : WhitneyFormula) :
    Work.Thom.chernClass 4 4 (stdTangentC 2) = Work.Thom.chernClass 6 4 stdTwoSrc := by
  change Work.Thom.chernClass 4 4 (stdTangentC 2)
    = Work.Thom.chernClass 6 4 (Work.Whitney.whitneySum (stdTangentC 2) stdTwoTriv)
  rw [stdTwo_whit_four hW (stdTangentC 2) stdTwoTriv]
  simp only [Work.Thom.chernClass_zero_eq_oneH,
    Work.Thom.chernClass_trivial (B := CP 2) (ι := Fin 1) (m := 2) (j := 1) (by norm_num),
    Work.Thom.chernClass_trivial (B := CP 2) (ι := Fin 1) (m := 2) (j := 2) (by norm_num),
    Work.Thom.chernClass_trivial (B := CP 2) (ι := Fin 1) (m := 2) (j := 3) (by norm_num),
    Work.Thom.chernClass_trivial (B := CP 2) (ι := Fin 1) (m := 2) (j := 4) (by norm_num),
    Work.Cohomology.cupH'_zero_left, Work.Cohomology.cupH'_one_left,
    Work.Cohomology.cupH'_one_right]
  simp

/-! ## Integer multiples as iterated sums -/

/-- `3 • x = x + (x + x)`. -/
theorem stdTwo_three_zsmul {M : Type} [AddCommGroup M] (x : M) :
    (3 : ℤ) • x = x + (x + x) := by
  have h : (3 : ℤ) = 2 + 1 := by norm_num
  rw [h, add_zsmul, one_zsmul, two_zsmul]
  abel

/-- `-(3 • x) = -x + -x + -x`. -/
theorem stdTwo_neg_three_zsmul {M : Type} [AddCommGroup M] (x : M) :
    -((3 : ℤ) • x) = -x + -x + -x := by
  rw [stdTwo_three_zsmul]
  abel

/-! ## The main computation -/

/-- **The Chern classes of the complexified tangent bundle of `ℂP²`**: with `u = c₁(O(1))` the
hyperplane class, `c(ℂ ⊗_ℝ TℂP²) = (1 - u²)³`, i.e.
`c₁ = 0`, `c₂ = -3u²`, `c₃ = 0`, `c₄ = 3u⁴`.

The proof routes through the complexified Euler sequence of `ℂP²`,
`ℂ ⊗ TℂP² ⊕ ε² ≅ (ℂ ⊗ O(1))³` (`Work.Gen.eulerSequence_iso_two`): iso-invariance of the Chern
classes identifies `c_j(T)` with `c_j` of the target whenever the trivial summand has been stripped
(`stdTwo_stab_*`), and the Chern classes of the three-fold sum of `ℂ ⊗ O(1)` are computed from the
Whitney formula (`stdTwo_Tgt_*`). -/
theorem stdTangentTwoChern (hW : Work.Gen.WhitneyFormula) :
    Work.Thom.chernClass 4 1 (Work.Gen.stdTangentC 2) = 0 ∧
    Work.Thom.chernClass 4 2 (Work.Gen.stdTangentC 2) = -((3 : ℤ) • Work.Gen.uSq 2) ∧
    Work.Thom.chernClass 4 3 (Work.Gen.stdTangentC 2) = 0 ∧
    Work.Thom.chernClass 4 4 (Work.Gen.stdTangentC 2) = (3 : ℤ) • Work.Gen.uFourth 2 := by
  obtain ⟨e⟩ := eulerSequence_iso_two
  have hiso : ∀ j, Work.Thom.chernClass 6 j stdTwoSrc = Work.Thom.chernClass 6 j stdTwoTgt :=
    fun j => Work.Thom.chernClass_BundleIso (j := j) stdTwoSrc stdTwoTgt e
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [stdTwo_stab_one hW, hiso 1, stdTwo_Tgt_one hW]
  · rw [stdTwo_stab_two hW, hiso 2, stdTwo_Tgt_two hW, stdTwo_neg_three_zsmul]
  · rw [stdTwo_stab_three hW, hiso 3, stdTwo_Tgt_three hW]
  · rw [stdTwo_stab_four hW, hiso 4, stdTwo_Tgt_four hW, stdTwo_three_zsmul]

end

end Work.Gen
