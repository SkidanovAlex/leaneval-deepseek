import Mathlib
import Submission.Work.Gen.Cp2Cp2TangentClasses
import Submission.Work.Gen.cp2cp2TangentClasses
import Submission.Work.Gen.Cp2Cp2TangentSplits
import Submission.Work.Gen.cp2cp2TangentSplits
import Submission.Work.Gen.WhFormulaCP4Par
import Submission.Work.Whitney.chernProductSum_eq_fin
import Submission.Work.LerayHirsch.WhitneyParacompact

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false

open scoped Manifold ContDiff Topology

namespace Work.Gen

noncomputable section

open Work.Projective

attribute [local instance] cp2cp2ChartedSpaceEuclid
attribute [local instance] cp2cp2IsManifoldEuclid
attribute [local instance] cp2ChartedSpace
attribute [local instance] cp2IsManifold

/- `ℂP²` and `ℂP² × ℂP²` are compact Hausdorff, hence paracompact: the two instances the
paracompact Whitney formula `Work.LerayHirsch.WhitneySumFormulaPar` consumes. -/
local instance instT2SpaceCP2Par : T2Space (CP 2) := Work.Projective.t2Space_CP 2
local instance instCompactSpaceCP2Par : CompactSpace (CP 2) := Work.Projective.compactSpace_CP 2
local instance instT2SpaceCP2CP2Par : T2Space (CP 2 × CP 2) := inferInstance
local instance instCompactSpaceCP2CP2Par : CompactSpace (CP 2 × CP 2) := inferInstance

local notation "ss2" => Work.Whitney.ssB (CP 2)

/-! ## The paracompact Whitney sum formula, restricted to the two bases this file uses

`Work.LerayHirsch.WhitneySumFormulaPar` is the Whitney formula over paracompact Hausdorff bases,
in the `Work.Whitney.chernProductSum` presentation.  The two bases used by
`Work.Gen.cp2cp2TangentClasses` are `ℂP²` (for the Euler-sequence computation of the factor `TℂP²`)
and `ℂP² × ℂP²` (for the product splitting); both are compact Hausdorff, hence paracompact.

`Work.Whitney.chernProductSum_eq_fin` converts the `chernProductSum` presentation into the
`Fin (j+1)` presentation in which the existing proofs are written, exactly as in
`Work.Gen.whFormulaCP4_of_par`. -/

/-- The Whitney sum formula over `ℂP²`, in the `Fin (j+1)` presentation, obtained from its
paracompact form. -/
def WhitneyFormulaCP2Par : Prop :=
  ∀ {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂] {m₁ m₂ j : ℕ}
    (Z₁ : VectorBundleCore ℂ (CP 2) (EuclideanSpace ℂ (Fin m₁)) ι₁)
    (Z₂ : VectorBundleCore ℂ (CP 2) (EuclideanSpace ℂ (Fin m₂)) ι₂),
    Work.Thom.chernClass (m₁ + m₂) j (Work.Whitney.whitneySum Z₁ Z₂)
      = ∑ a : Fin (j + 1),
          Work.Thom.cohTransport (by have h := a.isLt; omega)
            ((Work.Cohomology.cupH' ℤ (Work.Whitney.ssB (CP 2))
              (2 * (a : ℕ)) (2 * (j - (a : ℕ))))
              (Work.Thom.chernClass m₁ (a : ℕ) Z₁)
              (Work.Thom.chernClass m₂ (j - (a : ℕ)) Z₂))

/-- **The paracompact Whitney formula implies the `ℂP²`-restricted one.**  The bridge is
`Work.Whitney.chernProductSum_eq_fin`. -/
theorem whitneyFormulaCP2Par_of
    (h : ∀ m₁ m₂ : ℕ, Work.LerayHirsch.WhitneySumFormulaPar m₁ m₂) : WhitneyFormulaCP2Par := by
  intro ι₁ ι₂ _ _ m₁ m₂ j Z₁ Z₂
  rw [h m₁ m₂ Z₁ Z₂ j]
  exact Work.Whitney.chernProductSum_eq_fin Z₁ Z₂ j

/-- The Whitney sum formula over `ℂP² × ℂP²`, in the `Fin (j+1)` presentation, obtained from its
paracompact form. -/
def WhitneyFormulaCP2CP2Par : Prop :=
  ∀ {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂] {m₁ m₂ j : ℕ}
    (Z₁ : VectorBundleCore ℂ (CP 2 × CP 2) (EuclideanSpace ℂ (Fin m₁)) ι₁)
    (Z₂ : VectorBundleCore ℂ (CP 2 × CP 2) (EuclideanSpace ℂ (Fin m₂)) ι₂),
    Work.Thom.chernClass (m₁ + m₂) j (Work.Whitney.whitneySum Z₁ Z₂)
      = ∑ a : Fin (j + 1),
          Work.Thom.cohTransport (by have h := a.isLt; omega)
            ((Work.Cohomology.cupH' ℤ (Work.Whitney.ssB (CP 2 × CP 2))
              (2 * (a : ℕ)) (2 * (j - (a : ℕ))))
              (Work.Thom.chernClass m₁ (a : ℕ) Z₁)
              (Work.Thom.chernClass m₂ (j - (a : ℕ)) Z₂))

/-- **The paracompact Whitney formula implies the `ℂP² × ℂP²`-restricted one.** -/
theorem whitneyFormulaCP2CP2Par_of
    (h : ∀ m₁ m₂ : ℕ, Work.LerayHirsch.WhitneySumFormulaPar m₁ m₂) :
    WhitneyFormulaCP2CP2Par := by
  intro ι₁ ι₂ _ _ m₁ m₂ j Z₁ Z₂
  rw [h m₁ m₂ Z₁ Z₂ j]
  exact Work.Whitney.chernProductSum_eq_fin Z₁ Z₂ j

/-! ## The Chern classes of `ℂ ⊗_ℝ TℂP²` from the paracompact Whitney formula

This is the module `Submission/Work/Gen/stdTangentTwoChern.lean` with the arbitrary-base
`Work.Gen.WhitneyFormula` replaced by its paracompact counterpart `WhitneyFormulaCP2Par`; every
lemma below is the verbatim proof of its namesake, with `stdTwo` renamed `stdTwoPar` (the two
`abbrev`s `stdTwoParTriv`, `…W2`, `…Src`, `…Tgt` are definitionally the originals). -/

/-! ## The two bundles of the `ℂP²` Euler sequence, and the line bundle `ℂ ⊗ O(1)` -/

/-- The trivial complex rank-`2` bundle over `ℂP²` (the `ε²` of the Euler sequence). -/
abbrev stdTwoParTriv : VectorBundleCore ℂ (CP 2) (EuclideanSpace ℂ (Fin 2)) (Fin 1) :=
  trivialVectorBundleCore ℂ (CP 2) (EuclideanSpace ℂ (Fin 2)) (Fin 1)

/-- Two copies of `ℂ ⊗ O(1)` over `ℂP²`. -/
abbrev stdTwoParW2 : VectorBundleCore ℂ (CP 2) (EuclideanSpace ℂ (Fin 4))
    ((Fin 3 × Fin 3) × (Fin 3 × Fin 3)) :=
  Work.Whitney.whitneySum (lineC 2) (lineC 2)

/-- The source `ℂ ⊗_ℝ TℂP² ⊕ ε²` of the complexified Euler sequence of `ℂP²`. -/
abbrev stdTwoParSrc : VectorBundleCore ℂ (CP 2) (EuclideanSpace ℂ (Fin 6)) (Fin 3 × Fin 1) :=
  Work.Whitney.whitneySum (stdTangentC 2) stdTwoParTriv

/-- The target `(ℂ ⊗ O(1))³` of the complexified Euler sequence of `ℂP²`. -/
abbrev stdTwoParTgt : VectorBundleCore ℂ (CP 2) (EuclideanSpace ℂ (Fin 6))
    ((Fin 3 × Fin 3) × ((Fin 3 × Fin 3) × (Fin 3 × Fin 3))) :=
  Work.Whitney.whitneySum (lineC 2) stdTwoParW2

/-! ## The Whitney sum formula in degrees `1`–`4`, over `ℂP²`

These are verbatim the lemmas `Work.Gen.whitney_one`, `whitney_two`, `whitney_four` of
`Submission/Work/Gen/EulerChernAux.lean` (over `ℂP⁴`), and a new degree-`3` instance, with the base
replaced by `ℂP²`.  Each is a `Fin`-sum collapse of the single hypothesis `Work.Gen.WhitneyFormulaCP2Par`.
-/

/-- `3` as an element of `Fin 4` is `3`. -/
theorem stdTwoPar_fin4_three : (↑(3 : Fin 4) : ℕ) = 3 := rfl

/-- `4` as an element of `Fin 5` is `4`. -/
theorem stdTwoPar_fin5_four : (↑(4 : Fin 5) : ℕ) = 4 := rfl

/-- **Whitney formula in degree `1` over `ℂP²`.** -/
theorem stdTwoPar_whit_one (hW : WhitneyFormulaCP2Par) {m₁ m₂ : ℕ} {ι₁ ι₂ : Type} [Fintype ι₁]
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
theorem stdTwoPar_whit_two (hW : WhitneyFormulaCP2Par) {m₁ m₂ : ℕ} {ι₁ ι₂ : Type} [Fintype ι₁]
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
theorem stdTwoPar_whit_three (hW : WhitneyFormulaCP2Par) {m₁ m₂ : ℕ} {ι₁ ι₂ : Type} [Fintype ι₁]
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
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, stdTwoPar_fin4_three, Nat.sub_zero, Nat.sub_self,
    Nat.add_zero, Nat.mul_zero]
  rw [Work.Gen.cohTransport_eq_id', Work.Gen.cohTransport_eq_id', Work.Gen.cohTransport_eq_id',
    Work.Gen.cohTransport_eq_id']

/-- **Whitney formula in degree `4` over `ℂP²`.** -/
theorem stdTwoPar_whit_four (hW : WhitneyFormulaCP2Par) {m₁ m₂ : ℕ} {ι₁ ι₂ : Type} [Fintype ι₁]
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
theorem stdTwoPar_cupH_neg_left (x y : (Work.Cohomology.cochainC ℤ ss2).homology 4) :
    Work.Cohomology.cupH' ℤ ss2 4 4 (-x) y = -(Work.Cohomology.cupH' ℤ ss2 4 4 x y) := by
  rw [map_neg, LinearMap.neg_apply]

/-- The cup product of `x` with `-y` is the negative of `x ⌣ y`. -/
theorem stdTwoPar_cupH_neg_right (x y : (Work.Cohomology.cochainC ℤ ss2).homology 4) :
    Work.Cohomology.cupH' ℤ ss2 4 4 x (-y) = -(Work.Cohomology.cupH' ℤ ss2 4 4 x y) := by
  rw [map_neg]

/-- `(-u²) ⌣ (-u²) = u⁴`. -/
theorem stdTwoPar_cupH_uSq_neg_neg :
    Work.Cohomology.cupH' ℤ ss2 4 4 (-(uSq 2)) (-(uSq 2)) = uFourth 2 := by
  rw [stdTwoPar_cupH_neg_left, stdTwoPar_cupH_neg_right, neg_neg]
  rfl

/-- `(-u²) ⌣ (-u² + -u²) = u⁴ + u⁴`. -/
theorem stdTwoPar_cupH_uSq_nn2 :
    Work.Cohomology.cupH' ℤ ss2 4 4 (-(uSq 2)) (-(uSq 2) + -(uSq 2))
      = uFourth 2 + uFourth 2 := by
  rw [map_add, stdTwoPar_cupH_uSq_neg_neg]

/-! ## The Chern classes of `ℂ ⊗ O(1)` over `ℂP²` -/

/-- `c₁(ℂ ⊗ O(1)) = 0` over `ℂP²`. -/
theorem stdTwoPar_lineC_one (hW : WhitneyFormulaCP2Par) :
    Work.Thom.chernClass 2 1 (lineC 2) = 0 := by
  have hS : TautDualSign := tautDualSign
  rw [lineC, stdTwoPar_whit_one hW (tautDual 2) (tautLine 2)]
  simp only [Work.Thom.chernClass_zero_eq_oneH]
  rw [show Work.Thom.chernClass 1 1 (tautDual 2) = uCoh 2 from rfl,
      show Work.Thom.chernClass 1 1 (tautLine 2) = -uCoh 2 from by rw [hS 2]; rfl]
  rw [Work.Cohomology.cupH'_one_left, Work.Cohomology.cupH'_one_right]
  simp

/-- `c₂(ℂ ⊗ O(1)) = -u²` over `ℂP²`. -/
theorem stdTwoPar_lineC_two (hW : WhitneyFormulaCP2Par) :
    Work.Thom.chernClass 2 2 (lineC 2) = -uSq 2 := by
  have hS : TautDualSign := tautDualSign
  rw [lineC, stdTwoPar_whit_two hW (tautDual 2) (tautLine 2)]
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
theorem stdTwoPar_lineC_three : Work.Thom.chernClass 2 3 (lineC 2) = 0 :=
  Work.Thom.chernClass_eq_zero_of_lt (lineC 2) (by norm_num)

/-- `c₄(ℂ ⊗ O(1)) = 0` over `ℂP²`, for rank reasons. -/
theorem stdTwoPar_lineC_four : Work.Thom.chernClass 2 4 (lineC 2) = 0 :=
  Work.Thom.chernClass_eq_zero_of_lt (lineC 2) (by norm_num)

/-! ## The Chern classes of `(ℂ ⊗ O(1))²` over `ℂP²` -/

/-- `c₁((ℂ ⊗ O(1))²) = 0`. -/
theorem stdTwoPar_W2_one (hW : WhitneyFormulaCP2Par) :
    Work.Thom.chernClass 4 1 stdTwoParW2 = 0 := by
  change Work.Thom.chernClass 4 1 (Work.Whitney.whitneySum (lineC 2) (lineC 2)) = 0
  rw [stdTwoPar_whit_one hW (lineC 2) (lineC 2)]
  simp only [Work.Thom.chernClass_zero_eq_oneH, stdTwoPar_lineC_one hW]
  rw [Work.Cohomology.cupH'_one_left, Work.Cohomology.cupH'_one_right]
  simp

/-- `c₂((ℂ ⊗ O(1))²) = -u² + -u²`. -/
theorem stdTwoPar_W2_two (hW : WhitneyFormulaCP2Par) :
    Work.Thom.chernClass 4 2 stdTwoParW2 = -uSq 2 + -uSq 2 := by
  change Work.Thom.chernClass 4 2 (Work.Whitney.whitneySum (lineC 2) (lineC 2))
    = -uSq 2 + -uSq 2
  rw [stdTwoPar_whit_two hW (lineC 2) (lineC 2)]
  simp only [Work.Thom.chernClass_zero_eq_oneH, stdTwoPar_lineC_one hW, stdTwoPar_lineC_two hW,
    Work.Cohomology.cupH'_zero_left, Work.Cohomology.cupH'_zero_right,
    Work.Cohomology.cupH'_one_left, Work.Cohomology.cupH'_one_right]
  simp

/-- `c₃((ℂ ⊗ O(1))²) = 0`. -/
theorem stdTwoPar_W2_three (hW : WhitneyFormulaCP2Par) :
    Work.Thom.chernClass 4 3 stdTwoParW2 = 0 := by
  change Work.Thom.chernClass 4 3 (Work.Whitney.whitneySum (lineC 2) (lineC 2)) = 0
  rw [stdTwoPar_whit_three hW (lineC 2) (lineC 2)]
  simp only [Work.Thom.chernClass_zero_eq_oneH, stdTwoPar_lineC_one hW, stdTwoPar_lineC_two hW,
    stdTwoPar_lineC_three, Work.Cohomology.cupH'_zero_left, Work.Cohomology.cupH'_zero_right,
    Work.Cohomology.cupH'_one_left, Work.Cohomology.cupH'_one_right]
  simp

/-- `c₄((ℂ ⊗ O(1))²) = u⁴`. -/
theorem stdTwoPar_W2_four (hW : WhitneyFormulaCP2Par) :
    Work.Thom.chernClass 4 4 stdTwoParW2 = uFourth 2 := by
  change Work.Thom.chernClass 4 4 (Work.Whitney.whitneySum (lineC 2) (lineC 2)) = uFourth 2
  rw [stdTwoPar_whit_four hW (lineC 2) (lineC 2)]
  simp only [Work.Thom.chernClass_zero_eq_oneH, stdTwoPar_lineC_one hW, stdTwoPar_lineC_two hW,
    stdTwoPar_lineC_three, stdTwoPar_lineC_four, Work.Cohomology.cupH'_zero_left,
    Work.Cohomology.cupH'_zero_right, Work.Cohomology.cupH'_one_left,
    Work.Cohomology.cupH'_one_right, stdTwoPar_cupH_uSq_neg_neg]
  simp

/-! ## The Chern classes of the Euler-sequence target `(ℂ ⊗ O(1))³` over `ℂP²`

This is `c(T) = (1 - u²)³ = 1 - 3u² + 3u⁴ - u⁶`, truncated to the degrees that `H^*(ℂP²;ℤ)`
sees in the range `≤ 8`. -/

/-- `c₁((ℂ ⊗ O(1))³) = 0`. -/
theorem stdTwoPar_Tgt_one (hW : WhitneyFormulaCP2Par) :
    Work.Thom.chernClass 6 1 stdTwoParTgt = 0 := by
  change Work.Thom.chernClass 6 1 (Work.Whitney.whitneySum (lineC 2) stdTwoParW2) = 0
  rw [stdTwoPar_whit_one hW (lineC 2) stdTwoParW2]
  simp only [Work.Thom.chernClass_zero_eq_oneH, stdTwoPar_lineC_one hW, stdTwoPar_W2_one hW,
    Work.Cohomology.cupH'_zero_left, Work.Cohomology.cupH'_zero_right,
    Work.Cohomology.cupH'_one_left, Work.Cohomology.cupH'_one_right]
  simp

/-- `c₂((ℂ ⊗ O(1))³) = -u² + -u² + -u²`. -/
theorem stdTwoPar_Tgt_two (hW : WhitneyFormulaCP2Par) :
    Work.Thom.chernClass 6 2 stdTwoParTgt = -uSq 2 + -uSq 2 + -uSq 2 := by
  change Work.Thom.chernClass 6 2 (Work.Whitney.whitneySum (lineC 2) stdTwoParW2)
    = -uSq 2 + -uSq 2 + -uSq 2
  rw [stdTwoPar_whit_two hW (lineC 2) stdTwoParW2]
  simp only [Work.Thom.chernClass_zero_eq_oneH, stdTwoPar_lineC_one hW, stdTwoPar_lineC_two hW,
    stdTwoPar_W2_one hW, stdTwoPar_W2_two hW, Work.Cohomology.cupH'_zero_left,
    Work.Cohomology.cupH'_zero_right, Work.Cohomology.cupH'_one_left,
    Work.Cohomology.cupH'_one_right]
  simp

/-- `c₃((ℂ ⊗ O(1))³) = 0`. -/
theorem stdTwoPar_Tgt_three (hW : WhitneyFormulaCP2Par) :
    Work.Thom.chernClass 6 3 stdTwoParTgt = 0 := by
  change Work.Thom.chernClass 6 3 (Work.Whitney.whitneySum (lineC 2) stdTwoParW2) = 0
  rw [stdTwoPar_whit_three hW (lineC 2) stdTwoParW2]
  simp only [Work.Thom.chernClass_zero_eq_oneH, stdTwoPar_lineC_one hW, stdTwoPar_lineC_two hW,
    stdTwoPar_lineC_three, stdTwoPar_W2_one hW, stdTwoPar_W2_two hW, stdTwoPar_W2_three hW,
    Work.Cohomology.cupH'_zero_left, Work.Cohomology.cupH'_zero_right,
    Work.Cohomology.cupH'_one_left, Work.Cohomology.cupH'_one_right]
  simp

/-- `c₄((ℂ ⊗ O(1))³) = u⁴ + (u⁴ + u⁴)`. -/
theorem stdTwoPar_Tgt_four (hW : WhitneyFormulaCP2Par) :
    Work.Thom.chernClass 6 4 stdTwoParTgt = uFourth 2 + (uFourth 2 + uFourth 2) := by
  change Work.Thom.chernClass 6 4 (Work.Whitney.whitneySum (lineC 2) stdTwoParW2)
    = uFourth 2 + (uFourth 2 + uFourth 2)
  rw [stdTwoPar_whit_four hW (lineC 2) stdTwoParW2]
  simp only [Work.Thom.chernClass_zero_eq_oneH, stdTwoPar_lineC_one hW, stdTwoPar_lineC_two hW,
    stdTwoPar_lineC_three, stdTwoPar_lineC_four, stdTwoPar_W2_one hW, stdTwoPar_W2_two hW, stdTwoPar_W2_three hW,
    stdTwoPar_W2_four hW, Work.Cohomology.cupH'_zero_left, Work.Cohomology.cupH'_zero_right,
    Work.Cohomology.cupH'_one_left, Work.Cohomology.cupH'_one_right, stdTwoPar_cupH_uSq_neg_neg,
    stdTwoPar_cupH_uSq_nn2]
  simp

/-! ## Stability: stripping the trivial rank-`2` summand

`c_j(ℂ ⊗ TℂP² ⊕ ε²) = c_j(ℂ ⊗ TℂP²)` for `j = 1, …, 4`: the Whitney formula applied to
`Z ⊕ ε²`, using that the Chern classes of the trivial bundle vanish above degree `0`. -/

/-- **Stability in degree `1`**: `c₁` is unchanged by adding the trivial rank-`2` bundle. -/
theorem stdTwoPar_stab_one (hW : WhitneyFormulaCP2Par) :
    Work.Thom.chernClass 4 1 (stdTangentC 2) = Work.Thom.chernClass 6 1 stdTwoParSrc := by
  change Work.Thom.chernClass 4 1 (stdTangentC 2)
    = Work.Thom.chernClass 6 1 (Work.Whitney.whitneySum (stdTangentC 2) stdTwoParTriv)
  rw [stdTwoPar_whit_one hW (stdTangentC 2) stdTwoParTriv]
  simp only [Work.Thom.chernClass_zero_eq_oneH,
    Work.Thom.chernClass_trivial (B := CP 2) (ι := Fin 1) (m := 2) (j := 1) (by norm_num),
    Work.Cohomology.cupH'_zero_left, Work.Cohomology.cupH'_one_left,
    Work.Cohomology.cupH'_one_right]
  simp

/-- **Stability in degree `2`**: `c₂` is unchanged by adding the trivial rank-`2` bundle. -/
theorem stdTwoPar_stab_two (hW : WhitneyFormulaCP2Par) :
    Work.Thom.chernClass 4 2 (stdTangentC 2) = Work.Thom.chernClass 6 2 stdTwoParSrc := by
  change Work.Thom.chernClass 4 2 (stdTangentC 2)
    = Work.Thom.chernClass 6 2 (Work.Whitney.whitneySum (stdTangentC 2) stdTwoParTriv)
  rw [stdTwoPar_whit_two hW (stdTangentC 2) stdTwoParTriv]
  simp only [Work.Thom.chernClass_zero_eq_oneH,
    Work.Thom.chernClass_trivial (B := CP 2) (ι := Fin 1) (m := 2) (j := 1) (by norm_num),
    Work.Thom.chernClass_trivial (B := CP 2) (ι := Fin 1) (m := 2) (j := 2) (by norm_num),
    Work.Cohomology.cupH'_zero_left, Work.Cohomology.cupH'_one_left,
    Work.Cohomology.cupH'_one_right]
  simp

/-- **Stability in degree `3`**: `c₃` is unchanged by adding the trivial rank-`2` bundle. -/
theorem stdTwoPar_stab_three (hW : WhitneyFormulaCP2Par) :
    Work.Thom.chernClass 4 3 (stdTangentC 2) = Work.Thom.chernClass 6 3 stdTwoParSrc := by
  change Work.Thom.chernClass 4 3 (stdTangentC 2)
    = Work.Thom.chernClass 6 3 (Work.Whitney.whitneySum (stdTangentC 2) stdTwoParTriv)
  rw [stdTwoPar_whit_three hW (stdTangentC 2) stdTwoParTriv]
  simp only [Work.Thom.chernClass_zero_eq_oneH,
    Work.Thom.chernClass_trivial (B := CP 2) (ι := Fin 1) (m := 2) (j := 1) (by norm_num),
    Work.Thom.chernClass_trivial (B := CP 2) (ι := Fin 1) (m := 2) (j := 2) (by norm_num),
    Work.Thom.chernClass_trivial (B := CP 2) (ι := Fin 1) (m := 2) (j := 3) (by norm_num),
    Work.Cohomology.cupH'_zero_left, Work.Cohomology.cupH'_one_left,
    Work.Cohomology.cupH'_one_right]
  simp

/-- **Stability in degree `4`**: `c₄` is unchanged by adding the trivial rank-`2` bundle. -/
theorem stdTwoPar_stab_four (hW : WhitneyFormulaCP2Par) :
    Work.Thom.chernClass 4 4 (stdTangentC 2) = Work.Thom.chernClass 6 4 stdTwoParSrc := by
  change Work.Thom.chernClass 4 4 (stdTangentC 2)
    = Work.Thom.chernClass 6 4 (Work.Whitney.whitneySum (stdTangentC 2) stdTwoParTriv)
  rw [stdTwoPar_whit_four hW (stdTangentC 2) stdTwoParTriv]
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
theorem stdTwoPar_three_zsmul {M : Type} [AddCommGroup M] (x : M) :
    (3 : ℤ) • x = x + (x + x) := by
  have h : (3 : ℤ) = 2 + 1 := by norm_num
  rw [h, add_zsmul, one_zsmul, two_zsmul]
  abel

/-- `-(3 • x) = -x + -x + -x`. -/
theorem stdTwoPar_neg_three_zsmul {M : Type} [AddCommGroup M] (x : M) :
    -((3 : ℤ) • x) = -x + -x + -x := by
  rw [stdTwoPar_three_zsmul]
  abel

/-! ## The main computation -/

/-- **The Chern classes of the complexified tangent bundle of `ℂP²`**: with `u = c₁(O(1))` the
hyperplane class, `c(ℂ ⊗_ℝ TℂP²) = (1 - u²)³`, i.e.
`c₁ = 0`, `c₂ = -3u²`, `c₃ = 0`, `c₄ = 3u⁴`.

The proof routes through the complexified Euler sequence of `ℂP²`,
`ℂ ⊗ TℂP² ⊕ ε² ≅ (ℂ ⊗ O(1))³` (`Work.Gen.eulerSequence_iso_two`): iso-invariance of the Chern
classes identifies `c_j(T)` with `c_j` of the target whenever the trivial summand has been stripped
(`stdTwoPar_stab_*`), and the Chern classes of the three-fold sum of `ℂ ⊗ O(1)` are computed from the
Whitney formula (`stdTwoPar_Tgt_*`). -/
theorem stdTangentTwoChernPar (hW : Work.Gen.WhitneyFormulaCP2Par) :
    Work.Thom.chernClass 4 1 (Work.Gen.stdTangentC 2) = 0 ∧
    Work.Thom.chernClass 4 2 (Work.Gen.stdTangentC 2) = -((3 : ℤ) • Work.Gen.uSq 2) ∧
    Work.Thom.chernClass 4 3 (Work.Gen.stdTangentC 2) = 0 ∧
    Work.Thom.chernClass 4 4 (Work.Gen.stdTangentC 2) = (3 : ℤ) • Work.Gen.uFourth 2 := by
  obtain ⟨e⟩ := eulerSequence_iso_two
  have hiso : ∀ j, Work.Thom.chernClass 6 j stdTwoParSrc = Work.Thom.chernClass 6 j stdTwoParTgt :=
    fun j => Work.Thom.chernClass_BundleIso (j := j) stdTwoParSrc stdTwoParTgt e
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [stdTwoPar_stab_one hW, hiso 1, stdTwoPar_Tgt_one hW]
  · rw [stdTwoPar_stab_two hW, hiso 2, stdTwoPar_Tgt_two hW, stdTwoPar_neg_three_zsmul]
  · rw [stdTwoPar_stab_three hW, hiso 3, stdTwoPar_Tgt_three hW]
  · rw [stdTwoPar_stab_four hW, hiso 4, stdTwoPar_Tgt_four hW, stdTwoPar_three_zsmul]

/-! ## The Whitney formula in degrees `2` and `4` over `ℂP² × ℂP²` -/

/-- **The Whitney formula in degree `2`** over `ℂP² × ℂP²`, from its paracompact form. -/
theorem whitney_two_par (hW : WhitneyFormulaCP2CP2Par) {m₁ m₂ : ℕ} {ι₁ ι₂ : Type}
    [Fintype ι₁] [Fintype ι₂]
    (Z₁ : VectorBundleCore ℂ (CP 2 × CP 2) (EuclideanSpace ℂ (Fin m₁)) ι₁)
    (Z₂ : VectorBundleCore ℂ (CP 2 × CP 2) (EuclideanSpace ℂ (Fin m₂)) ι₂) :
    Work.Thom.chernClass (m₁ + m₂) 2 (Work.Whitney.whitneySum Z₁ Z₂)
      = Work.Cohomology.cupH' ℤ (Work.Whitney.ssB (CP 2 × CP 2)) 0 4
          (Work.Thom.chernClass m₁ 0 Z₁) (Work.Thom.chernClass m₂ 2 Z₂)
        + Work.Cohomology.cupH' ℤ (Work.Whitney.ssB (CP 2 × CP 2)) 2 2
          (Work.Thom.chernClass m₁ 1 Z₁) (Work.Thom.chernClass m₂ 1 Z₂)
        + Work.Cohomology.cupH' ℤ (Work.Whitney.ssB (CP 2 × CP 2)) 4 0
          (Work.Thom.chernClass m₁ 2 Z₁) (Work.Thom.chernClass m₂ 0 Z₂) := by
  rw [hW Z₁ Z₂ (j := 2), Fin.sum_univ_three]
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, Nat.sub_zero, Nat.sub_self, Nat.add_zero,
    Nat.mul_zero]
  rw [Work.Gen.cohTransport_eq_id', Work.Gen.cohTransport_eq_id', Work.Gen.cohTransport_eq_id']

/-- **The Whitney formula in degree `4`** over `ℂP² × ℂP²`, from its paracompact form. -/
theorem whitney_four_par (hW : WhitneyFormulaCP2CP2Par) {m₁ m₂ : ℕ} {ι₁ ι₂ : Type}
    [Fintype ι₁] [Fintype ι₂]
    (Z₁ : VectorBundleCore ℂ (CP 2 × CP 2) (EuclideanSpace ℂ (Fin m₁)) ι₁)
    (Z₂ : VectorBundleCore ℂ (CP 2 × CP 2) (EuclideanSpace ℂ (Fin m₂)) ι₂) :
    Work.Thom.chernClass (m₁ + m₂) 4 (Work.Whitney.whitneySum Z₁ Z₂)
      = Work.Cohomology.cupH' ℤ (Work.Whitney.ssB (CP 2 × CP 2)) 0 8
          (Work.Thom.chernClass m₁ 0 Z₁) (Work.Thom.chernClass m₂ 4 Z₂)
        + Work.Cohomology.cupH' ℤ (Work.Whitney.ssB (CP 2 × CP 2)) 2 6
          (Work.Thom.chernClass m₁ 1 Z₁) (Work.Thom.chernClass m₂ 3 Z₂)
        + Work.Cohomology.cupH' ℤ (Work.Whitney.ssB (CP 2 × CP 2)) 4 4
          (Work.Thom.chernClass m₁ 2 Z₁) (Work.Thom.chernClass m₂ 2 Z₂)
        + Work.Cohomology.cupH' ℤ (Work.Whitney.ssB (CP 2 × CP 2)) 6 2
          (Work.Thom.chernClass m₁ 3 Z₁) (Work.Thom.chernClass m₂ 1 Z₂)
        + Work.Cohomology.cupH' ℤ (Work.Whitney.ssB (CP 2 × CP 2)) 8 0
          (Work.Thom.chernClass m₁ 4 Z₁) (Work.Thom.chernClass m₂ 0 Z₂) := by
  rw [hW Z₁ Z₂ (j := 4), Fin.sum_univ_five]
  rw [Work.Gen.cohTransport_eq_id', Work.Gen.cohTransport_eq_id', Work.Gen.cohTransport_eq_id',
    Work.Gen.cohTransport_eq_id', Work.Gen.cohTransport_eq_id']
  rfl

/-! ## The main theorem -/

/-- **The `ℂP² × ℂP²`-restricted form of `Work.Gen.cp2cp2TangentClasses`, in the base class where
the Whitney formula is actually available.**

`Work.Gen.Cp2Cp2TangentClasses` (`Submission/Work/Gen/Cp2Cp2TangentClasses.lean`) is the statement
that the *defined* tangent classes of `ℂP² × ℂP²` (over the explicit `ℝ⁸`-atlas of
`Work.Gen.cp2cp2ChartedSpaceEuclid`, i.e. `Work.Thom.p1Tangent'`/`p2Tangent'`) are the classical
ones, `3(π₁^*u² + π₂^*u²)` and `9(π₁^*u² ⌣ π₂^*u²)`.  `Work.Gen.cp2cp2TangentClasses` proves it from
`Work.Gen.WhitneyFormula` — the *arbitrary-base* Whitney sum formula — together with the product
splitting `Work.Gen.Cp2Cp2TangentSplits`.

Here the base is `ℂP² × ℂP²`, compact Hausdorff, hence paracompact; and every base at which the
existing proof consumes the formula is `CP 2` or `CP 2 × CP 2`, also compact Hausdorff.  So the
*paracompact* form `Work.LerayHirsch.WhitneySumFormulaPar` suffices — and that is the form the
`Submission/Work/LerayHirsch/` machinery delivers (the arbitrary-base form is not reachable by the
splitting/flag-bundle route).  This is gap `3` of `Work.Gen.generators8` in the form in which the
surrounding development can supply it.

RECIPE (verified by the reviewers).  The existing proof uses `hW` only through `stdTangentTwoChern`
(bundles over `CP 2`) and `whitney_two_gen`/`whitney_four_gen` (bundles over `CP 2 × CP 2`); those
must be re-derived from `h m₁ m₂` at the corresponding compact bases, the bridge from the
`Work.Whitney.chernProductSum` form to the `Fin (j+1)` shape being exactly
`Work.Whitney.chernProductSum_eq_fin`, as in `Work.Gen.whFormulaCP4_of_par`
(`Submission/Work/Gen/WhFormulaCP4Par.lean`).  The `ParacompactSpace` instances come from
`CompactSpace` (`paracompact_of_compact`) and `T2Space` from the project's `t2Space_CP`. -/
theorem cp2cp2TangentClassesPar
    (h : ∀ m₁ m₂ : ℕ, Work.LerayHirsch.WhitneySumFormulaPar m₁ m₂)
    (hSplits : Work.Gen.Cp2Cp2TangentSplits) :
    Work.Gen.Cp2Cp2TangentClasses := by
  have hWF2 : WhitneyFormulaCP2Par := whitneyFormulaCP2Par_of h
  have hWF22 : WhitneyFormulaCP2CP2Par := whitneyFormulaCP2CP2Par_of h
  -- The isomorphism `cppLeftFin ≅ cppZ1 ⊕ cppZ2` in the finite presentations.
  have hiso : Nonempty (Work.Thom.BundleIso cppLeftFin (Work.Whitney.whitneySum cppZ1 cppZ2)) := by
    obtain ⟨e1⟩ := Work.Agree.nonempty_bundleIso_reindexCore_self cp2cp2TangentC cppCover8
      cppCover8Covers
    obtain ⟨e2⟩ := hSplits
    obtain ⟨ea⟩ := Work.Agree.nonempty_bundleIso_reindexCore_self (factorTangentC projFirst)
      (stdChart 2) (fun x => stdChart_covers 2 (projFirst x))
    obtain ⟨eb⟩ := Work.Agree.nonempty_bundleIso_reindexCore_self (factorTangentC projSecond)
      (stdChart 2) (fun x => stdChart_covers 2 (projSecond x))
    obtain ⟨e3⟩ := Work.Agree.nonempty_bundleIso_sumCore_congr (𝕜 := ℂ)
      (Work.Whitney.sumFibreC 4 4) (Work.Whitney.sumFibreC 4 4)
      (factorTangentC projFirst) cppZ1 (factorTangentC projSecond) cppZ2 ea.symm eb.symm
    exact ⟨e1.trans (e2.trans e3)⟩
  -- Presentation independence: the canonical finite-cover presentation has the Chern classes of
  -- `cppLeftFin`.
  have hpres (j : ℕ) : Work.Thom.chernClass
        (Module.finrank ℝ (EuclideanSpace ℝ (Fin 8))) j
        (Work.Thom.complexifiedTangentBundleFinite 𝓘(ℝ, EuclideanSpace ℝ (Fin 8)) (CP 2 × CP 2))
      = Work.Thom.chernClass 8 j cppLeftFin := by
    have h1 : (((Work.TangentClasses.tangentBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin 8))
          (CP 2 × CP 2)).mapFibre (Work.Thom.modelLinearEquiv (E := EuclideanSpace ℝ (Fin 8)))).reindex
            cppCover8 cppCover8Covers)
        = (((Work.TangentClasses.tangentBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin 8))
          (CP 2 × CP 2)).reindex cppCover8 cppCover8Covers).mapFibre
            (Work.Thom.modelLinearEquiv (E := EuclideanSpace ℝ (Fin 8)))) := rfl
    unfold Work.Thom.complexifiedTangentBundleFinite
    rw [h1]
    rw [Work.Gen.chernClass_complexificationCore_mapFibre (k := 8)
      (l := Module.finrank ℝ (EuclideanSpace ℝ (Fin 8))) finrank_euclideanSpace_fin
      ((Work.TangentClasses.tangentBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin 8))
        (CP 2 × CP 2)).reindex cppCover8 cppCover8Covers)
      (Work.Thom.modelLinearEquiv (E := EuclideanSpace ℝ (Fin 8))) j]
    rfl
  -- The Chern classes of the two factors, transported along the two projections.
  have hZ1c1 : Work.Thom.chernClass 4 1 cppZ1
      = (Work.Thom.CohMap projFirst ℤ 2).hom (Work.Thom.chernClass 4 1 (stdTangentC 2)) := by
    rw [cppZ1_eq]
    exact Work.Thom.chernClass_comap (m := 4) (j := 1) (stdTangentC 2) projFirst
  have hZ2c1 : Work.Thom.chernClass 4 1 cppZ2
      = (Work.Thom.CohMap projSecond ℤ 2).hom (Work.Thom.chernClass 4 1 (stdTangentC 2)) := by
    rw [cppZ2_eq]
    exact Work.Thom.chernClass_comap (m := 4) (j := 1) (stdTangentC 2) projSecond
  have hZ1c2 : Work.Thom.chernClass 4 2 cppZ1
      = (Work.Thom.CohMap projFirst ℤ 4).hom (Work.Thom.chernClass 4 2 (stdTangentC 2)) := by
    rw [cppZ1_eq]
    exact Work.Thom.chernClass_comap (m := 4) (j := 2) (stdTangentC 2) projFirst
  have hZ2c2 : Work.Thom.chernClass 4 2 cppZ2
      = (Work.Thom.CohMap projSecond ℤ 4).hom (Work.Thom.chernClass 4 2 (stdTangentC 2)) := by
    rw [cppZ2_eq]
    exact Work.Thom.chernClass_comap (m := 4) (j := 2) (stdTangentC 2) projSecond
  have hZ1c3 : Work.Thom.chernClass 4 3 cppZ1
      = (Work.Thom.CohMap projFirst ℤ (2 * 3)).hom
          (Work.Thom.chernClass 4 3 (stdTangentC 2)) := by
    rw [cppZ1_eq]
    exact Work.Thom.chernClass_comap (m := 4) (j := 3) (stdTangentC 2) projFirst
  have hZ2c3 : Work.Thom.chernClass 4 3 cppZ2
      = (Work.Thom.CohMap projSecond ℤ (2 * 3)).hom
          (Work.Thom.chernClass 4 3 (stdTangentC 2)) := by
    rw [cppZ2_eq]
    exact Work.Thom.chernClass_comap (m := 4) (j := 3) (stdTangentC 2) projSecond
  have hZ1c4 : Work.Thom.chernClass 4 4 cppZ1
      = (Work.Thom.CohMap projFirst ℤ (2 * 4)).hom
          (Work.Thom.chernClass 4 4 (stdTangentC 2)) := by
    rw [cppZ1_eq]
    exact Work.Thom.chernClass_comap (m := 4) (j := 4) (stdTangentC 2) projFirst
  have hZ2c4 : Work.Thom.chernClass 4 4 cppZ2
      = (Work.Thom.CohMap projSecond ℤ (2 * 4)).hom
          (Work.Thom.chernClass 4 4 (stdTangentC 2)) := by
    rw [cppZ2_eq]
    exact Work.Thom.chernClass_comap (m := 4) (j := 4) (stdTangentC 2) projSecond
  obtain ⟨hs1, hs2, hs3, hs4⟩ := stdTangentTwoChernPar hWF2
  -- The four Chern classes of the factors, in additive form (no integer multiples inside `⌣`).
  have hZ1_1 : Work.Thom.chernClass 4 1 cppZ1 = 0 := by rw [hZ1c1, hs1, map_zero]
  have hZ2_1 : Work.Thom.chernClass 4 1 cppZ2 = 0 := by rw [hZ2c1, hs1, map_zero]
  have hZ1_2 : Work.Thom.chernClass 4 2 cppZ1
      = -(((Work.Thom.CohMap projFirst ℤ 4).hom (uSq 2)
          + (Work.Thom.CohMap projFirst ℤ 4).hom (uSq 2))
          + (Work.Thom.CohMap projFirst ℤ 4).hom (uSq 2)) := by
    rw [hZ1c2, hs2]
    rw [map_neg (f := (Work.Thom.CohMap projFirst ℤ 4).hom)]
    rw [show (3 : ℤ) • (uSq 2) = ((uSq 2 + uSq 2) + uSq 2) from three_zsmul_eq (uSq 2)]
    rw [map_add (f := (Work.Thom.CohMap projFirst ℤ 4).hom)]
    rw [map_add (f := (Work.Thom.CohMap projFirst ℤ 4).hom)]
  have hZ2_2 : Work.Thom.chernClass 4 2 cppZ2
      = -(((Work.Thom.CohMap projSecond ℤ 4).hom (uSq 2)
          + (Work.Thom.CohMap projSecond ℤ 4).hom (uSq 2))
          + (Work.Thom.CohMap projSecond ℤ 4).hom (uSq 2)) := by
    rw [hZ2c2, hs2]
    rw [map_neg (f := (Work.Thom.CohMap projSecond ℤ 4).hom)]
    rw [show (3 : ℤ) • (uSq 2) = ((uSq 2 + uSq 2) + uSq 2) from three_zsmul_eq (uSq 2)]
    rw [map_add (f := (Work.Thom.CohMap projSecond ℤ 4).hom)]
    rw [map_add (f := (Work.Thom.CohMap projSecond ℤ 4).hom)]
  have hZ1_3 : Work.Thom.chernClass 4 3 cppZ1 = 0 := by rw [hZ1c3, hs3, map_zero]
  have hZ2_3 : Work.Thom.chernClass 4 3 cppZ2 = 0 := by rw [hZ2c3, hs3, map_zero]
  have hfour : Work.Thom.chernClass 4 4 (stdTangentC 2) = 0 := by
    rw [hs4]
    rw [show (3 : ℤ) • (Work.Gen.uFourth 2)
        = (Work.Gen.uFourth 2 + Work.Gen.uFourth 2) + Work.Gen.uFourth 2 from
      three_zsmul_eq (Work.Gen.uFourth 2)]
    rw [uFourthTwoZero, add_zero, add_zero]
  have hZ1_4 : Work.Thom.chernClass 4 4 cppZ1 = 0 := by rw [hZ1c4, hfour, map_zero]
  have hZ2_4 : Work.Thom.chernClass 4 4 cppZ2 = 0 := by rw [hZ2c4, hfour, map_zero]
  -- the same, with the total space of the finite cover's cohomology made explicit (the form in
  -- which `Work.Cohomology.cupH'` consumes its arguments)
  have hZ1_1u : (Work.Thom.chernClass 4 1 cppZ1 : (Work.Cohomology.SSetCochainComplex (R := ℤ)
      (Work.Whitney.ssB (CP 2 × CP 2))).homology (2 * 1)) = 0 := hZ1_1
  have hZ2_1u : (Work.Thom.chernClass 4 1 cppZ2 : (Work.Cohomology.SSetCochainComplex (R := ℤ)
      (Work.Whitney.ssB (CP 2 × CP 2))).homology (2 * 1)) = 0 := hZ2_1
  have hZ1_3u : (Work.Thom.chernClass 4 3 cppZ1 : (Work.Cohomology.SSetCochainComplex (R := ℤ)
      (Work.Whitney.ssB (CP 2 × CP 2))).homology (2 * 3)) = 0 := hZ1_3
  have hZ2_3u : (Work.Thom.chernClass 4 3 cppZ2 : (Work.Cohomology.SSetCochainComplex (R := ℤ)
      (Work.Whitney.ssB (CP 2 × CP 2))).homology (2 * 3)) = 0 := hZ2_3
  have hZ1_4u : (Work.Thom.chernClass 4 4 cppZ1 : (Work.Cohomology.SSetCochainComplex (R := ℤ)
      (Work.Whitney.ssB (CP 2 × CP 2))).homology (2 * 4)) = 0 := hZ1_4
  have hZ2_4u : (Work.Thom.chernClass 4 4 cppZ2 : (Work.Cohomology.SSetCochainComplex (R := ℤ)
      (Work.Whitney.ssB (CP 2 × CP 2))).homology (2 * 4)) = 0 := hZ2_4
  have hZ1_0 : Work.Thom.chernClass 4 0 cppZ1
      = Work.Cohomology.oneH ℤ (Work.Whitney.ssB (CP 2 × CP 2)) :=
    Work.Thom.chernClass_zero_eq_oneH cppZ1
  have hZ2_0 : Work.Thom.chernClass 4 0 cppZ2
      = Work.Cohomology.oneH ℤ (Work.Whitney.ssB (CP 2 × CP 2)) :=
    Work.Thom.chernClass_zero_eq_oneH cppZ2
  have hchern : ∀ j, Work.Thom.chernClass 8 j cppLeftFin
      = Work.Thom.chernClass 8 j (Work.Whitney.whitneySum cppZ1 cppZ2) :=
    fun j => Work.Thom.chernClass_BundleIso (j := j) cppLeftFin
      (Work.Whitney.whitneySum cppZ1 cppZ2) hiso.some
  unfold Work.Gen.Cp2Cp2TangentClasses
  refine ⟨?_, ?_⟩
  · show - Work.Thom.chernClass (Module.finrank ℝ (EuclideanSpace ℝ (Fin 8))) 2
        (Work.Thom.complexifiedTangentBundleFinite 𝓘(ℝ, EuclideanSpace ℝ (Fin 8))
          (CP 2 × CP 2))
      = (3 : ℤ) • ((Work.Thom.CohMap projFirst ℤ 4).hom (uSq 2)
          + (Work.Thom.CohMap projSecond ℤ 4).hom (uSq 2))
    rw [hpres 2, hchern 2, whitney_two_par hWF22 cppZ1 cppZ2, hZ1_0, hZ2_0, hZ1_1, hZ2_1,
      hZ1_2, hZ2_2]
    rw [Work.Cohomology.cupH'_zero_left]
    rw [cupH_one_left4]
    rw [cupH_one_right4]
    rw [show (3 : ℤ) • ((Work.Thom.CohMap projFirst ℤ 4).hom (uSq 2)
          + (Work.Thom.CohMap projSecond ℤ 4).hom (uSq 2))
        = (((Work.Thom.CohMap projFirst ℤ 4).hom (uSq 2)
            + (Work.Thom.CohMap projSecond ℤ 4).hom (uSq 2))
          + ((Work.Thom.CohMap projFirst ℤ 4).hom (uSq 2)
            + (Work.Thom.CohMap projSecond ℤ 4).hom (uSq 2)))
          + ((Work.Thom.CohMap projFirst ℤ 4).hom (uSq 2)
            + (Work.Thom.CohMap projSecond ℤ 4).hom (uSq 2)) from
      three_zsmul_eq ((Work.Thom.CohMap projFirst ℤ 4).hom (uSq 2)
          + (Work.Thom.CohMap projSecond ℤ 4).hom (uSq 2))]
    abel
  · show Work.Thom.chernClass (Module.finrank ℝ (EuclideanSpace ℝ (Fin 8))) 4
        (Work.Thom.complexifiedTangentBundleFinite 𝓘(ℝ, EuclideanSpace ℝ (Fin 8))
          (CP 2 × CP 2))
      = (9 : ℤ) • Work.Cohomology.cupH' ℤ (Work.Whitney.ssB (CP 2 × CP 2)) 4 4
          ((Work.Thom.CohMap projFirst ℤ 4).hom (uSq 2))
          ((Work.Thom.CohMap projSecond ℤ 4).hom (uSq 2))
    rw [hpres 4, hchern 4, whitney_four_par hWF22 cppZ1 cppZ2, hZ1_0, hZ2_0, hZ1_1u, hZ2_1u,
      hZ1_2, hZ2_2, hZ1_3u, hZ2_3u, hZ1_4u, hZ2_4u]
    simp only [map_zero, LinearMap.zero_apply, zero_add, add_zero]
    rw [cupH_neg_left4]
    rw [cupH_neg_right4]
    rw [cupH_add_left4 ((Work.Thom.CohMap projFirst ℤ 4).hom (uSq 2)
        + (Work.Thom.CohMap projFirst ℤ 4).hom (uSq 2))
      ((Work.Thom.CohMap projFirst ℤ 4).hom (uSq 2))
      (((Work.Thom.CohMap projSecond ℤ 4).hom (uSq 2)
        + (Work.Thom.CohMap projSecond ℤ 4).hom (uSq 2))
        + (Work.Thom.CohMap projSecond ℤ 4).hom (uSq 2))]
    rw [cupH_add_left4 ((Work.Thom.CohMap projFirst ℤ 4).hom (uSq 2))
      ((Work.Thom.CohMap projFirst ℤ 4).hom (uSq 2))
      (((Work.Thom.CohMap projSecond ℤ 4).hom (uSq 2)
        + (Work.Thom.CohMap projSecond ℤ 4).hom (uSq 2))
        + (Work.Thom.CohMap projSecond ℤ 4).hom (uSq 2))]
    rw [cupH_add_right4 ((Work.Thom.CohMap projFirst ℤ 4).hom (uSq 2))
      ((Work.Thom.CohMap projSecond ℤ 4).hom (uSq 2)
        + (Work.Thom.CohMap projSecond ℤ 4).hom (uSq 2))
      ((Work.Thom.CohMap projSecond ℤ 4).hom (uSq 2))]
    rw [cupH_add_right4 ((Work.Thom.CohMap projFirst ℤ 4).hom (uSq 2))
      ((Work.Thom.CohMap projSecond ℤ 4).hom (uSq 2))
      ((Work.Thom.CohMap projSecond ℤ 4).hom (uSq 2))]
    have hnine := nine_zsmul_eq (Work.Cohomology.cupH' ℤ (Work.Whitney.ssB (CP 2 × CP 2)) 4 4
      ((Work.Thom.CohMap projFirst ℤ 4).hom (uSq 2))
      ((Work.Thom.CohMap projSecond ℤ 4).hom (uSq 2)))
    rw [hnine]
    abel
end

end Work.Gen
