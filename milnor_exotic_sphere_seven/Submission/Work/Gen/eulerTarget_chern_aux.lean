import Mathlib
import Submission.Work.Gen.EulerChernAux

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false

/-!
# The Chern classes of `Work.Gen.eulerTarget = (ℂ ⊗ O(1))⁵`

This module carries out, for the five-fold sum `Work.Gen.eulerTarget` of `ℂ ⊗ O(1)` over `ℂP⁴`,
the *bookkeeping* half of the Euler-sequence computation: from the Whitney sum formula
(`Work.Gen.WhitneyFormula`, owned by `Submission/Work/Whitney/`) and the duality sign
`Work.Gen.TautDualSign`, it computes the second and fourth Chern classes

  `c₂(eulerTarget) = -5 • uSq 4`,   `c₄(eulerTarget) = 10 • uFourth 4`.

The computation is the iterated application of the Whitney formula to
`eulerTarget = L ⊕ (L ⊕ (L ⊕ (L ⊕ L)))`, `L = ℂ ⊗ O(1)`, using `c₁(L) = 0`, `c₂(L) = -u²`,
`cⱼ(L) = 0` for `j ≥ 3` (`Work.Gen.lineC4_one` … `Work.Gen.lineC4_four`).  The only cup-product
identities needed are the definitional `uSq 4 ⌣ uSq 4 = uFourth 4` and the (anti)linearity of the
cup product.  Everything is conditional on the two inputs `WhitneyFormula` and `TautDualSign`.
-/

open CategoryTheory
open Work.Projective

namespace Work.Gen

noncomputable section

local notation "ss" => Work.Whitney.ssB (CP 4)

/-! ## The cup product at the middle degrees of `ℂP⁴`

The middle-degree cohomology `H⁴(ℂP⁴;ℤ)`, in the form in which `Work.Cohomology.cupH'` expects it. -/

private abbrev CH4 := (Work.Cohomology.cochainC ℤ (Work.Whitney.ssB (CP 4))).homology 4
private abbrev CH8 := (Work.Cohomology.cochainC ℤ (Work.Whitney.ssB (CP 4))).homology 8

/-- The cup product is additive in its second argument. -/
private theorem cupH_add_right (x y z : CH4) :
    Work.Cohomology.cupH' ℤ ss 4 4 x (y + z)
      = Work.Cohomology.cupH' ℤ ss 4 4 x y + Work.Cohomology.cupH' ℤ ss 4 4 x z :=
  map_add _ y z

/-- The cup product of `-x` on the left with `y` is the negative of `x ⌣ y`. -/
private theorem cupH_neg_left (x y : CH4) :
    Work.Cohomology.cupH' ℤ ss 4 4 (-x) y = -(Work.Cohomology.cupH' ℤ ss 4 4 x y) := by
  rw [map_neg, LinearMap.neg_apply]

/-- The cup product of `x` with `-y` is the negative of `x ⌣ y`. -/
private theorem cupH_neg_right (x y : CH4) :
    Work.Cohomology.cupH' ℤ ss 4 4 x (-y) = -(Work.Cohomology.cupH' ℤ ss 4 4 x y) := by
  rw [map_neg]

/-- `1 ⌣ x = x` in degree `4`. -/
private theorem cupH_one_left_four (x : CH4) :
    Work.Cohomology.cupH' ℤ ss 0 4 (Work.Cohomology.oneH ℤ ss) x = x := by
  rw [Work.Cohomology.cupH'_one_left]

/-- `1 ⌣ x = x` in degree `8`. -/
private theorem cupH_one_left_eight (x : CH8) :
    Work.Cohomology.cupH' ℤ ss 0 8 (Work.Cohomology.oneH ℤ ss) x = x := by
  rw [Work.Cohomology.cupH'_one_left]

/-- `x ⌣ 1 = x` in degree `4`. -/
private theorem cupH_one_right_four (x : CH4) :
    Work.Cohomology.cupH' ℤ ss 4 0 x (Work.Cohomology.oneH ℤ ss) = x := by
  rw [Work.Cohomology.cupH'_one_right]

/-- `(-u²) ⌣ (-u²) = u⁴`. -/
private theorem cupH_uSq_neg_neg :
    Work.Cohomology.cupH' ℤ ss 4 4 (-(uSq 4)) (-(uSq 4)) = uFourth 4 := by
  rw [cupH_neg_left, cupH_neg_right, neg_neg]
  rfl

/-- `(-u²) ⌣ (-u² + -u²) = 2·u⁴`. -/
private theorem cupH_uSq_nn2 :
    Work.Cohomology.cupH' ℤ ss 4 4 (-(uSq 4)) (-(uSq 4) + -(uSq 4))
      = uFourth 4 + uFourth 4 := by
  rw [cupH_add_right, cupH_uSq_neg_neg]

/-- `(-u²) ⌣ (-u² + -u² + -u²) = 3·u⁴`. -/
private theorem cupH_uSq_nn3 :
    Work.Cohomology.cupH' ℤ ss 4 4 (-(uSq 4)) (-(uSq 4) + -(uSq 4) + -(uSq 4))
      = uFourth 4 + uFourth 4 + uFourth 4 := by
  rw [cupH_add_right, cupH_uSq_nn2, cupH_uSq_neg_neg]

/-- `(-u²) ⌣ (-u² + -u² + -u² + -u²) = 4·u⁴`. -/
private theorem cupH_uSq_nn4 :
    Work.Cohomology.cupH' ℤ ss 4 4 (-(uSq 4)) (-(uSq 4) + -(uSq 4) + -(uSq 4) + -(uSq 4))
      = uFourth 4 + uFourth 4 + uFourth 4 + uFourth 4 := by
  rw [cupH_add_right, cupH_uSq_nn3, cupH_uSq_neg_neg]

/-! ## Integer multiples, expanded into sums

These rewrite the integer multiples of the final statements into iterated sums, so that the whole
computation can be carried out with `+` and `-` only. -/

private theorem four_zsmul_eq {M : Type} [AddCommGroup M] (x : M) :
    (4 : ℤ) • x = x + x + x + x := by
  rw [show (4 : ℤ) = ((4 : ℕ) : ℤ) from rfl, natCast_zsmul,
      show (4 : ℕ) = 3 + 1 from rfl, add_nsmul, one_nsmul,
      show (3 : ℕ) = 2 + 1 from rfl, add_nsmul, one_nsmul,
      show (2 : ℕ) = 1 + 1 from rfl, add_nsmul, one_nsmul]

private theorem six_zsmul_eq {M : Type} [AddCommGroup M] (x : M) :
    (6 : ℤ) • x = x + x + x + x + x + x := by
  rw [show (6 : ℤ) = ((6 : ℕ) : ℤ) from rfl, natCast_zsmul,
      show (6 : ℕ) = 5 + 1 from rfl, add_nsmul, one_nsmul,
      show (5 : ℕ) = 4 + 1 from rfl, add_nsmul, one_nsmul,
      show (4 : ℕ) = 3 + 1 from rfl, add_nsmul, one_nsmul,
      show (3 : ℕ) = 2 + 1 from rfl, add_nsmul, one_nsmul,
      show (2 : ℕ) = 1 + 1 from rfl, add_nsmul, one_nsmul]

private theorem neg_five_zsmul_eq {M : Type} [AddCommGroup M] (x : M) :
    -((5 : ℤ) • x) = -x + -x + -x + -x + -x := by
  rw [show (5 : ℤ) = 4 + 1 from rfl, add_zsmul, one_zsmul, neg_add, four_zsmul_eq]
  simp only [neg_add]

private theorem ten_zsmul_eq {M : Type} [AddCommGroup M] (x : M) :
    (10 : ℤ) • x = (x + x + x + x + x + x) + (x + x + x + x) := by
  rw [show (10 : ℤ) = 6 + 4 from rfl, add_zsmul, six_zsmul_eq, four_zsmul_eq]

/-! ## The Chern classes of the iterated sums `W1 = L`, `W2`, `W3`, `W4`

`W2 = L ⊕ L`, `W3 = L ⊕ W2`, `W4 = L ⊕ W3` (`Work.Gen.W2` … `Work.Gen.W4`).  Since
`c₂(L) = -u²` and `c₄(L) = c₁(L) = c₃(L) = 0`, each step only produces sums of copies of `-u²`
(in degree `2`) and of `u⁴` (in degree `4`). -/

/-- `c₂` of two copies of `ℂ ⊗ O(1)`. -/
private theorem c2_sum2 (hW : WhitneyFormula) (hS : TautDualSign) :
    Work.Thom.chernClass 4 2 W2 = -(uSq 4) + -(uSq 4) := by
  change Work.Thom.chernClass 4 2 (Work.Whitney.whitneySum (lineC 4) (lineC 4))
    = -(uSq 4) + -(uSq 4)
  rw [whitney_two hW (lineC 4) (lineC 4)]
  simp only [Work.Thom.chernClass_zero_eq_oneH]
  rw [lineC4_one hW hS, lineC4_two hW hS, cupH_one_left_four, Work.Cohomology.cupH'_zero_left,
    cupH_one_right_four]
  simp

/-- `c₄` of two copies of `ℂ ⊗ O(1)`. -/
private theorem c4_sum2 (hW : WhitneyFormula) (hS : TautDualSign) :
    Work.Thom.chernClass 4 4 W2 = uFourth 4 := by
  change Work.Thom.chernClass 4 4 (Work.Whitney.whitneySum (lineC 4) (lineC 4)) = uFourth 4
  rw [whitney_four hW (lineC 4) (lineC 4)]
  simp only [Work.Thom.chernClass_zero_eq_oneH]
  rw [lineC4_one hW hS, lineC4_two hW hS, lineC4_three, lineC4_four]
  rw [Work.Cohomology.cupH'_zero_right, Work.Cohomology.cupH'_zero_left,
    Work.Cohomology.cupH'_zero_left, Work.Cohomology.cupH'_zero_left, cupH_uSq_neg_neg]
  simp

/-- `c₂` of three copies of `ℂ ⊗ O(1)`. -/
private theorem c2_sum3 (hW : WhitneyFormula) (hS : TautDualSign) :
    Work.Thom.chernClass 6 2 W3 = -(uSq 4) + -(uSq 4) + -(uSq 4) := by
  change Work.Thom.chernClass 6 2 (Work.Whitney.whitneySum (lineC 4) W2)
    = -(uSq 4) + -(uSq 4) + -(uSq 4)
  rw [whitney_two hW (lineC 4) W2]
  simp only [Work.Thom.chernClass_zero_eq_oneH]
  rw [lineC4_one hW hS, lineC4_two hW hS, c2_sum2 hW hS, cupH_one_left_four,
    Work.Cohomology.cupH'_zero_left, cupH_one_right_four]
  simp

/-- `c₄` of three copies of `ℂ ⊗ O(1)`. -/
private theorem c4_sum3 (hW : WhitneyFormula) (hS : TautDualSign) :
    Work.Thom.chernClass 6 4 W3 = uFourth 4 + uFourth 4 + uFourth 4 := by
  change Work.Thom.chernClass 6 4 (Work.Whitney.whitneySum (lineC 4) W2)
    = uFourth 4 + uFourth 4 + uFourth 4
  rw [whitney_four hW (lineC 4) W2]
  simp only [Work.Thom.chernClass_zero_eq_oneH]
  rw [lineC4_one hW hS, lineC4_two hW hS, lineC4_three, lineC4_four, c2_sum2 hW hS, c4_sum2 hW hS]
  simp only [cupH_one_left_eight, Work.Cohomology.cupH'_zero_left, cupH_uSq_nn2, add_zero]
  abel

/-- `c₂` of four copies of `ℂ ⊗ O(1)`. -/
private theorem c2_sum4 (hW : WhitneyFormula) (hS : TautDualSign) :
    Work.Thom.chernClass 8 2 W4 = -(uSq 4) + -(uSq 4) + -(uSq 4) + -(uSq 4) := by
  change Work.Thom.chernClass 8 2 (Work.Whitney.whitneySum (lineC 4) W3)
    = -(uSq 4) + -(uSq 4) + -(uSq 4) + -(uSq 4)
  rw [whitney_two hW (lineC 4) W3]
  simp only [Work.Thom.chernClass_zero_eq_oneH]
  rw [lineC4_one hW hS, lineC4_two hW hS, c2_sum3 hW hS, cupH_one_left_four,
    Work.Cohomology.cupH'_zero_left, cupH_one_right_four]
  simp

/-- `c₄` of four copies of `ℂ ⊗ O(1)`. -/
private theorem c4_sum4 (hW : WhitneyFormula) (hS : TautDualSign) :
    Work.Thom.chernClass 8 4 W4
      = (uFourth 4 + uFourth 4 + uFourth 4) + (uFourth 4 + uFourth 4 + uFourth 4) := by
  change Work.Thom.chernClass 8 4 (Work.Whitney.whitneySum (lineC 4) W3)
    = (uFourth 4 + uFourth 4 + uFourth 4) + (uFourth 4 + uFourth 4 + uFourth 4)
  rw [whitney_four hW (lineC 4) W3]
  simp only [Work.Thom.chernClass_zero_eq_oneH]
  rw [lineC4_one hW hS, lineC4_two hW hS, lineC4_three, lineC4_four, c2_sum3 hW hS, c4_sum3 hW hS]
  simp only [cupH_one_left_eight, Work.Cohomology.cupH'_zero_left, cupH_uSq_nn3, add_zero]

/-! ## The main computation -/

theorem eulerTarget_chern_aux (hW : Work.Gen.WhitneyFormula) (hS : Work.Gen.TautDualSign) :
    Work.Thom.chernClass 10 2 Work.Gen.eulerTarget = -((5 : ℤ) • Work.Gen.uSq 4) ∧
    Work.Thom.chernClass 10 4 Work.Gen.eulerTarget = (10 : ℤ) • Work.Gen.uFourth 4 := by
  constructor
  · change Work.Thom.chernClass 10 2 (Work.Whitney.whitneySum (lineC 4) W4)
      = -((5 : ℤ) • uSq 4)
    rw [whitney_two hW (lineC 4) W4]
    simp only [Work.Thom.chernClass_zero_eq_oneH]
    rw [lineC4_one hW hS, lineC4_two hW hS, c2_sum4 hW hS]
    simp only [cupH_one_left_four, Work.Cohomology.cupH'_zero_left, cupH_one_right_four, add_zero]
    rw [neg_five_zsmul_eq]
  · change Work.Thom.chernClass 10 4 (Work.Whitney.whitneySum (lineC 4) W4)
      = (10 : ℤ) • uFourth 4
    rw [whitney_four hW (lineC 4) W4]
    simp only [Work.Thom.chernClass_zero_eq_oneH]
    rw [lineC4_one hW hS, lineC4_two hW hS, lineC4_three, lineC4_four, c2_sum4 hW hS,
      c4_sum4 hW hS]
    simp only [cupH_one_left_eight, Work.Cohomology.cupH'_zero_left, cupH_uSq_nn4, add_zero]
    rw [ten_zsmul_eq]
    abel

end

end Work.Gen
