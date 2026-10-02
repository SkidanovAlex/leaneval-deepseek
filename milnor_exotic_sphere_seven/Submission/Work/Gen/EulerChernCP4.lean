import Mathlib
import Submission.Work.Gen.Euler
import Submission.Work.Gen.Basic
import Submission.Work.Gen.EulerDefs
import Submission.Work.Whitney.Basic
import Submission.Work.Whitney.Cup
import Submission.Work.Gen.chernClass_tautLine

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
# The Whitney sum formula over `ℂP⁴`, and the two `GEN`-area input `Prop`s

This module is a **home for the two input `Prop`s of the `GEN` area** (`Work.Gen.WhitneyFormula`,
`Work.Gen.TautDualSign` — previously in `Submission/Work/Gen/EulerChernTwo.lean`, since removed) and
for the **`ℂP⁴`-restricted form** of the Whitney sum formula that the `EulerChern` computation
actually consumes.

* `Work.Gen.WhitneyFormula` — the Whitney sum formula for complex gluing-data bundles over *every*
  topological base, in the `Fin (j+1)`-shaped presentation used by `Work.Thom.chernClass`.
* `Work.Gen.TautDualSign` — the duality sign `c₁(O(-1)) = -c₁(O(1))`; it is *proved* by
  `Work.Gen.chernClass_tautLine`, so it only needs to exist as a named `Prop`.
* `Work.Gen.WhFormulaCP4` — **the same formula restricted to bundles over `ℂP⁴`**, which is what
  the five-fold-sum computation needs (every bundle in `Work.Gen.whitney_one/_two/_four`,
  `Work.Gen.lineC4_*`, `Work.Gen.W2/W3/W4` and `Work.Gen.eulerTarget` lives over `ℂP⁴`).
  `WhFormulaCP4` is *implied* by `WhitneyFormula` (`whFormulaCP4_of_whitney`), and is the shape in
  which the metric/Leray–Hirsch route can plausibly deliver it (`ℂP⁴` is compact, hence
  paracompact, so the Hermitian-metric splitting
  `Work.Whitney.nonempty_bundleIso_of_nowhereZeroSection_of_paracompact` applies).
-/

open CategoryTheory
open Work.Projective

namespace Work.Gen

noncomputable section

local notation "ss" => Work.Whitney.ssB (CP 4)

/-- The degree cast at an equal degree is the identity, regardless of the proof. -/
theorem cohTransport_eq_id' {B : Type} [TopologicalSpace B] {n : ℕ}
    (h : n = n) (x : Work.Thom.Coh ℤ n B) : Work.Thom.cohTransport h x = x := by
  rw [Subsingleton.elim h rfl, Work.Thom.cohTransport_rfl]


/-- **The Whitney sum formula**, in the `Fin (j+1)`-indexed form. -/
def WhitneyFormula : Prop :=
  ∀ {B : Type} [TopologicalSpace B] {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂] {m₁ m₂ j : ℕ}
    (Z₁ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m₁)) ι₁)
    (Z₂ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m₂)) ι₂),
    Work.Thom.chernClass (m₁ + m₂) j (Work.Whitney.whitneySum Z₁ Z₂)
      = ∑ a : Fin (j + 1),
          Work.Thom.cohTransport (by have h := a.isLt; omega)
            ((Work.Cohomology.cupH' ℤ (TopCat.toSSet.obj (TopCat.of B))
              (2 * (a : ℕ)) (2 * (j - (a : ℕ))))
              (Work.Thom.chernClass m₁ (a : ℕ) Z₁)
              (Work.Thom.chernClass m₂ (j - (a : ℕ)) Z₂))

/-- **The duality sign** `c₁(O(-1)) = - c₁(O(1))` for the two tautological line bundles of `ℂPⁿ`.
It is proved by `Work.Gen.chernClass_tautLine`. -/
def TautDualSign : Prop :=
  ∀ n : ℕ, Work.Thom.chernClass 1 1 (tautLine n) = - Work.Thom.chernClass 1 1 (tautDual n)

/-- The duality sign, **proved** (`Work.Gen.chernClass_tautLine`). -/
theorem tautDualSign : TautDualSign := fun n => Work.Gen.chernClass_tautLine n

/-- **The Whitney sum formula over `ℂP⁴`**, in the `Fin (j+1)` presentation: for complex bundles
`Z₁`, `Z₂` over `ℂP⁴` of ranks `m₁`, `m₂` and every degree `j`,

`c_j(Z₁ ⊕ Z₂) = Σ_{a} c_a(Z₁) ⌣ c_{j-a}(Z₂)`.

This is the weakest input the `EulerChern` computation needs; see the module docstring. -/
def WhFormulaCP4 : Prop :=
  ∀ {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂] {m₁ m₂ j : ℕ}
    (Z₁ : VectorBundleCore ℂ (CP 4) (EuclideanSpace ℂ (Fin m₁)) ι₁)
    (Z₂ : VectorBundleCore ℂ (CP 4) (EuclideanSpace ℂ (Fin m₂)) ι₂),
    Work.Thom.chernClass (m₁ + m₂) j (Work.Whitney.whitneySum Z₁ Z₂)
      = ∑ a : Fin (j + 1),
          Work.Thom.cohTransport (by have h := a.isLt; omega)
            ((Work.Cohomology.cupH' ℤ (Work.Whitney.ssB (CP 4))
              (2 * (a : ℕ)) (2 * (j - (a : ℕ))))
              (Work.Thom.chernClass m₁ (a : ℕ) Z₁)
              (Work.Thom.chernClass m₂ (j - (a : ℕ)) Z₂))

/-- **The arbitrary-base Whitney formula implies the `ℂP⁴`-restricted one.** -/
theorem whFormulaCP4_of_whitney (hW : WhitneyFormula) : WhFormulaCP4 :=
  fun Z₁ Z₂ => hW Z₁ Z₂

/-! ## The instances in degrees `1`, `2`, `4` over `ℂP⁴` -/

/-- **The Whitney formula in degree `1` over `ℂP⁴`**, `Fin`-sum collapsed. -/
theorem whitney_one_CP4 (hW : WhFormulaCP4) {m₁ m₂ : ℕ} {ι₁ ι₂ : Type} [Fintype ι₁]
    [Fintype ι₂]
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

/-- **The Whitney formula in degree `2` over `ℂP⁴`**, `Fin`-sum collapsed. -/
theorem whitney_two_CP4 (hW : WhFormulaCP4) {m₁ m₂ : ℕ} {ι₁ ι₂ : Type} [Fintype ι₁]
    [Fintype ι₂]
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

/-- **The Whitney formula in degree `4` over `ℂP⁴`**, `Fin`-sum collapsed. -/
theorem whitney_four_CP4 (hW : WhFormulaCP4) {m₁ m₂ : ℕ} {ι₁ ι₂ : Type} [Fintype ι₁]
    [Fintype ι₂]
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


/-! ## The `ℂP⁴`-restricted bookkeeping chain

Verbatim copies of the lemmas of `Submission/Work/Gen/EulerChernAux.lean` and
`Submission/Work/Gen/eulerTarget_chern_aux.lean`, with the hypothesis weakened from
`Work.Gen.WhitneyFormula` to `Work.Gen.WhFormulaCP4` (the `ℂP⁴`-restricted form).  Everything here
is over `ℂP⁴`, which is where the whole `EulerChern` computation lives.
-/

section CP4Chain

/-! ## The iterated sums `W2, W3, W4` of `lineC 4` -/

/-- Two copies of `ℂ ⊗ O(1)` over `ℂP⁴`. -/
def W2CP4 : VectorBundleCore ℂ (CP 4) (EuclideanSpace ℂ (Fin 4)) (lineIdx × lineIdx) :=
  Work.Whitney.whitneySum (lineC 4) (lineC 4)

/-- Three copies of `ℂ ⊗ O(1)` over `ℂP⁴`. -/
def W3CP4 : VectorBundleCore ℂ (CP 4) (EuclideanSpace ℂ (Fin 6)) (lineIdx × (lineIdx × lineIdx)) :=
  Work.Whitney.whitneySum (lineC 4) W2CP4

/-- Four copies of `ℂ ⊗ O(1)` over `ℂP⁴`. -/
def W4CP4 : VectorBundleCore ℂ (CP 4) (EuclideanSpace ℂ (Fin 8))
    (lineIdx × (lineIdx × (lineIdx × lineIdx))) :=
  Work.Whitney.whitneySum (lineC 4) W3CP4

/-! ## The Chern classes of `ℂ ⊗ O(1)` -/

theorem lineC4_one_CP4 (hW : WhFormulaCP4) (hS : TautDualSign) :
    Work.Thom.chernClass 2 1 (lineC 4) = 0 := by
  rw [lineC, whitney_one_CP4 hW (tautDual 4) (tautLine 4)]
  simp only [Work.Thom.chernClass_zero_eq_oneH]
  rw [show Work.Thom.chernClass 1 1 (tautDual 4) = uCoh 4 from rfl,
      show Work.Thom.chernClass 1 1 (tautLine 4) = -uCoh 4 from by rw [hS 4]; rfl]
  rw [Work.Cohomology.cupH'_one_left, Work.Cohomology.cupH'_one_right]
  simp

theorem lineC4_two_CP4 (hW : WhFormulaCP4) (hS : TautDualSign) :
    Work.Thom.chernClass 2 2 (lineC 4) = -uSq 4 := by
  rw [lineC, whitney_two_CP4 hW (tautDual 4) (tautLine 4)]
  rw [Work.Thom.chernClass_eq_zero_of_lt (tautDual 4) (by norm_num : 1 < 2),
      Work.Thom.chernClass_eq_zero_of_lt (tautLine 4) (by norm_num : 1 < 2)]
  simp only [Work.Thom.chernClass_zero_eq_oneH]
  rw [show Work.Thom.chernClass 1 1 (tautDual 4) = uCoh 4 from rfl,
      show Work.Thom.chernClass 1 1 (tautLine 4) = -uCoh 4 from by rw [hS 4]; rfl]
  rw [Work.Cohomology.cupH'_zero_right, Work.Cohomology.cupH'_zero_left]
  rw [map_neg (f := Work.Cohomology.cupH' ℤ ss 2 2 (uCoh 4))]
  rw [show (Work.Cohomology.cupH' ℤ ss 2 2 (uCoh 4) (uCoh 4)) = uSq 4 from rfl]
  simp

theorem lineC4_three_CP4 : Work.Thom.chernClass 2 3 (lineC 4) = 0 :=
  Work.Thom.chernClass_eq_zero_of_lt (lineC 4) (by norm_num)

theorem lineC4_four_CP4 : Work.Thom.chernClass 2 4 (lineC 4) = 0 :=
  Work.Thom.chernClass_eq_zero_of_lt (lineC 4) (by norm_num)


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

`W2CP4 = L ⊕ L`, `W3CP4 = L ⊕ W2`, `W4CP4 = L ⊕ W3` (`Work.Gen.W2` … `Work.Gen.W4`).  Since
`c₂(L) = -u²` and `c₄(L) = c₁(L) = c₃(L) = 0`, each step only produces sums of copies of `-u²`
(in degree `2`) and of `u⁴` (in degree `4`). -/

/-- `c₂` of two copies of `ℂ ⊗ O(1)`. -/
private theorem c2_sum2_CP4 (hW : WhFormulaCP4) (hS : TautDualSign) :
    Work.Thom.chernClass 4 2 W2CP4 = -(uSq 4) + -(uSq 4) := by
  change Work.Thom.chernClass 4 2 (Work.Whitney.whitneySum (lineC 4) (lineC 4))
    = -(uSq 4) + -(uSq 4)
  rw [whitney_two_CP4 hW (lineC 4) (lineC 4)]
  simp only [Work.Thom.chernClass_zero_eq_oneH]
  rw [lineC4_one_CP4 hW hS, lineC4_two_CP4 hW hS, cupH_one_left_four, Work.Cohomology.cupH'_zero_left,
    cupH_one_right_four]
  simp

/-- `c₄` of two copies of `ℂ ⊗ O(1)`. -/
private theorem c4_sum2_CP4 (hW : WhFormulaCP4) (hS : TautDualSign) :
    Work.Thom.chernClass 4 4 W2CP4 = uFourth 4 := by
  change Work.Thom.chernClass 4 4 (Work.Whitney.whitneySum (lineC 4) (lineC 4)) = uFourth 4
  rw [whitney_four_CP4 hW (lineC 4) (lineC 4)]
  simp only [Work.Thom.chernClass_zero_eq_oneH]
  rw [lineC4_one_CP4 hW hS, lineC4_two_CP4 hW hS, lineC4_three_CP4, lineC4_four_CP4]
  rw [Work.Cohomology.cupH'_zero_right, Work.Cohomology.cupH'_zero_left,
    Work.Cohomology.cupH'_zero_left, Work.Cohomology.cupH'_zero_left, cupH_uSq_neg_neg]
  simp

/-- `c₂` of three copies of `ℂ ⊗ O(1)`. -/
private theorem c2_sum3_CP4 (hW : WhFormulaCP4) (hS : TautDualSign) :
    Work.Thom.chernClass 6 2 W3CP4 = -(uSq 4) + -(uSq 4) + -(uSq 4) := by
  change Work.Thom.chernClass 6 2 (Work.Whitney.whitneySum (lineC 4) W2CP4)
    = -(uSq 4) + -(uSq 4) + -(uSq 4)
  rw [whitney_two_CP4 hW (lineC 4) W2CP4]
  simp only [Work.Thom.chernClass_zero_eq_oneH]
  rw [lineC4_one_CP4 hW hS, lineC4_two_CP4 hW hS, c2_sum2_CP4 hW hS, cupH_one_left_four,
    Work.Cohomology.cupH'_zero_left, cupH_one_right_four]
  simp

/-- `c₄` of three copies of `ℂ ⊗ O(1)`. -/
private theorem c4_sum3_CP4 (hW : WhFormulaCP4) (hS : TautDualSign) :
    Work.Thom.chernClass 6 4 W3CP4 = uFourth 4 + uFourth 4 + uFourth 4 := by
  change Work.Thom.chernClass 6 4 (Work.Whitney.whitneySum (lineC 4) W2CP4)
    = uFourth 4 + uFourth 4 + uFourth 4
  rw [whitney_four_CP4 hW (lineC 4) W2CP4]
  simp only [Work.Thom.chernClass_zero_eq_oneH]
  rw [lineC4_one_CP4 hW hS, lineC4_two_CP4 hW hS, lineC4_three_CP4, lineC4_four_CP4, c2_sum2_CP4 hW hS, c4_sum2_CP4 hW hS]
  simp only [cupH_one_left_eight, Work.Cohomology.cupH'_zero_left, cupH_uSq_nn2, add_zero]
  abel

/-- `c₂` of four copies of `ℂ ⊗ O(1)`. -/
private theorem c2_sum4_CP4 (hW : WhFormulaCP4) (hS : TautDualSign) :
    Work.Thom.chernClass 8 2 W4CP4 = -(uSq 4) + -(uSq 4) + -(uSq 4) + -(uSq 4) := by
  change Work.Thom.chernClass 8 2 (Work.Whitney.whitneySum (lineC 4) W3CP4)
    = -(uSq 4) + -(uSq 4) + -(uSq 4) + -(uSq 4)
  rw [whitney_two_CP4 hW (lineC 4) W3CP4]
  simp only [Work.Thom.chernClass_zero_eq_oneH]
  rw [lineC4_one_CP4 hW hS, lineC4_two_CP4 hW hS, c2_sum3_CP4 hW hS, cupH_one_left_four,
    Work.Cohomology.cupH'_zero_left, cupH_one_right_four]
  simp

/-- `c₄` of four copies of `ℂ ⊗ O(1)`. -/
private theorem c4_sum4_CP4 (hW : WhFormulaCP4) (hS : TautDualSign) :
    Work.Thom.chernClass 8 4 W4CP4
      = (uFourth 4 + uFourth 4 + uFourth 4) + (uFourth 4 + uFourth 4 + uFourth 4) := by
  change Work.Thom.chernClass 8 4 (Work.Whitney.whitneySum (lineC 4) W3CP4)
    = (uFourth 4 + uFourth 4 + uFourth 4) + (uFourth 4 + uFourth 4 + uFourth 4)
  rw [whitney_four_CP4 hW (lineC 4) W3CP4]
  simp only [Work.Thom.chernClass_zero_eq_oneH]
  rw [lineC4_one_CP4 hW hS, lineC4_two_CP4 hW hS, lineC4_three_CP4, lineC4_four_CP4, c2_sum3_CP4 hW hS, c4_sum3_CP4 hW hS]
  simp only [cupH_one_left_eight, Work.Cohomology.cupH'_zero_left, cupH_uSq_nn3, add_zero]

/-! ## The main computation -/

theorem eulerTarget_chern_aux_CP4 (hW : Work.Gen.WhFormulaCP4) (hS : Work.Gen.TautDualSign) :
    Work.Thom.chernClass 10 2 Work.Gen.eulerTarget = -((5 : ℤ) • Work.Gen.uSq 4) ∧
    Work.Thom.chernClass 10 4 Work.Gen.eulerTarget = (10 : ℤ) • Work.Gen.uFourth 4 := by
  constructor
  · change Work.Thom.chernClass 10 2 (Work.Whitney.whitneySum (lineC 4) W4CP4)
      = -((5 : ℤ) • uSq 4)
    rw [whitney_two_CP4 hW (lineC 4) W4CP4]
    simp only [Work.Thom.chernClass_zero_eq_oneH]
    rw [lineC4_one_CP4 hW hS, lineC4_two_CP4 hW hS, c2_sum4_CP4 hW hS]
    simp only [cupH_one_left_four, Work.Cohomology.cupH'_zero_left, cupH_one_right_four, add_zero]
    rw [neg_five_zsmul_eq]
  · change Work.Thom.chernClass 10 4 (Work.Whitney.whitneySum (lineC 4) W4CP4)
      = (10 : ℤ) • uFourth 4
    rw [whitney_four_CP4 hW (lineC 4) W4CP4]
    simp only [Work.Thom.chernClass_zero_eq_oneH]
    rw [lineC4_one_CP4 hW hS, lineC4_two_CP4 hW hS, lineC4_three_CP4, lineC4_four_CP4, c2_sum4_CP4 hW hS,
      c4_sum4_CP4 hW hS]
    simp only [cupH_one_left_eight, Work.Cohomology.cupH'_zero_left, cupH_uSq_nn4, add_zero]
    rw [ten_zsmul_eq]
    abel


end CP4Chain

end

end Work.Gen
