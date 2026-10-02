import Mathlib
import Submission.Work.Gen.Euler
import Submission.Work.Gen.Basic
import Submission.Work.Gen.EulerDefs
import Submission.Work.Gen.EulerChernCP4
import Submission.Work.Gen.EulerChernAux
import Submission.Work.Gen.eulerSequence_iso
import Submission.Work.Gen.chernClass_tautLine
import Submission.Work.Gen.WhFormulaCP4Par
import Submission.Work.Gen.eulerTarget_chern_aux
import Submission.Work.Whitney.Basic
import Submission.Work.Whitney.Cup
import Submission.Work.Whitney.Stability

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
# `Work.Gen.EulerChern`: the Chern classes of the complexified tangent bundle of `ℂP⁴`

The second and fourth Chern classes of `ℂ ⊗_ℝ TℂP⁴` are `-5 c₁(O(1))²` and `10 c₁(O(1))⁴`.

The proof is the composition of three inputs:

* the **complexified Euler sequence** `ℂ ⊗ TℂP⁴ ⊕ ε² ≅ (ℂ ⊗ O(1))⁵`
  (`Work.Gen.eulerSequence_iso`), here in the shape
  `Work.Gen.stdTangentC 4 ⊕ ε² ≅ Work.Gen.eulerTarget`;
* the **Whitney sum formula** `c_j(E ⊕ F) = Σ_{a+b=j} c_a(E) ⌣ c_b(F)`
  (`Work.Whitney.chernClass_whitneySum`, the subproject `Submission/Work/Whitney/`), used
  *once and only once* — through the named hypothesis `hW : Work.Gen.WhitneyFormula` below — to
  (a) strip the trivial rank-`2` summand and (b) compute the Chern classes of the five-fold sum
  `eulerTarget` (`Work.Gen.eulerTarget_chern_aux`);
* the **duality sign** `c₁(O(-1)) = -c₁(O(1))` (`Work.Gen.chernClass_tautLine`), packaged as
  `Work.Gen.TautDualSign`.
-/

namespace Work.Gen

open CategoryTheory
open Work.Projective

noncomputable section

/-- The trivial complex rank-`2` bundle over `ℂP⁴`. -/
abbrev trivTwo : VectorBundleCore ℂ (CP 4) (EuclideanSpace ℂ (Fin 2)) (Fin 1) :=
  trivialVectorBundleCore ℂ (CP 4) (EuclideanSpace ℂ (Fin 2)) (Fin 1)

/-- **Stability** for the trivial rank-`2` summand, in degree `2` (the presentation of
`Work.Gen.eulerSequence_iso`). -/
theorem chernClass_stdTangentC_trivTwo_two (hW : WhitneyFormula) :
    Work.Thom.chernClass 10 2 (Work.Whitney.whitneySum (stdTangentC 4) trivTwo)
      = Work.Thom.chernClass 8 2 (stdTangentC 4) := by
  rw [whitney_two hW (stdTangentC 4) trivTwo]
  rw [Work.Thom.chernClass_trivial (B := CP 4) (ι := Fin 1) (m := 2) (j := 2) (by norm_num),
    Work.Thom.chernClass_trivial (B := CP 4) (ι := Fin 1) (m := 2) (j := 1) (by norm_num)]
  simp only [Work.Thom.chernClass_zero_eq_oneH]
  rw [Work.Cohomology.cupH'_zero_right, Work.Cohomology.cupH'_zero_right,
    Work.Cohomology.cupH'_one_right]
  simp

/-- **Stability** for the trivial rank-`2` summand, in degree `4`. -/
theorem chernClass_stdTangentC_trivTwo_four (hW : WhitneyFormula) :
    Work.Thom.chernClass 10 4 (Work.Whitney.whitneySum (stdTangentC 4) trivTwo)
      = Work.Thom.chernClass 8 4 (stdTangentC 4) := by
  rw [whitney_four hW (stdTangentC 4) trivTwo]
  rw [Work.Thom.chernClass_trivial (B := CP 4) (ι := Fin 1) (m := 2) (j := 4) (by norm_num),
    Work.Thom.chernClass_trivial (B := CP 4) (ι := Fin 1) (m := 2) (j := 3) (by norm_num),
    Work.Thom.chernClass_trivial (B := CP 4) (ι := Fin 1) (m := 2) (j := 2) (by norm_num),
    Work.Thom.chernClass_trivial (B := CP 4) (ι := Fin 1) (m := 2) (j := 1) (by norm_num)]
  simp only [Work.Thom.chernClass_zero_eq_oneH]
  rw [Work.Cohomology.cupH'_zero_right, Work.Cohomology.cupH'_zero_right,
    Work.Cohomology.cupH'_zero_right, Work.Cohomology.cupH'_zero_right,
    Work.Cohomology.cupH'_one_right]
  simp

/-- **Stability** for the trivial rank-`2` summand, in degree `2`, from the `ℂP⁴`-restricted
Whitney formula. -/
theorem chernClass_stdTangentC_trivTwo_two_CP4 (hW : WhFormulaCP4) :
    Work.Thom.chernClass 10 2 (Work.Whitney.whitneySum (stdTangentC 4) trivTwo)
      = Work.Thom.chernClass 8 2 (stdTangentC 4) := by
  rw [whitney_two_CP4 hW (stdTangentC 4) trivTwo]
  rw [Work.Thom.chernClass_trivial (B := CP 4) (ι := Fin 1) (m := 2) (j := 2) (by norm_num),
    Work.Thom.chernClass_trivial (B := CP 4) (ι := Fin 1) (m := 2) (j := 1) (by norm_num)]
  simp only [Work.Thom.chernClass_zero_eq_oneH]
  rw [Work.Cohomology.cupH'_zero_right, Work.Cohomology.cupH'_zero_right,
    Work.Cohomology.cupH'_one_right]
  simp

/-- **Stability** for the trivial rank-`2` summand, in degree `4`, from the `ℂP⁴`-restricted
Whitney formula. -/
theorem chernClass_stdTangentC_trivTwo_four_CP4 (hW : WhFormulaCP4) :
    Work.Thom.chernClass 10 4 (Work.Whitney.whitneySum (stdTangentC 4) trivTwo)
      = Work.Thom.chernClass 8 4 (stdTangentC 4) := by
  rw [whitney_four_CP4 hW (stdTangentC 4) trivTwo]
  rw [Work.Thom.chernClass_trivial (B := CP 4) (ι := Fin 1) (m := 2) (j := 4) (by norm_num),
    Work.Thom.chernClass_trivial (B := CP 4) (ι := Fin 1) (m := 2) (j := 3) (by norm_num),
    Work.Thom.chernClass_trivial (B := CP 4) (ι := Fin 1) (m := 2) (j := 2) (by norm_num),
    Work.Thom.chernClass_trivial (B := CP 4) (ι := Fin 1) (m := 2) (j := 1) (by norm_num)]
  simp only [Work.Thom.chernClass_zero_eq_oneH]
  rw [Work.Cohomology.cupH'_zero_right, Work.Cohomology.cupH'_zero_right,
    Work.Cohomology.cupH'_zero_right, Work.Cohomology.cupH'_zero_right,
    Work.Cohomology.cupH'_one_right]
  simp

/-- **`Work.Gen.EulerChern`, from the `ℂP⁴`-restricted Whitney sum formula**: the statement is
`Work.Gen.EulerChern`; the only input is `Work.Gen.WhFormulaCP4`, the Whitney formula for pairs of
complex bundles **over `ℂP⁴`** (strictly weaker than `Work.Gen.WhitneyFormula`, and implied by it
via `Work.Gen.whFormulaCP4_of_whitney`). -/
theorem EulerChern_of_CP4 (hW : WhFormulaCP4) :
    Work.Thom.chernClass 8 2 (stdTangentC 4) = -((5 : ℤ) • uSq 4) ∧
    Work.Thom.chernClass 8 4 (stdTangentC 4) = (10 : ℤ) • uFourth 4 := by
  have hS : TautDualSign := tautDualSign
  obtain ⟨h2, h4⟩ := eulerTarget_chern_aux_CP4 hW hS
  obtain ⟨e⟩ := eulerSequence_iso
  exact ⟨(chernClass_stdTangentC_trivTwo_two_CP4 hW).symm.trans
      ((Work.Thom.chernClass_BundleIso
        (Work.Whitney.whitneySum (stdTangentC 4) trivTwo) eulerTarget e).trans h2),
    (chernClass_stdTangentC_trivTwo_four_CP4 hW).symm.trans
      ((Work.Thom.chernClass_BundleIso
        (Work.Whitney.whitneySum (stdTangentC 4) trivTwo) eulerTarget e).trans h4)⟩


/-- **`Work.Gen.EulerChern`**: the second and fourth Chern classes of `ℂ ⊗_ℝ TℂP⁴`.

`c₂ = -5 c₁(O(1))²` and `c₄ = 10 c₁(O(1))⁴`, i.e. `c(ℂ ⊗ TℂP⁴) = (1 - u²)⁵` truncated, with
`u = c₁(O(1))`.  The Whitney formula enters exactly once, in the `have hW` below. -/
theorem EulerChern :
    Work.Thom.chernClass 8 2 (stdTangentC 4) = -((5 : ℤ) • uSq 4) ∧
    Work.Thom.chernClass 8 4 (stdTangentC 4) = (10 : ℤ) • uFourth 4 := by
  -- The Whitney sum formula **over `ℂP⁴`**: the ONE isolated input, taken in the *paracompact*
  -- form which the `Submission/Work/LerayHirsch/` machinery delivers
  -- (`Work.Gen.whFormulaCP4_of_par`; `ℂP⁴` is compact Hausdorff, hence paracompact).  When
  -- `whitneySumFormulaPar_of_lerayHirsch`/`_of_kunnethCP` land (their inputs being
  -- `Work.Whitney.TopClassMul` and `Work.Gen.whitneySumFormulaPar_one_N`), replace the `sorry`
  -- below by the delivered `∀ m₁ m₂, WhitneySumFormulaPar m₁ m₂`.
  -- The single remaining input: the Leray--Hirsch theorem (`Work.LerayHirsch.LerayHirschFull`)
  -- for every complex bundle; the `(1,N)` input of the roof is the proved
  -- `Work.Gen.whitneySumFormulaPar_one_N`.
  have hLH : ∀ {m : ℕ} {B : Type} [TopologicalSpace B] {ι : Type} [Fintype ι]
      (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι),
      Work.LerayHirsch.LerayHirschFull Z := Work.Gen.lerayHirschFull_all
  have hpar : ∀ m₁ m₂ : ℕ, Work.LerayHirsch.WhitneySumFormulaPar m₁ m₂ :=
    whitneySumFormulaPar_of_lerayHirsch' hLH
  exact EulerChern_of_CP4 (whFormulaCP4_of_par hpar)

end

end Work.Gen
