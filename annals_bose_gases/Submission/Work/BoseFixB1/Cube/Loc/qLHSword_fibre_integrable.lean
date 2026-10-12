import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseFixB1.Cube.Loc.qLHSword_fibreSplit_of_integrable
import Submission.Work.BoseFixB1.Cube.Loc.tBdiagFormInd_fibreSplit
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace Work.BoseFixB1.Cube.Loc

open Submission.BoseGases

set_option autoImplicit false
set_option linter.unusedVariables false

/-- The potential slot's **fibre integrability**: the `y`-marginal of the potential word
`qLHSword (N := k) a μ w w1` at the fibre state `fibre k m Φ y` is integrable on the outer box
`abox m a`.  Companion of the PROVED `Work.BoseFixB1.Cube.Loc.qLHSword_fibreSplit_of_integrable`
(same hypotheses: the sub-sector support, the two-sided vanishing of `w`, the vanishing of `w1Fibre`,
and the integrability `hint = (★)` of the potential density of `Φ` on the box), needed to split the sum
`bGapCoeff·cn + tBdiag + qLHSword` inside the `Dloc`-integral of the Step-Loc assembly
(`Work.BoseFixB1.Cube.Loc.sbWordCube_fibreSplit_of_integrable`).

Route.  (i) `hint` transported along the a.e. equality `Φ²·qLHSden (k+m) = Φ²·qLHSden1` on the
sub-sector (`SubsectorSupp` + `qLHSden_eq_qLHSden1_of_subsector` from the sibling file), giving
`IntegrableOn (fun x => Φ x ^ 2 * qLHSden1 (N1 := k) (N2 := m) a μ w w1 x) (abox (k + m) a)`.
(ii) The measure-preserving block merge `Submission.BoseGases.aboxSplit_measurePreserving_restrict k m a`
(`Submission.BoseGases.blockSplitEquiv`) pushes that to
`Integrable (fun q : X k × X m => Φ (mergeBlock k m q) ^ 2 * qLHSden1 (N1 := k) (N2 := m) a μ w w1
(mergeBlock k m q)) ((volume.restrict (abox k a)).prod (volume.restrict (abox m a)))` — exactly the
first step of the proved `Submission.BoseGases.aboxFubini_swapped` (copy its `hmp.integrable_comp_emb`
+ `mergeBlock_eq` computation).
(iii) `Integrable.integral_prod_right` gives integrability of
`y ↦ ∫ z in abox k a, Φ (mergeBlock k m (z,y)) ^ 2 * qLHSden1 (N1 := k) (N2 := m) a μ w w1
(mergeBlock k m (z,y))`, which is `qLHSword (N := k) a μ w w1 (fibre k m Φ y)` by
`qLHSden1_merge` and `qLHSword_eq_integral_qLHSden` (with `fibre k m Φ y z = Φ (mergeBlock k m (z,y))`).
Finish with `Integrable.congr`. -/
theorem qLHSword_fibre_integrable {k m : ℕ} {a μ : ℝ} (ha : 0 < a) (hk : 0 < k)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    {w w1 : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ}
    (hw : ∀ x y, x ∉ A → w x y = 0) (hw' : ∀ x y, y ∉ A → w x y = 0)
    (hw1 : ∀ x, x ∉ A → Submission.BoseGases.w1Fibre a w1 x = 0)
    {Φ : Submission.BoseGases.X (k + m) → ℝ} (hΦm : Measurable Φ)
    (hsupp : Work.BoseFixB1.Cube.Loc.SubsectorSupp k m a A Φ)
    (hint : MeasureTheory.IntegrableOn (fun x => (Φ x) ^ 2 *
        Submission.BoseGases.qLHSden (k + m) a μ w w1 x)
        (Submission.BoseGases.abox (k + m) a) MeasureTheory.volume) :
    MeasureTheory.IntegrableOn
      (fun y : Submission.BoseGases.X m =>
        Submission.BoseGases.qLHSword (N := k) a μ w w1
          (Work.BoseFixB1.Cube.Loc.fibre k m Φ y))
      (Submission.BoseGases.abox m a) MeasureTheory.volume := by
  -- ### (i) on the sub-sector the potential density collapses onto its block-1 part
  have hden : (fun x : X (k + m) => (Φ x) ^ 2 * qLHSden (k + m) a μ w w1 x)
      =ᵐ[(volume : Measure (X (k + m))).restrict (abox (k + m) a)]
      (fun x : X (k + m) => (Φ x) ^ 2 * qLHSden1 (N1 := k) (N2 := m) a μ w w1 x) := by
    filter_upwards [hsupp] with x hx
    by_cases h : Φ x = 0
    · rw [h]; ring
    · rw [qLHSden_eq_qLHSden1_of_subsector hw hw' hw1 (hx h)]
  have hint1 : IntegrableOn (fun x : X (k + m) => (Φ x) ^ 2 *
      qLHSden1 (N1 := k) (N2 := m) a μ w w1 x) (abox (k + m) a) volume :=
    hint.congr hden
  -- ### (ii) push it forward along the measure-preserving block merge
  have hG : Integrable (fun q : X k × X m => Φ (mergeBlock k m q) ^ 2 *
      qLHSden1 (N1 := k) (N2 := m) a μ w w1 (mergeBlock k m q))
      ((volume.restrict (abox k a)).prod (volume.restrict (abox m a))) := by
    have hif := (aboxSplit_measurePreserving_restrict k m a).integrable_comp_emb
      (blockSplitEquiv k m).measurableEmbedding
      (g := fun q : X k × X m => Φ (mergeBlock k m q) ^ 2 *
        qLHSden1 (N1 := k) (N2 := m) a μ w w1 (mergeBlock k m q))
    apply hif.1
    change Integrable (fun x : X (k + m) => Φ (mergeBlock k m (blockSplitEquiv k m x)) ^ 2 *
      qLHSden1 (N1 := k) (N2 := m) a μ w w1 (mergeBlock k m (blockSplitEquiv k m x)))
      (volume.restrict (abox (k + m) a))
    have hpt : (fun x : X (k + m) => Φ (mergeBlock k m (blockSplitEquiv k m x)) ^ 2 *
        qLHSden1 (N1 := k) (N2 := m) a μ w w1 (mergeBlock k m (blockSplitEquiv k m x)))
        = fun x : X (k + m) => (Φ x) ^ 2 *
            qLHSden1 (N1 := k) (N2 := m) a μ w w1 x := by
      funext x
      simp only [blockSplitEquiv_apply, mergeBlock_eq]
    rw [hpt]
    exact hint1
  -- ### (iii) integrate out the in-box variables
  refine hG.integral_prod_right.congr (Filter.Eventually.of_forall fun y => ?_)
  simp only []
  rw [qLHSword_eq_integral_qLHSden]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  simp only [fibre, mkSlot_eq_mergeBlock, qLHSden1_merge]

end Work.BoseFixB1.Cube.Loc
