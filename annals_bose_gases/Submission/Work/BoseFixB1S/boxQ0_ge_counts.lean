import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1.BoxQ0Value
import Submission.Work.BoseFixB1S.boxFlatSqJensen
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1S

open MeasureTheory

theorem boxQ0_ge_counts {N : ℕ} {ℓ volA μ : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {w1 w2 : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ}
    (hw2i : MeasureTheory.Integrable
      (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) => w2 p.1 p.2)
      ((MeasureTheory.volume : MeasureTheory.Measure
        (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3))).restrict (A ×ˢ A)))
    (hfib : MeasureTheory.IntegrableOn
      (fun z : EuclideanSpace ℝ (Fin 3) => Submission.BoseGases.w1Fibre ℓ w1 z) A)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ) (hμ : 0 ≤ μ)
    (hM1nn : 0 ≤ Work.BoseFixB1S.boxM1 ℓ A w1)
    (hM2 : Work.BoseFixB1S.boxM1 ℓ A w1 ≤ Work.BoseFixB1S.boxM2 volA A w2)
    (hPcnn : 0 ≤ Work.BoseFixB1S.boxPairCount volA ℓ A Φ) :
    (1 / 2) * (Work.BoseFixB1S.boxM1 ℓ A w1 / volA ^ 2)
        * ((Work.BoseFixB1S.boxFlatCount volA ℓ A Φ) ^ 2
            - Work.BoseFixB1S.boxFlatCount volA ℓ A Φ
              * (∫ x in Submission.BoseGases.abox N ℓ, (Φ x) ^ 2))
        / (∫ x in Submission.BoseGases.abox N ℓ, (Φ x) ^ 2)
      - μ * (Work.BoseFixB1S.boxM1 ℓ A w1 / volA)
          * Work.BoseFixB1S.boxFlatCount volA ℓ A Φ
    ≤ Work.BoseFixB1S.boxQ0 volA ℓ μ A w1 w2 Φ := by
  -- the `μ`-line cancels *exactly* against the value identity `boxQ0_value` (the one-body
  -- identity `Q0C.one_value` says `∫(PᵢΦ)²·w₁-fibre(xᵢ) = (M₁/volA)·∫(PᵢΦ)²`), so the
  -- hypothesis `hμ : 0 ≤ μ` is not needed by this inequality; it is kept because the caller
  -- states it.
  have _hμnn : 0 ≤ μ := hμ
  -- the exact value of the condensate word
  have hval := Work.BoseFixB1.boxQ0_value (μ := μ) hℓ hvol hA hvolA hAc hw2i hfib hΦc
  -- the flat-count Jensen inequality
  have hj := Work.BoseFixB1S.boxFlatSqJensen hℓ hvol hA hvolA hAc hΦc
  -- the box integral of `Φ²` is nonnegative
  have hI : 0 ≤ ∫ x in Submission.BoseGases.abox N ℓ, (Φ x) ^ 2 := by
    apply MeasureTheory.integral_nonneg
    intro x
    positivity
  -- divide the Jensen inequality by it
  have hdiv : (Work.BoseFixB1S.boxFlatCount volA ℓ A Φ ^ 2
        - Work.BoseFixB1S.boxFlatCount volA ℓ A Φ
          * (∫ x in Submission.BoseGases.abox N ℓ, (Φ x) ^ 2))
      / (∫ x in Submission.BoseGases.abox N ℓ, (Φ x) ^ 2)
      ≤ Work.BoseFixB1S.boxPairCount volA ℓ A Φ := by
    rcases lt_or_eq_of_le hI with hpos | heq
    · rw [div_le_iff₀ hpos]
      calc Work.BoseFixB1S.boxFlatCount volA ℓ A Φ ^ 2
              - Work.BoseFixB1S.boxFlatCount volA ℓ A Φ
                * (∫ x in Submission.BoseGases.abox N ℓ, (Φ x) ^ 2)
            ≤ (∫ x in Submission.BoseGases.abox N ℓ, (Φ x) ^ 2)
                * Work.BoseFixB1S.boxPairCount volA ℓ A Φ := hj
        _ = Work.BoseFixB1S.boxPairCount volA ℓ A Φ
                * (∫ x in Submission.BoseGases.abox N ℓ, (Φ x) ^ 2) := by ring
    · rw [← heq, mul_zero, sub_zero, div_zero]
      exact hPcnn
  -- the two nonnegativities of the coefficients
  have ha : 0 ≤ (1 / 2) * (Work.BoseFixB1S.boxM1 ℓ A w1 / volA ^ 2) := by
    have h : 0 ≤ Work.BoseFixB1S.boxM1 ℓ A w1 / volA ^ 2 :=
      div_nonneg hM1nn (by positivity)
    linarith
  have hab : (1 / 2) * (Work.BoseFixB1S.boxM1 ℓ A w1 / volA ^ 2)
      ≤ (1 / 2) * (Work.BoseFixB1S.boxM2 volA A w2 / volA ^ 2) := by
    have h : Work.BoseFixB1S.boxM1 ℓ A w1 / volA ^ 2
        ≤ Work.BoseFixB1S.boxM2 volA A w2 / volA ^ 2 :=
      div_le_div_of_nonneg_right hM2 (by positivity)
    linarith
  -- multiply the divided Jensen inequality by `½(M₁/volA²) ≥ 0`, then upgrade `M₁ ↦ M₂`
  have step1 : (1 / 2) * (Work.BoseFixB1S.boxM1 ℓ A w1 / volA ^ 2)
        * ((Work.BoseFixB1S.boxFlatCount volA ℓ A Φ ^ 2
            - Work.BoseFixB1S.boxFlatCount volA ℓ A Φ
              * (∫ x in Submission.BoseGases.abox N ℓ, (Φ x) ^ 2))
          / (∫ x in Submission.BoseGases.abox N ℓ, (Φ x) ^ 2))
      ≤ (1 / 2) * (Work.BoseFixB1S.boxM1 ℓ A w1 / volA ^ 2)
        * Work.BoseFixB1S.boxPairCount volA ℓ A Φ :=
    mul_le_mul_of_nonneg_left hdiv ha
  have step2 : (1 / 2) * (Work.BoseFixB1S.boxM1 ℓ A w1 / volA ^ 2)
        * Work.BoseFixB1S.boxPairCount volA ℓ A Φ
      ≤ (1 / 2) * (Work.BoseFixB1S.boxM2 volA A w2 / volA ^ 2)
        * Work.BoseFixB1S.boxPairCount volA ℓ A Φ :=
    mul_le_mul_of_nonneg_right hab hPcnn
  have hmain : (1 / 2) * (Work.BoseFixB1S.boxM1 ℓ A w1 / volA ^ 2)
        * ((Work.BoseFixB1S.boxFlatCount volA ℓ A Φ) ^ 2
            - Work.BoseFixB1S.boxFlatCount volA ℓ A Φ
              * (∫ x in Submission.BoseGases.abox N ℓ, (Φ x) ^ 2))
        / (∫ x in Submission.BoseGases.abox N ℓ, (Φ x) ^ 2)
      ≤ (1 / 2) * (Work.BoseFixB1S.boxM2 volA A w2 / volA ^ 2)
        * Work.BoseFixB1S.boxPairCount volA ℓ A Φ := by
    rw [mul_div_assoc]
    exact le_trans step1 step2
  rw [hval]
  linarith [hmain]

end Work.BoseFixB1S
