import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseB1Cube.ConeC.BoseFixB1S_boxMuSumAgree
import Submission.Work.BoseFixB1S.boxPairRaw_eq
import Submission.Work.BoseFixB1S.qLHSword_split
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1S

/-- `boxQSum` unfolded against the raw pair sums `pairRaw` and the three `μ`-integrals
`boxMuP`/`boxMuQP`/`boxMuQ`: the potential part of the five box words is the seven raw pair
sums, and the `μ`-parts combine with coefficients `1, 2, 1`.  (Pure unfolding and `ring`.) -/
theorem boxQSum_eq {N : ℕ} (volA ℓ μ : ℝ) (A : Set (EuclideanSpace ℝ (Fin 3)))
    (w w1 w2 om : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ)
    (Φ : Submission.BoseGases.X N → ℝ) :
    boxQSum volA ℓ μ A w w1 w2 om Φ
      = pairRaw volA ℓ A w w1 w2 om Φ
        - μ * ((∑ i : Fin N, boxMuP volA ℓ A w1 Φ i)
            + 2 * (∑ i : Fin N, boxMuQP volA ℓ A w1 Φ i)
            + (∑ i : Fin N, boxMuQ volA ℓ A w1 Φ i)) := by
  unfold boxQSum boxQ0 boxQ1 boxQ2 boxQ3 boxQ4 pairRaw boxMuP boxMuQP boxMuQ
  ring

/-- **The box potential split** (`Work.BoseFixB1S.boxQSum`): the potential word `qLHSword` of the
corpus equals the five-word sum `boxQ0 + … + boxQ4` built from the FS-faithful box projections
`boxPInd`/`boxQInd`, for abstract kernels `w, w1, w2, ω` with `w1 = w(1−ω)`, `w2 = w(1−ω²)` and
`w` supported in `A × A`.

The three halves of the identity are separate lemmas: `qLHSword_split` (the left-hand side as the
`μ`-weight plus the half pair sum), `boxMuSumAgree` (the `μ`-weighted box words reassemble into
`Φ²`), and `boxPairRaw_eq` (the seven raw pair sums of the box words reassemble into the half pair
sum); `boxQSum_eq` then relates `boxQSum` to those two raw objects. -/
theorem boxPotsplitExpect {N : ℕ} {ℓ volA μ : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {w w1 w2 om : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ}
    (hwc : Continuous (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) => w p.1 p.2))
    (homc : Continuous (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) => om p.1 p.2))
    (hwsym : ∀ x y : EuclideanSpace ℝ (Fin 3), w x y = w y x)
    (homsym : ∀ x y : EuclideanSpace ℝ (Fin 3), om x y = om y x)
    (hw1rel : ∀ x y : EuclideanSpace ℝ (Fin 3), w1 x y = w x y * (1 - om x y))
    (hw2rel : ∀ x y : EuclideanSpace ℝ (Fin 3), w2 x y = w x y * (1 - om x y ^ 2))
    (hsuppA : ∀ x y : EuclideanSpace ℝ (Fin 3), w x y ≠ 0 → x ∈ A ∧ y ∈ A)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ) :
    Submission.BoseGases.qLHSword (N := N) ℓ μ w w1 Φ
      = Work.BoseFixB1S.boxQSum volA ℓ μ A w w1 w2 om Φ := by
  have hw1c : Continuous (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
      w1 p.1 p.2) := Submission.BoseGases.w1_continuous hwc homc hw1rel
  have hL := qLHSword_split (N := N) (μ := μ) hℓ hwc homc hw1rel hΦc
  have hM := boxMuSumAgree hℓ hvol hA hvolA hAc hw1c hwc hw1rel hsuppA hΦc
  have hR := boxPairRaw_eq hℓ hvol hA hvolA hAc hwc homc hwsym homsym hw1rel hw2rel hsuppA hΦc
  have hW := boxQSum_eq volA ℓ μ A w w1 w2 om Φ
  rw [hL, hW, hR, hM]
  ring

end Work.BoseFixB1S
