import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1.PairBlockCore
import Submission.Work.BoseFixB1S.BoxPotOper
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1S

theorem pairBlock_ae_pairFive {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal) (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {w w₁ w₂ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ}
    (om : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ)
    (hw1 : ∀ x y : EuclideanSpace ℝ (Fin 3), w₁ x y = w x y * (1 - om x y))
    (hw2 : ∀ x y : EuclideanSpace ℝ (Fin 3), w₂ x y = w x y * (1 - om x y ^ 2))
    (hwsym : ∀ x y : EuclideanSpace ℝ (Fin 3), w x y = w y x)
    (homsym : ∀ x y : EuclideanSpace ℝ (Fin 3), om x y = om y x)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ)
    {i j : Fin N} (hij : i ≠ j) :
    (fun x : Submission.BoseGases.X N =>
        Work.BoseFixB1.pairBlock volA A w om Φ (i, j) x)
      =ᵐ[MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)]
    (fun x : Submission.BoseGases.X N =>
        Work.BoseFixB1.pairFive volA A w w₁ w₂ om Φ (i, j) x
        + Work.BoseFixB1.pairFive volA A w w₁ w₂ om Φ (j, i) x) := by
  filter_upwards [MeasureTheory.self_mem_ae_restrict (Submission.BoseGases.abox_measurable N ℓ)]
    with x hx
  exact (Work.BoseFixB1.pairFive_add_swap volA A w w₁ w₂ om x hw1 hw2 hwsym homsym
    (boxPPswap hℓ hvol hA hvolA hAc hij hΦc x)
    (boxQQswap hℓ hvol hA hvolA hAc hij hΦc x hx).symm
    (boxPQswap hℓ hvol hA hvolA hAc hij hΦc x hx)
    (boxQPswap hℓ hvol hA hvolA hAc hij hΦc x hx)).symm

end Work.BoseFixB1S
