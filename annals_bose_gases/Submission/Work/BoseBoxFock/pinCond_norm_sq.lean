import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.PotCubicPins
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.pinCond_norm_sq` — the pinned condensate is a unit vector

The condensate pin is `pinCond v μ c x = c·θ_Λ(x)` where `θ_Λ = 1_{Λ(ℓ)}` is the **sharp**
indicator of the box `Λ(ℓ)` of side `ℓ = ellH v μ` (`Work.BoseB4.BoxData.thetaFun`,
`Work.BoseK15.corpusBox`).  Its `L²`-norm is therefore controlled by the pair
`(‖c‖², volume Λ(ℓ))`:

    ∫ ‖pinCond v μ c x‖² dx = ‖c‖² · volume Λ(ℓ) = ‖c‖² · ℓ³,

and the pinning hypothesis `(conj c)·c = (ℓ³)⁻¹` (which says `‖c‖² = ℓ^{-3}`, the atomistic
normalisation `∫ θ̄θ = ℓ³`) makes this exactly `1`.  The hypothesis is read as the *real*
statement `‖c‖² = ((ellH v μ)³)⁻¹` via `Complex.ofReal_inj` and `Complex.mul_conj`
(`Complex.normSq_eq_norm_sq`), and the box volume is `Work.BoseB4.BoxData.volume_boxL`.
-/

namespace Work.BoseBoxFock

open MeasureTheory

theorem pinCond_norm_sq {v : EuclideanSpace ℝ (Fin 3) → ℝ} {μ : ℝ} {c : ℂ}
    (hc : (starRingEnd ℂ) c * c = ((Work.BoseBoxFock.ellH v μ) ^ 3)⁻¹) :
    ∫ x : EuclideanSpace ℝ (Fin 3), ‖Work.BoseBoxFock.pinCond v μ c x‖ ^ 2 = 1 := by
  classical
  -- the box side is positive (`ellH` is `sideAt μ (a v)` when positive, and `1` otherwise)
  have hℓ : 0 < ellH v μ := ellH_pos v μ
  -- the pinning hypothesis, as the real identity `‖c‖² = (ℓ³)⁻¹`
  have hcA : ‖c‖ ^ 2 = ((ellH v μ) ^ 3)⁻¹ := by
    have h1 : ((Complex.normSq c : ℝ) : ℂ) = ((((ellH v μ) ^ 3)⁻¹ : ℝ) : ℂ) := by
      rw [← Complex.mul_conj c, mul_comm]
      exact hc
    have h2 : Complex.normSq c = ((ellH v μ) ^ 3)⁻¹ := Complex.ofReal_inj.mp h1
    rwa [Complex.normSq_eq_norm_sq] at h2
  -- `θ_Λ` is the indicator of the box, and `‖θ_Λ‖²` is its indicator
  have hz : ∀ x : EuclideanSpace ℝ (Fin 3),
      ‖Work.BoseK15.corpusBox.thetaFun (ellH v μ) x‖ ^ 2
        = Set.indicator (Work.BoseK15.corpusBox.boxL (ellH v μ))
            (1 : EuclideanSpace ℝ (Fin 3) → ℝ) x := by
    intro x
    rw [Work.BoseB4.BoxData.thetaFun_apply]
    by_cases hx : x ∈ Work.BoseK15.corpusBox.boxL (ellH v μ)
    · rw [if_pos hx, Set.indicator_of_mem hx]; norm_num
    · rw [if_neg hx, Set.indicator_of_notMem hx]; norm_num
  have hpt : ∀ x : EuclideanSpace ℝ (Fin 3),
      ‖Work.BoseBoxFock.pinCond v μ c x‖ ^ 2
        = ‖c‖ ^ 2 * Set.indicator (Work.BoseK15.corpusBox.boxL (ellH v μ))
            (1 : EuclideanSpace ℝ (Fin 3) → ℝ) x := by
    intro x
    rw [show Work.BoseBoxFock.pinCond v μ c x
        = c * Work.BoseK15.corpusBox.thetaFun (ellH v μ) x from rfl,
      norm_mul, mul_pow, hz x]
  -- the mass of the box: `∫_Λ 1 = ℓ³`
  have hii : (∫ x : EuclideanSpace ℝ (Fin 3), Set.indicator
        (Work.BoseK15.corpusBox.boxL (ellH v μ))
        (1 : EuclideanSpace ℝ (Fin 3) → ℝ) x) = (ellH v μ) ^ 3 := by
    rw [MeasureTheory.integral_indicator_one
        (Work.BoseK15.corpusBox.boxL_measurableSet (ellH v μ)),
      MeasureTheory.Measure.real_def,
      Work.BoseB4.BoxData.volume_boxL _ hℓ,
      ENNReal.toReal_ofReal (by positivity)]
  calc ∫ x : EuclideanSpace ℝ (Fin 3), ‖Work.BoseBoxFock.pinCond v μ c x‖ ^ 2
      = ∫ x : EuclideanSpace ℝ (Fin 3), ‖c‖ ^ 2 * Set.indicator
          (Work.BoseK15.corpusBox.boxL (ellH v μ))
          (1 : EuclideanSpace ℝ (Fin 3) → ℝ) x :=
        integral_congr_ae (Filter.Eventually.of_forall hpt)
    _ = ‖c‖ ^ 2 * ∫ x : EuclideanSpace ℝ (Fin 3), Set.indicator
          (Work.BoseK15.corpusBox.boxL (ellH v μ))
          (1 : EuclideanSpace ℝ (Fin 3) → ℝ) x := by
        rw [MeasureTheory.integral_const_mul]
    _ = ‖c‖ ^ 2 * ((ellH v μ) ^ 3) := by rw [hii]
    _ = 1 := by
        rw [hcA, inv_mul_cancel₀ (ne_of_gt (pow_pos hℓ 3))]

end Work.BoseBoxFock
