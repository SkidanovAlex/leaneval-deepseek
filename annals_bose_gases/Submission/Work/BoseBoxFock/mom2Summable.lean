import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.frame_lattice_ball
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Summability of the `ℓ⁻³`-weighted lattice samples of the kinetic transform

For a smooth compactly supported `w` living in the box `Λ(ℓ) = boxL ℓ`, the family

`n ↦ (ℓ³)⁻¹‖kinFT w ((2π/ℓ)·n)‖²`

is summable.  This is the statement `S0 < ∞` of the lattice-Riemann-sum bookkeeping
(`FINDING_kinRow_lattice.md`): it is what lets one treat the lattice sums of the box model as
finite quantities.

The proof is *not* a decay estimate.  `frame_lattice_ball` computes the value of the whole
`tsum` (Poisson summation on the box):

`∑' n, (ℓ³)⁻¹‖kinFT w (kmomInt ℓ n)‖² = (2π)⁻³ ∫_p ‖kinFT w p‖²`.

For a real family which is nonnegative this value alone does not certify summability — `tsum`
of a non-summable family is *defined* to be `0`, not `∞`.  So we split:

* if the integral `∫_p ‖kinFT w p‖²` is nonzero then the `tsum` is nonzero (the prefactor
  `(2π)⁻³` is nonzero) and `tsum_eq_zero_of_not_summable` gives summability;
* if the integral vanishes, then by Plancherel (`kinFT_plancherel`) `∫_x ‖w x‖² = 0`; since
  `‖w‖²` is continuous nonnegative and integrable (`ContDiff` + compact support), it vanishes
  a.e., so `w =ᵐ 0`, hence `kinFT w = 0` everywhere and the family is identically zero.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseBoxFock

theorem mom2Summable {ℓ : ℝ} (hℓ : 0 < ℓ) {w : EuclideanSpace ℝ (Fin 3) → ℂ}
    (hw : ContDiff ℝ (⊤ : ENat) w) (hwc : HasCompactSupport w)
    (hws : tsupport w ⊆ Work.BoseK15.corpusBox.boxL ℓ) :
    Summable (fun n : Fin 3 → ℤ =>
      (ℓ ^ 3)⁻¹ * ‖Submission.BoseGases.kinFT w (Work.BoseBoxFock.kmomInt ℓ n)‖ ^ 2) := by
  -- Poisson summation on the box: the value of the whole `tsum`.
  have hframe := frame_lattice_ball hℓ hw hwc hws
  have hmem : MemLp w 2 volume := hw.continuous.memLp_of_hasCompactSupport hwc
  by_cases hI : ∫ p, ‖Submission.BoseGases.kinFT w p‖ ^ 2 = 0
  · -- Degenerate case: the transform vanishes identically, so every sample does.
    have hw2 : ∫ x, ‖w x‖ ^ 2 = 0 := by
      rw [← kinFT_plancherel hw hwc, hI, mul_zero]
    have hwae : w =ᵐ[volume] 0 := by
      have hint : Integrable (fun x => ‖w x‖ ^ 2) volume := hmem.integrable_norm_pow (by norm_num)
      have h := (MeasureTheory.integral_eq_zero_iff_of_nonneg_ae
        (Filter.Eventually.of_forall (fun x => sq_nonneg _)) hint).mp hw2
      filter_upwards [h] with x hx
      exact norm_eq_zero.mp (sq_eq_zero_iff.mp hx)
    have hkin : ∀ p, Submission.BoseGases.kinFT w p = 0 := by
      intro p
      unfold Submission.BoseGases.kinFT
      have hae : (fun y : EuclideanSpace ℝ (Fin 3) =>
            Complex.exp (-(Complex.I * (inner ℝ p y : ℂ))) * w y)
          =ᵐ[volume] (fun y => Complex.exp (-(Complex.I * (inner ℝ p y : ℂ))) * (0 : ℂ)) := by
        filter_upwards [hwae] with y hy
        simp [hy]
      rw [MeasureTheory.integral_congr_ae hae]
      simp
    have hzero : (fun n : Fin 3 → ℤ =>
        (ℓ ^ 3)⁻¹ * ‖Submission.BoseGases.kinFT w (Work.BoseBoxFock.kmomInt ℓ n)‖ ^ 2) =
        fun _ => 0 := by
      funext n; rw [hkin]; simp
    rw [hzero]; exact summable_zero
  · -- Non-degenerate case: the computed value of the `tsum` is nonzero, hence it is summable
    -- (`tsum` of a non-summable family would be `0`).
    have hne : (∑' n, (ℓ ^ 3)⁻¹ *
        ‖Submission.BoseGases.kinFT w (Work.BoseBoxFock.kmomInt ℓ n)‖ ^ 2) ≠ 0 := by
      rw [hframe]
      exact mul_ne_zero (by positivity) hI
    exact not_not.mp (fun hsum => hne (tsum_eq_zero_of_not_summable hsum))

end Work.BoseBoxFock
