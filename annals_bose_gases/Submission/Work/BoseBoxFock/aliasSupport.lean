import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.AliasDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.aliasSupport` — the autocorrelation kernel vanishes off the ball of radius `ℓ`

The autocorrelation `A g u = ∫_x g x · conj (g (x − u))` is an overlap integral: the integrand
vanishes unless *both* `x` and `x − u` lie in the support of `g`.  If
`tsupport g ⊆ ball 0 (ℓ/2)` and `‖u‖ ≥ ℓ`, no such `x` exists, because
`‖u‖ ≤ ‖x − u‖ + ‖x‖ < ℓ/2 + ℓ/2 = ℓ`.

Hence `aliasKernel g u = (autocorr g u).re = 0` for `‖u‖ ≥ ℓ`, which is exactly the statement
that the images in the aliasing identity `Λ − R = Σ_{m ≠ 0} ∫_u aliasKernel g u · heatK t (ℓ m − u)`
have non-overlapping supports.
-/

namespace Work.BoseBoxFock

open MeasureTheory
open scoped BigOperators Real

theorem aliasSupport {ℓ : ℝ} (hℓ : 0 < ℓ)
    {g : EuclideanSpace ℝ (Fin 3) → ℂ} (hg : ContDiff ℝ (⊤ : ENat) g)
    (hgsupp : tsupport g ⊆ Metric.ball 0 (ℓ/2))
    {u : EuclideanSpace ℝ (Fin 3)} (hu : ℓ ≤ ‖u‖) :
    Work.BoseBoxFock.aliasKernel g u = 0 := by
  -- `ℓ > 0` enters through `linarith` below (`hℓ'` is the same fact, kept named for the linter).
  have hℓ' : (0:ℝ) < ℓ := hℓ
  -- Any point at which the integrand is non-zero would lie in `ball 0 (ℓ/2)` together with its
  -- translate by `u`, forcing `‖u‖ < ℓ`.
  have hzero : ∀ x, g x * starRingEnd ℂ (g (x - u)) = 0 := by
    intro x
    by_contra h
    have hx : g x ≠ 0 := fun hx0 => h (by simp [hx0])
    have hy : g (x - u) ≠ 0 := fun hy0 => h (by simp [hy0])
    have hxmem : x ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) (ℓ/2) :=
      hgsupp (subset_closure (Function.mem_support.mpr hx))
    have hymem : x - u ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) (ℓ/2) :=
      hgsupp (subset_closure (Function.mem_support.mpr hy))
    rw [Metric.mem_ball, dist_eq_norm, sub_zero] at hxmem hymem
    have h1 : ‖u‖ ≤ ‖x - u‖ + ‖x‖ := by
      have h2 : ‖u‖ ≤ ‖u - x‖ + ‖x‖ := by
        have := norm_add_le (u - x) x
        simpa using this
      simpa [norm_sub_rev u x] using h2
    linarith
  -- The integrand is *identically* zero, so the integral is zero.
  have : autocorr g u = 0 := by
    rw [autocorr, show (fun x => g x * starRingEnd ℂ (g (x - u))) = fun _ => 0 from funext hzero]
    simp
  simp [aliasKernel, this]

end Work.BoseBoxFock
