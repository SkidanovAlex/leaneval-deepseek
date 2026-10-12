import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Submission.Work.BoseFixB1.w2_sub_w1_pointwise
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1

/-- Intended module `Submission.Work.BoseFixB1.wSmallPair_integral_eq_autocorr`, namespace
`Work.BoseFixB1`.  The iterated pair-mass integral of the localised kernel equals the lag-integral
of `psi` times the autocorrelation of the sliding cutoff.  Route: `wSmallPair_eq_chi_mul` writes
`wSmallPair M ℓ d u f x y = chiB x * (f (x-y)/E (x-y)) * chiB y`; the *inner* substitution
`y ↦ x - z` is `MeasureTheory.integral_sub_left_eq_self` (unconditional), turning it into
`∫ x, ∫ z, psiPairKernel M ℓ d u f (x,z)`; `MeasureTheory.integral_integral_swap` with the
integrability hypothesis `hI` swaps the two (the uncurried function is exactly
`psiPairKernel M ℓ d u f`); finally `MeasureTheory.integral_const_mul` pulls `f z / E z` out of the
`x`-integral, leaving `Work.BoseFixB1.autocorr (M := M) ℓ d u z`. -/
theorem wSmallPair_integral_eq_autocorr {f : EuclideanSpace ℝ (Fin 3) → ℝ} {M : ℕ} {ℓ d : ℝ}
    (u : EuclideanSpace ℝ (Fin 3))
    (hI : MeasureTheory.Integrable (Work.BoseFixB1.psiPairKernel M ℓ d u f)
      (MeasureTheory.volume.prod MeasureTheory.volume)) :
    (∫ x : EuclideanSpace ℝ (Fin 3), ∫ y : EuclideanSpace ℝ (Fin 3),
        Submission.BoseGases.wSmallPair M ℓ d u f x y)
      = ∫ z : EuclideanSpace ℝ (Fin 3),
          (f z / (Submission.BoseGases.convScaleSmall M (ℓ * d) z
              * Submission.BoseGases.convScale ℓ z))
            * Work.BoseFixB1.autocorr (M := M) ℓ d u z := by
  -- The inner integral: substitute `y ↦ x - y` (the lag variable).
  have hpt : ∀ x : EuclideanSpace ℝ (Fin 3),
      (∫ y : EuclideanSpace ℝ (Fin 3), Submission.BoseGases.wSmallPair M ℓ d u f x y)
        = ∫ z : EuclideanSpace ℝ (Fin 3),
            Work.BoseFixB1.psiPairKernel M ℓ d u f (x, z) := by
    intro x
    have h1 : (∫ y, Submission.BoseGases.wSmallPair M ℓ d u f x y)
        = ∫ y, (fun z => Work.BoseFixB1.psiPairKernel M ℓ d u f (x, z)) (x - y) := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with y
      rw [Work.BoseFixB1.wSmallPair_eq_chi_mul M ℓ d u x y f,
        Work.BoseFixB1.psiPairKernel_apply, sub_sub_cancel]
    rw [h1]
    exact MeasureTheory.integral_sub_left_eq_self
      (fun z => Work.BoseFixB1.psiPairKernel M ℓ d u f (x, z)) MeasureTheory.volume x
  -- The `x`-integral of the lag kernel, at fixed lag `z`.
  have hz : ∀ z : EuclideanSpace ℝ (Fin 3),
      (∫ x : EuclideanSpace ℝ (Fin 3), Work.BoseFixB1.psiPairKernel M ℓ d u f (x, z))
        = (f z / (Submission.BoseGases.convScaleSmall M (ℓ * d) z
              * Submission.BoseGases.convScale ℓ z))
            * Work.BoseFixB1.autocorr (M := M) ℓ d u z := by
    intro z
    have hfun : (fun x : EuclideanSpace ℝ (Fin 3) =>
          Work.BoseFixB1.psiPairKernel M ℓ d u f (x, z))
        = fun x : EuclideanSpace ℝ (Fin 3) =>
            (f z / (Submission.BoseGases.convScaleSmall M (ℓ * d) z
                * Submission.BoseGases.convScale ℓ z))
              * (Submission.BoseGases.chiSmallB M ℓ d u x
                  * Submission.BoseGases.chiSmallB M ℓ d u (x - z)) := by
      funext x
      rw [Work.BoseFixB1.psiPairKernel_apply]
      ring
    rw [hfun, MeasureTheory.integral_const_mul, Work.BoseFixB1.autocorr_apply]
  -- Fubini, using the integrability hypothesis of the uncurried kernel.
  have hI' : MeasureTheory.Integrable
      (Function.uncurry (fun x z => Work.BoseFixB1.psiPairKernel M ℓ d u f (x, z)))
      (MeasureTheory.volume.prod MeasureTheory.volume) := by
    refine hI.congr (Filter.Eventually.of_forall (fun p => ?_))
    simp [Function.uncurry]
  calc (∫ x : EuclideanSpace ℝ (Fin 3), ∫ y : EuclideanSpace ℝ (Fin 3),
        Submission.BoseGases.wSmallPair M ℓ d u f x y)
      = ∫ x : EuclideanSpace ℝ (Fin 3), ∫ z : EuclideanSpace ℝ (Fin 3),
          Work.BoseFixB1.psiPairKernel M ℓ d u f (x, z) := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards with x
        exact hpt x
    _ = ∫ z : EuclideanSpace ℝ (Fin 3), ∫ x : EuclideanSpace ℝ (Fin 3),
          Work.BoseFixB1.psiPairKernel M ℓ d u f (x, z) :=
        MeasureTheory.integral_integral_swap hI'
    _ = ∫ z : EuclideanSpace ℝ (Fin 3),
          (f z / (Submission.BoseGases.convScaleSmall M (ℓ * d) z
              * Submission.BoseGases.convScale ℓ z))
            * Work.BoseFixB1.autocorr (M := M) ℓ d u z := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards with z
        exact hz z

end Work.BoseFixB1
