import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Submission.Work.BoseFixB1.pairMassB_defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1

/-- Intended module `Submission.Work.BoseFixB1.psiAutocorrIdentity`, namespace `Work.BoseFixB1`.
IMPORT CONSTRAINT: this module must depend ONLY on `Submission.Work.BoseFixB1.pairMassB_defs` (and
Mathlib).  In particular do NOT import `Submission.Work.BoseFixB1.w2_sub_w1_pointwise`: its import
cone contains `Submission.Work.BoseFixB1.perSectorBoundG_holds`, which redeclares
`Work.BoseFixB1.psiWeight_one_le_mu_sq_of_le` and therefore cannot coexist with
`Submission.Work.BoseFixB1.perBoxF_flat`, which the consumer must import.  The needed unfolding
`Work.BoseFixB1.wSmallPair_eq_kernel` is already in `pairMassB_defs`.

The iterated pair-mass integral of the localised kernel equals the lag-integral of `psi` times the
autocorrelation of the sliding cutoff.  Route: `Work.BoseFixB1.wSmallPair_eq_kernel` writes
`wSmallPair M ℓ d u f x y = chiB x * (f (x-y)/E (x-y)) * chiB y` (with
`E = convScaleSmall M (ℓd) · convScale ℓ`); the *inner* substitution `y ↦ x - z` is
`MeasureTheory.integral_sub_left_eq_self` (unconditional), turning it into
`∫ x, ∫ z, psiPairKernel M ℓ d u f (x,z)`; `MeasureTheory.integral_integral_swap` with the
integrability hypothesis `hI` swaps the two (the uncurried function is exactly
`psiPairKernel M ℓ d u f`); finally `MeasureTheory.integral_const_mul` pulls `f z / E z` out of the
`x`-integral, leaving `Work.BoseFixB1.autocorr (M := M) ℓ d u z`. -/
theorem psiAutocorrIdentity {f : EuclideanSpace ℝ (Fin 3) → ℝ} {M : ℕ} {ℓ d : ℝ}
    (u : EuclideanSpace ℝ (Fin 3))
    (hI : MeasureTheory.Integrable (Work.BoseFixB1.psiPairKernel M ℓ d u f)
      (MeasureTheory.volume.prod MeasureTheory.volume)) :
    (∫ x : EuclideanSpace ℝ (Fin 3), ∫ y : EuclideanSpace ℝ (Fin 3),
        Submission.BoseGases.wSmallPair M ℓ d u f x y)
      = ∫ z : EuclideanSpace ℝ (Fin 3),
          (f z / (Submission.BoseGases.convScaleSmall M (ℓ * d) z
              * Submission.BoseGases.convScale ℓ z))
            * Work.BoseFixB1.autocorr (M := M) ℓ d u z := by
  -- Step 1 (`wSmallPair_eq_kernel` first, then the unconditional inner substitution
  -- `y ↦ x - z`): the inner `y`-integral is the `z`-integral of `psiPairKernel (x, ·)`.
  have hstep1 : ∀ x : EuclideanSpace ℝ (Fin 3),
      (∫ y : EuclideanSpace ℝ (Fin 3), Submission.BoseGases.wSmallPair M ℓ d u f x y)
        = ∫ z : EuclideanSpace ℝ (Fin 3), Work.BoseFixB1.psiPairKernel M ℓ d u f (x, z) := by
    intro x
    simp only [Work.BoseFixB1.wSmallPair_eq_kernel]
    have hsub :
        (∫ y : EuclideanSpace ℝ (Fin 3),
            Submission.BoseGases.chiSmallB M ℓ d u x
              * (f (x - y) / (Submission.BoseGases.convScaleSmall M (ℓ * d) (x - y)
                  * Submission.BoseGases.convScale ℓ (x - y)))
              * Submission.BoseGases.chiSmallB M ℓ d u y)
          = ∫ z : EuclideanSpace ℝ (Fin 3),
              Submission.BoseGases.chiSmallB M ℓ d u x
                * (f z / (Submission.BoseGases.convScaleSmall M (ℓ * d) z
                    * Submission.BoseGases.convScale ℓ z))
                * Submission.BoseGases.chiSmallB M ℓ d u (x - z) := by
      have h := MeasureTheory.integral_sub_left_eq_self
        (fun t : EuclideanSpace ℝ (Fin 3) =>
          Submission.BoseGases.chiSmallB M ℓ d u x
            * (f (x - t) / (Submission.BoseGases.convScaleSmall M (ℓ * d) (x - t)
                * Submission.BoseGases.convScale ℓ (x - t)))
            * Submission.BoseGases.chiSmallB M ℓ d u t) MeasureTheory.volume x
      simpa using h.symm
    rw [hsub]
    rfl
  rw [show (∫ x : EuclideanSpace ℝ (Fin 3), ∫ y : EuclideanSpace ℝ (Fin 3),
        Submission.BoseGases.wSmallPair M ℓ d u f x y)
      = ∫ x : EuclideanSpace ℝ (Fin 3), ∫ z : EuclideanSpace ℝ (Fin 3),
          Work.BoseFixB1.psiPairKernel M ℓ d u f (x, z) from by simp only [hstep1]]
  -- Step 2: Fubini, whose hypothesis is exactly `hI`.
  rw [MeasureTheory.integral_integral_swap
    (f := fun x z : EuclideanSpace ℝ (Fin 3) => Work.BoseFixB1.psiPairKernel M ℓ d u f (x, z)) hI]
  -- Step 3: pull the `z`-dependent constant out of the `x`-integral.
  apply MeasureTheory.integral_congr_ae
  filter_upwards with z
  have hfun : (fun x : EuclideanSpace ℝ (Fin 3) => Work.BoseFixB1.psiPairKernel M ℓ d u f (x, z))
      = fun x : EuclideanSpace ℝ (Fin 3) =>
          (f z / (Submission.BoseGases.convScaleSmall M (ℓ * d) z
              * Submission.BoseGases.convScale ℓ z))
            * (Submission.BoseGases.chiSmallB M ℓ d u x
                * Submission.BoseGases.chiSmallB M ℓ d u (x - z)) := by
    funext x
    simp only [Work.BoseFixB1.psiPairKernel_apply]
    ring
  rw [hfun, MeasureTheory.integral_const_mul]
  rfl

end Work.BoseFixB1
