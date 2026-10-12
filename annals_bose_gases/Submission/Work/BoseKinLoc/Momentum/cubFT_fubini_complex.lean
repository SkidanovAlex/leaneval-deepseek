import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import ChallengeDeps
import Submission.Work.BoseKinLoc.Momentum.cubFT_defs
import Submission.Work.ESYRound9.Condensate.modeV_zero_deviation
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Complex-valued Fubini on the centred cube

`cubFT_fubini_complex` is the `ℂ`-valued companion of
`Work.ESYRound10.Couple.integral_acube_prod_eq_prod`: for an arbitrary (not necessarily
measurable, not necessarily integrable) family of complex-valued one-dimensional functions
`F j`, the integral over `Λ(ℓ) = [−ℓ/2, ℓ/2]³` of `∏ j, F j (z j)` factors as the product of
the one-dimensional integrals over `Icc (−ℓ/2) (ℓ/2)`.

The proof is the same two-step transport as in the real case:

1. the measure-preserving measurable equivalence `cgEuc3 : (Fin 3 → ℝ) ≃ᵐ ℝ³` identifies
   `Λ(ℓ)` with the coordinate cube `acubeF ℓ` (Mathlib `integral_map_equiv`, valid for an
   arbitrary Bochner integrand);
2. Fubini in three variables, `MeasureTheory.integral_fintype_prod_eq_prod` with `𝕜 = ℂ`
   (its `RCLike` hypothesis is satisfied by `ℂ`).

Neither step needs measurability or integrability of `F j`.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseKinLoc.Momentum

theorem cubFT_fubini_complex (ℓ : ℝ) (F : Fin 3 → ℝ → ℂ) :
    ∫ z in Submission.BoseGases.acube ℓ, (∏ j : Fin 3, F j (z j))
      = ∏ j : Fin 3, ∫ t in Set.Icc (-ℓ / 2) (ℓ / 2), F j t := by
  -- Step 1: transport the cube integral to the coordinate cube `acubeF ℓ`.
  have h₁ : (∫ z in Submission.BoseGases.acube ℓ, (∏ j : Fin 3, F j (z j)))
      = ∫ x : Fin 3 → ℝ, (∏ j : Fin 3, F j (x j))
          ∂((volume : Measure (Fin 3 → ℝ)).restrict (Submission.BoseGases.acubeF ℓ)) := by
    rw [show (∫ z in Submission.BoseGases.acube ℓ, (∏ j : Fin 3, F j (z j)))
        = ∫ z, (∏ j : Fin 3, F j (z j))
            ∂((volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict
                (Submission.BoseGases.acube ℓ)) from rfl]
    rw [Submission.BoseGases.acube_restrict_eq_map ℓ]
    rw [integral_map_equiv Submission.BoseGases.cgEuc3
          (fun z : EuclideanSpace ℝ (Fin 3) => ∏ j : Fin 3, F j (z j))]
    simp [Submission.BoseGases.cgEuc3]
  -- Step 2: Fubini in three variables on the product measure.
  have h₂ : (∫ x : Fin 3 → ℝ, (∏ j : Fin 3, F j (x j))
          ∂((volume : Measure (Fin 3 → ℝ)).restrict (Submission.BoseGases.acubeF ℓ)))
      = ∏ j : Fin 3, ∫ t in Set.Icc (-ℓ / 2) (ℓ / 2), F j t := by
    rw [Submission.BoseGases.acubeF_restrict_eq_pi ℓ]
    exact MeasureTheory.integral_fintype_prod_eq_prod F
  rw [h₁, h₂]

end Work.BoseKinLoc.Momentum
