import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.UBBInputs9.B.integrable_fderiv_chiBPhi_sq
import Submission.Work.UBBInputs9.B.pd_defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.UBBInputs9.B.pd_aux.integral_kinInt_pdMu_eq`

The sliding Dirichlet integrand `kinInt ℓ d Φ u x` is by definition the finite sum over
`k : Fin 3` of the squared directional derivatives of `y ↦ χ_{B(u)}(y 0)·Φ y` at `x`.
The product measure `pdMu ℓ` on `ℝ³ × X 1` is `volume.prod (volume ↾ abox 1 ℓ)`.

Consequently the integral of `kinInt` against `pdMu ℓ` is computed by (i) pulling the finite
sum out of the Bochner integral and (ii) Fubini over the product measure:

    `∫_{(u,x)} kinInt ℓ d Φ u x ∂(pdMu ℓ)
       = ∑_k ∫_u ∫_{x ∈ abox 1 ℓ} (∂_k (χ_{B(u)}·Φ)(x))² dx du`.

The `L¹`-input of Fubini, i.e. the integrability of each `k`-summand against `pdMu ℓ`, is the
product-measure swap of `B/integrable_fderiv_chiBPhi_sq` (`MeasureTheory.Integrable.swap`).
-/

noncomputable section

open MeasureTheory
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.UBBInputs9.B.pd_aux

theorem integral_kinInt_pdMu_eq {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    {Φ : Submission.BoseGases.X 1 → ℝ} (hΦ : ContDiff ℝ (⊤ : ENat) Φ)
    (hcs : HasCompactSupport Φ) :
    (∫ p : (EuclideanSpace ℝ (Fin 3)) × Submission.BoseGases.X 1,
        Work.UBBInputs9.B.kinInt ℓ d Φ p.1 p.2 ∂(Work.UBBInputs9.B.pdMu ℓ))
      = ∑ k : Fin 3, ∫ u : EuclideanSpace ℝ (Fin 3),
          ∫ x in Submission.BoseGases.abox 1 ℓ,
            (fderiv ℝ (fun y : Submission.BoseGases.X 1 =>
              Submission.BoseGases.chiB ℓ d u (y 0) * Φ y) x
                (Submission.BoseGases.kcDir 1 0 k)) ^ 2 := by
  classical
  -- Each `k`-summand of the kinetic integrand is `L¹` for the product measure `pdMu ℓ`: this is
  -- the product-measure swap of `integrable_fderiv_chiBPhi_sq`.
  have hInt : ∀ k : Fin 3,
      Integrable (fun p : (EuclideanSpace ℝ (Fin 3)) × Submission.BoseGases.X 1 =>
        (fderiv ℝ (fun y : Submission.BoseGases.X 1 =>
          Submission.BoseGases.chiB ℓ d p.1 (y 0) * Φ y) p.2
            (Submission.BoseGases.kcDir 1 0 k)) ^ 2) (Work.UBBInputs9.B.pdMu ℓ) :=
    fun k => (Work.UBBInputs9.B.integrable_fderiv_chiBPhi_sq ℓ d hℓ hd hΦ hcs k).swap
  -- `kinInt` is a finite sum: pull the sum out of the Bochner integral.
  simp only [Work.UBBInputs9.B.kinInt]
  rw [MeasureTheory.integral_finsetSum Finset.univ (fun k _ => hInt k)]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  -- Fubini for the product measure `pdMu ℓ = volume.prod (volume ↾ abox 1 ℓ)`.
  simp only [Work.UBBInputs9.B.pdMu]
  rw [integral_prod _ (hInt k)]

end Work.UBBInputs9.B.pd_aux
