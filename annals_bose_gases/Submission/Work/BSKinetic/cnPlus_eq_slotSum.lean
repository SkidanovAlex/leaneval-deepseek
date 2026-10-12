import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BSKinetic.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BSKinetic.cnPlus_eq_slotSum` — the excited count as a sum of slot fibres

The corpus's excited-particle count on the centred analysis box is

`cnPlus ℓ Φ  =  Σ_i ‖QᵢΦ‖²  =  Σ_i ∫_{abox (n+1) ℓ} (aQ ℓ i Φ x)²`,

where `Qᵢ = 1 − Pᵢ` and `Pᵢ` is the slot-`i` condensate mean over `acube ℓ`
(`Submission.BoseGases.aQ`, `aP`).

Peeling the `i`-th particle out of the product box via the measure-preserving
split `kcInsN n i : ℝ³ × X n ≃ᵐ X (n+1)` (`Submission.BoseGases.abox_integral_peel`)
and evaluating `Pᵢ` on an inserted configuration
(`Submission.BoseGases.aP_kcInsN`, `PᵢΦ (x_{i←z}) = (ℓ³)⁻¹∫_w Φ(x_{i←w})`),
each slot term becomes the mean-free square of the fibre `z ↦ Φ(x_{i←z})`:

`∫_{abox (n+1) ℓ} (QᵢΦ)²
   = ∫_{abox n ℓ} ∫_{acube ℓ}
       (Φ(x_{i←z}) − (ℓ³)⁻¹∫_{acube ℓ} Φ(x_{i←w}))²`.

This is the `cnPlus` analogue of `Work.BSKinetic.kinWord_eq_slotSum`.
-/

namespace Work.BSKinetic

open MeasureTheory
open scoped ContDiff Topology Real BigOperators
open Submission.BoseGases

set_option autoImplicit false

/-- **The excited count as a sum of slot fibres.**  Peeling one particle at a time out of the
product box `abox (n+1) ℓ`, the box-restricted excited count

`cnPlus ℓ Φ = Σᵢ ∫_{abox (n+1) ℓ} (QᵢΦ)²`

is the slot sum of the mean-free squares of the fibres `z ↦ Φ(x_{i←z})` over the remaining box
`abox n ℓ`: each term is `∫_{abox n ℓ} ∫_{acube ℓ} (Φ(x_{i←z}) − (ℓ³)⁻¹∫_{acube ℓ} Φ(x_{i←w}))²`.

The two ingredients are the measure-preserving peel of the centred box
(`Submission.BoseGases.abox_integral_peel`) and the evaluation of the fibre mean
(`Submission.BoseGases.aP_kcInsN`). -/
theorem cnPlus_eq_slotSum {ℓ : ℝ} (hℓ : 0 < ℓ) (n : ℕ)
    (Φ : Submission.BoseGases.X (n + 1) → ℝ) (hΦ : ContDiff ℝ (⊤ : ENat) Φ) :
    Submission.BoseGases.cnPlus ℓ Φ
      = ∑ i : Fin (n + 1), ∫ r in Submission.BoseGases.abox n ℓ,
          ∫ z in Submission.BoseGases.acube ℓ,
            (Φ (Submission.BoseGases.kcInsN n i (z, r))
              - (ℓ ^ 3)⁻¹ * ∫ w in Submission.BoseGases.acube ℓ,
                  Φ (Submission.BoseGases.kcInsN n i (w, r))) ^ 2 := by
  -- The per-slot identity: peel slot `i`, then evaluate `Qᵢ` on the inserted configuration.
  have hkey : ∀ i : Fin (n + 1),
      (∫ x in abox (n + 1) ℓ, (aQ ℓ i Φ x) ^ 2)
        = ∫ r in abox n ℓ, ∫ z in acube ℓ,
            (Φ (kcInsN n i (z, r))
              - (ℓ ^ 3)⁻¹ * ∫ w in acube ℓ, Φ (kcInsN n i (w, r))) ^ 2 := by
    intro i
    -- the square of `QᵢΦ` is integrable on the centred `(n+1)`-box
    have hFint : IntegrableOn (fun x : X (n + 1) => (aQ ℓ i Φ x) ^ 2)
        (abox (n + 1) ℓ) volume :=
      integrableOn_sq_aQ hℓ i hΦ.continuous
    -- the peel of the slot-`i` coordinate square
    have hpeel := abox_integral_peel (i := i) (F := fun x : X (n + 1) => (aQ ℓ i Φ x) ^ 2) hFint
    rw [hpeel]
    -- the peeled integrand is `(QᵢΦ (x_{i←z}))²`, which is the mean-free square of the fibre
    apply integral_congr_ae
    filter_upwards with r
    apply integral_congr_ae
    filter_upwards with z
    congr 1
    rw [aQ, aP_kcInsN, one_div]
  unfold cnPlus
  exact Finset.sum_congr rfl (fun i _ => hkey i)

end Work.BSKinetic
