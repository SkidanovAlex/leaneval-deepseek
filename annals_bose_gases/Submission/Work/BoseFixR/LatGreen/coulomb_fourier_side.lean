import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixR.Rb5Lin.chat_sq_div_integral_eq_coulomb
import Submission.Work.BoseRowsFS.coulomb_pair_integrable
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixR.LatGreen.coulomb_fourier_side`

The **Coulomb/Newtonian-energy identity** in the normalization used by the lattice-Green
reduction: for an integrable, pointwise nonnegative, even `V : ℝ³ → ℝ` whose `p`-convention
Fourier transform `V̂ = Work.BoseFixR.chat V` has finite Coulomb energy in momentum space,

  `4 · (2π)⁻³ ∫ q, V̂(q)²/(2‖q‖²) = (2π)⁻¹ ∫∫ p, V p.1 · V p.2 / ‖p.1 − p.2‖`.

This is the classical identity

  `∫ q, V̂(q)²/(2‖q‖²) dq/(2π)³ = (1/8π) ∫∫ V(x)V(y)/‖x − y‖ dxdy`

(`Work.BoseFixR.Rb5Lin.chat_sq_div_integral_eq_coulomb`, proved in the corpus) multiplied by
`4`: indeed `4 · (1/8π) = (2π)⁻¹`.  The two finiteness hypotheses that the corpus theorem asks
for are discharged here by `hint` and by `Work.BoseRowsFS.coulomb_pair_integrable`, which
derives the position-space pair integrability from the very same momentum-space `hint`.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseFixR.LatGreen

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem coulomb_fourier_side {V : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hV1 : MeasureTheory.Integrable V)
    (hVnn : ∀ x, 0 ≤ V x) (hVev : ∀ x, V (-x) = V x)
    (hint : MeasureTheory.Integrable
      (fun q : EuclideanSpace ℝ (Fin 3) => (Work.BoseFixR.chat V q) ^ 2 / (2 * ‖q‖ ^ 2))) :
    4 * ((2 * Real.pi) ^ 3)⁻¹ *
        ∫ q : EuclideanSpace ℝ (Fin 3), (Work.BoseFixR.chat V q) ^ 2 / (2 * ‖q‖ ^ 2)
      = (2 * Real.pi)⁻¹ * ∫ p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3),
          V p.1 * V p.2 / ‖p.1 - p.2‖ := by
  have hnn_ae : 0 ≤ᵐ[volume] V := Filter.Eventually.of_forall hVnn
  -- 1. `hint` gives finiteness of the momentum-space `∫⁻`
  have hmom_nn : 0 ≤ᵐ[volume]
      (fun q : E3 => (Work.BoseFixR.chat V q) ^ 2 / (2 * ‖q‖ ^ 2)) :=
    Filter.Eventually.of_forall fun q => div_nonneg (sq_nonneg _) (by positivity)
  have hmom : (∫⁻ q : E3,
      ENNReal.ofReal ((Work.BoseFixR.chat V q) ^ 2 / (2 * ‖q‖ ^ 2))) < ⊤ :=
    (MeasureTheory.hasFiniteIntegral_iff_ofReal hmom_nn).mp hint.hasFiniteIntegral
  -- 2. the position-space pair kernel is integrable (this is the content of the `hint2`
  --    finiteness hypothesis of the corpus theorem), hence its `∫⁻` is finite
  have hpairI : MeasureTheory.Integrable
      (fun p : E3 × E3 => V p.1 * V p.2 / ‖p.1 - p.2‖) (volume.prod volume) :=
    Work.BoseRowsFS.coulomb_pair_integrable hV1 hnn_ae hVev hint
  have hpair_nn : 0 ≤ᵐ[volume.prod volume]
      (fun p : E3 × E3 => V p.1 * V p.2 / ‖p.1 - p.2‖) :=
    Filter.Eventually.of_forall fun p =>
      div_nonneg (mul_nonneg (hVnn p.1) (hVnn p.2)) (norm_nonneg _)
  have hpair : (∫⁻ p : E3 × E3,
      ENNReal.ofReal (V p.1 * V p.2 / ‖p.1 - p.2‖)) < ⊤ :=
    (MeasureTheory.hasFiniteIntegral_iff_ofReal hpair_nn).mp hpairI.hasFiniteIntegral
  -- 3. the corpus Fourier–Coulomb identity, with all five hypotheses discharged
  have h := Work.BoseFixR.Rb5Lin.chat_sq_div_integral_eq_coulomb hV1 hnn_ae hVev hmom hpair
  rw [mul_assoc, h]
  field_simp
  ring

end Work.BoseFixR.LatGreen
