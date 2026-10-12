import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.PCFU.ChWordChains
import Submission.Work.BoseBoxFock.PCFU.lowSlot_boxRestrictR_factor
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.PCFU.taperIntegrand_box_eq`

The box restriction `boxRestrictR ℓ Φ = Φ · 1_{abox n ℓ}` may be removed from the *taper* integrand
of the pair term `⟨Φ, χ_iχ_j T(x_j − x_i) lowSlot_j(aQ_j aP_i Φ)⟩`, at the price of integrating
over the centred box only:

    ∫_{X n} (boxRestrictR ℓ Φ) · χ_i · χ_j · T(x_j − x_i) · lowSlot_j (aQ_j aP_i (boxRestrictR ℓ Φ))
      = ∫_{x ∈ abox n ℓ} Φ · χ_i · χ_j · T(x_j − x_i) · lowSlot_j (aQ_j aP_i Φ) .

The proof is the PROVED pointwise factorisation `lowSlot_boxRestrictR_factor`
(`boxRestrictR ℓ Φ x · lowSlot_j(aQ_j aP_i (boxRestrictR ℓ Φ)) x
  = 1_{abox}(x) · Φ x · lowSlot_j(aQ_j aP_i Φ) x`, whose content is
`lowSlot_boxRestrictR_agree` — the slot-`j` update of a box configuration is a box configuration,
where the `aP`/`aQ` towers of `boxRestrictR ℓ Φ` and of `Φ` agree) together with the standard
`∫ f = ∫_{abox} f` comparison `MeasureTheory.integral_indicator` (the box is measurable,
`abox_measurable`), after casting the real identity to `ℂ`.

Note that the hypothesis `hij` is *not* needed for this identity (the factorisation
`lowSlot_boxRestrictR_agree` holds for every pair of slots); it is kept in the statement for
compatibility with the consumers.  Everything below is `sorry`-free.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseBoxFock.PCFU

local notation "Ω" => EuclideanSpace ℝ (Fin 3)

set_option linter.unusedVariables false

theorem taperIntegrand_box_eq {n : ℕ} (i j : Fin n) (hij : i ≠ j)
    (fc : Work.BoseBoxFix.LowCut) {κ ℓ : ℝ}
    {Φ : Submission.BoseGases.X n → ℝ} (T : EuclideanSpace ℝ (Fin 3) → ℂ) :
    (∫ x : Submission.BoseGases.X n,
        ((Work.BoseBoxFock.boxRestrictR ℓ Φ x : ℝ) : ℂ)
          * ((Submission.BoseGases.chiScale ℓ (x i) : ℝ) : ℂ)
          * ((Submission.BoseGases.chiScale ℓ (x j) : ℝ) : ℂ)
          * T (x j - x i)
          * ((Work.BoseBoxFix.lowSlot fc κ ℓ j
              (Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i
                (Work.BoseBoxFock.boxRestrictR ℓ Φ))) x : ℝ) : ℂ))
      = ∫ x in Submission.BoseGases.abox n ℓ,
          ((Φ x : ℝ) : ℂ)
            * ((Submission.BoseGases.chiScale ℓ (x i) : ℝ) : ℂ)
            * ((Submission.BoseGases.chiScale ℓ (x j) : ℝ) : ℂ)
            * T (x j - x i)
            * ((Work.BoseBoxFix.lowSlot fc κ ℓ j
                (Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Φ)) x : ℝ) : ℂ) := by
  -- Turn the box integral on the right into the integral of the box indicator.
  rw [← MeasureTheory.integral_indicator (Submission.BoseGases.abox_measurable n ℓ)]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with x
  -- `boxRestrictR ℓ Φ x = Φ x · 1_{abox}(x)`, cast to `ℂ`.
  have hA : ((Work.BoseBoxFock.boxRestrictR ℓ Φ x : ℝ) : ℂ)
      = ((Φ x : ℝ) : ℂ)
        * (((Submission.BoseGases.abox n ℓ).indicator (fun _ => (1 : ℝ)) x : ℝ) : ℂ) := by
    have h : Work.BoseBoxFock.boxRestrictR ℓ Φ x
        = Φ x * (Submission.BoseGases.abox n ℓ).indicator (fun _ => (1 : ℝ)) x := rfl
    rw [h, Complex.ofReal_mul]
  rw [hA]
  -- Case split on `x ∈ abox n ℓ`: on the box the indicator is `1` and the `lowSlot`s agree, off it
  -- both sides vanish.
  by_cases hx : x ∈ Submission.BoseGases.abox n ℓ
  · have hC : (((Submission.BoseGases.abox n ℓ).indicator (fun _ => (1 : ℝ)) x : ℝ) : ℂ) = 1 := by
      rw [Set.indicator_of_mem hx]; norm_num
    have hB : ((Work.BoseBoxFix.lowSlot fc κ ℓ j
        (Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i
          (Work.BoseBoxFock.boxRestrictR ℓ Φ))) x : ℝ) : ℂ)
      = ((Work.BoseBoxFix.lowSlot fc κ ℓ j
          (Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Φ)) x : ℝ) : ℂ) := by
      rw [lowSlot_boxRestrictR_agree fc κ ℓ i j Φ hx]
    rw [hC, hB, Set.indicator_of_mem hx]
    ring
  · have hC : (((Submission.BoseGases.abox n ℓ).indicator (fun _ => (1 : ℝ)) x : ℝ) : ℂ) = 0 := by
      rw [Set.indicator_of_notMem hx]; norm_num
    rw [hC, Set.indicator_of_notMem hx]
    ring

end Work.BoseBoxFock.PCFU
