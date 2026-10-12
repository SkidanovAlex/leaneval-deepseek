import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.cIPn_boxSlotOf_two_slot
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock

open MeasureTheory

local notation "Ω" => EuclideanSpace ℝ (Fin 3)

/-- **A.e. statements about the one-particle variable pull back along a coordinate of a finite
product.**  `Measure.quasiMeasurePreserving_eval` plus `volume_pi`. -/
private theorem ae_eval_volume_pi {N : ℕ} (i : Fin N) {P : Ω → Prop}
    (h : ∀ᵐ a ∂(volume : Measure Ω), P a) :
    ∀ᵐ x ∂(volume : Measure (Fin N → Ω)), P (x i) := by
  rw [MeasureTheory.volume_pi]
  exact (Measure.quasiMeasurePreserving_eval (μ := fun _ : Fin N => (volume : Measure Ω)) i).ae h

/-- **The two-slot `cIPn`-pairing, with the slot modes replaced by their pinned representatives.**

This is `Work.BoseBoxFock.cIPn_boxSlotOf_two_slot` (the triple-integral form of the pairing of a
distinct-slot composition) with the superposition `η_w = Σ_l w_l·e_l = Work.BoseDict.etaOf e w`
replaced, in each of the four places it occurs, by an a.e.-equal given function `W`:

    `cIPn d Θ (boxSlotOf e w₁ v₁ i (boxSlotOf e w₂ v₂ j Θ))`
      `= ∫_x ∫_s ∫_u conj(Θ x)·W₁(x i)·conj(V₁ s)·W₂(x j)·conj(V₂ u)·Θ(x[i↦s][j↦u])`

whenever `η_{w₁} =ᵐ W₁`, `η_{v₁} =ᵐ V₁`, `η_{w₂} =ᵐ W₂`, `η_{v₂} =ᵐ V₂` (a.e. for the Lebesgue
measure on `ℝ³`).

It is the step that inserts the three *pinning* facts of the honest mode bundle into the row
estimates — in the cubic `Q̃₃` row, with the weights `w₁ = evec0`, `v₁ = f (s−k)`, `w₂ = g s`,
`v₂ = f k`, the pinned representatives are `c·thetaFun ℓ`, `ℓ^{-3/2}qVec(ℓ,k)`,
`ℓ^{-3/2}thetaExp(ℓ,s)`, `ℓ^{-3/2}qVec(ℓ,k')` (the pin `e 0 =ᵐ c·thetaFun` of `e0_prop_theta`,
`Work.BoseBoxFock.qVec_eq_etaOf_of_pairing`, `Work.BoseBoxFock.thetaExp_eq_etaOf_of_pairing`, all
at the box side `ℓ = ellH v μ`) — and it is what turns the *mode* sums of `potCubic` into sums over
the explicit functions `qVec`, `thetaExp`, `thetaFun`, i.e. into the shape to which the frame
identity (`Work.BoseBoxFock.latSampling_pair` / `…latSampling_one` / `…latSampling_decay`) applies.

The proof is the a.e. substitution in the three nested integrals: the equality
`η_w(x i) =ᵐ W(x i)` pulls back along the coordinate projections `(x,s,u) ↦ x i`, `… ↦ s`,
`… ↦ x j`, `… ↦ u` (`QuasiMeasurePreserving.ae_eq_comp`; the pushforward of the product volume
along a coordinate projection is a scalar multiple of the Lebesgue measure, so null sets pull back
to null sets), and `MeasureTheory.integral_congr_ae` finishes.  The five bundle hypotheses are those
of the base lemma; they are not used by the identity itself. -/
theorem cIPn_boxSlotOf_two_slot_congr {m d : ℕ} {ℓ : ℝ}
    {e : Fin m → EuclideanSpace ℝ (Fin 3) → ℂ}
    (w₁ v₁ w₂ v₂ : Fin m → ℝ) (W₁ V₁ W₂ V₂ : EuclideanSpace ℝ (Fin 3) → ℂ)
    (i j : Fin d) (hij : i ≠ j) (Θ : (Fin d → EuclideanSpace ℝ (Fin 3)) → ℂ)
    (h₁ : Work.BoseDict.etaOf e w₁ =ᵐ[MeasureTheory.volume] W₁)
    (h₂ : Work.BoseDict.etaOf e v₁ =ᵐ[MeasureTheory.volume] V₁)
    (h₃ : Work.BoseDict.etaOf e w₂ =ᵐ[MeasureTheory.volume] W₂)
    (h₄ : Work.BoseDict.etaOf e v₂ =ᵐ[MeasureTheory.volume] V₂)
    (hmeas : ∀ l, Measurable (e l))
    (hbdd : ∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (hΘm : Measurable Θ) (hΘb : ∃ C : ℝ, ∀ x, ‖Θ x‖ ≤ C) :
    Work.BoseDict.cIPn d Θ
        (Work.BoseDict.boxSlotOf e w₁ v₁ i (Work.BoseDict.boxSlotOf e w₂ v₂ j Θ))
      = ∫ x : (Fin d → EuclideanSpace ℝ (Fin 3)),
          ∫ s : EuclideanSpace ℝ (Fin 3),
            ∫ u : EuclideanSpace ℝ (Fin 3),
              (starRingEnd ℂ) (Θ x) * W₁ (x i) * (starRingEnd ℂ) (V₁ s) * W₂ (x j)
                * (starRingEnd ℂ) (V₂ u) * Θ (Function.update (Function.update x i s) j u) := by
  -- The base lemma, in the `η_w`-form.
  rw [cIPn_boxSlotOf_two_slot hmeas hbdd hsupp w₁ v₁ w₂ v₂ i j hij Θ hΘm hΘb]
  -- The four substitutions, each pulled back along the coordinate it lives on.
  have hx₁ : ∀ᵐ x ∂(volume : Measure (Fin d → Ω)), Work.BoseDict.etaOf e w₁ (x i) = W₁ (x i) :=
    ae_eval_volume_pi i h₁
  have hx₂ : ∀ᵐ x ∂(volume : Measure (Fin d → Ω)), Work.BoseDict.etaOf e w₂ (x j) = W₂ (x j) :=
    ae_eval_volume_pi j h₃
  refine integral_congr_ae ?_
  filter_upwards [hx₁, hx₂] with x hx₁ hx₂
  refine integral_congr_ae ?_
  filter_upwards [h₂] with s hs
  refine integral_congr_ae ?_
  filter_upwards [h₄] with u hu
  rw [hx₁, hx₂, hs, hu]

end Work.BoseBoxFock
