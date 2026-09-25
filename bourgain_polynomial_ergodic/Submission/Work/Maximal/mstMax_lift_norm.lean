import Mathlib
import Submission.Work.BourgainPlan.Thm52.CircleLiftDefs

/-!
# The `ℓᵖ` norm of the fundamental-domain lift is the circle norm

For the fundamental-domain lift

`circleLift f x = if x ∈ Ioc (-1/2) (1/2] then f (-(x : Circ)) else 0`

of a circle function `f : Circ → ℂ` (`Circ = AddCircle 1`) we prove

`∫⁻ x : ℝ, ‖circleLift f x‖ₑ ^ p ∂volume = ∫⁻ ξ : Circ, ‖f ξ‖ₑ ^ p ∂haar`,

i.e. the `p`-th power of the `Lᵖ` norm is preserved by the lift.  No measurability
hypothesis on `f` is needed: the equality is a statement about the *measure* `volume` on
`Circ` being the pushforward of the Lebesgue measure of one period.

The proof has three ingredients.

* `MeasureTheory.lintegral_indicator` together with the two evaluation lemmas of
  `circleLift` turns the integral over `ℝ` into the integral over the fundamental domain
  `Ioc (-1/2) (1/2]`.
* `AddCircle.lintegral_preimage` (Mathlib, `MeasureTheory/Integral/...`, derived from
  `AddCircle.measurePreserving_mk`) is the *unrestricted* change-of-variables identity

  `∫⁻ a in Set.Ioc t (t + T), g ↑a = ∫⁻ b : AddCircle T, g b`

  for an **arbitrary** function `g : AddCircle T → ℝ≥0∞` — no measurability needed.  With
  `T = 1`, `t = -1/2` and `g ξ = ‖f (-ξ)‖ₑ ^ p` this identifies the integral over the
  fundamental domain with the integral over the circle of the reflected symbol.
* The reflection `ξ ↦ -ξ` of the circle preserves the Haar measure; since `Neg.neg` is a
  `MeasurableEmbedding` (`measurableEmbedding_neg`) with `map Neg.neg volume = volume`
  (`Measure.map_neg_eq_self`), `MeasurePreserving.lintegral_comp_emb` gives the identity

  `∫⁻ ξ, ‖f (-ξ)‖ₑ ^ p ∂volume = ∫⁻ ξ, ‖f ξ‖ₑ ^ p ∂volume`

  again for an arbitrary `f`.  Finally `AddCircle.volume_eq_smul_haarAddCircle` at `T = 1`
  and `ENNReal.ofReal_one` identify the normalised `volume` with `AddCircle.haarAddCircle`.
-/

namespace Work.Maximal

open MeasureTheory

local notation "Circ" => Work.BourgainPlan.IonescuWainger.Circle

/-- The `p`-th power of the `Lᵖ` norm is invariant under the fundamental-domain lift: the
Lebesgue integral over `ℝ` of `‖circleLift f‖ₑ ^ p` is the Haar integral over the circle of
`‖f‖ₑ ^ p`.  (Here `hp : 0 < p` is only needed for the value `0 ^ p = 0` at the points where
the lift vanishes; no measurability of `f` is required.) -/
theorem mstMax_lift_norm (p : ℝ) (hp : 0 < p)
    (f : Work.BourgainPlan.IonescuWainger.Circle → ℂ) :
    ∫⁻ x : ℝ, ‖Work.BourgainPlan.Thm52.circleLift f x‖ₑ ^ p ∂MeasureTheory.volume
      = ∫⁻ ξ : Work.BourgainPlan.IonescuWainger.Circle, ‖f ξ‖ₑ ^ p
          ∂(AddCircle.haarAddCircle (T := 1)) := by
  -- Step 1: the lift vanishes off the fundamental domain `Ioc (-1/2) (1/2]`.
  have h1 : ∫⁻ x : ℝ, ‖Work.BourgainPlan.Thm52.circleLift f x‖ₑ ^ p ∂MeasureTheory.volume
      = ∫⁻ x in Set.Ioc (-(1/2:ℝ)) (1/2), ‖f (-(x : Circ))‖ₑ ^ p ∂MeasureTheory.volume := by
    rw [← lintegral_indicator measurableSet_Ioc (fun y : ℝ => ‖f (-(y : Circ))‖ₑ ^ p)]
    refine lintegral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    change ‖Work.BourgainPlan.Thm52.circleLift f x‖ₑ ^ p
      = (Set.Ioc (-(1/2:ℝ)) (1/2)).indicator (fun y : ℝ => ‖f (-(y : Circ))‖ₑ ^ p) x
    by_cases hx : x ∈ Set.Ioc (-(1/2:ℝ)) (1/2)
    · rw [Set.indicator_of_mem hx, Work.BourgainPlan.Thm52.circleLift_of_mem hx]
    · rw [Set.indicator_of_notMem hx, Work.BourgainPlan.Thm52.circleLift_of_notMem hx]
      rw [show ‖(0:ℂ)‖ₑ = 0 by simp, ENNReal.zero_rpow_of_pos hp]
  -- Step 2: the fundamental domain is one period, so its Lebesgue integral is the Haar
  -- integral of the reflected symbol (`AddCircle.lintegral_preimage`, arbitrary integrand).
  have hpre := AddCircle.lintegral_preimage (1:ℝ) (-(1/2))
      (fun ξ : Circ => ‖f (-ξ)‖ₑ ^ p)
  rw [show (-(1/2:ℝ)) + 1 = (1/2) by norm_num] at hpre
  -- Step 3: the reflection `ξ ↦ -ξ` of the circle preserves the measure; `Neg.neg` is a
  -- measurable embedding, so the identity holds for the arbitrary integrand `‖f ·‖ₑ ^ p`.
  have h3 : ∫⁻ ξ : Circ, ‖f (-ξ)‖ₑ ^ p ∂MeasureTheory.volume
      = ∫⁻ ξ : Circ, ‖f ξ‖ₑ ^ p ∂MeasureTheory.volume :=
    MeasureTheory.MeasurePreserving.lintegral_comp_emb
      (⟨measurable_neg, MeasureTheory.Measure.map_neg_eq_self (MeasureTheory.volume)⟩ :
        MeasureTheory.MeasurePreserving (Neg.neg : Circ → Circ)
          MeasureTheory.volume MeasureTheory.volume)
      measurableEmbedding_neg (fun ξ : Circ => ‖f ξ‖ₑ ^ p)
  -- Step 4: `volume` on `AddCircle 1` is the normalised Haar measure.
  have hvol : (MeasureTheory.volume : MeasureTheory.Measure Circ) =
      AddCircle.haarAddCircle (T := 1) := by
    rw [AddCircle.volume_eq_smul_haarAddCircle (T := 1)]
    simp
  rw [h1, hpre, h3, hvol]

end Work.Maximal
