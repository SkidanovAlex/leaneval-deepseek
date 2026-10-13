import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.Spaces.sin_two_rpow

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.H2W

/-!
## Elementary facts about the angular weight `sEta θ = sin(2θ)^{-η}`

`sEta` is the `i = 0` (purely radial) angular weight of the `ℋ^k` norm of the Elgindi project,
`Work.FTS.EllipticEst.sEta θ = (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))` with
`η = 99/100`.  On the angular interval `Iθ = [0, π/2]` it is a nonnegative function which is
integrable with a fixed universal bound on its integral (`10^4`, which is in fact sharp:
`100 / (1 - η) = 10^4`), equals at least `1` on the open interval `(0, π/2)`, and is continuous
there.  These are the facts needed whenever one compares the weighted slice functional with a
plain slice integral.
-/

/-- `sEta` is nonnegative on the angular interval `Iθ = [0, π/2]`: there `2θ ∈ [0, π]`, so
`sin(2θ) ≥ 0`, and a nonnegative base has a nonnegative real power. -/
theorem sEta_nonneg_of_mem_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Work.FTS.EllipticEst.sEta θ := by
  rw [Work.FTS.EllipticEst.sEta]
  refine Real.rpow_nonneg ?_ _
  refine Real.sin_nonneg_of_mem_Icc ⟨?_, ?_⟩
  · linarith [hθ.1]
  · have := Real.pi_pos; linarith [hθ.2]

/-- `1 ≤ sEta θ` on the open interval `(0, π/2)`: there `0 < sin(2θ) ≤ 1` and the exponent
`-η` is negative, so `sin(2θ)^{-η} ≥ 1`. -/
theorem one_le_sEta {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    1 ≤ Work.FTS.EllipticEst.sEta θ := by
  have h0 : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hle1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have h := Real.rpow_le_rpow_of_exponent_ge h0 hle1
    (show -(Work.Spaces.eta) ≤ (0 : ℝ) by have := Work.Spaces.eta_pos; linarith)
  simpa [Work.FTS.EllipticEst.sEta, Real.rpow_zero] using h

/-- `sEta` is continuous at every point of the open interval `(0, π/2)`, where its base
`sin(2θ)` is strictly positive. -/
theorem continuousAt_sEta {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    ContinuousAt Work.FTS.EllipticEst.sEta θ := by
  have h0 : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hcont : ContinuousAt (fun θ : ℝ => Real.sin (2 * θ)) θ :=
    Real.continuous_sin.continuousAt.comp (continuous_const.mul continuous_id).continuousAt
  have h := ContinuousAt.rpow hcont
    (continuousAt_const : ContinuousAt (fun _ : ℝ => -(Work.Spaces.eta)) θ)
    (Or.inl (ne_of_gt h0))
  change ContinuousAt (fun t : ℝ => Real.sin (2 * t) ^ (-(Work.Spaces.eta))) θ
  exact h

/-- Integrability of `sEta` on `Iθ`, with the universal bound `∫_{Iθ} sEta ≤ 10^4` on its
integral.  Both come from `Work.Spaces.sin_two_rpow` at the exponent `p = -η ∈ (-1, 0)`:
`100 / (1 - η) = 10^4`, so the stated constant is exactly the one produced by the general
β-integral estimate. -/
theorem integrableOn_sEta_and_integral_le :
    MeasureTheory.IntegrableOn (fun θ => Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ ∧
      (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.sEta θ) ≤ 10 ^ 4 := by
  have hmain := Work.Spaces.sin_two_rpow (-(Work.Spaces.eta))
    (by norm_num [Work.Spaces.eta]) (by norm_num [Work.Spaces.eta])
  refine ⟨hmain.1, ?_⟩
  calc ∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.sEta θ
      = ∫ θ in Work.Spaces.Iθ, Real.sin (2 * θ) ^ (-(Work.Spaces.eta)) := rfl
    _ ≤ 100 / (-(Work.Spaces.eta) + 1) := hmain.2
    _ = 10 ^ 4 := by norm_num [Work.Spaces.eta]

theorem SliceEtaFacts :
    MeasureTheory.IntegrableOn (fun θ => Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ ∧
      (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.sEta θ) ≤ 10 ^ 4 ∧
      (∀ θ ∈ Set.Ioo 0 (Real.pi / 2), 1 ≤ Work.FTS.EllipticEst.sEta θ) ∧
      (∀ θ ∈ Work.Spaces.Iθ, 0 ≤ Work.FTS.EllipticEst.sEta θ) ∧
      (∀ θ ∈ Set.Ioo 0 (Real.pi / 2), ContinuousAt Work.FTS.EllipticEst.sEta θ) :=
  ⟨integrableOn_sEta_and_integral_le.1, integrableOn_sEta_and_integral_le.2,
    fun _ hθ => one_le_sEta hθ, fun _ hθ => sEta_nonneg_of_mem_Iθ hθ,
    fun _ hθ => continuousAt_sEta hθ⟩

end Work.FTS.EllipticEst.H2W
