import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.AngSecond.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Integrability of the `σ_η`-weighted slice mass on `(1,∞)`

At level `0` the `H^k`-integrand of `Work.Spaces.HkMem α 0 F` collapses to the single square

    `HkIntegrand α 0 F z θ = (F z θ · w z / sin(2θ)^{η/2})²`,

which on the angular interval is *literally* the weighted slice mass of `F`,

    `HkIntegrand α 0 F z θ = w z² · ((F z θ)² · sin(2θ)^{-η})`   (`AngSecond.sq_mul_W`).

Hence, for `z ∈ (1,∞)` (where `w z = (1+z)²/z² ≥ 1`), the honest `θ`-slice

    `z ↦ ∫_θ (F z θ)² sin(2θ)^{-η}`

is the slice mass of the `H^k`-integrand divided by `w z²`, and `HkMem α 0 F` says exactly that
the latter is integrable on `Iz ⊇ (1,∞)`.  Dividing by `w z² ≥ 1` cannot destroy integrability, so
the `σ_η`-weighted slice mass is integrable on `(1,∞)`.

The only two things that have to be checked besides the pointwise identity are (a) the measurability
of `z ↦ ∫_θ (F z θ)² sin(2θ)^{-η}` on `(1,∞)` — which is *not* part of `HkMem`, but follows from
the identity above and the a.e. strong measurability of the (integrable) `Iθ`-integral `h`, and
(b) the pointwise bound `‖G z‖ ≤ h z`, i.e. nonnegativity of the slice mass and `w z² ≥ 1`.
-/

namespace Work.FTS.PhiStar.Honesty

open MeasureTheory Filter

/-- At `k = 0` the `H^k`-integrand collapses to a single square: the `D_z`-sum has the one term
`i = 0` and the mixed double sum is empty. -/
private lemma HkIntegrand_zero_eq (α : ℝ) (F : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α 0 F z θ
      = (F z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
  simp [Work.Spaces.HkIntegrand]

/-- On `[1,∞)` the radial weight is at least `1`: `w z = ((1+z)/z)² ≥ 1`. -/
private lemma one_le_w_sq {z : ℝ} (hz : 1 ≤ z) : 1 ≤ (Work.Spaces.w z) ^ 2 := by
  have h1 : 1 ≤ Work.Spaces.w z := by
    change 1 ≤ (1 + z) ^ 2 / z ^ 2
    rw [one_le_div (by positivity : (0 : ℝ) < z ^ 2)]
    nlinarith [hz]
  nlinarith [h1]

theorem integrableOn_sliceMass_Ioi_one_of_HkMem {α : ℝ} {F : ℝ → ℝ → ℝ}
    (hF : Work.Spaces.HkMem α 0 F) :
    MeasureTheory.IntegrableOn
      (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
        (F z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) (Set.Ioi 1) := by
  classical
  -- The `σ_η`-weighted slice mass `G` and the `H^k`-slice mass `h`.
  set G : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ,
        (F z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) with hG
  set h : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 F z θ with hh
  set W2 : ℝ → ℝ := fun z => (Work.Spaces.w z) ^ 2 with hW2
  have hIθ : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  -- The two integrands agree on the angular interval, up to the factor `w z²`.
  have hpt : ∀ z θ, θ ∈ Work.Spaces.Iθ →
      Work.Spaces.HkIntegrand α 0 F z θ
        = (Work.Spaces.w z) ^ 2
          * ((F z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by
    intro z θ hθ
    rw [HkIntegrand_zero_eq α F z θ, Work.FTS.EllipticEst.AngSecond.sq_mul_W F hθ]
    simp only [Work.FTS.EllipticEst.AngSecond.w2, Work.FTS.EllipticEst.AngSecond.sig, sq]
    ring
  -- Hence the slice identity `h z = w z² · G z`.
  have hslice : ∀ z, h z = W2 z * G z := by
    intro z
    simp only [hh, hG, hW2]
    rw [show (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 F z θ)
        = ∫ θ in Work.Spaces.Iθ, (Work.Spaces.w z) ^ 2
            * ((F z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) from
      setIntegral_congr_fun hIθ (fun θ hθ => hpt z θ hθ)]
    rw [MeasureTheory.integral_const_mul]
  -- `h` is integrable on `(1,∞)`, being the `H^k`-outer integral restricted to a subset of `Iz`.
  have hInt_h : IntegrableOn h (Set.Ioi 1) := by
    exact hF.2.mono_set (show Set.Ioi 1 ⊆ Work.Spaces.Iz from
      fun z hz => (le_trans (by norm_num) (le_of_lt hz) : (0 : ℝ) ≤ z))
  -- Measurability of the radial factor `w z²`.
  have hmeas_w : Measurable Work.Spaces.w := by
    change Measurable (fun z : ℝ => (1 + z) ^ 2 / z ^ 2)
    fun_prop
  have hmeasW : AEStronglyMeasurable W2 (volume.restrict (Set.Ioi 1)) := by
    have : Measurable W2 := by
      simpa only [hW2] using hmeas_w.pow_const 2
    exact this.aestronglyMeasurable
  -- Measurability of `G` on `(1,∞)`: it agrees there with `h / w z²`.
  have hmeasG : AEStronglyMeasurable G (volume.restrict (Set.Ioi 1)) := by
    have hd : AEMeasurable (fun z => h z / W2 z) (volume.restrict (Set.Ioi 1)) :=
      hInt_h.aemeasurable.div hmeasW.aemeasurable
    refine hd.aestronglyMeasurable.congr ?_
    exact ae_restrict_of_forall_mem measurableSet_Ioi fun z hz => by
      have hz1 : (1 : ℝ) ≤ z := le_of_lt hz
      have hw2 : W2 z ≠ 0 := by
        have := one_le_w_sq hz1
        linarith
      change h z / W2 z = G z
      rw [hslice z]
      field_simp
  -- The pointwise domination `‖G z‖ ≤ h z` on `(1,∞)`, since `w z² ≥ 1` and `G z ≥ 0`.
  have hbound : ∀ᵐ z ∂(volume.restrict (Set.Ioi 1)), ‖G z‖ ≤ h z := by
    rw [ae_restrict_iff' measurableSet_Ioi]
    refine Eventually.of_forall fun z hz => ?_
    have hz1 : (1 : ℝ) ≤ z := le_of_lt hz
    have hw2 : 1 ≤ W2 z := one_le_w_sq hz1
    have hgnn : 0 ≤ G z := by
      show 0 ≤ ∫ θ in Work.Spaces.Iθ,
        (F z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
      exact setIntegral_nonneg hIθ fun θ hθ => mul_nonneg (sq_nonneg _)
        (Real.rpow_nonneg (Work.FTS.EllipticEst.AngSecond.sin_two_nonneg hθ) _)
    have hhnn : 0 ≤ h z := by
      show 0 ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 F z θ
      exact setIntegral_nonneg hIθ fun θ _ => Work.Spaces.HkIntegrand_nonneg α 0 F z θ
    have hGeq : G z = h z / W2 z := by
      have hz0 : W2 z ≠ 0 := by linarith
      rw [hslice z, mul_div_cancel_left₀ _ hz0]
    rw [Real.norm_eq_abs, abs_of_nonneg hgnn, hGeq]
    exact div_le_self hhnn hw2
  exact Integrable.mono' hInt_h hmeasG hbound

end Work.FTS.PhiStar.Honesty
