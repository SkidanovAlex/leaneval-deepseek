import Mathlib
import Submission.Work.BourgainPlan.Oscillation.lacunary_defs
import Submission.Work.BourgainPlan.Oscillation.lacunary_truncated_maximal_l2
import Submission.Work.BourgainPlan.Oscillation.lacScale_error_tsum_le

/-!
# The two cut families of the `t ↔ ⌊ρ^i⌋` scaling comparison

For the oscillation-at-lacunary-scales argument one needs to compare the family of sharp frequency
cuts at the shifted radii `t · ρ^{-i}` (a single positive real `t`, the radii an exact geometric
progression) with the family at the *floored* radii `t / ⌊ρ^i⌋` (the radii dictated by the lacunary
scale `⌊ρ^i⌋ = lacScale ρ i`).

* `cutFam r f T shift` is the general sharp-cut family: its `i`-th element is the Fourier integral
  `x ↦ ∫_0^1 (r θ · 1_{θ ≤ shift i}) · (Σ_{n ∈ T} f n e(nθ)) · e(-2πi x θ) dθ`.
  The *shifted* family is `cutFam r f T (fun i => t * ρ^{-i})`, and the *floored* family (the one
  appearing in the target) is `cutFam r f T (fun i => t / ⌊ρ^i⌋)`.
* `gapFam ρ t r f T` is the difference of the two, whose `i`-th multiplier is the indicator of the
  annulus `(t ρ^{-i}, t / ⌊ρ^i⌋]`: the "flooring gap" of the lacunary scale. Only `O_ρ(1)` of these
  annuli meet at any frequency (`gap_count`), which is what makes this error term square-summable.
-/

namespace Work.BourgainPlan.Oscillation.Lacunary

open Finset MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

/-- The general sharp-cut family at the radii `shift i`. -/
def cutFam (r : ℝ → ℂ) (f : ℤ → ℂ) (T : Finset ℤ) (shift : ℕ → ℝ) (i : ℕ) (x : ℤ) : ℂ :=
  ∫ θ in (0:ℝ)..1,
    (r θ * (if θ ≤ shift i then (1:ℂ) else 0)) *
    (∑ n ∈ T, f n * Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * (θ : ℂ))) *
    Complex.exp (-(2 * Real.pi * Complex.I * ((x : ℤ) : ℂ) * (θ : ℂ)))

/-- The **flooring-gap family**: the difference between the cut at `t / ⌊ρ^i⌋` and the cut at
`t ρ^{-i}`; its `i`-th symbol is the indicator of the annulus `(t ρ^{-i}, t / ⌊ρ^i⌋]`. -/
def gapFam (ρ t : ℝ) (r : ℝ → ℂ) (f : ℤ → ℂ) (T : Finset ℤ) (i : ℕ) (x : ℤ) : ℂ :=
  ∫ θ in (0:ℝ)..1,
    (r θ * (if t * ρ ^ (-(i:ℤ)) < θ ∧
        θ ≤ t / (Work.BourgainPlan.Oscillation.lacScale ρ i : ℝ) then (1:ℂ) else 0)) *
    (∑ n ∈ T, f n * Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * (θ : ℂ))) *
    Complex.exp (-(2 * Real.pi * Complex.I * ((x : ℤ) : ℂ) * (θ : ℂ)))

/-! ## Elementary facts

The pointwise splitting of a cut into a smaller cut and an annulus, the corresponding splitting of
the Fourier integrals, and the comparison of the shifted and the floored radius. -/

/-- Splitting a cut: for `d ≤ c` the sharp cut at `c` is the cut at `d` plus the annulus
indicator `1_{(d, c]}`. -/
lemma cut_split_pointwise (r : ℝ → ℂ) (d c θ : ℝ) (h : d ≤ c) :
    r θ * (if θ ≤ d then (1:ℂ) else 0) + r θ * (if d < θ ∧ θ ≤ c then (1:ℂ) else 0)
      = r θ * (if θ ≤ c then (1:ℂ) else 0) := by
  by_cases h1 : θ ≤ d
  · have h2 : θ ≤ c := le_trans h1 h
    have h3 : ¬ (d < θ ∧ θ ≤ c) := fun hh => absurd hh.1 (not_lt.mpr h1)
    rw [if_pos h1, if_pos h2, if_neg h3]; ring
  · have h1' : d < θ := lt_of_not_ge h1
    by_cases h2 : θ ≤ c
    · rw [if_neg h1, if_pos ⟨h1', h2⟩, if_pos h2]; ring
    · have h3 : ¬ (d < θ ∧ θ ≤ c) := fun hh => absurd hh.2 h2
      rw [if_neg h1, if_neg h3, if_neg h2]; ring

/-- Additivity of the interval integral over `(0,1]` for integrands which agree with a sum of two
bounded measurable functions. -/
lemma intervalIntegral_split (F G H : ℝ → ℂ) (hF : Measurable F) (hG : Measurable G)
    (CF CG : ℝ) (hFb : ∀ θ, ‖F θ‖ ≤ CF) (hGb : ∀ θ, ‖G θ‖ ≤ CG)
    (hFG : ∀ θ, H θ = F θ + G θ) :
    (∫ θ in (0:ℝ)..1, H θ) = (∫ θ in (0:ℝ)..1, F θ) + (∫ θ in (0:ℝ)..1, G θ) := by
  have hH : (∫ θ in (0:ℝ)..1, H θ) = ∫ θ in (0:ℝ)..1, (F θ + G θ) :=
    intervalIntegral.integral_congr (fun θ _ => hFG θ)
  rw [hH, intervalIntegral_eq_mu01, intervalIntegral_eq_mu01, intervalIntegral_eq_mu01]
  exact integral_add (integrable_Ioc_of_bound hF hFb) (integrable_Ioc_of_bound hG hGb)

/-- The shifted lacunary radius never exceeds the floored one. -/
lemma mul_zpow_le_div_lacScale {ρ t : ℝ} (hρ : 1 ≤ ρ) (ht : 0 ≤ t) (i : ℕ) :
    t * ρ ^ (-(i:ℤ)) ≤ t / (Work.BourgainPlan.Oscillation.lacScale ρ i : ℝ) := by
  have hρ0 : 0 < ρ := lt_of_lt_of_le zero_lt_one hρ
  have hNpos : (0:ℝ) < (Work.BourgainPlan.Oscillation.lacScale ρ i : ℝ) := by
    exact_mod_cast one_le_lacScale ρ hρ i
  have hpipos : (0:ℝ) < ρ ^ i := pow_pos hρ0 i
  have hNle : (Work.BourgainPlan.Oscillation.lacScale ρ i : ℝ) ≤ ρ ^ i :=
    lacScale_le_pow ρ hρ0.le i
  have hz : ρ ^ (-(i:ℤ)) = (ρ ^ i)⁻¹ := by
    rw [zpow_neg, zpow_natCast]
  have hinv : ρ ^ (-(i:ℤ)) ≤ ((Work.BourgainPlan.Oscillation.lacScale ρ i : ℝ))⁻¹ := by
    rw [hz]
    exact (inv_le_inv₀ hpipos hNpos).mpr hNle
  calc t * ρ ^ (-(i:ℤ)) ≤ t * ((Work.BourgainPlan.Oscillation.lacScale ρ i : ℝ))⁻¹ :=
        mul_le_mul_of_nonneg_left hinv ht
    _ = t / (Work.BourgainPlan.Oscillation.lacScale ρ i : ℝ) := by rw [div_eq_mul_inv]

end

end Work.BourgainPlan.Oscillation.Lacunary
