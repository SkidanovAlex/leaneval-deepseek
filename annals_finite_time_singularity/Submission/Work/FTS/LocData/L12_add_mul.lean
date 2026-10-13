/-
# `Work.FTS.LocData.L12_add_mul` — linearity of `L₁₂` on the localised data

The operator of the fundamental model,

  `L₁₂(f)(z) = ∫_z^∞ ∫_0^{π/2} K(θ) f(s,θ)/s dθ ds`   (`K(θ) = 3 sin θ cos²θ`),

is an *integral*, so it is additive and homogeneous in the profile `f` — this is the
`L₁₂`-linearity on which the localisation chapter runs (it lets one pass between the localised
profile `locData = F_*·χ(z/L) + β h` and its pieces, exactly as `Work.Stability.L12Add` does for
`F_* + g` in the global chapter).

The two identities are proved at the level of the **angular density**
`L12dens K f s = ∫_0^{π/2} K(θ) f(s,θ)/s dθ` (`L12dens_add_of_integrableOn`,
`L12dens_const_mul`), and then integrated over `(z,∞)`:

* additivity of the density needs the two `θ`-slices to be integrable on the compact interval
  `Iθ = [0,π/2]` (`MeasureTheory.integral_add`); the outer step needs the two densities to be
  integrable on `(z,∞)`;
* homogeneity in the constant `c` is *unconditional* at the level of the density
  (`MeasureTheory.integral_const_mul`, which Mathlib states with no integrability hypothesis),
  and correspondingly the outer step needs nothing beyond the density being equal to the scaled
  one pointwise.

These are the hypotheses `h1`–`h4` of the statement; no smoothness is used, only integrability.
-/
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.LocData.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.LocData

set_option autoImplicit false

/-- **Additivity of the angular density of `L₁₂`.**  For an arbitrary angular profile `K`, if the
two `θ`-slices `θ ↦ K θ f(s,θ)/s` are integrable on `Iθ = [0,π/2]`, then the density of the sum
is the sum of the densities (the integrands are pointwise equal by distributivity). -/
theorem L12dens_add_of_integrableOn (K : ℝ → ℝ) {a b : ℝ → ℝ → ℝ} {s : ℝ}
    (ha : MeasureTheory.IntegrableOn (fun θ => K θ * a s θ / s) Work.Spaces.Iθ)
    (hb : MeasureTheory.IntegrableOn (fun θ => K θ * b s θ / s) Work.Spaces.Iθ) :
    Work.FM.L12dens K (fun z θ => a z θ + b z θ) s
      = Work.FM.L12dens K a s + Work.FM.L12dens K b s := by
  have hpt : (fun θ => K θ * (a s θ + b s θ) / s)
      = fun θ => K θ * a s θ / s + K θ * b s θ / s := by
    funext θ
    ring
  simp only [Work.FM.L12dens]
  rw [hpt]
  exact MeasureTheory.integral_add ha hb

/-- **Homogeneity of the angular density of `L₁₂`.**  For an arbitrary angular profile `K` and
constant `c` the density of `c·a` is `c` times the density of `a`, with no integrability
hypothesis at all: both sides are the integral of the pointwise-equal integrands, and
`MeasureTheory.integral_const_mul` is unconditional. -/
theorem L12dens_const_mul (K : ℝ → ℝ) (c : ℝ) (a : ℝ → ℝ → ℝ) (s : ℝ) :
    Work.FM.L12dens K (fun z θ => c * a z θ) s = c * Work.FM.L12dens K a s := by
  have hpt : (fun θ => K θ * (c * a s θ) / s) = fun θ => c * (K θ * a s θ / s) := by
    funext θ
    ring
  simp only [Work.FM.L12dens]
  rw [hpt]
  exact MeasureTheory.integral_const_mul c _

/-- **Linearity of `L₁₂` on the localised data:** it is additive, and homogeneous in a constant.

`h1`, `h2` are the integrability of the two angular slices on `Iθ` for every `s > z` (this is
what makes the inner integrals split), and `h3`, `h4` the integrability of the two densities on
`(z,∞)` (this is what makes the outer integrals split; the additive identity of the densities
holds merely pointwise on `(z,∞)`, no integrability of the density of the sum is needed).  The
homogeneity statement needs no hypothesis beyond `h1`'s shape of the integrand. -/
theorem L12_add_mul (c : ℝ) {a b : ℝ → ℝ → ℝ} {z : ℝ}
    (h1 : ∀ s ∈ Set.Ioi z, MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.K θ * a s θ / s) Work.Spaces.Iθ)
    (h2 : ∀ s ∈ Set.Ioi z, MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.K θ * b s θ / s) Work.Spaces.Iθ)
    (h3 : MeasureTheory.IntegrableOn (Work.FM.L12dens Work.Spaces.K a) (Set.Ioi z))
    (h4 : MeasureTheory.IntegrableOn (Work.FM.L12dens Work.Spaces.K b) (Set.Ioi z)) :
    Work.Construction.L12 (fun z θ => a z θ + b z θ) z
        = Work.Construction.L12 a z + Work.Construction.L12 b z ∧
      Work.Construction.L12 (fun z θ => c * a z θ) z = c * Work.Construction.L12 a z := by
  constructor
  · -- additivity: split the inner integral pointwise, then the outer one by integrability
    simp only [Work.Construction.L12, Work.FM.L12]
    rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
      (fun s hs => L12dens_add_of_integrableOn Work.Spaces.K (h1 s hs) (h2 s hs))]
    exact MeasureTheory.integral_add h3 h4
  · -- homogeneity: pull the constant out of the inner and then the outer integral
    simp only [Work.Construction.L12, Work.FM.L12]
    rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
      (fun s _ => L12dens_const_mul Work.Spaces.K c a s)]
    exact MeasureTheory.integral_const_mul c _

end Work.FTS.LocData
