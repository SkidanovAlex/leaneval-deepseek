/-
# `Work.FTS.RegPkgGal.Der.L12densAngIntegralHolder` — the angular integral of `L₁₂` is `α`-Hölder
in the radial variable

The angular density of the fundamental model is

  `L12dens K f s = ∫_{θ∈Iθ} K(θ)·f(s,θ)/s`   (`K(θ) = 3 sin θ cos²θ`),

so the *undivided* angular integral `A(s) := ∫_{θ∈Iθ} K(θ)·F s θ τ` is the numerator of the
density.  The requested lemma is that `s ↦ A(s)` is `α`-Hölder on `(0,∞)`, with the *explicit*
constant `N·∫|K|`: the modulus constant `N` of the `Jet` box times the total angular mass of the
*weight*, `∫_{Iθ} |K| = 1` (which is why no loss occurs — the sharp weight `|K|` is used, not the
constant `3` times the mass `π/2` of `Iθ`).

## The estimate

For `s, s' > 0`, `τ ∈ [0,S]`,

  `A(s) - A(s') = ∫_{θ∈Iθ} K(θ)·(F s θ τ - F s' θ τ) dθ`

(the two integrals exist because `θ ↦ K(θ)·F z θ τ` is continuous on the compact `Iθ`), and the
radial Hölder modulus of the `Jet` (`Jet.zmod`, available at `s, s' ≥ 0`, hence at `s, s' > 0`)
gives the pointwise bound

  `|K(θ)·(F s θ τ - F s' θ τ)| ≤ |K(θ)|·N·|s - s'|^α`.

Integrating against the sharp weight `|K|` gives

  `|A(s) - A(s')| ≤ (∫_{Iθ}|K|)·N·|s - s'|^α = (N·∫_{Iθ}|K|)·|s - s'|^α`,

which is the stated bound.  The only measure theory used is `norm_integral_le_integral_norm` +
`integral_mono_of_nonneg` on the finite measure `volume ↾ Iθ` together with the integrability of
the two slices and of the dominating function (continuity on the compact interval `Iθ`).

Note that `hα : 0 < α` is used only to obtain that the angular slices are continuous on `Iθ`
(`continuousOn_of_holder` from `L12fBasic`), hence `L¹`; the Hölder bound itself uses only
`Jet.zmod`, and `hN : 0 ≤ N` is not needed at all (the pointwise comparison and the final
rearrangement are sign-free) — it is kept because the statement is used in that form.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.RegPkgGal.Der.L12fDensDiff

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS.RegPkgGal.Der

set_option autoImplicit false
-- `hN : 0 ≤ N` is kept because the requested statement carries it, but the estimate is sign-free
-- and does not need it.
set_option linter.unusedVariables false

/-- `θ ↦ |K(θ)|` is continuous on `ℝ`, where `K(θ) = 3 sin θ cos²θ`. -/
theorem continuous_abs_K : Continuous (fun θ : ℝ => |Work.Spaces.K θ|) := continuous_K.abs

/-- `θ ↦ K(θ)·F z θ τ` is `L¹` on the angular interval `Iθ`, for `z ≥ 0` and `τ ∈ [0,S]`
(this is `integrableOn_K_mul_jet_slice` with the set written as `Work.Spaces.Iθ`). -/
theorem integrableOn_K_mul_jet_slice_Iθ {α S N : ℝ} {F : ℝ → ℝ → ℝ → ℝ}
    (hα : 0 < α) (hJ : Work.FTS.Regularity.Jet α S N F) {z τ : ℝ} (hz : 0 ≤ z)
    (hτ : τ ∈ Set.Icc 0 S) :
    IntegrableOn (fun θ => Work.Spaces.K θ * F z θ τ) Work.Spaces.Iθ := by
  have h : Set.Icc (0 : ℝ) (Real.pi / 2) = Work.Spaces.Iθ := rfl
  rw [← h]
  exact integrableOn_K_mul_jet_slice hα hJ hz hτ

/-- `θ ↦ |K θ|` is `L¹` on the angular interval `Iθ` (continuous on the compact `Iθ`, and the
interval has finite measure). -/
theorem integrableOn_abs_K :
    IntegrableOn (fun θ : ℝ => |Work.Spaces.K θ|) Work.Spaces.Iθ := by
  have h : Set.Icc (0 : ℝ) (Real.pi / 2) = Work.Spaces.Iθ := rfl
  rw [← h]
  exact continuous_abs_K.continuousOn.integrableOn_Icc

/-- **The angular integral of `L₁₂` is `α`-Hölder in the radial variable.**  For a `Jet` profile
`F` (bounded by `N` on `z ≥ 0`, `θ ∈ Iθ`, `τ ∈ [0,S]` and jointly `α`-Hölder there with constant
`N`), the map `s ↦ ∫_{Iθ} K(θ)·F s θ τ` is `α`-Hölder on `(0,∞)` with the explicit constant
`N·∫_{Iθ}|K|`, uniformly in `τ ∈ [0,S]`. -/
theorem L12densAngIntegralHolder {α S N : ℝ} {F : ℝ → ℝ → ℝ → ℝ}
    (hα : 0 < α) (hN : 0 ≤ N) (hJ : Work.FTS.Regularity.Jet α S N F) :
    ∀ τ ∈ Set.Icc 0 S, ∀ s ∈ Set.Ioi (0 : ℝ), ∀ s' ∈ Set.Ioi (0 : ℝ),
      |(∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * F s θ τ)
        - (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * F s' θ τ)|
      ≤ (N * (∫ θ in Work.Spaces.Iθ, |Work.Spaces.K θ|)) * |s - s'| ^ α := by
  intro τ hτ s hs s' hs'
  have hs0 : (0 : ℝ) ≤ s := le_of_lt hs
  have hs'0 : (0 : ℝ) ≤ s' := le_of_lt hs'
  -- integrability of the two angular slices (`K·F z · τ` is continuous on the compact `Iθ`)
  have hIntS : IntegrableOn (fun θ => Work.Spaces.K θ * F s θ τ) Work.Spaces.Iθ :=
    integrableOn_K_mul_jet_slice_Iθ hα hJ hs0 hτ
  have hIntS' : IntegrableOn (fun θ => Work.Spaces.K θ * F s' θ τ) Work.Spaces.Iθ :=
    integrableOn_K_mul_jet_slice_Iθ hα hJ hs'0 hτ
  -- integrability of the dominating function `|K|·(N·|s-s'|^α)`
  have hIntD : Integrable (fun θ : ℝ => |Work.Spaces.K θ| * (N * |s - s'| ^ α))
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    have h : Set.Icc (0 : ℝ) (Real.pi / 2) = Work.Spaces.Iθ := rfl
    rw [← h]
    exact (continuous_abs_K.continuousOn.mul continuousOn_const).integrableOn_Icc
  -- the pointwise bound of the difference of the integrands
  have hpt : ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.K θ * F s θ τ - Work.Spaces.K θ * F s' θ τ|
        ≤ |Work.Spaces.K θ| * (N * |s - s'| ^ α) := by
    intro θ hθ
    have hdiff : |F s θ τ - F s' θ τ| ≤ N * |s - s'| ^ α := hJ.zmod hs0 hs'0 hθ hτ
    have hre : Work.Spaces.K θ * F s θ τ - Work.Spaces.K θ * F s' θ τ
        = Work.Spaces.K θ * (F s θ τ - F s' θ τ) := by ring
    rw [hre, abs_mul]
    exact mul_le_mul_of_nonneg_left hdiff (abs_nonneg _)
  -- the difference of the two integrals is the integral of the difference
  have hsplit : |(∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * F s θ τ)
        - (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * F s' θ τ)|
      = |∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.K θ * F s θ τ - Work.Spaces.K θ * F s' θ τ)| := by
    rw [MeasureTheory.integral_sub hIntS hIntS']
  -- the norm of the integral is bounded by the integral of the norm
  have h1 : |∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.K θ * F s θ τ - Work.Spaces.K θ * F s' θ τ)|
      ≤ ∫ θ in Work.Spaces.Iθ,
        |Work.Spaces.K θ * F s θ τ - Work.Spaces.K θ * F s' θ τ| := by
    have hb := MeasureTheory.norm_integral_le_integral_norm
      (μ := MeasureTheory.volume.restrict Work.Spaces.Iθ)
      (fun θ => Work.Spaces.K θ * F s θ τ - Work.Spaces.K θ * F s' θ τ)
    simpa only [Real.norm_eq_abs] using hb
  -- the monotone integral bound, then the sharp weight integral
  have h2 : (∫ θ in Work.Spaces.Iθ,
        |Work.Spaces.K θ * F s θ τ - Work.Spaces.K θ * F s' θ τ|)
      ≤ ∫ θ in Work.Spaces.Iθ, |Work.Spaces.K θ| * (N * |s - s'| ^ α) :=
    MeasureTheory.integral_mono_of_nonneg
      (μ := MeasureTheory.volume.restrict Work.Spaces.Iθ)
      (Filter.Eventually.of_forall fun θ => abs_nonneg _) hIntD
      (by
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
        exact hpt θ hθ)
  have h3 : (∫ θ in Work.Spaces.Iθ, |Work.Spaces.K θ| * (N * |s - s'| ^ α))
      = (N * (∫ θ in Work.Spaces.Iθ, |Work.Spaces.K θ|)) * |s - s'| ^ α := by
    rw [MeasureTheory.integral_mul_const]
    ring
  rw [hsplit]
  exact le_trans h1 (le_trans h2 (le_of_eq h3))

end Work.FTS.RegPkgGal.Der
