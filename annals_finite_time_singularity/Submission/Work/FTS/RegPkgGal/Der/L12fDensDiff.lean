/-
# `Work.FTS.RegPkgGal.Der.L12fDensDiff` — the `τ`-Hölder modulus of the density of `L₁₂^K`

The angular density of the fundamental model is

  `L12dens K f s = ∫_0^{π/2} K(θ)·f(s,θ)/s dθ`   (`K(θ) = 3 sin θ cos²θ`),

and the requested lemma is the **time-Hölder continuity of this density in the strip time**, with
the *same* exponent `α` as the profile and a modulus which is *uniform in `s > 0`* — this is what
makes `L₁₂^K(g̃(·,·,τ))` a `Jet` in `τ` (the module `Der/jet_L12f`).

## The estimate

For `τ, τ' ∈ [0,S]` and `s > 0`,

  `L12dens K (gSlice F τ) s - L12dens K (gSlice F τ') s
     = ∫_0^{π/2} K(θ)·(F s θ τ - F s θ τ')/s dθ`,

so, with `|K θ| ≤ 3` on `Iθ` (`abs_K_le_three`) and the pointwise hypothesis

  `|F s θ τ - F s θ τ'| ≤ Nt·s·|τ - τ'|^α`   (`htau`),

the integrand is bounded by `3·Nt·|τ - τ'|^α` — **the factor `s` cancels** — and the angular mass
`π/2` gives

  `|…| ≤ 3·Nt·|τ - τ'|^α·(π/2) ≤ 6·Nt·|τ - τ'|^α`   (since `π < 4`).

The two ingredients that make the two integrals well-behaved (so that the difference of the
integrals may be turned into the integral of the difference) are:

* the angular slices `θ ↦ F s θ τ`, `θ ↦ F s θ τ'` are **continuous** on `Iθ`, because `Jet`
  carries the `θ`-Hölder modulus `N·|Δθ|^α` at fixed `(z,τ)` (`Jet.thmod`) and a Hölder modulus on
  a set implies continuity there (`continuousOn_of_holder`);
* `K` is continuous, so both integrands are continuous on the compact `Iθ`, hence integrable
  (`ContinuousOn.integrableOn_Icc`).

Only `hα : 0 < α` (for `continuousOn_of_holder`), `hJ.nonneg` (the modulus constant `N ≥ 0`) and
the *second* conjunct of `htau` are used; `Nt ≥ 0` (`htau.1`) enters the final arithmetic only
through the sign of the constant, so the estimate is also valid as stated when `Nt < 0` (the
right-hand side is then nonpositive, and the left-hand side is `0` because `htau.2` forces
`F s θ τ = F s θ τ'`).
-/
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.RegPkgGal.Der.L12fBasic

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

/-! ## Elementary angular facts -/

/-- `K(θ) = 3 sin θ cos²θ` is continuous on `ℝ`. -/
theorem continuous_K : Continuous (fun θ : ℝ => Work.Spaces.K θ) := by
  simp only [Work.Spaces.K]
  exact (continuous_const.mul Real.continuous_sin).mul (Real.continuous_cos.pow 2)

/-- **The angular slice of a `Jet` is continuous.**  For `z ≥ 0` and `τ ∈ [0,S]` the `θ`-Hölder
modulus of `Jet.thmod` makes `θ ↦ K(θ)·F z θ τ` continuous on `Iθ`. -/
theorem continuousOn_K_mul_jet_slice {α S N : ℝ} {F : ℝ → ℝ → ℝ → ℝ} (hα : 0 < α)
    (hJ : Work.FTS.Regularity.Jet α S N F) {z τ : ℝ} (hz : 0 ≤ z)
    (hτ : τ ∈ Set.Icc 0 S) :
    ContinuousOn (fun θ => Work.Spaces.K θ * F z θ τ) (Set.Icc 0 (Real.pi / 2)) :=
  continuous_K.continuousOn.mul
    (continuousOn_of_holder hJ.nonneg hα fun θ hθ θ' hθ' => by
      simpa using hJ.thmod hz hθ hθ' hτ)

/-- **The angular slice is integrable.**  A continuous function on the compact interval `Iθ` is
`L¹` for the Lebesgue measure; this is the integrability that lets the difference of the two
`L12dens`-integrals be written as the integral of the difference. -/
theorem integrableOn_K_mul_jet_slice {α S N : ℝ} {F : ℝ → ℝ → ℝ → ℝ} (hα : 0 < α)
    (hJ : Work.FTS.Regularity.Jet α S N F) {z τ : ℝ} (hz : 0 ≤ z)
    (hτ : τ ∈ Set.Icc 0 S) :
    IntegrableOn (fun θ => Work.Spaces.K θ * F z θ τ) (Set.Icc 0 (Real.pi / 2)) :=
  (continuousOn_K_mul_jet_slice hα hJ hz hτ).integrableOn_Icc

/-! ## The `τ`-modulus of the density -/

/-- **The time-Hölder modulus of the angular density of `L₁₂^K`.**  If the profile family `F` is a
`Jet` and its `τ`-increments obey the *uniform in `z`* bound `|ΔF| ≤ Nt·z·|Δτ|^α`, then the
density `s ↦ L12dens K (gSlice F τ) s` is `α`-Hölder in `τ` with the same modulus, uniformly in
`s > 0`:

  `|L12dens K (gSlice F τ) s - L12dens K (gSlice F τ') s| ≤ 6·Nt·|τ - τ'|^α`.

The proof uses only `|K| ≤ 3` on `Iθ` and the angular mass `π/2 < 2`. -/
theorem L12fDensDiff {α S N Nt : ℝ} {F : ℝ → ℝ → ℝ → ℝ}
    (hα : 0 < α)
    (hJ : Work.FTS.Regularity.Jet α S N F)
    (htau : 0 ≤ Nt ∧ ∀ τ ∈ Set.Icc 0 S, ∀ τ' ∈ Set.Icc 0 S, ∀ θ ∈ Work.Spaces.Iθ,
      ∀ z ∈ Set.Ici (0 : ℝ), |F z θ τ - F z θ τ'| ≤ Nt * z * |τ - τ'| ^ α) :
    ∀ τ ∈ Set.Icc 0 S, ∀ τ' ∈ Set.Icc 0 S, ∀ s : ℝ, 0 < s →
      |Work.FM.L12dens Work.Spaces.K (Work.FTS.Regularity.gSlice F τ) s
        - Work.FM.L12dens Work.Spaces.K (Work.FTS.Regularity.gSlice F τ') s|
      ≤ 6 * Nt * |τ - τ'| ^ α := by
  intro τ hτ τ' hτ' s hs
  have hs0 : (0 : ℝ) ≤ s := le_of_lt hs
  have hne : s ≠ 0 := ne_of_gt hs
  -- integrability of the two angular slices at the radial value `s > 0`
  have hIntτ : IntegrableOn (fun θ => Work.Spaces.K θ * F s θ τ) (Set.Icc 0 (Real.pi / 2)) :=
    integrableOn_K_mul_jet_slice hα hJ hs0 hτ
  have hIntτ' : IntegrableOn (fun θ => Work.Spaces.K θ * F s θ τ') (Set.Icc 0 (Real.pi / 2)) :=
    integrableOn_K_mul_jet_slice hα hJ hs0 hτ'
  -- the difference of the integrals is the integral of the difference, divided by `s`
  have hsplit : (∫ θ in Set.Icc 0 (Real.pi / 2), Work.Spaces.K θ * F s θ τ) / s
      - (∫ θ in Set.Icc 0 (Real.pi / 2), Work.Spaces.K θ * F s θ τ') / s
      = ∫ θ in Set.Icc 0 (Real.pi / 2),
          (Work.Spaces.K θ * F s θ τ - Work.Spaces.K θ * F s θ τ') / s := by
    rw [← sub_div, ← MeasureTheory.integral_sub hIntτ hIntτ', ← MeasureTheory.integral_div]
  -- unfold the density (`L12dens_eq`: the factor `1/s` may be pulled out of the integral)
  rw [Work.FM.L12dens_eq hne, Work.FM.L12dens_eq hne]
  simp only [Work.FTS.Regularity.gSlice_apply]
  rw [hsplit]
  -- pointwise bound: `|K θ| ≤ 3`, and the factor `s` cancels
  have hpt : ∀ θ ∈ Set.Icc 0 (Real.pi / 2),
      |(Work.Spaces.K θ * F s θ τ - Work.Spaces.K θ * F s θ τ') / s|
        ≤ 3 * (Nt * |τ - τ'| ^ α) := by
    intro θ hθ
    have h1 : |F s θ τ - F s θ τ'| ≤ Nt * s * |τ - τ'| ^ α :=
      htau.2 τ hτ τ' hτ' θ hθ s (le_of_lt hs)
    have hK : |Work.Spaces.K θ| ≤ 3 := abs_K_le_three hθ
    have hnum_eq : Work.Spaces.K θ * F s θ τ - Work.Spaces.K θ * F s θ τ'
        = Work.Spaces.K θ * (F s θ τ - F s θ τ') := by ring
    rw [hnum_eq, abs_div, abs_of_pos hs, abs_mul]
    have hnum : |Work.Spaces.K θ| * |F s θ τ - F s θ τ'| ≤ 3 * (Nt * s * |τ - τ'| ^ α) :=
      mul_le_mul hK h1 (abs_nonneg _) (by norm_num)
    have hstep := div_le_div_of_nonneg_right hnum hs0
    have hfin : 3 * (Nt * s * |τ - τ'| ^ α) / s = 3 * (Nt * |τ - τ'| ^ α) := by
      have hre : 3 * (Nt * s * |τ - τ'| ^ α) = (3 * (Nt * |τ - τ'| ^ α)) * s := by ring
      rw [hre, mul_div_cancel_right₀ _ hne]
    rw [hfin] at hstep
    exact hstep
  -- the norm of the integral is bounded by the integral of the norm
  have h1 : |∫ θ in Set.Icc 0 (Real.pi / 2),
        (Work.Spaces.K θ * F s θ τ - Work.Spaces.K θ * F s θ τ') / s|
      ≤ ∫ θ in Set.Icc 0 (Real.pi / 2),
        |(Work.Spaces.K θ * F s θ τ - Work.Spaces.K θ * F s θ τ') / s| := by
    have hb := MeasureTheory.norm_integral_le_integral_norm
      (μ := MeasureTheory.volume.restrict (Set.Icc 0 (Real.pi / 2)))
      (fun θ => (Work.Spaces.K θ * F s θ τ - Work.Spaces.K θ * F s θ τ') / s)
    simpa only [Real.norm_eq_abs] using hb
  -- the angular mass `π/2` and the final arithmetic
  refine le_trans h1 (le_trans (setIntegral_abs_le_of_bound hpt) ?_)
  have hX : 0 ≤ Nt * |τ - τ'| ^ α :=
    mul_nonneg htau.1 (Real.rpow_nonneg (abs_nonneg _) _)
  have hpi2 : Real.pi / 2 ≤ 2 := le_of_lt (by linarith [Real.pi_lt_four])
  have h3 : (3 * (Nt * |τ - τ'| ^ α)) * (Real.pi / 2)
      ≤ (3 * (Nt * |τ - τ'| ^ α)) * 2 :=
    mul_le_mul_of_nonneg_left hpi2 (by linarith)
  have h4 : (3 * (Nt * |τ - τ'| ^ α)) * 2 = 6 * Nt * |τ - τ'| ^ α := by ring
  linarith [h3, h4]

end Work.FTS.RegPkgGal.Der
