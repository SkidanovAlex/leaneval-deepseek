import Mathlib

/-!
# Holomorphic square roots of nonvanishing holomorphic functions

Mathlib provides *continuous* branches of `n`-th roots and logarithms on open
simply connected domains:

* `Complex.exists_continuousOn_pow_eq`: on an open simply connected `U`,
  a function `g` continuous on `U` with `0 ∉ g '' U` has a continuous
  `n`-th root on `U`.

The purpose of this module is the classical upgrade

> a *continuous* branch of the square root of a *holomorphic* nonvanishing
> function is automatically *holomorphic*

(and similarly, with one more line, the existence of a *holomorphic*
square root on simply connected domains).

This is the first layer of the "monodromy" part of the analytic engine of the
proof of Dimitrov's theorem (`Submission.Engine`): the algebraic branch
`f(X) = √(X⁻²ᵈ P₂(X) P₄(X))` must be shown holomorphic on a large simply
connected domain avoiding the zeros of `P₂ P₄`; the *continuous* branch comes
from Mathlib's covering-space theorem, and this module upgrades continuity to
holomorphy.

## Proof of the local lemma (`hasDerivAt_of_sq_eq`)

Let `c := g z₀ ≠ 0`, `w₀ := log c` (so `exp w₀ = c` by `Complex.exp_log`).
Near `z₀` define the holomorphic logarithm of `g`:

    L z := w₀ + log (g z / c)

Since `g z / c → 1 ∈ slitPlane`, the chain rule with `Complex.hasDerivAt_log`
gives `HasDerivAt L (g' / c) z₀`, and `exp (L z) = c · (g z / c) = g z`
near `z₀` (`exp_log` for the nonzero `g z / c`).

Then `s z := exp (L z / 2)` is holomorphic near `z₀` and satisfies
`s z ^ 2 = g z`.  Since also `f z ^ 2 = g z`, the continuous function
`q z := f z / s z` satisfies `q z ^ 2 = 1` near `z₀`, so `q` is locally
constant with value `±1` (continuity + discreteness of `{1, -1}`); hence
`f` agrees near `z₀` with `± s`, which is holomorphic, and the derivative is
`g' / (2 * f z₀)` (signs cancel because `q z₀ ^ 2 = 1`).

## Global statements

* `differentiableOn_of_sq_eq`: same conclusion at every point of an open set.
* `exists_holomorphic_sq_eq`: on an open simply connected `U`, a holomorphic
  nonvanishing `g` has a holomorphic square root on `U` (combine
  `Complex.exists_continuousOn_pow_eq` with `differentiableOn_of_sq_eq`).

You may add helper lemmas.  Do NOT change the statements.  No sorries may
remain in this file.
-/

noncomputable section

open Complex
open Filter
open scoped Real Topology

namespace Submission.HoloSqrt

/-- **Local upgrade.**  If `g` is differentiable at `z₀` with `g z₀ ≠ 0`,
`f` is continuous at `z₀`, and `f² = g` on a neighbourhood of `z₀`
(hence in particular at `z₀`), then `f` is differentiable at `z₀` with
derivative `g' / (2 * f z₀)`. -/
lemma hasDerivAt_of_sq_eq {f g : ℂ → ℂ} {z₀ g' : ℂ}
    (hder : HasDerivAt g g' z₀) (hg0 : g z₀ ≠ 0)
    (hf : ContinuousAt f z₀) (hfg₀ : f z₀ ^ 2 = g z₀)
    (hfg : ∀ᶠ z in 𝓝 z₀, f z ^ 2 = g z) :
    HasDerivAt f (g' / (2 * f z₀)) z₀ := by
  have hfz₀ : f z₀ ≠ 0 := by
    intro hfz
    apply hg0
    rw [← hfg₀, hfz]
    simp
  -- derivative of `g` as a limit of slopes on the punctured neighbourhood
  have hgslope : Tendsto (slope g z₀) (𝓝[≠] z₀) (𝓝 g') := by
    simpa using (hasDerivAt_iff_tendsto_slope.mp hder)
  -- on the punctured neighbourhood `f² = g`, so the slopes of `f` and `g`
  -- are related by `slope f z₀ z · (f z + f z₀) = slope g z₀ z`
  have hfg' : ∀ᶠ z in 𝓝[≠] z₀, f z ^ 2 = g z :=
    hfg.filter_mono nhdsWithin_le_nhds
  have hid : (fun z => slope f z₀ z * (f z + f z₀)) =ᶠ[𝓝[≠] z₀] slope g z₀ := by
    filter_upwards [hfg'] with z hz
    rw [slope_def_field, slope_def_field]
    rw [← hz, ← hfg₀]
    ring
  have hprod : Tendsto (fun z => slope f z₀ z * (f z + f z₀)) (𝓝[≠] z₀) (𝓝 g') := by
    exact (Filter.tendsto_congr' hid).mpr hgslope
  -- `f z + f z₀ → 2 * f z₀ ≠ 0` by continuity of `f` at `z₀`
  have hcst : Tendsto (fun z : ℂ => f z₀) (𝓝 z₀) (𝓝 (f z₀)) := tendsto_const_nhds
  have hcont : Tendsto (fun z => f z + f z₀) (𝓝 z₀) (𝓝 (2 * f z₀)) := by
    simpa [two_mul] using (hf.tendsto.add hcst)
  have hd : Tendsto (fun z => f z + f z₀) (𝓝[≠] z₀) (𝓝 (2 * f z₀)) :=
    hcont.mono_left nhdsWithin_le_nhds
  have hd0 : (2 : ℂ) * f z₀ ≠ 0 := mul_ne_zero two_ne_zero hfz₀
  have hdnz : ∀ᶠ z in 𝓝[≠] z₀, f z + f z₀ ≠ 0 := hd.eventually_ne hd0
  -- now divide the product relation by the nonzero `f z + f z₀`
  have hcancel : (fun z => (slope f z₀ z * (f z + f z₀)) / (f z + f z₀)) =ᶠ[𝓝[≠] z₀]
      (fun z => slope f z₀ z) := by
    filter_upwards [hdnz] with z hz
    field_simp [hz]
  have hdiv : Tendsto (fun z => (slope f z₀ z * (f z + f z₀)) / (f z + f z₀))
      (𝓝[≠] z₀) (𝓝 (g' / (2 * f z₀))) := by
    exact hprod.div hd hd0
  have hslope : Tendsto (slope f z₀) (𝓝[≠] z₀) (𝓝 (g' / (2 * f z₀))) := by
    exact (Filter.tendsto_congr' hcancel).mp hdiv
  exact hasDerivAt_iff_tendsto_slope.mpr hslope

/-- **Global upgrade.**  Let `U` be open.  If `g` is holomorphic and
nonvanishing on `U`, `f` is continuous on `U`, and `f² = g` pointwise on
`U`, then `f` is holomorphic on `U`. -/
theorem differentiableOn_of_sq_eq {U : Set ℂ} (hUo : IsOpen U)
    {f g : ℂ → ℂ} (hg : DifferentiableOn ℂ g U) (hg0 : ∀ z ∈ U, g z ≠ 0)
    (hf : ContinuousOn f U) (hfg : ∀ z ∈ U, f z ^ 2 = g z) :
    DifferentiableOn ℂ f U := by
  intro z₀ hz₀U
  have hU₀ : U ∈ 𝓝 z₀ := hUo.mem_nhds hz₀U
  have hfz : ContinuousAt f z₀ := hf.continuousAt hU₀
  have hgz : DifferentiableAt ℂ g z₀ := hg.differentiableAt hU₀
  have hfge : ∀ᶠ z in 𝓝 z₀, f z ^ 2 = g z := by
    filter_upwards [hU₀] with z hzU
    exact hfg z hzU
  have hder : HasDerivAt f (deriv g z₀ / (2 * f z₀)) z₀ :=
    hasDerivAt_of_sq_eq hgz.hasDerivAt (hg0 z₀ hz₀U) hfz (hfg z₀ hz₀U) hfge
  exact hder.differentiableAt.differentiableWithinAt

/-- **Holomorphic square root on a simply connected domain.**  Let `U` be open
and simply connected.  A holomorphic function `g` that does not vanish on `U`
has a holomorphic square root on `U`. -/
theorem exists_holomorphic_sq_eq {U : Set ℂ} (hUo : IsOpen U) (hUc : IsSimplyConnected U)
    {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g U) (hg0 : ∀ z ∈ U, g z ≠ 0) :
    ∃ f : ℂ → ℂ, DifferentiableOn ℂ f U ∧ ∀ z ∈ U, f z ^ 2 = g z := by
  have hU₀ : 0 ∉ g '' U := by
    rintro ⟨z, hzU, hgz⟩
    exact hg0 z hzU hgz
  rcases Complex.exists_continuousOn_pow_eq hUc hUo hg.continuousOn hU₀
    (by norm_num : (2 : ℕ) ≠ 0) with ⟨f, hfc, hf⟩
  refine ⟨f, differentiableOn_of_sq_eq hUo hg hg0 hfc (fun z hz => hf z), fun z hz => hf z⟩

end Submission.HoloSqrt

end
