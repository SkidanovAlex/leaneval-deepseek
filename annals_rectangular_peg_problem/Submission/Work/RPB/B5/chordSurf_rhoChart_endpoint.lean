import Mathlib
import Submission.Work.RPB.B5.chart_C12
import Submission.Work.RPB.Defs

/-!
# B5: the `ρ`-chart at the right endpoint `r = π/2`

`Work.RPB.B5.chordSurf_rhoChart` produces a `ρ = r²`-chart `W` of the chord annulus which
reproduces `chordSurf c a τ t r` at `ρ = r²` for `0 < r < ρ₀`, with `ρ₀ > 0` small.  The chart `W`
is in fact defined (and smooth) on the *whole* interval `(-ρ₀, ρ₀)` of `ρ`, so it is meaningful
and true at `ρ = (π/2)²` as well, provided that `(π/2)² < ρ₀`.

This file proves that the identification extends to the right endpoint `r = π/2`:

if `W` is any function that is `C¹` in `(τ, t, ρ)` on
`Icc 0 1 × univ × Ioo (-ρ₀) ρ₀` and agrees with `chordSurf c a τ t r` at `ρ = r²` for
`0 < r < π/2`, then it also agrees with `chordSurf c a τ t (π/2)` at `ρ = (π/2)²`.

The proof is the expected one: both `r ↦ W τ t (r²)` and `r ↦ chordSurf c a τ t r` are
continuous at `r = π/2` (the first because `(π/2)²` lies in the open `ρ`-interval on which `W` is
`C¹`, the second because `c` is smooth and the phase lift `a` is smooth on `Icc 0 π`, and `π/2`
is an interior point of that interval), and the two functions agree on the left neighbourhood
`Ioo 0 (π/2)`. Hence their limits at `π/2` coincide.

Note that no continuity of `a` (or of `chordSurf`) at `r = 0` is needed, nor any control of the
values of `a` for `r < 0`: only the right endpoint is at issue.
-/

open RectangularPegProblem
open Manifold Complex Real
open scoped ContDiff
open scoped Topology

set_option autoImplicit false

noncomputable section

namespace Work.RPB.B5

theorem chordSurf_rhoChart_endpoint (CI : Work.RPV.CurveIsotopy) (a : ℝ → ℝ → ℝ → ℝ)
    (ha : Work.RPB.IsChordPhase CI.c a)
    (ρ₀ : ℝ) (hρ₀ : 0 < ρ₀) (hπρ₀ : Real.pi ^ 2 / 4 < ρ₀)
    (W : ℝ → ℝ → ℝ → Work.RPV.PS)
    (hW : ContDiffOn ℝ 1 (fun z : ℝ × (ℝ × ℝ) => W z.1 z.2.1 z.2.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-ρ₀) ρ₀))
    (h : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ r ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      W τ t (r ^ 2) = Work.RPB.chordSurf CI.c a τ t r) :
    ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ,
      W τ t ((Real.pi / 2) ^ 2) = Work.RPB.chordSurf CI.c a τ t (Real.pi / 2) := by
  intro τ hτ t
  have hpi2pos : 0 < Real.pi / 2 := by linarith [Real.pi_pos]
  -- `(π/2)² = π²/4` lies strictly inside the `ρ`-interval of the chart
  have hx₀ : (Real.pi / 2) ^ 2 ∈ Set.Ioo (-ρ₀) ρ₀ := by
    constructor
    · nlinarith [sq_nonneg (Real.pi / 2)]
    · nlinarith [hπρ₀]
  -- Continuity of `r ↦ W τ t (r²)` at `π/2`: `(τ, t, r²)` stays in the domain of `hW` for `r`
  -- in a neighbourhood of `π/2`, where that domain is a neighbourhood of the point.
  have hfcont : ContinuousAt (fun r : ℝ => W τ t (r ^ 2)) (Real.pi / 2) := by
    have hγ : ContinuousOn (fun r : ℝ => (τ, (t, r ^ 2)))
        {r : ℝ | r ^ 2 ∈ Set.Ioo (-ρ₀) ρ₀} := by fun_prop
    have hmap : Set.MapsTo (fun r : ℝ => (τ, (t, r ^ 2)))
        {r : ℝ | r ^ 2 ∈ Set.Ioo (-ρ₀) ρ₀}
        (Set.Icc (0:ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-ρ₀) ρ₀) := by
      intro r hr
      exact ⟨hτ, trivial, hr⟩
    have hcomp : ContinuousOn (fun r : ℝ => W τ t (r ^ 2))
        {r : ℝ | r ^ 2 ∈ Set.Ioo (-ρ₀) ρ₀} :=
      hW.continuousOn.comp hγ hmap
    have hUopen : {r : ℝ | r ^ 2 ∈ Set.Ioo (-ρ₀) ρ₀} ∈ 𝓝 (Real.pi / 2) := by
      have hopen : IsOpen {r : ℝ | r ^ 2 ∈ Set.Ioo (-ρ₀) ρ₀} := by
        have hc : Continuous (fun r : ℝ => r ^ 2) := by fun_prop
        exact isOpen_Ioo.preimage hc
      exact hopen.mem_nhds hx₀
    exact hcomp.continuousAt hUopen
  -- Continuity of `r ↦ chordSurf c a τ t r` at `π/2` from its three constituents.
  have hCcont : ContinuousAt (fun r : ℝ => Work.RPB.chordSurf CI.c a τ t r) (Real.pi / 2) := by
    have h1 : ContinuousAt (fun r : ℝ => CI.c τ (t + r)) (Real.pi / 2) :=
      (CI.smooth.continuous.comp (by fun_prop : Continuous (fun r : ℝ => (τ, t + r)))).continuousAt
    have h2 : ContinuousAt (fun r : ℝ => CI.c τ (t - r)) (Real.pi / 2) :=
      (CI.smooth.continuous.comp (by fun_prop : Continuous (fun r : ℝ => (τ, t - r)))).continuousAt
    -- the phase lift `a` is smooth on `Icc 0 π`, and `π/2` is an interior point of that set
    have h3 : ContinuousAt (fun r : ℝ => a τ t r) (Real.pi / 2) := by
      have hAcontOn : ContinuousOn (fun r : ℝ => a τ t r) (Set.Ioo (0:ℝ) Real.pi) := by
        have hγ : ContinuousOn (fun r : ℝ => (τ, (t, r))) (Set.Ioo (0:ℝ) Real.pi) := by fun_prop
        have hmap : Set.MapsTo (fun r : ℝ => (τ, (t, r))) (Set.Ioo (0:ℝ) Real.pi)
            (Set.Icc (0:ℝ) 1 ×ˢ Set.univ ×ˢ Set.Icc (0:ℝ) Real.pi) := by
          intro r hr
          exact ⟨hτ, trivial, ⟨le_of_lt hr.1, le_of_lt hr.2⟩⟩
        exact ha.1.continuousOn.comp hγ hmap
      exact hAcontOn.continuousAt (Ioo_mem_nhds hpi2pos (by linarith [Real.pi_pos]))
    unfold Work.RPB.chordSurf Work.RPV.chordPS
    fun_prop
  -- the two functions agree on the left neighbourhood of `π/2`
  have hev : (fun r : ℝ => W τ t (r ^ 2)) =ᶠ[𝓝[<] (Real.pi / 2)]
      (fun r : ℝ => Work.RPB.chordSurf CI.c a τ t r) := by
    filter_upwards [Ioo_mem_nhdsLT hpi2pos] with r hr
    exact h τ hτ t r hr
  -- uniqueness of the two limits along `𝓝[<] (π/2)`
  exact tendsto_nhds_unique
    (Filter.Tendsto.congr' hev (hfcont.tendsto.mono_left nhdsWithin_le_nhds))
    (hCcont.tendsto.mono_left nhdsWithin_le_nhds)

end Work.RPB.B5
