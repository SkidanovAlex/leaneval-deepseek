import Mathlib
import Submission.Work.Smooth.Morse.Gauge
import Submission.Work.Smooth.Morse.Gauge.gaugeSandwich
import Submission.Work.Smooth.Morse.Gauge.exists_smooth_gauge_of_not_mem_centre

/-!
# A `C^∞` rounded-box gauge with Pardon's sandwich

The two ingredients of the rounded box are in the sibling modules
`Submission.Work.Smooth.Morse.Gauge.gaugeSandwich` (the renormalised `ℓ^{2k}` gauge satisfies
`PBox(t) ⊆ {g < t} ⊆ PBox((1+δ) t)` with the room `δ = 3^{1/(2k)} - 1`) and
`Submission.Work.Smooth.Morse.Gauge.exists_smooth_gauge_of_not_mem_centre` (the gauge can be
replaced by a `C^∞` function with literally the same sublevel regions, provided the centre of the
box is off the surface).

This file composes them: rescaling the smoothed gauge by `1/(1+δ)` gives a single `C^∞` function
satisfying the sandwich, i.e. exactly the hypotheses `hlow`/`hup` of the box-sweep statements
`Work.Smooth.Morse.boxSweep_containsEssentialLoop_on` and
`Work.Smooth.Morse.boxSweep_containsEssentialLoop_of_crossing_on`.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.Smooth.Morse.Gauge

noncomputable section

/-- **There is a `C^∞` gauge satisfying Pardon's box sandwich.**

For every `k ≥ 1` and every centre `c` off the surface there are a `C^∞` function `g` and a room
`δ > 0` with

`PBox(t) ⊆ {g < t}` (on the surface) and `{g < t} ⊆ PBox((1+δ) t)`

for **every** `t : ℝ`.  The room is the one of the `ℓ^{2k}` gauge, `δ = 3^{1/(2k)} - 1 → 0`. -/
theorem exists_smooth_gauge_with_sandwich (ψ : Submission.Diffeo) {c : R3}
    {σ : Equiv.Perm (Fin 3)} {k : ℕ} (hk : 1 ≤ k) (hc : c ∉ (Work.Smooth.Morse.torus ψ).carrier) :
    ∃ g : R3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) g ∧ ∃ δ : ℝ, 0 < δ ∧
      (∀ t : ℝ, Submission.PBox t c σ ∩ (Work.Smooth.Morse.torus ψ).carrier ⊆
        Work.Smooth.Morse.region ψ g t) ∧
      (∀ t : ℝ, Work.Smooth.Morse.region ψ g t ⊆ Submission.PBox ((1 + δ) * t) c σ) := by
  obtain ⟨δ, hδ, hlow, hup⟩ := gaugeSandwich ψ c σ k hk
  obtain ⟨g₀, hg₀, hregions⟩ := exists_smooth_gauge_of_not_mem_centre (ψ := ψ) (c := c)
    (σ := σ) (k := k) hc
  have hpos : 0 < 1 + δ := by linarith
  -- rescaling the smoothed gauge by `1/(1+δ)` changes every level by the factor `(1+δ)`
  have hregion : ∀ t : ℝ, Work.Smooth.Morse.region ψ (fun y => g₀ y / (1 + δ)) t =
      Work.Smooth.Morse.region ψ (fun y => Work.Smooth.Morse.boxGauge c σ k y / (1 + δ)) t := by
    intro t
    have h1 : {x : R3 | g₀ x / (1 + δ) < t} = {x : R3 | g₀ x < (1 + δ) * t} := by
      ext x
      simp only [Set.mem_ofPred_eq, div_lt_iff₀ hpos, mul_comm]
    have h2 : {x : R3 | Work.Smooth.Morse.boxGauge c σ k x / (1 + δ) < t} =
        {x : R3 | Work.Smooth.Morse.boxGauge c σ k x < (1 + δ) * t} := by
      ext x
      simp only [Set.mem_ofPred_eq, div_lt_iff₀ hpos, mul_comm]
    simpa only [Work.Smooth.Morse.region, h1, h2] using hregions ((1 + δ) * t)
  refine ⟨fun y => g₀ y / (1 + δ), hg₀.div_const (1 + δ), δ, hδ, ?_, ?_⟩
  · intro t
    rw [hregion t]
    exact hlow t
  · intro t
    rw [hregion t]
    exact hup t

end

end Work.Smooth.Morse.Gauge
