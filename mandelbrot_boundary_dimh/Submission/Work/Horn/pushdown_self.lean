import Mathlib
import Submission.Work.Horn.basic
import Submission.Work.Repel.pushdown_holo
import Submission.Work.L62.pushdown_section
import Submission.Work.Interfaces.Parabolic

/-!
# `pushdown` of a `T`-equivariant map that is asymptotic to the identity at the upper end

Let `Bu` be an open, `T`-invariant (`w ↦ w + 1`) subset of `ℂ` containing the half-plane
`{w | η < Im w}` for some `η > 0`, and let `s : ℂ → ℂ` be holomorphic on `Bu`,
`T`-equivariant there (`s (y + 1) = s y + 1`) and asymptotic to the identity at the upper end
(`s y - y → 0` as `Im y → +∞` along `Bu`).

Then the pushed-down map `pushdown s` (the map on the cylinder `ℂ/ℤ ≅ ℂ*` induced by `s`) is
holomorphic on `{0} ∪ π '' Bu` and has derivative `1` at the origin.

This is the general form of the `HornData` fields `g_holo` / `g_deriv`: the holomorphy away from
`0` is the user-independent statement `Work.Repel.pushdown_holo` (the local lift
`ζ ↦ w₀ + log (ζ / π w₀)/(2πi)`, which avoids the branch cut of `log`), and the derivative at
`0` is the purely asymptotic statement `Work.L62.hasDerivAt_pushdown_of_tendsto`
(`pushdown s ζ = π (s w) = π w · π (s w - w) = ζ · (1 + o(1))` along the principal lift
`w = log ζ/(2πi)`, which runs to the upper end as `ζ → 0`).
-/

namespace Work.Horn

open Filter Topology Metric
open scoped Topology

theorem pushdown_self {s : ℂ → ℂ} {Bu : Set ℂ} {η : ℝ}
    (hη : 0 < η) (hBuO : IsOpen Bu) (htBu : MandelDim.IsTInvariant Bu)
    (hup : {w : ℂ | η < w.im} ⊆ Bu)
    (hs : DifferentiableOn ℂ s Bu) (hTeq : ∀ y ∈ Bu, s (y + 1) = s y + 1)
    (hasymp : ∀ ε > 0, ∃ R : ℝ, ∀ y ∈ Bu, R < y.im → ‖s y - y‖ < ε) :
    DifferentiableOn ℂ (MandelDim.pushdown s) (insert 0 (MandelDim.piExp '' Bu)) ∧
      HasDerivAt (MandelDim.pushdown s) 1 0 := by
  have heq : MandelDim.IsTEquivariantOn s Bu := ⟨htBu, hTeq⟩
  -- holomorphy away from `0`
  have hholo : DifferentiableOn ℂ (MandelDim.pushdown s) (MandelDim.piExp '' Bu) :=
    Work.Repel.pushdown_holo heq hs
  -- the asymptotic hypothesis as a filter statement: `s w - w → 0` at the upper end
  have hasymp' : Filter.Tendsto (fun w : ℂ => s w - w) MandelDim.upperEnd (nhds 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨R, hR⟩ := hasymp ε hε
    have hset : {w : ℂ | max R η < w.im} ∈ MandelDim.upperEnd := by
      rw [MandelDim.upperEnd, Filter.mem_comap]
      exact ⟨Set.Ioi (max R η), Filter.Ioi_mem_atTop _, fun w hw => hw⟩
    exact Filter.mem_of_superset hset (fun w hw => by
      have hwη : η < w.im := lt_of_le_of_lt (le_max_right R η) hw
      have hwR : R < w.im := lt_of_le_of_lt (le_max_left R η) hw
      have hwB : w ∈ Bu := hup hwη
      simpa [dist_eq_norm] using hR w hwB hwR)
  -- derivative at `0`
  have hderiv : HasDerivAt (MandelDim.pushdown s) 1 0 := by
    have h := Work.L62.hasDerivAt_pushdown_of_tendsto (β := 0) (σ := s)
      (by simpa using hasymp')
    simpa [MandelDim.piExp] using h
  refine ⟨?_, hderiv⟩
  intro ζ hζ
  rw [Set.mem_insert_iff] at hζ
  rcases hζ with rfl | hζ
  · exact hderiv.differentiableAt.differentiableWithinAt
  · rcases hholo ζ hζ with ⟨f', hf'⟩
    exact ⟨f', (hasFDerivWithinAt_insert).mpr hf'⟩

end Work.Horn
