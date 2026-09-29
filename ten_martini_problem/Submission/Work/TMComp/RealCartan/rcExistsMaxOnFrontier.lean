import Mathlib

/-!
# Existence of a maximum of `W` on the frontier of `Ω`

Let `Ω ⊆ ℂ` be open, bounded and nonempty, and let `W : ℂ → ℝ` be continuous on `closure Ω`.
Assume that `W` satisfies a **strict** sub-mean-value inequality on circles: for every `z ∈ Ω`
there is `r > 0` with `closedBall z r ⊆ Ω` and `W z < circleAverage W z r`.

Then `W` attains its maximum over `closure Ω` at a point `zstar` of the frontier of `Ω`.

Indeed, `closure Ω` is compact (as `Ω` is bounded) and nonempty (as `Ω` is), so `W` attains a
maximum there at some `z₀`.  If `z₀ ∈ Ω`, the strict mean value inequality would give
`W z₀ < circleAverage W z₀ r ≤ W z₀`, since `W ≤ W z₀` on the circle `sphere z₀ r ⊆ Ω`; a
contradiction.  Hence `z₀ ∉ Ω` and, since `Ω` is open, `z₀ ∈ closure Ω \ Ω = frontier Ω`.
-/

open Metric Set

namespace Work.TMComp.RealCartan

theorem rcExistsMaxOnFrontier {Ω : Set ℂ} (hΩ : IsOpen Ω) (hbdd : Bornology.IsBounded Ω)
    (hne : Ω.Nonempty)
    {W : ℂ → ℝ} (hWc : ContinuousOn W (closure Ω))
    (hW : ∀ z ∈ Ω, ∃ r : ℝ, 0 < r ∧ Metric.closedBall z r ⊆ Ω ∧
      W z < Real.circleAverage W z r) :
    ∃ zstar ∈ frontier Ω, ∀ z ∈ closure Ω, W z ≤ W zstar := by
  -- `closure Ω` is compact and nonempty, so `W` attains its maximum there.
  have hcpt : IsCompact (closure Ω) := hbdd.isCompact_closure
  obtain ⟨z0, hz0cl, hz0max⟩ := hcpt.exists_isMaxOn (hne.mono subset_closure) hWc
  refine ⟨z0, ?_, fun z hz => hz0max hz⟩
  -- `Ω` is open, so `frontier Ω = closure Ω \ Ω`; it remains to see that `z0 ∉ Ω`.
  rw [hΩ.frontier_eq]
  refine ⟨hz0cl, ?_⟩
  intro hz0Ω
  obtain ⟨r, hr, hrΩ, hlt⟩ := hW z0 hz0Ω
  -- The circle of radius `r` around `z0` lies in `Ω ⊆ closure Ω`.
  have hsub : Metric.sphere z0 |r| ⊆ closure Ω := by
    intro x hx
    refine subset_closure (hrΩ ?_)
    have hx' := Metric.mem_sphere.mp hx
    rw [Metric.mem_closedBall]
    rw [hx', abs_of_pos hr]
  -- Hence `W ≤ W z0` on that circle, and so `circleAverage W z0 r ≤ W z0`.
  have hle : Real.circleAverage W z0 r ≤ W z0 :=
    Real.circleAverage_mono_on_of_le_circle
      (ContinuousOn.circleIntegrable' (hWc.mono hsub))
      (fun x hx => hz0max (hsub hx))
  linarith

end Work.TMComp.RealCartan
