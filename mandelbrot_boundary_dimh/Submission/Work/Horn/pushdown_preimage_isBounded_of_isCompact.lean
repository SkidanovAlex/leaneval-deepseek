import Mathlib
import Submission.Work.Horn.pushdown_fiber_bounded
import Submission.Work.Horn.pushdown_lower_end_linear_growth

/-!
# Preimages of bounded sets under the pushed-down horn map

`pushdown d.E` is asymptotically linear at `∞` with slope `π(cl) = exp (2πi cl) ≠ 0`
(`pushdown_lower_end_linear_growth`).  Consequently `‖pushdown d.E ζ‖ ≥ (‖π cl‖/2)·‖ζ‖`
for all sufficiently large `‖ζ‖`, and the preimage of any bounded set — in particular of a
compact set — is bounded.  (The horn-specific input is exactly the non-vanishing slope at the
lower end; `exp z - 1`-type maps have unbounded preimages of points.)
-/

namespace Work.Horn

noncomputable section

open Filter Topology Metric
open scoped Topology

/-- Abstract form: if `‖g ζ‖ ≥ c · ‖ζ‖` for every `ζ` with `‖ζ‖ ≥ R`, with `c > 0`, then
`g ⁻¹' L` is bounded whenever `L` is bounded. -/
theorem isBounded_preimage_of_norm_lower_bound {g : ℂ → ℂ} {c R : ℝ} (hc : 0 < c)
    (h : ∀ ζ : ℂ, R ≤ ‖ζ‖ → c * ‖ζ‖ ≤ ‖g ζ‖)
    {L : Set ℂ} (hL : Bornology.IsBounded L) :
    Bornology.IsBounded (g ⁻¹' L) := by
  obtain ⟨M₀, hM₀⟩ : ∃ M : ℝ, ∀ y ∈ L, ‖y‖ ≤ M := by
    obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℂ)).mp hL
    exact ⟨r, fun y hy => by
      have h1 := hr hy
      rwa [Metric.mem_closedBall, dist_eq_norm, sub_zero] at h1⟩
  set M : ℝ := max M₀ 0 with hMdef
  have hM : ∀ y ∈ L, ‖y‖ ≤ M := fun y hy => le_trans (hM₀ y hy) (le_max_left _ _)
  have hMnn : 0 ≤ M := le_max_right _ _
  refine (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := max R (2 * M / c))).subset ?_
  intro ζ hζ
  rw [Set.mem_preimage] at hζ
  rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
  by_cases hR : R ≤ ‖ζ‖
  · have h1 : c * ‖ζ‖ ≤ M := le_trans (h ζ hR) (hM _ hζ)
    have h2 : ‖ζ‖ ≤ 2 * M / c := by
      rw [le_div_iff₀ hc]
      linarith
    exact le_trans h2 (le_max_right _ _)
  · exact le_trans (le_of_lt (lt_of_not_ge hR)) (le_max_left _ _)

/-- **Preimages of compact sets under the pushed-down horn map are bounded.**

Given a lower-end limit `cl` of the lifted horn map (`d.E w - w → cl` as `Im w → -∞`), the
pushed-down map `pushdown d.E` grows like the non-zero linear map `ζ ↦ π(cl)·ζ` at `∞`; hence
`(pushdown d.E) ⁻¹' L` is bounded for every compact (indeed every bounded) `L`. -/
theorem pushdown_preimage_isBounded_of_isCompact {f₀ : ℂ → ℂ} {D₀ : Set ℂ}
    (d : MandelDim.ParabData f₀ D₀) {cl : ℂ}
    (hcl : Filter.Tendsto (fun w : ℂ => d.E w - w) MandelDim.lowerEnd (nhds cl))
    {L : Set ℂ} (hL : IsCompact L) :
    Bornology.IsBounded ((MandelDim.pushdown d.E) ⁻¹' L) := by
  have hne : MandelDim.piExp cl ≠ 0 := by
    rw [MandelDim.piExp]
    exact Complex.exp_ne_zero _
  have hpos : 0 < ‖MandelDim.piExp cl‖ := norm_pos_iff.mpr hne
  obtain ⟨R, hR⟩ := pushdown_lower_end_linear_growth d hcl (‖MandelDim.piExp cl‖ / 2)
    (by positivity)
  refine isBounded_preimage_of_norm_lower_bound (g := MandelDim.pushdown d.E)
    (c := ‖MandelDim.piExp cl‖ / 2) (R := R) (by positivity) ?_ hL.isBounded
  intro ζ hζ
  have h := hR ζ hζ
  have h2 : ‖MandelDim.piExp cl‖ * ‖ζ‖ ≤
      ‖MandelDim.pushdown d.E ζ‖ + ‖MandelDim.pushdown d.E ζ - MandelDim.piExp cl * ζ‖ := by
    rw [← norm_mul]
    calc ‖MandelDim.piExp cl * ζ‖
        = ‖MandelDim.pushdown d.E ζ -
            (MandelDim.pushdown d.E ζ - MandelDim.piExp cl * ζ)‖ := by
          congr 1; ring
      _ ≤ _ := norm_sub_le _ _
  linarith

end

end Work.Horn
