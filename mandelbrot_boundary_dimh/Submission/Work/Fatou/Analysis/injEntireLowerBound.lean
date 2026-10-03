import Mathlib

/-!
# A lower bound for an injective entire function outside the unit disc

If `f : ℂ → ℂ` is entire and injective then `‖f z - f 0‖` is bounded below by a positive
constant on `‖z‖ ≥ 1`.

Proof: `f` is analytic at `0`, so by the local open mapping theorem
(`AnalyticAt.eventually_constant_or_nhds_le_map_nhds_aux`) either `f` is constant near `0` —
impossible since `f` is injective and any neighbourhood of `0` contains a point different
from `0` — or `f` maps every neighbourhood of `0` to a neighbourhood of `f 0`. In particular
`f '' ball 0 1` is a neighbourhood of `f 0`, so it contains a ball `ball (f 0) ρ`, `ρ > 0`.
If `‖z‖ ≥ 1` and `‖f z - f 0‖ < ρ` then `f z = f w` for some `w` with `‖w‖ < 1`, and
injectivity forces `w = z`, contradicting `1 ≤ ‖z‖`.
-/

namespace Work.Fatou.Analysis

lemma injEntireLowerBound (f : ℂ → ℂ) (hf : Differentiable ℂ f) (hinj : Function.Injective f) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ z : ℂ, 1 ≤ ‖z‖ → ρ ≤ ‖f z - f 0‖ := by
  have hana : AnalyticAt ℂ f 0 := hf.analyticAt 0
  -- The local open mapping theorem: some ball around `f 0` is contained in `f '' ball 0 1`.
  have hkey : f '' Metric.ball (0 : ℂ) 1 ∈ nhds (f 0) := by
    rcases hana.eventually_constant_or_nhds_le_map_nhds_aux with hconst | hopen
    · -- `f` cannot be constant near `0`, because it is injective.
      exfalso
      obtain ⟨ε, hε, hεb⟩ := Metric.eventually_nhds_iff.mp hconst
      have hpos : (0 : ℝ) < ε / 2 := by linarith
      have hz : ((ε / 2 : ℝ) : ℂ) ∈ Metric.ball (0 : ℂ) ε := by
        rw [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos hpos]
        linarith
      have hfeq : f ((ε / 2 : ℝ) : ℂ) = f 0 := hεb hz
      have hzero : ((ε / 2 : ℝ) : ℂ) = 0 := hinj hfeq
      rw [Complex.ofReal_eq_zero] at hzero
      linarith
    · -- The image of every neighbourhood of `0` is a neighbourhood of `f 0`.
      exact hopen (Filter.mem_map.mpr
        (Filter.mem_of_superset (Metric.ball_mem_nhds 0 one_pos)
          (fun z hz => ⟨z, hz, rfl⟩)))
  obtain ⟨ρ, hρpos, hρsub⟩ := Metric.mem_nhds_iff.mp hkey
  refine ⟨ρ, hρpos, fun z hz => ?_⟩
  by_contra hlt
  rw [not_le] at hlt
  have hmem : f z ∈ Metric.ball (f 0) ρ := by
    rw [Metric.mem_ball, dist_eq_norm]; exact hlt
  obtain ⟨w, hw, hfw⟩ := hρsub hmem
  have hwz : w = z := hinj hfw
  rw [← hwz] at hz
  have hw1 : ‖w‖ < 1 := by simpa [Metric.mem_ball, dist_eq_norm] using hw
  linarith

end Work.Fatou.Analysis
