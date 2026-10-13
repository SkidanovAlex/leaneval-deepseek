import Mathlib.MeasureTheory.Integral.DominatedConvergence

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Topology
open MeasureTheory

namespace Work.FTS.StrongEps.EComparison

/-- The left primitive `t ↦ ∫ z in t..b, f z` of a function `f` that is locally integrable on
`(0, ∞)` is continuous on `(0, ∞)`, provided `b > 0` — so that the whole interval between the
variable point `t` and `b` stays inside the half-line on which `f` is controlled. -/
theorem continuousOn_integral_left {f : ℝ → ℝ} {b : ℝ} (hb : 0 < b)
    (hf : MeasureTheory.LocallyIntegrableOn f (Set.Ioi 0)) :
    ContinuousOn (fun t => ∫ z in t..b, f z) (Set.Ioi 0) := by
  intro t₀ ht₀
  have ht₀pos : (0 : ℝ) < t₀ := ht₀
  -- An interval `[b₁, b₂]` with `0 < b₁ < t₀ < b₂`.
  obtain ⟨b₁, b₂, hb₁pos, hb₁lt, ht₀lt⟩ : ∃ b₁ b₂ : ℝ, 0 < b₁ ∧ b₁ < t₀ ∧ t₀ < b₂ := by
    refine ⟨min (b / 2) (t₀ / 2), b + t₀ + 1, ?_, ?_, ?_⟩
    · exact lt_min (by linarith) (by linarith)
    · have hle : min (b / 2) (t₀ / 2) ≤ t₀ / 2 := min_le_right _ _
      linarith
    · linarith
  -- `f` is integrable on `[min b b₁, max b b₂]`, which lies inside `(0, ∞)`.
  have hsub : Set.uIcc (min b b₁) (max b b₂) ⊆ Set.Ioi 0 := by
    intro x hx
    have hx' := Set.mem_uIcc.mp hx
    have hpos : (0 : ℝ) < min b b₁ := lt_min hb hb₁pos
    rcases hx' with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact lt_of_lt_of_le hpos h1
    · exact lt_of_lt_of_le (lt_of_lt_of_le hb (le_max_left b b₂)) h1
  have hIntU : MeasureTheory.IntegrableOn f (Set.uIcc (min b b₁) (max b b₂)) :=
    hf.integrableOn_compact_subset hsub isCompact_uIcc
  have hInt : IntervalIntegrable f volume (min b b₁) (max b b₂) := hIntU.intervalIntegrable
  -- Fundamental theorem of calculus: the primitive of the upper limit is continuous.
  have key : ContinuousWithinAt (fun x => ∫ z in b..x, f z) (Set.Icc b₁ b₂) t₀ :=
    intervalIntegral.continuousWithinAt_primitive (MeasureTheory.measure_singleton t₀) hInt
  have hmem : Set.Icc b₁ b₂ ∈ 𝓝[Set.Ioi 0] t₀ :=
    mem_nhdsWithin_of_mem_nhds (Icc_mem_nhds hb₁lt ht₀lt)
  have key' : ContinuousWithinAt (fun x => ∫ z in b..x, f z) (Set.Ioi 0) t₀ :=
    key.mono_left (nhdsWithin_le_iff.mpr hmem)
  -- `∫ z in t..b, f z = -∫ z in b..t, f z`.
  have hF : (fun t => ∫ z in t..b, f z) = fun t => -∫ z in b..t, f z := by
    funext t
    rw [intervalIntegral.integral_symm]
  rw [hF]
  exact key'.neg

end Work.FTS.StrongEps.EComparison
