import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Submission.Work.FTS.Physical.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Topology

namespace Work.FTS.Physical.Clock

/-- **The clock is continuous on the fake-time half-line.**  `t(τ) = ∫₀^τ A` is the primitive of
the amplitude `A`, which is continuous on `[0,∞)` by `PhysClock.hAcont`; the continuity of the
primitive in its upper limit (`intervalIntegral.continuousOn_primitive_interval'`, applied on the
window `[0, τ₀+1]`) gives continuity at every `τ₀ ≥ 0`.

This is a *local* statement: no integrability of `A` at infinity is needed, only continuity on
`[0,∞)`, so it does not pre-suppose the finiteness of the blow-up time `T = ∫₀^∞ A`. -/
theorem continuousOn_t (C : Work.FTS.Physical.PhysClock) : ContinuousOn C.t (Set.Ici 0) := by
  intro τ₀ hτ₀
  have hτ0 : (0 : ℝ) ≤ τ₀ := hτ₀
  -- Work on the window `[0, τ₀+1]`, on which `A` is continuous (it is contained in `[0,∞)`).
  set b : ℝ := τ₀ + 1 with hb
  have hb0 : (0 : ℝ) ≤ b := by simp only [hb]; linarith
  have hτb : τ₀ ≤ b := by simp only [hb]; linarith
  have hint : IntervalIntegrable C.A MeasureTheory.volume 0 b := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hb0]
    exact C.hAcont.mono Set.Icc_subset_Ici_self
  -- Continuity of the primitive on the window.
  have hprim : ContinuousOn (fun x => ∫ s in (0 : ℝ)..x, C.A s) (Set.Icc (0 : ℝ) b) := by
    have h := intervalIntegral.continuousOn_primitive_interval' hint (a := (0 : ℝ)) Set.left_mem_uIcc
    rwa [Set.uIcc_of_le hb0] at h
  have hmem : τ₀ ∈ Set.Icc (0 : ℝ) b := ⟨hτ0, hτb⟩
  -- The window is a neighbourhood of `τ₀` relative to `[0,∞)`.
  have hnhds : Set.Icc (0 : ℝ) b ∈ 𝓝[Set.Ici (0 : ℝ)] τ₀ := by
    rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
    refine ⟨Set.Iio ((τ₀ + b) / 2), IsOpen.mem_nhds isOpen_Iio ?_, ?_⟩
    · simp only [Set.mem_Iio]; linarith
    · intro x hx
      simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_Ici] at hx
      exact ⟨hx.2, by linarith [hx.1]⟩
  exact (hprim.continuousWithinAt hmem).mono_of_mem_nhdsWithin hnhds

end Work.FTS.Physical.Clock
