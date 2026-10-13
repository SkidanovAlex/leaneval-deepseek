import Mathlib.MeasureTheory.Integral.DominatedConvergence

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Cert.GbarSin

/-- The primitive `z ↦ ∫ s in 0..z, f s` of a function which is interval integrable on
`[0, z]` for every `z > 0` is continuous on `(0, ∞)`.

At a point `x > 0` the primitive agrees, near `x`, with the primitive of the *fixed*
interval `[0, 2x]`: `f` is interval integrable on `[0, 2x]` by hypothesis, so
`intervalIntegral.continuousOn_primitive_interval'` gives continuity on `Icc 0 (2x)`,
and `x` lies in the interior of that interval. -/
theorem continuousOn_primitive_Ioi {f : ℝ → ℝ}
    (hf : ∀ z, 0 < z → IntervalIntegrable f MeasureTheory.volume 0 z) :
    ContinuousOn (fun z => ∫ s in (0 : ℝ)..z, f s) (Set.Ioi 0) := by
  intro x hx
  have hx0 : (0 : ℝ) < x := hx
  have h_int : IntervalIntegrable f MeasureTheory.volume 0 (2 * x) := hf (2 * x) (by linarith)
  have ha : (0 : ℝ) ∈ Set.uIcc (0 : ℝ) (2 * x) := by
    rw [Set.uIcc_of_le (by linarith : (0 : ℝ) ≤ 2 * x)]
    exact ⟨le_rfl, by linarith⟩
  have hcont : ContinuousOn (fun z => ∫ s in (0 : ℝ)..z, f s)
      (Set.uIcc (0 : ℝ) (2 * x)) :=
    intervalIntegral.continuousOn_primitive_interval' h_int ha
  have hmem : Set.uIcc (0 : ℝ) (2 * x) ∈ nhds x := by
    rw [Set.uIcc_of_le (by linarith : (0 : ℝ) ≤ 2 * x)]
    exact Icc_mem_nhds (by linarith) (by linarith)
  exact (hcont.continuousAt hmem).continuousWithinAt

end Work.FTS.EllipticEst.Cert.GbarSin
