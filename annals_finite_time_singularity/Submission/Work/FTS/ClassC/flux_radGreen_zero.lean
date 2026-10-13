import Mathlib.Analysis.Calculus.Deriv.Basic
import Submission.Work.FTS.ClassC.ModeEnergyDefs
import Submission.Work.FTS.PhiStar.Radial.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.ClassC

set_option autoImplicit false

/-!
# `Work.FTS.ClassC.flux_radGreen_zero`

The boundary term `flux α a` of the per-mode weighted energy identity
(`FTS/ClassC/ModeEnergyDefs.lean`) is

  `flux α a z = α²·(rw z · a'·a) - (α²/2)·(rwb z · a²) + ((α(5+α))/2)·(rw z / z)·a²`,

with `rw z = (1+z)^4/z^2` and `rwb z = (1+z)^3(2z-2)/z^3`.  The two hypotheses of the target say
that, for `a = radGreen α m c`,

  `a(z)²/z³ → 0`  and  `a'(z)·a(z)/z² → 0`  as `z → 0⁺`.

These are exactly what is needed: for `z ≠ 0`

  `rw z·(a'·a)   = (1+z)^4 · (a'·a/z²)`,
  `rwb z·a²      = ((1+z)^3(2z-2)) · (a²/z³)`,
  `(rw z/z)·a²   = (1+z)^4 · (a²/z³)`,

so `flux α a` is a sum of three products of a coefficient *continuous at `0`* with one of the
two quantities tending to `0` — hence it tends to `0` at `0⁺`.  Since `flux α a 0 = 0`
(`flux_zero`), this is continuity within `[0,∞)` at `0`.

Neither `m` nor `c` (nor the structure of `radGreen`) is used: the statement holds for any `α`
and any function satisfying the two decay hypotheses.
-/

/-- If `a` decays at `0⁺` in the two weighted senses recorded by the boundary term of the
per-mode energy identity, then that boundary term `flux α a` tends to `0` at `0⁺`. -/
lemma flux_tendsto_zero_of_small {α : ℝ} {a : ℝ → ℝ}
    (h1 : Tendsto (fun z => (a z) ^ 2 / z ^ 3) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0))
    (h2 : Tendsto (fun z => deriv a z * a z / z ^ 2) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)) :
    Tendsto (flux α a) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  -- the three coefficients of `flux`, as functions continuous at `0`
  have hc1 : Tendsto (fun z : ℝ => α ^ 2 * (1 + z) ^ 4)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (α ^ 2)) := by
    have hcont : Continuous fun z : ℝ => α ^ 2 * (1 + z) ^ 4 := by fun_prop
    simpa using (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
  have hc2 : Tendsto (fun z : ℝ => (α ^ 2 / 2) * ((1 + z) ^ 3 * (2 * z - 2)))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds ((α ^ 2 / 2) * (-2))) := by
    have hcont : Continuous fun z : ℝ => (α ^ 2 / 2) * ((1 + z) ^ 3 * (2 * z - 2)) := by fun_prop
    simpa using (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
  have hc3 : Tendsto (fun z : ℝ => ((α * (5 + α)) / 2) * (1 + z) ^ 4)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds ((α * (5 + α)) / 2)) := by
    have hcont : Continuous fun z : ℝ => ((α * (5 + α)) / 2) * (1 + z) ^ 4 := by fun_prop
    simpa using (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
  -- the three summands of the re-associated expression
  have hT1 : Tendsto (fun z : ℝ => α ^ 2 * (1 + z) ^ 4 * (deriv a z * a z / z ^ 2))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    simpa using hc1.mul h2
  have hT2 : Tendsto (fun z : ℝ =>
      (α ^ 2 / 2) * ((1 + z) ^ 3 * (2 * z - 2)) * ((a z) ^ 2 / z ^ 3))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    simpa using hc2.mul h1
  have hT3 : Tendsto (fun z : ℝ =>
      ((α * (5 + α)) / 2) * (1 + z) ^ 4 * ((a z) ^ 2 / z ^ 3))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    simpa using hc3.mul h1
  have hsum : Tendsto (fun z : ℝ => α ^ 2 * (1 + z) ^ 4 * (deriv a z * a z / z ^ 2)
      - (α ^ 2 / 2) * ((1 + z) ^ 3 * (2 * z - 2)) * ((a z) ^ 2 / z ^ 3)
      + ((α * (5 + α)) / 2) * (1 + z) ^ 4 * ((a z) ^ 2 / z ^ 3))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    simpa using (hT1.sub hT2).add hT3
  refine Tendsto.congr' ?_ hsum
  filter_upwards [self_mem_nhdsWithin] with z hz
  have hz0 : z ≠ 0 := ne_of_gt hz
  simp only [flux, rw, rwb]
  field_simp
  try ring

theorem flux_radGreen_zero {α : ℝ} (m : ℕ) {c : ℝ → ℝ}
    (h1 : Filter.Tendsto
      (fun z => (Work.FTS.PhiStar.Radial.radGreen α m c z) ^ 2 / z ^ 3)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0))
    (h2 : Filter.Tendsto
      (fun z => deriv (Work.FTS.PhiStar.Radial.radGreen α m c) z
        * Work.FTS.PhiStar.Radial.radGreen α m c z / z ^ 2)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)) :
    ContinuousWithinAt (Work.FTS.ClassC.flux α (Work.FTS.PhiStar.Radial.radGreen α m c))
      (Set.Ici 0) 0 := by
  have hlim := flux_tendsto_zero_of_small (α := α)
    (a := Work.FTS.PhiStar.Radial.radGreen α m c) h1 h2
  have hIci : Set.Ici (0 : ℝ) = insert 0 (Set.Ioi 0) := by
    ext x; simp [le_iff_lt_or_eq, eq_comm]
  rw [ContinuousWithinAt, hIci, nhdsWithin_insert,
    flux_zero α (Work.FTS.PhiStar.Radial.radGreen α m c)]
  rw [tendsto_sup]
  refine ⟨?_, hlim⟩
  show map (flux α (Work.FTS.PhiStar.Radial.radGreen α m c)) (pure 0) ≤ 𝓝 (0 : ℝ)
  rw [map_pure, flux_zero α (Work.FTS.PhiStar.Radial.radGreen α m c)]
  exact pure_le_nhds 0

end Work.FTS.ClassC
