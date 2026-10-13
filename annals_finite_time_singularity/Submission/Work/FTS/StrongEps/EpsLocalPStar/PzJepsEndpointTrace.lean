import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Submission.Work.FTS.ClassC.Defs
import Submission.Work.FTS.ClassC.tendsto_of_sin_rpow_sq
import Submission.Work.FTS.StrongEps.PZero
import Submission.Work.FTS.StrongEps.BumpDefs
import Submission.Work.FTS.StrongEps.Basic
import Submission.Work.FTS.Vocab

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsLocalPStar

open scoped Real Topology
open MeasureTheory Set Filter

/-- `bump` vanishes in an angular neighbourhood of the endpoint `θ = 0`: its angular cut-off
`thCut` is supported on `[π/4, 3π/8]`. -/
theorem bump_eq_zero_of_lt_pi_div_four (z θ : ℝ) (hθ : θ < Real.pi / 4) :
    Work.FTS.StrongEps.bump z θ = 0 := by
  rw [Work.FTS.StrongEps.bump, Work.FTS.StrongEps.thCut,
    Real.smoothTransition.zero_of_nonpos (show θ - Real.pi / 4 ≤ 0 by linarith),
    zero_mul, mul_zero]

/-- `bump` vanishes in an angular neighbourhood of the endpoint `θ = π/2`. -/
theorem bump_eq_zero_of_lt_pi_three_eighths (z θ : ℝ) (hθ : 3 * Real.pi / 8 < θ) :
    Work.FTS.StrongEps.bump z θ = 0 := by
  rw [Work.FTS.StrongEps.bump, Work.FTS.StrongEps.thCut,
    Real.smoothTransition.zero_of_nonpos (show 3 * Real.pi / 8 - θ ≤ 0 by linarith),
    mul_zero, mul_zero]

/-- The projection `Pz` differs from the identity by a multiple of `bump`, which is supported
away from the angular endpoints, so it does not change the angular traces at `θ = 0` and
`θ = π/2`. -/
theorem Pz_eq_self_near_angular_endpoints {f : Work.FTS.Galerkin.Fn} {z : ℝ} :
    (∀ᶠ θ in nhdsWithin (0 : ℝ) (Set.Ioi 0), Work.FTS.StrongEps.Pz f z θ = f z θ) ∧
    (∀ᶠ θ in nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)),
      Work.FTS.StrongEps.Pz f z θ = f z θ) := by
  constructor
  · filter_upwards [nhdsWithin_le_nhds (isOpen_Iio.mem_nhds
        (show (0 : ℝ) < Real.pi / 4 by linarith [Real.pi_pos]))] with θ hθ
    rw [Work.FTS.StrongEps.Pz_apply, bump_eq_zero_of_lt_pi_div_four z θ hθ, mul_zero, sub_zero]
  · filter_upwards [nhdsWithin_le_nhds (isOpen_Ioi.mem_nhds
        (show (3 : ℝ) * Real.pi / 8 < Real.pi / 2 by linarith [Real.pi_pos]))] with θ hθ
    rw [Work.FTS.StrongEps.Pz_apply, bump_eq_zero_of_lt_pi_three_eighths z θ hθ, mul_zero,
      sub_zero]

theorem PzJepsEndpointTrace {α : ℝ} (hα : 0 < α) {ρ : ℝ × ℝ → ℝ} {ε : ℝ} {δ : ℝ → ℝ → ℝ}
    (hg : Work.FTS.ClassC.ClassC α (Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε δ))) :
    (∀ z ∈ Set.Ioi (0 : ℝ), Filter.Tendsto (fun θ => Work.FTS.StrongEps.Jeps ρ ε δ z θ)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)) ∧
    (∀ z ∈ Set.Ioi (0 : ℝ), Filter.Tendsto (fun θ => Work.FTS.StrongEps.Jeps ρ ε δ z θ)
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0)) := by
  have hγ : 1 < Work.Spaces.gam α := by
    rw [Work.Spaces.gam]; linarith
  -- the `BdryTraces` clause of the class, at the slot `(a, b) = (0, 0)`
  have hbdry := hg.tr 0 0 (by norm_num)
  constructor
  · intro z hz
    have hPz : Filter.Tendsto (fun θ => Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
        * (Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε δ) z θ) ^ 2)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      simpa only [Work.Spaces.mixed, Work.Spaces.DzIter_zero, Work.Spaces.DthIter_zero]
        using (hbdry.2 z hz).1
    have hJ : Filter.Tendsto (fun θ => Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
        * (Work.FTS.StrongEps.Jeps ρ ε δ z θ) ^ 2)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
      Filter.Tendsto.congr' (Pz_eq_self_near_angular_endpoints (f := Work.FTS.StrongEps.Jeps ρ ε δ)
        |>.1.mono fun θ hθ => by rw [hθ]) hPz
    exact Work.FTS.ClassC.tendsto_of_sin_rpow_sq hγ
      (Ioo_mem_nhdsGT (show (0 : ℝ) < Real.pi / 2 by linarith [Real.pi_pos])) hJ
  · intro z hz
    have hPz : Filter.Tendsto (fun θ => Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
        * (Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε δ) z θ) ^ 2)
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
      simpa only [Work.Spaces.mixed, Work.Spaces.DzIter_zero, Work.Spaces.DthIter_zero]
        using (hbdry.2 z hz).2
    have hJ : Filter.Tendsto (fun θ => Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
        * (Work.FTS.StrongEps.Jeps ρ ε δ z θ) ^ 2)
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) :=
      Filter.Tendsto.congr' (Pz_eq_self_near_angular_endpoints (f := Work.FTS.StrongEps.Jeps ρ ε δ)
        |>.2.mono fun θ hθ => by rw [hθ]) hPz
    exact Work.FTS.ClassC.tendsto_of_sin_rpow_sq hγ
      (Ioo_mem_nhdsLT (show (0 : ℝ) < Real.pi / 2 by linarith [Real.pi_pos])) hJ

end Work.FTS.StrongEps.EpsLocalPStar
