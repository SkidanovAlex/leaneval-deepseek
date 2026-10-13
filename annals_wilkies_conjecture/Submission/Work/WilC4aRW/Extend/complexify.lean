import Mathlib
import Submission.Work.WilC4aRW.Defs
import Submission.Work.WilC4aRW.Extend.Defs

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section
open Classical Filter Topology
open scoped Topology BigOperators

namespace Work.WilC4aRW.Extend

/-- A real function with a power series expansion at the origin extends to a complex analytic
function on a neighbourhood of the origin in `ℂ^N`. -/
theorem complexify {N : ℕ} (f : (Fin N → ℝ) → ℝ) (p : FormalMultilinearSeries ℝ (Fin N → ℝ) ℝ)
    (hp : HasFPowerSeriesAt f p 0) :
    ∃ F : (Fin N → ℂ) → ℂ, AnalyticAt ℂ F 0 ∧
      ∀ᶠ x in nhds (0 : Fin N → ℝ), F (Work.WilC4aRW.cplxIncl x) = f x := by
  have hrad : 0 < p.radius := hp.radius_pos
  obtain ⟨r, hr⟩ := hp
  have hqrad : 0 < (cplxSeries p).radius := cplxSeries_radius_pos p hrad
  have hq : HasFPowerSeriesOnBall (cplxSeries p).sum (cplxSeries p) 0 (cplxSeries p).radius :=
    (cplxSeries p).hasFPowerSeriesOnBall hqrad
  refine ⟨(cplxSeries p).sum, ⟨cplxSeries p, (cplxSeries p).radius, hq⟩, ?_⟩
  have h1 : ∀ᶠ x : Fin N → ℝ in 𝓝 0, x ∈ Metric.eball (0 : Fin N → ℝ) r :=
    Metric.eball_mem_nhds 0 hr.r_pos
  have h2 : ∀ᶠ x : Fin N → ℝ in 𝓝 0,
      cplxIncl x ∈ Metric.eball (0 : Fin N → ℂ) (cplxSeries p).radius :=
    ((cplxInclCLM N).continuous.continuousAt).preimage_mem_nhds
      (by simpa using Metric.eball_mem_nhds (0 : Fin N → ℂ) hqrad)
  refine (h1.and h2).mono ?_
  intro x ⟨hxr, hxc⟩
  have hsumr : HasSum (fun n : ℕ => p n (fun _ => x)) (f x) := by
    simpa using hr.hasSum hxr
  have hsumc : HasSum (fun n : ℕ => cplxSeries p n (fun _ => cplxIncl x))
      ((cplxSeries p).sum (cplxIncl x)) := by
    simpa using hq.hasSum hxc
  have hmain : (cplxSeries p).sum (cplxIncl x) = ((f x : ℝ) : ℂ) := by
    rw [← hsumc.tsum_eq, tsum_congr fun n => cplxSeries_apply_diag p n x,
      ← Complex.ofReal_tsum, hsumr.tsum_eq]
  simpa using hmain

end Work.WilC4aRW.Extend
