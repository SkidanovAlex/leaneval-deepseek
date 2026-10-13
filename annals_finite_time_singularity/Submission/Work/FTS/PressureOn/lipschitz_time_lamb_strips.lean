import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.PressureOn.Defs
import Submission.Work.FTS.PressureOn.continuousOn_time_omega_of_strips
import Submission.Work.FTS.PressureOn.lipschitz_time_of_hasDerivWithinAt
import Submission.Work.FTS.PressureOn.lipschitzTimeOmegaIcc
import Submission.Work.FTS.PressureOn.omegaSliceRegularPos
import Submission.Work.FTS.PressureOn.aeStronglyMeasurableAndBoundAtZero
import Submission.Work.FTS.PressureOn.biotSavartDecayExplicit
import Submission.Work.StabilityFar.Decay.biotSavart_sub

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PressureOn

/-- **Joint Lipschitz dependence on time, of the vorticity and of the physical velocity.**

`Work.FTS.PressureOn.lipschitz_time_lamb_strips`.

Both conclusions are *uniform in the space variable* Lipschitz bounds on `[0,S]`, `S < T`, with
`t ∈ [0,S]` as the base point.

* **The vorticity.**  This is `Work.FTS.PressureOn.lipschitzTimeOmegaIcc`: `∂ₜω` is jointly
  continuous on the half-open strip `ℝ³ × [0,T)`, so it is bounded on the compact box
  `B(0,max R 0) × [0,S]`, and off that box the slice is identically `0` on `[0,S]`, so its right
  derivative vanishes there as well (the only point needing care is `s = 0`, where uniqueness of
  the one-sided derivative on the half-line is used); the mean value inequality
  (`Work.FTS.PressureOn.lipschitz_time_of_hasDerivWithinAt`) finishes.  The time-continuity of the
  curves `s ↦ ω x s` is `Work.FTS.PressureOn.continuousOn_time_omega_of_strips`.

* **The velocity.**  `physVel ω x s = BS(ω · s) x` is linear in the vorticity argument
  (`Work.StabilityFar.Decay.biotSavart_sub`), so the difference of the two slices is the
  Biot–Savart field of the *difference* vorticity, which is supported in `B(0,max R 0)` and
  bounded by `C |s - t|` by the vorticity bound.  The explicit-constant Biot–Savart estimate
  `Work.FTS.PressureOn.biotSavartDecayExplicit` then gives
  `‖BS(ω · s - ω · t) x‖ ≤ 3 (C|s-t|) R (1+4R²)/(1+‖x‖²) ≤ 3 C R (1+4R²) |s-t|`
  — the uniformity in `x` coming from the `(1+‖x‖²)⁻¹` decay of the Biot–Savart field of a
  compactly supported vorticity.  The inputs of the two additivity/decay lemmas (uniform bound
  and a.e. strong measurability of the slices on `[0,S]`) are
  `Work.FTS.PressureOn.omegaSliceRegularPos` on `(0,S]` together with the extension to `s = 0`
  `Work.FTS.PressureOn.aeStronglyMeasurableAndBoundAtZero`. -/
theorem lipschitz_time_lamb_strips {α : NNReal} {ω : R3 → ℝ → R3} {T S t : ℝ}
    (hS : S ∈ Set.Ioo 0 T) (ht : t ∈ Set.Icc 0 S)
    (hstrips : ∀ S' ∈ Set.Ioo 0 T,
      IsContDiffHolderOn ℝ α (Work.FTS.Physical.physVel ω).uncurry (Set.univ ×ˢ Set.Icc 0 S'))
    (hcurl : ∀ s ∈ Set.Ico 0 T, ∀ x,
      FiniteTimeSingularity.vorticity (fun z => Work.FTS.Physical.physVel ω z s) x = ω x s)
    (hsupp : ∃ R, ∀ s ∈ Set.Icc 0 S, ∀ x, ω x s ≠ 0 → ‖x‖ ≤ R)
    (hcontDt : ContinuousOn (fun q : R3 × ℝ => FiniteTimeSingularity.timeDeriv ω q.1 q.2)
      (Set.univ ×ˢ Set.Ico 0 T))
    (hderiv : ∀ x, ∀ s ∈ Set.Ico 0 T,
      HasDerivWithinAt (ω x) (FiniteTimeSingularity.timeDeriv ω x s) (Set.Ici s) s) :
    (∃ C : ℝ, ∀ x : R3, ∀ s ∈ Set.Icc 0 S, ‖ω x s - ω x t‖ ≤ C * |s - t|) ∧
      (∃ C : ℝ, ∀ x : R3, ∀ s ∈ Set.Icc 0 S,
        ‖Work.FTS.Physical.physVel ω x s - Work.FTS.Physical.physVel ω x t‖ ≤ C * |s - t|) := by
  -- time-continuity of the vorticity curves on `[0,S]`
  have hcontω : ∀ x, ContinuousOn (fun s => ω x s) (Set.Icc 0 S) :=
    continuousOn_time_omega_of_strips hS hstrips hcurl
  -- (a) the vorticity is Lipschitz in time, uniformly in `x`
  obtain ⟨C, hC, hlip⟩ := lipschitzTimeOmegaIcc hS hsupp hcontDt hderiv hcontω
  refine ⟨⟨C, fun x s hs => hlip x s hs t ht⟩, ?_⟩
  -- the support radius, normalised to be nonnegative
  obtain ⟨R₀, hR₀⟩ := hsupp
  set R : ℝ := max R₀ 0 with hRdef
  have hR : 0 ≤ R := by rw [hRdef]; exact le_max_right _ _
  have hsuppR : ∀ s ∈ Set.Icc 0 S, ∀ x, ω x s ≠ 0 → ‖x‖ ≤ R := by
    intro s hs x hx
    rw [hRdef]
    exact le_trans (hR₀ s hs x hx) (le_max_left _ _)
  -- uniform bound and a.e. strong measurability of the vorticity slices on `[0,S]`
  obtain ⟨⟨M, hM, hbdd_pos⟩, hmeas_pos⟩ := omegaSliceRegularPos hS hstrips hcurl
  obtain ⟨hbdd0, hmeas0⟩ :=
    aeStronglyMeasurableAndBoundAtZero hS.1 hM hbdd_pos hmeas_pos hcontω
  have hbdd : ∀ s ∈ Set.Icc 0 S, ∀ x, ‖ω x s‖ ≤ M := by
    intro s hs x
    rcases eq_or_lt_of_le hs.1 with h | h
    · rw [← h]; exact hbdd0 x
    · exact hbdd_pos s ⟨h, hs.2⟩ x
  have hmeas : ∀ s ∈ Set.Icc 0 S,
      MeasureTheory.AEStronglyMeasurable (fun z => ω z s) MeasureTheory.volume := by
    intro s hs
    rcases eq_or_lt_of_le hs.1 with h | h
    · rw [← h]; exact hmeas0
    · exact hmeas_pos s ⟨h, hs.2⟩
  -- (b) the velocity is Lipschitz in time, uniformly in `x`
  refine ⟨3 * C * R * (1 + 4 * R ^ 2), fun x s hs => ?_⟩
  -- linearity of Biot–Savart on the difference of the two slices
  have hsub : Work.LWP.biotSavart (fun z => ω z s - ω z t) x
      = Work.LWP.biotSavart (fun z => ω z s) x - Work.LWP.biotSavart (fun z => ω z t) x := by
    have h := Work.StabilityFar.Decay.biotSavart_sub (f := fun z => ω z s) (g := fun z => ω z t)
      hR hM (fun z => hbdd s hs z) (fun z => hbdd t ht z)
      (fun z hz => by simpa [Metric.mem_closedBall, dist_eq_norm] using hsuppR s hs z hz)
      (fun z hz => by simpa [Metric.mem_closedBall, dist_eq_norm] using hsuppR t ht z hz)
      (hmeas s hs) (hmeas t ht) x
    rwa [show (fun z => ω z s) - (fun z => ω z t) = fun z => ω z s - ω z t from by
      funext z; rw [Pi.sub_apply]] at h
  have hdiff : Work.FTS.Physical.physVel ω x s - Work.FTS.Physical.physVel ω x t
      = Work.LWP.biotSavart (fun z => ω z s - ω z t) x := by
    rw [Work.FTS.Physical.physVel_apply ω x s, Work.FTS.Physical.physVel_apply ω x t, ← hsub]
  rw [hdiff]
  -- the difference field is supported in `B(0,R)`
  have hgsupp : ∀ z, ω z s - ω z t ≠ 0 → z ∈ Metric.closedBall (0 : R3) R := by
    intro z hz
    have h1 : ω z s ≠ 0 ∨ ω z t ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hz (by rw [hcon.1, hcon.2, sub_zero])
    rcases h1 with h | h
    · simpa [Metric.mem_closedBall, dist_eq_norm] using hsuppR s hs z h
    · simpa [Metric.mem_closedBall, dist_eq_norm] using hsuppR t ht z h
  -- the explicit-constant decay of the Biot–Savart field of the difference
  have hdec := biotSavartDecayExplicit (R := R) (M := C * |s - t|) hR
    (mul_nonneg hC (abs_nonneg _)) (fun z => hlip z s hs t ht) hgsupp x
  calc ‖Work.LWP.biotSavart (fun z => ω z s - ω z t) x‖
      ≤ 3 * (C * |s - t|) * R * (1 + 4 * R ^ 2) / (1 + ‖x‖ ^ 2) := hdec
    _ ≤ 3 * (C * |s - t|) * R * (1 + 4 * R ^ 2) :=
        div_le_self (by positivity) (by nlinarith [sq_nonneg ‖x‖])
    _ = (3 * C * R * (1 + 4 * R ^ 2)) * |s - t| := by ring

end Work.FTS.PressureOn
