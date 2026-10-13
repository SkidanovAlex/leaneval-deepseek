/-
# `Work.FTS.PressureOn.tendsto_lamb_decay`

**The Lamb vector of the physical Biot–Savart solution decays at infinity.**  With
`u := physVel ω = BS(ω · t)` the physical Biot–Savart velocity, the claim is

  `∂ₜu(·,t) - u(·,t) × ω(·,t) → 0`   along the cocompact filter of `ℝ³`,

which is the far-field statement consumed by the pressure reconstruction
(`Work.FTS.PressureOn.PressureReconstructionOn`, step "decay of `Φ = ∂ₜu - u×ω`").

## The mathematics

Both terms decay.

* The **cross product** `u(·,t) × ω(·,t)` is *compactly supported*: `ω(·,t)` is supported in the
  ball `B(0,R)` for `t ∈ [0,S]` by hypothesis, so `u × ω` vanishes identically off `B(0,R)`; on
  the cocompact filter one is therefore eventually inside the complement of `B(0,R)`, where the
  term is `0`.

* The **time derivative** `∂ₜu(·,t)`.  The vorticity slices `ω · s` are uniformly bounded and
  a.e. strongly measurable on `[0,S]` (`omegaSliceRegularPos` on `(0,S]` together with the
  extension to `s = 0`, `aeStronglyMeasurableAndBoundAtZero`, which uses the time-continuity of
  the curves `s ↦ ω x s`, `continuousOn_time_omega_of_strips`), and `ω` is Lipschitz in time on
  `[0,S]` uniformly in the space variable (`lipschitzTimeOmegaIcc`: `∂ₜω` is jointly continuous on
  the strip and supported in `B(0,R)`, hence bounded by compactness, and the one-sided mean value
  inequality applies).  Consequently, for every `x`, the *slopes* of `s ↦ u x s` on `(t,S)` are
  bounded by `3 C R (1+4R²)/(1+‖x‖²)`: the difference of the two Biot–Savart fields is the
  Biot–Savart field of the difference vorticity (`biotSavart_sub`), which is supported in `B(0,R)`
  and bounded by `C |y - t|`, and the explicit-constant far-field decay
  (`biotSavartDecayExplicit`) produces the decaying factor `(1+‖x‖²)⁻¹`
  (`normSlopePhysVelLe`).  Since the two-sided derivative at `t`, when it exists, is the limit of
  the right-hand slopes (`deriv_le_of_slope_le_aux`), this gives

    `‖∂ₜu(x,t)‖ ≤ 3 C R (1+4R²)/(1+‖x‖²)`,

  and `(1+‖x‖²)⁻¹ → 0` along the cocompact filter
  (`tendsto_inv_one_add_normSq_cocompact_aux`).

This file only assembles the pieces above, all of which live — already proved — in this directory.
The two `_aux` lemmas at the top are reproduced (verbatim, and only for self-containedness) from
`Submission.Work.FTS.PressureOn.tendsto_timeDeriv_physVel`, so that the present file does not
depend on that module.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.PressureOn.Defs
import Submission.Work.FTS.PressureOn.continuousOn_time_omega_of_strips
import Submission.Work.FTS.PressureOn.lipschitz_time_of_hasDerivWithinAt
import Submission.Work.FTS.PressureOn.lipschitzTimeOmegaIcc
import Submission.Work.FTS.PressureOn.omegaSliceRegularPos
import Submission.Work.FTS.PressureOn.aeStronglyMeasurableAndBoundAtZero
import Submission.Work.FTS.PressureOn.normSlopePhysVelLe

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open Filter Set MeasureTheory
open scoped Topology

namespace Work.FTS.PressureOn

/-! ## Two elementary one-variable / filter lemmas (reproduced, see the module docstring) -/

/-- **A two-sided derivative is bounded by a bound on one-sided difference quotients.**

If the slopes of `g` at `t` are bounded by `K` on `(t,S)`, then so is `deriv g t`: when `g` is
differentiable at `t` the two-sided derivative is the limit of the slopes along `𝓝[Ioi t] t`
(`hasDerivWithinAt_iff_tendsto_slope` + `le_of_tendsto`), and otherwise `deriv g t = 0`
(`deriv_zero_of_not_differentiableAt`). -/
theorem deriv_le_of_slope_le_aux {g : ℝ → R3} {t S K : ℝ} (htS : t < S) (hK : 0 ≤ K)
    (hslope : ∀ y ∈ Set.Ioo t S, ‖(y - t)⁻¹ • (g y - g t)‖ ≤ K) :
    ‖deriv g t‖ ≤ K := by
  have hmem : Set.Ioo t S ∈ 𝓝[Set.Ioi t] t := by
    rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
    exact ⟨Set.Iio S, isOpen_Iio.mem_nhds htS, fun y hy => ⟨hy.2, hy.1⟩⟩
  by_cases hd : DifferentiableAt ℝ g t
  · have hc : HasDerivAt g (deriv g t) t := hd.hasDerivAt
    have hsl : HasDerivWithinAt g (deriv g t) (Set.Ici t) t := hc.hasDerivWithinAt
    have htend : Tendsto (slope g t) (𝓝[Set.Ioi t] t) (𝓝 (deriv g t)) := by
      have h := hasDerivWithinAt_iff_tendsto_slope.mp hsl
      have hset : Set.Ici t \ {t} = Set.Ioi t := by
        ext y
        simp only [Set.mem_sdiff, Set.mem_Ici, Set.mem_singleton_iff, Set.mem_Ioi]
        constructor
        · rintro ⟨h1, h2⟩; exact lt_of_le_of_ne h1 (Ne.symm h2)
        · intro h1; exact ⟨le_of_lt h1, ne_of_gt h1⟩
      rwa [hset] at h
    have h1 : Tendsto (fun y => ‖slope g t y‖) (𝓝[Set.Ioi t] t) (𝓝 ‖deriv g t‖) :=
      (continuous_norm.tendsto _).comp htend
    refine le_of_tendsto h1 ?_
    filter_upwards [hmem] with y hy
    have hsl' : slope g t y = (y - t)⁻¹ • (g y - g t) := rfl
    rw [hsl']
    exact hslope y hy
  · rw [deriv_zero_of_not_differentiableAt hd]
    simpa using hK

/-- **The cocompact squeeze input**: `(1 + ‖x‖²)⁻¹ → 0` along the cocompact filter of `ℝ³`. -/
theorem tendsto_inv_one_add_normSq_cocompact_aux :
    Tendsto (fun x : R3 => (1 + ‖x‖ ^ 2)⁻¹) (cocompact R3) (nhds 0) := by
  have h4 : Tendsto (fun x : R3 => 1 + ‖x‖ ^ 2) (cocompact R3) atTop :=
    tendsto_atTop_mono (fun x => by nlinarith [norm_nonneg x, sq_nonneg (‖x‖ - 1 / 2)])
      tendsto_norm_cocompact_atTop
  exact h4.inv_tendsto_atTop

/-! ## The main statement -/

theorem tendsto_lamb_decay {α : NNReal} {ω : R3 → ℝ → R3} {T S t : ℝ}
    (hS : S ∈ Set.Ioo 0 T) (ht : t ∈ Set.Ico 0 S)
    (hstrips : ∀ S' ∈ Set.Ioo 0 T,
      IsContDiffHolderOn ℝ α (Work.FTS.Physical.physVel ω).uncurry (Set.univ ×ˢ Set.Icc 0 S'))
    (hcurl : ∀ s ∈ Set.Ico 0 T, ∀ x,
      FiniteTimeSingularity.vorticity (fun z => Work.FTS.Physical.physVel ω z s) x = ω x s)
    (hsupp : ∃ R, ∀ s ∈ Set.Icc 0 S, ∀ x, ω x s ≠ 0 → ‖x‖ ≤ R)
    (hcontDt : ContinuousOn (fun q : R3 × ℝ => FiniteTimeSingularity.timeDeriv ω q.1 q.2)
      (Set.univ ×ˢ Set.Ico 0 T))
    (hderiv : ∀ x, ∀ s ∈ Set.Ico 0 T,
      HasDerivWithinAt (ω x) (FiniteTimeSingularity.timeDeriv ω x s) (Set.Ici s) s) :
    Filter.Tendsto (fun x : R3 =>
      FiniteTimeSingularity.timeDeriv (Work.FTS.Physical.physVel ω) x t
        - crossVec (Work.FTS.Physical.physVel ω x t) (ω x t))
      (Filter.cocompact R3) (nhds 0) := by
  have htS : t < S := ht.2
  have ht0 : 0 ≤ t := ht.1
  have htIcc : t ∈ Set.Icc (0 : ℝ) S := ⟨ht0, ht.2.le⟩
  -- time-continuity of the vorticity curves on `[0,S]`
  have hcontω : ∀ x, ContinuousOn (fun s => ω x s) (Set.Icc (0 : ℝ) S) :=
    continuousOn_time_omega_of_strips hS hstrips hcurl
  -- Lipschitz dependence of `ω` on time, uniformly in space
  obtain ⟨C, hC, hlip⟩ := lipschitzTimeOmegaIcc hS hsupp hcontDt hderiv hcontω
  -- uniform bound and a.e. strong measurability of the vorticity slices on `[0,S]`
  obtain ⟨⟨M, hM, hbdd_pos⟩, hmeas_pos⟩ := omegaSliceRegularPos hS hstrips hcurl
  obtain ⟨hbdd0, hmeas0⟩ :=
    aeStronglyMeasurableAndBoundAtZero hS.1 hM hbdd_pos hmeas_pos hcontω
  have hbdd : ∀ s ∈ Set.Icc (0 : ℝ) S, ∀ x, ‖ω x s‖ ≤ M := by
    intro s hs x
    rcases eq_or_lt_of_le hs.1 with h | h
    · rw [← h]; exact hbdd0 x
    · exact hbdd_pos s ⟨h, hs.2⟩ x
  have hmeas : ∀ s ∈ Set.Icc (0 : ℝ) S,
      MeasureTheory.AEStronglyMeasurable (fun z => ω z s) MeasureTheory.volume := by
    intro s hs
    rcases eq_or_lt_of_le hs.1 with h | h
    · rw [← h]; exact hmeas0
    · exact hmeas_pos s ⟨h, hs.2⟩
  -- the support radius, normalised to be nonnegative
  obtain ⟨R₀, hR₀⟩ := hsupp
  set R : ℝ := max R₀ 0 with hRdef
  have hR : 0 ≤ R := by rw [hRdef]; exact le_max_right _ _
  have hsuppR : ∀ s ∈ Set.Icc (0 : ℝ) S, ∀ x, ω x s ≠ 0 → ‖x‖ ≤ R := by
    intro s hs x hx
    rw [hRdef]
    exact le_trans (hR₀ s hs x hx) (le_max_left _ _)
  -- the decaying bound on the time-slopes of the velocity
  have hslope := normSlopePhysVelLe (ω := ω) (S := S) (t := t) (M := M) (C := C) (R := R)
    htIcc hM hC hR hsuppR hbdd hmeas hlip
  -- the decaying bound on `∂ₜu(·,t)`
  have hderivBound : ∀ x : R3,
      ‖FiniteTimeSingularity.timeDeriv (Work.FTS.Physical.physVel ω) x t‖
        ≤ 3 * C * R * (1 + 4 * R ^ 2) / (1 + ‖x‖ ^ 2) := by
    intro x
    have hK : 0 ≤ 3 * C * R * (1 + 4 * R ^ 2) / (1 + ‖x‖ ^ 2) := by positivity
    have h := deriv_le_of_slope_le_aux (g := fun s => Work.FTS.Physical.physVel ω x s)
      (t := t) (S := S) (K := 3 * C * R * (1 + 4 * R ^ 2) / (1 + ‖x‖ ^ 2)) htS hK
      (fun y hy => hslope x y hy)
    simpa only [FiniteTimeSingularity.timeDeriv] using h
  -- `∂ₜu(·,t) → 0` at infinity
  have hA : Filter.Tendsto (fun x : R3 =>
      FiniteTimeSingularity.timeDeriv (Work.FTS.Physical.physVel ω) x t)
      (Filter.cocompact R3) (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero (fun x => norm_nonneg _) (fun x => hderivBound x) ?_
    have h0 : Filter.Tendsto
        (fun x : R3 => 3 * C * R * (1 + 4 * R ^ 2) * (1 + ‖x‖ ^ 2)⁻¹)
        (Filter.cocompact R3) (nhds 0) := by
      simpa using Filter.Tendsto.const_mul (3 * C * R * (1 + 4 * R ^ 2))
        tendsto_inv_one_add_normSq_cocompact_aux
    simpa only [div_eq_mul_inv] using h0
  -- `u(·,t) × ω(·,t) → 0` at infinity: it vanishes off `B(0,R)`
  have hB : Filter.Tendsto (fun x : R3 =>
      crossVec (Work.FTS.Physical.physVel ω x t) (ω x t))
      (Filter.cocompact R3) (nhds 0) := by
    refine Tendsto.congr' ?_ tendsto_const_nhds
    rw [Filter.eventuallyEq_iff_exists_mem]
    refine ⟨(Metric.closedBall (0 : R3) R)ᶜ,
      (isCompact_closedBall (0 : R3) R).compl_mem_cocompact, ?_⟩
    intro x hx
    have hx' : R < ‖x‖ := by
      have h := hx
      rw [Set.mem_compl_iff, Metric.mem_closedBall, dist_eq_norm, sub_zero] at h
      exact not_le.mp h
    have hω0 : ω x t = 0 := by
      by_contra hne
      exact absurd (hsuppR t htIcc x hne) (not_le.mpr hx')
    simp [crossVec, hω0]
  simpa using hA.sub hB

end Work.FTS.PressureOn
