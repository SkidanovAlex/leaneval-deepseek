import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Submission.Work.FTS.PressureOn.Defs
import Submission.Work.FTS.PressureOn.lipschitz_time_of_hasDerivWithinAt

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Topology

namespace Work.FTS.PressureOn

/-- **Lipschitz (hence `α`-Hölder, `α ≤ 1`) dependence of the vorticity on time, on `[0,S]`.**
(piece of `tendsto_timeDeriv_physVel`.)

If `ω · s` is supported in a fixed ball for `s ∈ Icc 0 S` with `S ∈ (0,T)`, the right derivative
`∂ₜω` is jointly continuous on `ℝ³ × [0,T)`, `∂ₜω` is the right derivative of `ω` along `Ici s`
at every `s ∈ [0,T)`, and every curve `ω x ·` is continuous on `[0,S]`, then there is a constant
`C ≥ 0` with `‖ω x s - ω x t‖ ≤ C |s - t|` for all `x` and all `s, t ∈ [0,S]`.

Recipe:
* a *uniform* bound `∃ C ≥ 0, ∀ y, ∀ s ∈ Ico 0 S, ‖timeDeriv ω y s‖ ≤ C`: on the compact set
  `Metric.closedBall 0 (max R 0) ×ˢ Icc 0 S ⊆ univ ×ˢ Ico 0 T` use
  `IsCompact.exists_bound_of_continuousOn` and `hcontDt`; off the support ball (`‖y‖ > max R 0`)
  the slice `ω y ·` is identically `0` on `[0,S]`, so for `s ∈ Ico 0 S` the function is locally
  `0` on `Ici s` (there is room `(s, (s+S)/2) ⊆ [0,S]`), whence `HasDerivWithinAt (ω y) 0 (Ici s) s`
  (`Filter.EventuallyEq.hasDerivWithinAt_iff` + `hasDerivWithinAt_const`), and uniqueness of the
  within-derivative on the uniquely-differentiable set `Ici s` (`uniqueDiffWithinAt_Ici` together
  with `hderiv`) gives `timeDeriv ω y s = 0`.  (`HasFDerivWithinAt.unique`.)
* the Lipschitz bound then follows from `Work.FTS.PressureOn.lipschitz_time_of_hasDerivWithinAt`
  (same directory, sorry-free) applied with `T := S`, `hcont := hcontω`, `hderiv` restricted to
  `Ico 0 S ⊆ Ico 0 T`, and the bound above.

Note the bound at `s = 0` for `‖y‖ > max R 0` genuinely needs the uniqueness argument (`Ici 0` is
not a two-sided neighbourhood of `0`), which is why the compactness
`Work.StabilityFar.Decay.timeDeriv_eq_zero_of_notMem_closedBall` is *not* directly applicable. -/
theorem lipschitzTimeOmegaIcc {ω : R3 → ℝ → R3} {T S : ℝ}
    (hS : S ∈ Set.Ioo 0 T)
    (hsupp : ∃ R, ∀ s ∈ Set.Icc 0 S, ∀ x, ω x s ≠ 0 → ‖x‖ ≤ R)
    (hcontDt : ContinuousOn (fun q : R3 × ℝ => FiniteTimeSingularity.timeDeriv ω q.1 q.2)
      (Set.univ ×ˢ Set.Ico 0 T))
    (hderiv : ∀ x, ∀ s ∈ Set.Ico 0 T,
      HasDerivWithinAt (ω x) (FiniteTimeSingularity.timeDeriv ω x s) (Set.Ici s) s)
    (hcontω : ∀ x, ContinuousOn (fun s => ω x s) (Set.Icc 0 S)) :
    ∃ C, 0 ≤ C ∧ ∀ x, ∀ s ∈ Set.Icc 0 S, ∀ t ∈ Set.Icc 0 S,
      ‖ω x s - ω x t‖ ≤ C * |s - t| := by
  obtain ⟨R, hR⟩ := hsupp
  -- `[0,S]` sits inside `[0,T)`
  have hIcc_sub : Set.Icc (0 : ℝ) S ⊆ Set.Ico 0 T :=
    fun x hx => ⟨hx.1, lt_of_le_of_lt hx.2 hS.2⟩
  have hIco_sub : Set.Ico (0 : ℝ) S ⊆ Set.Ico 0 T :=
    fun x hx => ⟨hx.1, lt_of_lt_of_le hx.2 (le_of_lt hS.2)⟩
  -- the compact box `closedBall 0 (max R 0) × [0,S]` lies in the domain of `hcontDt`
  have hKcompact : IsCompact (Metric.closedBall (0 : R3) (max R 0) ×ˢ Set.Icc (0 : ℝ) S) :=
    (isCompact_closedBall 0 (max R 0)).prod isCompact_Icc
  have hKcont : ContinuousOn (fun q : R3 × ℝ => FiniteTimeSingularity.timeDeriv ω q.1 q.2)
      (Metric.closedBall (0 : R3) (max R 0) ×ˢ Set.Icc (0 : ℝ) S) :=
    hcontDt.mono (Set.prod_mono (Set.subset_univ _) hIcc_sub)
  obtain ⟨C₀, hC₀⟩ := hKcompact.exists_bound_of_continuousOn hKcont
  refine ⟨max C₀ 0, le_max_right _ _, ?_⟩
  -- uniform bound for `∂ₜω` on `[0,S]`
  have hbound : ∀ y, ∀ s ∈ Set.Ico 0 S,
      ‖FiniteTimeSingularity.timeDeriv ω y s‖ ≤ max C₀ 0 := by
    intro y s hs
    by_cases hy : ‖y‖ ≤ max R 0
    · have hmem : (y, s) ∈ Metric.closedBall (0 : R3) (max R 0) ×ˢ Set.Icc (0 : ℝ) S :=
        ⟨by simpa [Metric.mem_closedBall, dist_eq_norm] using hy, ⟨hs.1, le_of_lt hs.2⟩⟩
      exact le_trans (hC₀ (y, s) hmem) (le_max_left _ _)
    · -- off the support ball the slice is identically `0` on `[0,S]`, hence so is its derivative
      rw [not_le] at hy
      have hz : ∀ s' ∈ Set.Icc (0 : ℝ) S, ω y s' = 0 := by
        intro s' hs'
        by_contra hne
        exact absurd (hR s' hs' y hne) (not_le.mpr (lt_of_le_of_lt (le_max_left R 0) hy))
      have hzero : FiniteTimeSingularity.timeDeriv ω y s = 0 := by
        have hd1 : HasDerivWithinAt (ω y) (FiniteTimeSingularity.timeDeriv ω y s)
            (Set.Ici s) s := hderiv y s (hIco_sub hs)
        -- `ω y` agrees with `0` on a relative neighbourhood of `s` in `Ici s`
        have hmem : Set.Ici s ∩ Set.Iio S ∈ 𝓝[Set.Ici s] s := by
          rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
          exact ⟨Set.Iio S, Iio_mem_nhds hs.2, fun x hx => ⟨hx.2, hx.1⟩⟩
        have hsub : Set.EqOn (fun x => ω y x) (fun _ => (0 : R3)) (Set.Ici s ∩ Set.Iio S) :=
          fun x hx => hz x ⟨le_trans hs.1 hx.1, le_of_lt hx.2⟩
        have hev : (fun x => ω y x) =ᶠ[𝓝[Set.Ici s] s] (fun _ => (0 : R3)) :=
          Filter.eventuallyEq_of_mem hmem hsub
        have hd2 : HasDerivWithinAt (ω y) 0 (Set.Ici s) s :=
          (hev.hasDerivWithinAt_iff_of_mem (le_refl s)).mpr
            (hasDerivWithinAt_const s (Set.Ici s) (0 : R3))
        -- uniqueness of the within-derivative on the half-line `Ici s`
        have huniq := (uniqueDiffWithinAt_Ici s).eq hd1.hasFDerivWithinAt hd2.hasFDerivWithinAt
        have hval := congrArg (fun L : ℝ →L[ℝ] R3 => L 1) huniq
        simpa using hval
      rw [hzero, norm_zero]
      exact le_max_right _ _
  exact lipschitz_time_of_hasDerivWithinAt (T := S) hcontω
    (fun y s hs => hderiv y s (hIco_sub hs)) hbound

end Work.FTS.PressureOn
