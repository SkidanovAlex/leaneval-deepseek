import Mathlib
import Submission.Work.RPCore.Defs
import Submission.Work.RPCore.Flow.Basic
import Submission.Work.RPCore.Flow.flow_dist_le
import Submission.Work.RPCore.Flow.uniform_fderiv_sub_le
import Submission.Work.RPCore.Flow.gronwallBound_zero_le
import Submission.Work.RPCore.Flow.variational_solution

/-!
# The variational equation of a flow

For a `C¹` vector field `X : E → E` on a finite-dimensional normed space with a global bound
`‖fderiv ℝ X z‖ ≤ K`, and for *any* map `Φ : ℝ → E → E` such that every point `y` is reached at
time `t` by an integral curve of `X` starting at `y` (`Φ t y`), the flow is differentiable in the
initial condition and its derivative `M t` solves the variational (linearised) equation

`M 0 = 1`,  `M'(t) = fderiv ℝ X (Φ t z) ∘L M t`,

with the Grönwall bound `‖M t - 1‖ ≤ exp (K * t) - 1` on `[0, δ]`, whenever `δ * K < 1`.

The proof has three parts.

* `variational_solution` (delegated): the fundamental solution `M` of a linear ODE
  `N' = A(t) ∘ N`, `N 0 = 1` with `A` continuous and `‖A t‖ ≤ K` exists on `[-T, T]` for
  `T * K < 1`, with `‖N t - 1‖ ≤ exp (K * t) - 1` and `‖N t‖ ≤ exp (K * t)` for `t ∈ [0, T]`.
  Here the interval is taken slightly larger than `[0, δ]`, so that the derivative of `M` is
  two-sided at the endpoints of `[0, δ]`.

* `flow_dist_le` (delegated): Grönwall's inequality along two integral curves gives
  `dist (Φ t y) (Φ t z) ≤ exp (K * t) * dist y z` for `t ≥ 0`.

* The remaining step is the differentiability of `Φ t` at `z`.  Writing
  `W s = Φ s y - Φ s z`, `R s = W s - M s (y - z)` and
  `ρ s = X (Φ s y) - X (Φ s z) - fderiv ℝ X (Φ s z) (W s)`, the ODEs for `W` and `M` give
  `R' = A s (R s) + ρ s` and `R 0 = 0`, and Grönwall yields
  `‖R t‖ ≤ exp (K t) ∫₀ᵗ ‖ρ s‖ ds`.  Uniform differentiability of `X` on the compact trajectory
  (`uniform_fderiv_sub_le`) bounds `‖ρ s‖ ≤ ε ‖W s‖ ≤ ε exp (K δ) ‖y - z‖`, so
  `‖R t‖ = O(‖y - z‖)` with a constant that can be made arbitrarily small.  This is precisely
  `HasFDerivAt (Φ t) (M t) z`.
-/

set_option autoImplicit false

open scoped Topology ContDiff
open Set

namespace Work.RPCore.Flow

theorem flow_variational_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [FiniteDimensional ℝ E] (X : E → E) (hX : ContDiff ℝ 1 X) (K : ℝ)
    (hK : ∀ z, ‖fderiv ℝ X z‖ ≤ K) (Φ : ℝ → E → E)
    (hΦ : ∀ t y, ∃ γ : ℝ → E, γ 0 = y ∧ IsIntegralCurve γ (fun _ z => X z) ∧ γ t = Φ t y)
    {δ : ℝ} (hδ : 0 < δ) (hδK : δ * K < 1) (z : E) :
    ∃ M : ℝ → E →L[ℝ] E, M 0 = 1 ∧
      (∀ t ∈ Set.Icc 0 δ, HasDerivAt M (fderiv ℝ X (Φ t z) ∘L M t) t) ∧
      (∀ t ∈ Set.Icc 0 δ, HasFDerivAt (Φ t) (M t) z) ∧
      (∀ t ∈ Set.Icc 0 δ, ‖M t - 1‖ ≤ Real.exp (K * t) - 1) := by
  classical
  -- `K ≥ 0`, continuity of the derivative and the integral curves of `hΦ`
  have hK0 : 0 ≤ K := (norm_nonneg (fderiv ℝ X 0)).trans (hK 0)
  have hXc : Continuous (fderiv ℝ X) := hX.continuous_fderiv (by norm_num)
  have hLip : LipschitzWith (Port.ODE.lipConst K) X := Port.ODE.lipschitzWith_lipConst hX hK
  have hcurve : ∀ y : E, IsIntegralCurve (fun s : ℝ => Φ s y) (fun _ z => X z) :=
    fun y => Port.ODE.isIntegralCurve_flow hLip Φ hΦ y
  have hcurvez : Continuous (fun s : ℝ => Φ s z) := (hcurve z).continuous
  -- a time `T > δ` with `T * K < 1`, so that `[0, δ]` sits in the interior of `[-T, T]`
  set T : ℝ := δ + (1 - δ * K) / (2 * max K 1) with hTdef
  have hden : 0 < 2 * max K 1 := by
    have h : (1:ℝ) ≤ max K 1 := le_max_right _ _
    linarith
  have hnum : 0 < 1 - δ * K := by linarith
  have hTgt : δ < T := by
    rw [hTdef]
    have : 0 < (1 - δ * K) / (2 * max K 1) := div_pos hnum hden
    linarith
  have hTpos : 0 < T := lt_trans hδ hTgt
  have hKle : K ≤ max K 1 := le_max_left _ _
  have hTK : T * K < 1 := by
    have h2 : (1 - δ * K) / (2 * max K 1) * K ≤ (1 - δ * K) / 2 := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ hden (by norm_num : (0:ℝ) < 2)]
      nlinarith [hnum, hKle]
    have h1 : T * K = δ * K + (1 - δ * K) / (2 * max K 1) * K := by rw [hTdef]; ring
    rw [h1]; linarith
  -- the fundamental solution of the variational equation
  obtain ⟨M, hM0, hMder, _hMbd, hM1bd⟩ :=
    variational_solution (fun t => fderiv ℝ X (Φ t z)) hTpos
      (hXc.comp hcurvez).continuousOn (fun t _ => hK _) hTK
  refine ⟨M, hM0, ?_, ?_, ?_⟩
  · -- the variational equation: `M' = fderiv X (Φ t z) ∘L M t` on `[0, δ]`
    intro t ht
    have htT : t ∈ Set.Icc (-T) T := ⟨by linarith [ht.1], by linarith [ht.2, hTgt]⟩
    exact (hMder t htT).hasDerivAt (Icc_mem_nhds (by linarith [ht.1]) (by linarith [ht.2, hTgt]))
  · -- differentiability of `Φ t` at `z`, with derivative `M t`
    intro t ht
    rw [hasFDerivAt_iff_isLittleO_nhds_zero]
    refine Asymptotics.IsLittleO.of_bound ?_
    intro c hc
    set C : ℝ := δ * Real.exp (2 * K * δ) + 1 with hCdef
    have hCpos : 0 < C := by rw [hCdef]; positivity
    set εd : ℝ := c / C with hεddef
    have hεdpos : 0 < εd := by rw [hεddef]; exact div_pos hc hCpos
    -- uniform differentiability of `X` on the compact trajectory, at tolerance `εd`
    obtain ⟨η, hηpos, hη⟩ :=
      uniform_fderiv_sub_le X hX (isCompact_Icc.image hcurvez) hεdpos
    set ρ : ℝ := η / Real.exp (K * δ) with hρdef
    have hρpos : 0 < ρ := by rw [hρdef]; positivity
    filter_upwards [Metric.ball_mem_nhds (0:E) hρpos] with h hh
    have hhnorm : ‖h‖ < ρ := by rw [Metric.mem_ball, dist_zero_right] at hh; exact hh
    have hηρ : Real.exp (K * δ) * ρ = η := by rw [hρdef]; field_simp
    -- the difference of the two trajectories, the second-order remainder and the error
    set W : ℝ → E := fun s => Φ s (z + h) - Φ s z with hWdef
    set ρs : ℝ → E := fun s => X (Φ s (z + h)) - X (Φ s z) - fderiv ℝ X (Φ s z) (W s) with hρsdef
    set R : ℝ → E := fun s => W s - M s h with hRdef
    have hMcont : ContinuousOn M (Set.Icc (-T) T) := fun s hs => (hMder s hs).continuousWithinAt
    have hMcont' : ContinuousOn M (Set.Icc 0 t) :=
      hMcont.mono (fun s hs => ⟨by linarith [hs.1], by linarith [hs.2, ht.2, hTgt]⟩)
    have hRcont : ContinuousOn R (Set.Icc 0 t) := by
      have hWc : Continuous W := (hcurve (z+h)).continuous.sub (hcurve z).continuous
      have hMh : ContinuousOn (fun s => M s h) (Set.Icc 0 t) := hMcont'.clm_apply continuousOn_const
      have hsub : ContinuousOn (W - fun s => M s h) (Set.Icc 0 t) := hWc.continuousOn.sub hMh
      rw [hRdef]
      convert hsub using 1
    -- `R` satisfies the linear ODE with source `ρs`
    have hRderiv : ∀ s ∈ Set.Ico 0 t,
        HasDerivWithinAt R (fderiv ℝ X (Φ s z) (R s) + ρs s) (Set.Ici s) s := by
      intro s hs
      have hsT : s ∈ Set.Icc (-T) T := ⟨by linarith [hs.1], by linarith [hs.2, ht.2, hTgt]⟩
      have hMs : HasDerivAt M (fderiv ℝ X (Φ s z) ∘L M s) s :=
        (hMder s hsT).hasDerivAt
          (Icc_mem_nhds (by linarith [hs.1]) (by linarith [hs.2, ht.2, hTgt]))
      have h1 : HasDerivWithinAt W (X (Φ s (z+h)) - X (Φ s z)) (Set.Ici s) s :=
        ((hcurve (z+h)) s).hasDerivWithinAt.sub ((hcurve z) s).hasDerivWithinAt
      have h2 : HasDerivWithinAt (fun y => M y h) (fderiv ℝ X (Φ s z) (M s h)) (Set.Ici s) s := by
        have hh2 := hMs.clm_apply (hasDerivAt_const (x := s) h)
        simpa using hh2.hasDerivWithinAt
      have h3 : HasDerivWithinAt (fun y => W y - M y h)
          (X (Φ s (z+h)) - X (Φ s z) - fderiv ℝ X (Φ s z) (M s h)) (Set.Ici s) s := by
        convert h1.sub h2 using 1
      have h4 : fderiv ℝ X (Φ s z) (R s) + ρs s
          = X (Φ s (z+h)) - X (Φ s z) - fderiv ℝ X (Φ s z) (M s h) := by
        simp only [hRdef, hρsdef, hWdef, map_sub]
        abel
      rw [h4, hRdef]
      exact h3
    -- the source term is small: `‖ρs s‖ ≤ εd exp (K δ) ‖h‖`
    have hρbound : ∀ s ∈ Set.Icc 0 t, ‖ρs s‖ ≤ εd * Real.exp (K * δ) * ‖h‖ := by
      intro s hs
      have hsδ : s ∈ Set.Icc 0 δ := ⟨hs.1, le_trans hs.2 ht.2⟩
      have hWs : ‖W s‖ ≤ Real.exp (K * δ) * ‖h‖ := by
        have hflow := flow_dist_le X hX hK Φ hΦ (t := s) hs.1 (z + h) z
        rw [dist_eq_norm, dist_eq_norm, add_sub_cancel_left] at hflow
        calc ‖W s‖ = ‖Φ s (z+h) - Φ s z‖ := by simp [hWdef]
          _ ≤ Real.exp (K * s) * ‖h‖ := hflow
          _ ≤ Real.exp (K * δ) * ‖h‖ := mul_le_mul_of_nonneg_right
                (Real.exp_le_exp.mpr (by nlinarith [hsδ.2, hK0])) (norm_nonneg h)
      have hWsη : ‖Φ s (z+h) - Φ s z‖ ≤ η := by
        have h2 : ‖W s‖ < η := by
          calc ‖W s‖ ≤ Real.exp (K*δ) * ‖h‖ := hWs
            _ < Real.exp (K*δ) * ρ := mul_lt_mul_of_pos_left hhnorm (Real.exp_pos _)
            _ = η := hηρ
        simpa [hWdef] using h2.le
      have hηs := hη (Φ s z) ⟨s, hsδ, rfl⟩ (Φ s (z+h)) hWsη
      calc ‖ρs s‖ = ‖X (Φ s (z+h)) - X (Φ s z) - fderiv ℝ X (Φ s z) (Φ s (z+h) - Φ s z)‖ := by
              simp [hρsdef, hWdef]
        _ ≤ εd * ‖Φ s (z+h) - Φ s z‖ := hηs
        _ ≤ εd * (Real.exp (K * δ) * ‖h‖) :=
              mul_le_mul_of_nonneg_left (by simpa [hWdef] using hWs) hεdpos.le
        _ = εd * Real.exp (K * δ) * ‖h‖ := by ring
    -- Grönwall for the error
    have hgron : ‖R t‖ ≤ εd * Real.exp (K * δ) * ‖h‖ * t * Real.exp (K * t) := by
      have hε0 : 0 ≤ εd * Real.exp (K * δ) * ‖h‖ :=
        mul_nonneg (mul_nonneg hεdpos.le (Real.exp_pos _).le) (norm_nonneg h)
      have hmain := norm_le_gronwallBound_of_norm_deriv_right_le
        (f := R) (f' := fun s => fderiv ℝ X (Φ s z) (R s) + ρs s)
        (δ := 0) (K := K) (ε := εd * Real.exp (K * δ) * ‖h‖) (a := 0) (b := t)
        hRcont hRderiv (by
          have hz1 : Φ 0 (z+h) = z+h := Port.ODE.flow_zero Φ hΦ (z+h)
          have hz2 : Φ 0 z = z := Port.ODE.flow_zero Φ hΦ z
          have hz : R 0 = 0 := by simp [hRdef, hWdef, hM0, hz1, hz2]
          rw [hz, norm_zero]) (by
          intro s hs
          have h1 : ‖fderiv ℝ X (Φ s z) (R s)‖ ≤ K * ‖R s‖ := by
            calc ‖fderiv ℝ X (Φ s z) (R s)‖ ≤ ‖fderiv ℝ X (Φ s z)‖ * ‖R s‖ :=
                  ContinuousLinearMap.le_opNorm _ _
              _ ≤ K * ‖R s‖ := mul_le_mul_of_nonneg_right (hK _) (norm_nonneg _)
          calc ‖fderiv ℝ X (Φ s z) (R s) + ρs s‖
              ≤ ‖fderiv ℝ X (Φ s z) (R s)‖ + ‖ρs s‖ := norm_add_le _ _
            _ ≤ K * ‖R s‖ + εd * Real.exp (K * δ) * ‖h‖ :=
                  add_le_add h1 (hρbound s ⟨hs.1, le_of_lt hs.2⟩))
      have := hmain t ⟨ht.1, le_rfl⟩
      rw [sub_zero] at this
      calc ‖R t‖ ≤ gronwallBound 0 K (εd * Real.exp (K*δ) * ‖h‖) t := this
        _ ≤ (εd * Real.exp (K*δ) * ‖h‖) * t * Real.exp (K * t) :=
            gronwallBound_zero_le hK0 hε0 ht.1
    -- the resulting estimate, with `h`-linear constant
    have hfinal : ‖R t‖ ≤ εd * δ * Real.exp (2 * K * δ) * ‖h‖ := by
      have hb : 0 ≤ εd * Real.exp (K*δ) * ‖h‖ :=
        mul_nonneg (mul_nonneg hεdpos.le (Real.exp_pos _).le) (norm_nonneg h)
      have hexp : Real.exp (K * t) ≤ Real.exp (K * δ) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht.2 hK0)
      have hb2 : 0 ≤ εd * Real.exp (K*δ) * ‖h‖ * t := mul_nonneg hb ht.1
      calc ‖R t‖ ≤ εd * Real.exp (K*δ) * ‖h‖ * t * Real.exp (K*t) := hgron
        _ ≤ εd * Real.exp (K*δ) * ‖h‖ * t * Real.exp (K*δ) :=
              mul_le_mul_of_nonneg_left hexp hb2
        _ ≤ εd * Real.exp (K*δ) * ‖h‖ * δ * Real.exp (K*δ) :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ht.2 hb) (Real.exp_pos _).le
        _ = εd * δ * Real.exp (2 * K * δ) * ‖h‖ := by
              rw [show Real.exp (2 * K * δ) = Real.exp (K*δ) * Real.exp (K*δ) from by
                rw [← Real.exp_add]; ring_nf]
              ring
    have hlast : εd * δ * Real.exp (2 * K * δ) * ‖h‖ ≤ c * ‖h‖ := by
      rw [hεddef]
      have hfrac : δ * Real.exp (2 * K * δ) / C ≤ 1 := by
        rw [div_le_one hCpos]
        linarith [hCdef, Real.exp_pos (2 * K * δ)]
      calc c / C * δ * Real.exp (2 * K * δ) * ‖h‖
          = c * (δ * Real.exp (2 * K * δ) / C) * ‖h‖ := by ring
        _ ≤ c * 1 * ‖h‖ :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hfrac hc.le) (norm_nonneg h)
        _ = c * ‖h‖ := by ring
    calc ‖Φ t (z + h) - Φ t z - M t h‖ = ‖R t‖ := by simp [hRdef, hWdef]
      _ ≤ εd * δ * Real.exp (2 * K * δ) * ‖h‖ := hfinal
      _ ≤ c * ‖h‖ := hlast
  · -- the Grönwall bound on `M`
    intro t ht
    exact hM1bd t ⟨ht.1, by linarith [ht.2, hTgt]⟩

end Work.RPCore.Flow
