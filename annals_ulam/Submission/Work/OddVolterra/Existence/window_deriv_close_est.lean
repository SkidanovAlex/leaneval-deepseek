import Mathlib
import Submission.Work.OddVolterra.Existence.C1Bounds
import Submission.Work.OddVolterra.WinData.clamped_hder_unit
import Submission.Work.OddVolterra.WinData.clamped_base_identity
import Submission.Work.OddVolterra.WinData.thetaM_deriv_close_ext
import Submission.Work.OddVolterra.WinData.thetaM_state_lipschitz_ext
import Submission.Work.OddVolterra.WinData.xi_deriv_close
import Submission.Work.OddVolterra.WinData.gcl_deriv_close
import Submission.Work.OddCurveB.Engine.volterra_long_exists_ball
import Submission.Work.VolterraLong.GronwallUnique
import Submission.Work.VolterraLong.deriv_from_equation_eps
import Submission.Work.OddVolterra.Existence.godd_injective_modulus_state_ball_compat
import Submission.Work.OddCurveB.Step2.DerivWide

namespace Work.OddVolterra.Existence

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

/-- **The `C¹`-closeness of the window solution on the closed window `[1/4, 19/20]`.**

Reduction to the wide derivative-closeness core `Work.OddCurveB.Step2.w_window_deriv_close_core`
(`Submission/Work/OddCurveB/Step2/DerivWide.lean`), which gives the estimate on the *open*
window `Ioo (1/4) (9/10)` for every solution satisfying the paper's system, agreeing with
`baseState` past `9/10` and lying in the ball of radius `1/2` around `baseState` on `[1/4,1]`.

The two reductions are:

* the ball hypothesis of the core follows from the hypotheses here, because `19/20 > 9/10`:
  on `[1/4, 19/20]` the state is within `9/20 ≤ 1/2` of the ball's state, while on
  `[19/20, 1] ⊂ [9/10, 1]` it *equals* the ball's state by the tail hypothesis;
* the conclusion is then extended from the open window to `[1/4, 19/20]`: on `(9/10, 19/20]`
  the state coincides with `baseState` on a neighbourhood, so the derivatives agree; the two
  endpoints `s = 1/4` and `s = 9/10` follow from the continuity of `deriv Z` (as `Z` is `C^∞`
  on the open set `(0,∞)`) and of `deriv baseState`. -/
theorem window_deriv_close_est (n : ℕ) (hn : 1 ≤ n) :
    ∃ K ε₁ : ℝ, 0 < K ∧ 0 < ε₁ ∧ ε₁ ≤ 1 / 100 ∧
      ∀ (h : ℝ → ℝ) (Z : ℝ → Work.OddVolterra.St) (ε : ℝ), 0 < ε → ε ≤ ε₁ →
        Work.OddVolterra.Existence.IsSmallFlatBumpThree n ε h → h 0 = 0 →
        ContDiffOn ℝ (⊤ : ℕ∞) Z (Set.Ioi (0 : ℝ)) →
        (∀ s ∈ Set.Ioo (1 / 4 : ℝ) 1,
          Work.OddVolterra.Godd n h s (Z s) =
            (∫ σ in s..(1 : ℝ), Work.OddVolterra.Theta n h s σ (Z σ)) +
              Work.OddVolterra.Xi n h s) →
        (∀ s : ℝ, 1 - Work.OddVolterra.tau ≤ s → Z s = Work.OddVolterra.baseState s) →
        (∀ s ∈ Set.Icc (1 / 4 : ℝ) (19 / 20 : ℝ),
          dist (Z s) (Work.OddVolterra.baseState s) ≤ 9 / 20) →
        ∀ s ∈ Set.Icc (1 / 4 : ℝ) (19 / 20 : ℝ),
          dist (deriv Z s) (deriv (Work.OddVolterra.baseState : ℝ → Work.OddVolterra.St) s)
            ≤ K * ε := by
  -- the derivative-closeness core on the wide open window `(1/4, 9/10)`
  obtain ⟨C, ε₁, hCpos, hε₁pos, hε₁100, hwide⟩ :=
    Work.OddCurveB.Step2.w_window_deriv_close_core n hn
  refine ⟨C, ε₁, hCpos, hε₁pos, hε₁100, ?_⟩
  intro h Z ε hεpos hεε₁ hbump _h0 hZsm0 heq htail hball
  -- the tail hypothesis rewritten with `tau = 1/10`
  have htau : (1 : ℝ) - Work.OddVolterra.tau = 9 / 10 := by
    rw [show Work.OddVolterra.tau = 1 / 10 from rfl]; norm_num
  have htail' : ∀ s : ℝ, 9 / 10 ≤ s → Z s = Work.OddVolterra.baseState s :=
    fun s hs => htail s (by rw [htau]; exact hs)
  -- smoothness on `(1/4,∞)` and continuity on `[1/4,1]`
  have hZsm : ContDiffOn ℝ (⊤ : ℕ∞) Z (Set.Ioi (1 / 4 : ℝ)) :=
    hZsm0.mono (Set.Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 1 / 4))
  have hZcont : ContinuousOn Z (Set.Icc (1 / 4 : ℝ) 1) :=
    (hZsm0.continuousOn).mono (fun x hx => by
      simp only [Set.mem_Ioi] at *; linarith [hx.1])
  -- the radius-`1/2` state ball on `[1/4,1]`: the gap `(19/20,1]` is inside the tail `[9/10,1]`
  have hball2 : ∀ s ∈ Set.Icc (1 / 4 : ℝ) 1,
      dist (Z s) (Work.OddVolterra.baseState s) ≤ 1 / 2 := by
    intro s hs
    rcases lt_or_ge s (19 / 20 : ℝ) with hlt | hle
    · have h1 := hball s ⟨hs.1, le_of_lt hlt⟩
      linarith
    · rw [htail' s (by linarith), dist_self]
      norm_num
  -- the core itself
  have hmain : ∀ s ∈ Set.Ioo (1 / 4 : ℝ) (9 / 10 : ℝ),
      dist (deriv Z s) (deriv (Work.OddVolterra.baseState : ℝ → Work.OddVolterra.St) s)
        ≤ C * ε :=
    hwide h Z ε hεpos hεε₁ hbump hZsm hZcont heq htail' hball2
  -- continuity of the two derivatives at the two endpoints
  have hdZ : ContinuousOn (deriv Z) (Set.Ioi (0 : ℝ)) :=
    hZsm0.continuousOn_deriv_of_isOpen isOpen_Ioi (by simp)
  have hdZc : ∀ x ∈ Set.Ioi (0 : ℝ), ContinuousAt (deriv Z) x :=
    fun x hx => hdZ.continuousAt (isOpen_Ioi.mem_nhds hx)
  have hdb : Continuous (deriv (Work.OddVolterra.baseState : ℝ → Work.OddVolterra.St)) := by
    have hcb : ContDiff ℝ (⊤ : ℕ∞)
        (Work.OddVolterra.baseState : ℝ → Work.OddVolterra.St) :=
      contDiff_baseState_comp.comp (contDiff_id.prodMk
        (contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (fun _ : ℝ => (0 : Work.OddVolterra.St))))
    exact hcb.continuous_deriv (by simp)
  intro s hs
  rcases lt_trichotomy s (9 / 10 : ℝ) with hlt9 | heq9 | hgt9
  · -- `s < 9/10`: either interior, or the left endpoint
    rcases eq_or_lt_of_le hs.1 with h14 | h14
    · -- `s = 1/4`: right-hand limit
      subst h14
      haveI : (𝓝[>] (1 / 4 : ℝ)).NeBot := nhdsWithin_Ioi_neBot le_rfl
      have hF : Tendsto (fun u : ℝ => dist (deriv Z u)
            (deriv (Work.OddVolterra.baseState : ℝ → Work.OddVolterra.St) u))
          (𝓝[>] (1 / 4 : ℝ))
          (𝓝 (dist (deriv Z (1 / 4))
            (deriv (Work.OddVolterra.baseState : ℝ → Work.OddVolterra.St) (1 / 4)))) :=
        ((hdZc (1 / 4) (by norm_num)).tendsto.dist hdb.continuousAt).mono_left
          nhdsWithin_le_nhds
      refine le_of_tendsto hF ?_
      rw [eventually_nhdsWithin_iff]
      filter_upwards [Iio_mem_nhds (show (1 / 4 : ℝ) < 9 / 10 by norm_num)] with u hu hgu
      exact hmain u ⟨hgu, hu⟩
    · exact hmain s ⟨h14, hlt9⟩
  · -- `s = 9/10`: left-hand limit
    subst heq9
    haveI : (𝓝[<] (9 / 10 : ℝ)).NeBot := nhdsWithin_Iio_neBot le_rfl
    have hF : Tendsto (fun u : ℝ => dist (deriv Z u)
          (deriv (Work.OddVolterra.baseState : ℝ → Work.OddVolterra.St) u))
        (𝓝[<] (9 / 10 : ℝ))
        (𝓝 (dist (deriv Z (9 / 10))
          (deriv (Work.OddVolterra.baseState : ℝ → Work.OddVolterra.St) (9 / 10)))) :=
      ((hdZc (9 / 10) (by norm_num)).tendsto.dist hdb.continuousAt).mono_left
        nhdsWithin_le_nhds
    refine le_of_tendsto hF ?_
    rw [eventually_nhdsWithin_iff]
    filter_upwards [Ioi_mem_nhds (show (1 / 4 : ℝ) < 9 / 10 by norm_num)] with u hu hlu
    exact hmain u ⟨hu, hlu⟩
  · -- `9/10 < s`: `Z` agrees with `baseState` on a neighbourhood
    have hev : Z =ᶠ[𝓝 s] (Work.OddVolterra.baseState : ℝ → Work.OddVolterra.St) := by
      filter_upwards [Ici_mem_nhds hgt9] with x hx
      exact htail' x hx
    rw [hev.deriv_eq, dist_self]
    exact le_of_lt (mul_pos hCpos hεpos)

end Work.OddVolterra.Existence
