import Mathlib
import Submission.Lib.Unif2.Work.Drive.weakcase_deps
import Submission.Lib.Unif2.Work.Drive.unitPolePlan
import Submission.Lib.Unif2.Work.SimplyConnected.ABS.sweep_domination_aux
import Submission.Lib.Unif2.Commons.Analysis.Complex.exists_ball_factorization_of_analyticAt_zero

open Filter Set
open scoped Topology

namespace Work.Drive

theorem extremal_zero_factorization {X : Type*} [TopologicalSpace X] [T2Space X]
    [ConnectedSpace X] [SecondCountableTopology X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] {y : X} {h : X → ℂ}
    (hh : h ∈ Submission.extremalFamily y) (hne : ∃ x : X, h x ≠ 0) :
    ∃ (ρ r : ℝ) (k : ℕ) (ψ : ℂ → ℂ) (M m : ℝ),
      0 < ρ ∧ ρ ≤ r ∧ 1 ≤ k ∧ 1 ≤ M ∧ 0 < m ∧ m ≤ M ∧
      Metric.closedBall ((chartAt ℂ y) y) r ⊆ (chartAt ℂ y).target ∧
      M * ρ ^ k ≤ 1 ∧
      (∀ w : ℂ, dist w ((chartAt ℂ y) y) < r →
        (h ∘ (chartAt ℂ y).symm) w = (w - (chartAt ℂ y) y) ^ k * ψ w) ∧
      (∀ w : ℂ, dist w ((chartAt ℂ y) y) < r → m ≤ ‖ψ w‖ ∧ ‖ψ w‖ ≤ M) := by
  classical
  obtain ⟨hhol, hbd, hy0⟩ := hh
  let c : OpenPartialHomeomorph X ℂ := chartAt ℂ y
  let a : ℂ := c y
  have hsrc : y ∈ c.source := mem_chart_source ℂ y
  have hsymm : c.symm a = y := by
    show c.symm (c y) = y
    exact c.left_inv hsrc
  have hatgt : a ∈ c.target := by
    show c y ∈ c.target
    exact c.map_source hsrc
  -- the chart pullback of `h` is analytic at `a = c y`
  have hHana : AnalyticAt ℂ (h ∘ c.symm) a := hhol y (mem_univ y)
  have ha0 : (h ∘ c.symm) a = 0 := by
    show h (c.symm a) = 0
    rw [hsymm]
    exact hy0
  -- `h` does not vanish identically near `y` (identity theorem + connectedness)
  have hnotzero : ¬ ∀ᶠ w in 𝓝 a, (h ∘ c.symm) w = 0 := by
    intro hz
    have hev : h =ᶠ[𝓝 y] (fun _ : X => (0 : ℂ)) := by
      have h1 : c.source ∈ 𝓝 y := c.open_source.mem_nhds hsrc
      have h2 : ∀ᶠ z in 𝓝 y, (h ∘ c.symm) (c z) = 0 := (c.continuousAt hsrc).eventually hz
      filter_upwards [h2, h1] with z hz2 hzsrc
      have h3 : h (c.symm (c z)) = 0 := hz2
      rw [c.left_inv hzsrc] at h3
      exact h3
    obtain ⟨x, hx⟩ := hne
    exact hx (Work.SimplyConnected.ABS.holomorphicOnX_eq_zero_of_eventuallyEq_zero hhol hev x)
  -- the local factorization `h ∘ c.symm = (· - a)^k · ψ`, ψ analytic and non-zero at `a`
  obtain ⟨R, k, ψ, hRpos, hRlt, hk1, hψan, hψne, hψeq⟩ :=
    Commons.Analysis.Complex.exists_ball_factorization_of_analyticAt_zero (f := h ∘ c.symm)
      (c := a) (ρ := 1) one_pos hHana ha0 hnotzero
  have hψa_ne : ψ a ≠ 0 := hψne a (Metric.mem_ball_self hRpos)
  have hψa_an : AnalyticAt ℂ ψ a := hψan a (Metric.mem_ball_self hRpos)
  have hψcont : ContinuousAt ψ a := hψa_an.continuousAt
  have hξpos : 0 < ‖ψ a‖ := norm_pos_iff.mpr hψa_ne
  -- a disc on which `‖ψ‖` is comparable to `‖ψ a‖`
  obtain ⟨δ, hδpos, hδ⟩ : ∃ δ : ℝ, 0 < δ ∧
      ∀ w : ℂ, dist w a < δ → dist (ψ w) (ψ a) < ‖ψ a‖ / 2 :=
    Metric.continuousAt_iff.mp hψcont (‖ψ a‖ / 2) (by linarith)
  have hδn : ∀ w : ℂ, dist w a < δ → ‖ψ w - ψ a‖ < ‖ψ a‖ / 2 := by
    intro w hw
    simpa only [dist_eq_norm] using hδ w hw
  -- a disc inside the chart target
  obtain ⟨ε, hεpos, hε⟩ : ∃ ε : ℝ, 0 < ε ∧ Metric.ball a ε ⊆ c.target :=
    Metric.isOpen_iff.mp c.open_target a hatgt
  let M : ℝ := max 1 (3 * ‖ψ a‖ / 2)
  let m : ℝ := ‖ψ a‖ / 2
  let r : ℝ := min (min R δ) (min (ε / 2) (1 / M))
  have hM1 : 1 ≤ M := le_max_left _ _
  have hMpos : 0 < M := lt_of_lt_of_le one_pos hM1
  have hmpos : 0 < m := by
    dsimp only [m]
    linarith
  have hmM : m ≤ M := by
    dsimp only [m, M]
    exact le_trans (by linarith) (le_max_right _ _)
  have hrpos : 0 < r := by
    dsimp only [r]
    exact lt_min (lt_min hRpos hδpos) (lt_min (by linarith) (one_div_pos.mpr hMpos))
  have hrR : r ≤ R := by
    dsimp only [r]
    exact le_trans (min_le_left _ _) (min_le_left _ _)
  have hrδ : r ≤ δ := by
    dsimp only [r]
    exact le_trans (min_le_left _ _) (min_le_right _ _)
  have hrε : r ≤ ε / 2 := by
    dsimp only [r]
    exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hrM : r ≤ 1 / M := by
    dsimp only [r]
    exact le_trans (min_le_right _ _) (min_le_right _ _)
  refine ⟨r, r, k, ψ, M, m, hrpos, le_rfl, hk1, hM1, hmpos, hmM, ?_, ?_, ?_, ?_⟩
  · -- the closed disc of radius `r` sits inside the chart target
    refine subset_trans (Metric.closedBall_subset_closedBall hrε) ?_
    exact subset_trans (Metric.closedBall_subset_ball (by linarith)) hε
  · -- `M * r ^ k ≤ 1`
    have hdiv : 1 / M ≤ 1 := by
      simpa using one_div_le_one_div_of_le (a := (1 : ℝ)) (b := M) one_pos hM1
    have hr1 : r ≤ 1 := le_trans hrM hdiv
    have hpow : r ^ k ≤ r := by
      simpa using pow_le_pow_of_le_one (le_of_lt hrpos) hr1 hk1
    calc M * r ^ k ≤ M * r := mul_le_mul_of_nonneg_left hpow (le_of_lt hMpos)
      _ ≤ M * (1 / M) := mul_le_mul_of_nonneg_left hrM (le_of_lt hMpos)
      _ = 1 := by rw [one_div, mul_inv_cancel₀ hMpos.ne']
  · -- the factorization on the disc of radius `r`
    intro w hw
    exact hψeq w (Metric.mem_ball.mpr (lt_of_lt_of_le hw hrR))
  · -- the two-sided bound on `ψ`
    intro w hw
    have hwδ : dist w a < δ := lt_of_lt_of_le hw hrδ
    have h1 : ‖ψ w - ψ a‖ < ‖ψ a‖ / 2 := hδn w hwδ
    have h2 : ‖ψ a - ψ w‖ < ‖ψ a‖ / 2 := by
      rwa [norm_sub_rev] at h1
    constructor
    · dsimp only [m]
      have h3 : ‖ψ a‖ - ‖ψ w‖ ≤ ‖ψ a - ψ w‖ :=
        (abs_le.mp (abs_norm_sub_norm_le (ψ a) (ψ w))).2
      linarith
    · dsimp only [M]
      have h3 : ‖ψ w‖ - ‖ψ a‖ ≤ ‖ψ w - ψ a‖ :=
        (abs_le.mp (abs_norm_sub_norm_le (ψ w) (ψ a))).2
      exact le_trans (by linarith) (le_max_right _ _)

end Work.Drive
