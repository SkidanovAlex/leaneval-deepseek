import Mathlib
import Submission.Lib.Unif2.Work.SimplyConnected.ABS.Defs
import Submission.Lib.Unif2.RiemannSurface
import Submission.Lib.Unif2.DirichletX
import Submission.Lib.Unif2.GreenFunction
import Submission.Lib.Unif2.Work.Analysis.RiemannSurface.chartBall_open
import Submission.Lib.Unif2.Work.Analysis.RiemannSurface.chartBall_cover
import Submission.Lib.Unif2.Work.SimplyConnected.ABS.localRemovability
import Submission.Lib.Unif2.Work.Potential.punctured_ball_abs_le_of_bounded_near

namespace Work.Drive

open Filter Set Metric
open scoped Topology

/-- **The unit logarithmic pole passes to the locally uniform limit** of the normalized Green functions of a *nested* exhaustion.  `Ω n` is an increasing sequence of open sets with `a ∈ Ω n`, `G n` is the Green function of `Ω n` with pole `a` (`IsGreenOn`: positive and harmonic off `a`, with a bounded unit logarithmic pole and relatively compact superlevel sets), `E` is the locally uniform limit of the normalized functions `G (φ k) · - G (φ k) x₁` on `X \ {a}`, and those normalized functions are uniformly bounded on compact subsets of `X \ {a}`.  Then `E` has a unit log pole at `a`.

Route.  Monotonicity and openness make `Ω 0` a neighbourhood of `a`, so a chart ball `D ∋ a` lies in `Ω n` for every `n`.  For each `n` the function `v n := (G n · - G n x₁) + log ‖ζ_a · - ζ_a a‖` is harmonic on `D \ {a}` (the two logarithmic singularities cancel) and is bounded near `a` by the `HasLogPoleOn` clause of `IsGreenOn` (whose constant may depend on `n`), so it extends to a harmonic function on `D`; its supremum and infimum on `D` are attained on the bounding sphere, where the normalized function is bounded by the assumed local bound and `|log ‖ζ_a · - ζ_a a‖| = |log ρ|`.  Hence `|v n| ≤ C` on `D \ {a}` with `C` independent of `n`, and the locally uniform convergence of `G (φ k) · - G (φ k) x₁` to `E` gives `|E + log ‖ζ_a · - ζ_a a‖| ≤ C` on `D \ {a}`. -/
theorem hasLogPoleOn_of_isGreenOn_limit {X : Type*} [TopologicalSpace X] [T2Space X]
    [ConnectedSpace X] [SecondCountableTopology X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    {a x₁ : X} {Ω : ℕ → Set X} {G : ℕ → X → ℝ} {φ : ℕ → ℕ} {E : X → ℝ}
    (haΩ : ∀ n, a ∈ Ω n) (hΩo : ∀ n, IsOpen (Ω n)) (hmono : ∀ n, Ω n ⊆ Ω (n + 1))
    (hG : ∀ n, Work.SimplyConnected.ABS.IsGreenOn (Ω n) a (G n))
    (hconv : TendstoLocallyUniformlyOn (fun k => fun x => G (φ k) x - G (φ k) x₁) E atTop
      (Set.univ \ {a}))
    (hbdd : ∀ K : Set X, IsCompact K → K ⊆ Set.univ \ {a} → ∃ C : ℝ, ∀ n, ∀ x ∈ K,
        |G n x - G n x₁| ≤ C) :
    Work.SimplyConnected.ABS.HasLogPoleOn (Set.univ \ {a}) a E := by
  classical
  let c : OpenPartialHomeomorph X ℂ := chartAt ℂ a
  -- ## 1. Radii: a chart ball around `a` inside `Ω 0`, whose closed disc lies in the chart target
  obtain ⟨ρ₀, hρ₀, hρ₀sub⟩ :=
    Work.Analysis.RiemannSurface.exists_chartBall_subset_of_mem_isOpen (hΩo 0) (haΩ 0)
  obtain ⟨ρ₁, hρ₁, hρ₁sub⟩ :=
    Metric.isOpen_iff.mp c.open_target (c a) (c.map_source (mem_chart_source ℂ a))
  let ρ : ℝ := min ρ₀ (ρ₁ / 2)
  have hρpos : 0 < ρ := lt_min hρ₀ (half_pos hρ₁)
  have hρρ₀ : ρ ≤ ρ₀ := min_le_left _ _
  have hρρ₁ : ρ < ρ₁ := lt_of_le_of_lt (min_le_right _ _) (half_lt_self hρ₁)
  have htgt : Metric.closedBall (c a) ρ ⊆ c.target :=
    (Metric.closedBall_subset_ball hρρ₁).trans hρ₁sub
  have hbtgt : Metric.ball (c a) ρ ⊆ c.target := Metric.ball_subset_closedBall.trans htgt
  have hballρ : Submission.chartBall c (c a) ρ ⊆ Ω 0 := fun y hy =>
    hρ₀sub ⟨hy.1, Metric.ball_subset_ball hρρ₀ hy.2⟩
  let r : ℝ := ρ / 2
  have hrpos : 0 < r := half_pos hρpos
  have hrρ : r < ρ := half_lt_self hρpos
  have htgr : Metric.closedBall (c a) r ⊆ c.target :=
    (Metric.closedBall_subset_closedBall (le_of_lt hrρ)).trans htgt
  -- ## 2. The exhaustion is monotone, so the chart ball lies in every `Ω n`
  have hmono0 : ∀ n : ℕ, Ω 0 ⊆ Ω n := by
    intro n
    induction n with
    | zero => exact subset_rfl
    | succ k ih => exact ih.trans (hmono k)
  have hballn : ∀ n : ℕ, Submission.chartBall c (c a) ρ ⊆ Ω n :=
    fun n => hballρ.trans (hmono0 n)
  -- ## 3. The chart sphere is compact and the normalized functions are uniformly bounded on it
  have hsphere_eq : Submission.chartSphere c (c a) r = c.symm '' Metric.sphere (c a) r := by
    ext x
    constructor
    · rintro ⟨hxs, hx⟩
      exact ⟨c x, hx, c.left_inv hxs⟩
    · rintro ⟨w, hw, rfl⟩
      have hwt : w ∈ c.target := htgr (Metric.sphere_subset_closedBall hw)
      refine ⟨c.map_target hwt, ?_⟩
      show c (c.symm w) ∈ Metric.sphere (c a) r
      rw [c.right_inv hwt]
      exact hw
  have hKcpt : IsCompact (Submission.chartSphere c (c a) r) := by
    rw [hsphere_eq]
    exact (isCompact_sphere (c a) r).image_of_continuousOn
      (c.continuousOn_symm.mono (Metric.sphere_subset_closedBall.trans htgr))
  have hKsub : Submission.chartSphere c (c a) r ⊆ Set.univ \ {a} := by
    intro x hx
    refine ⟨mem_univ x, ?_⟩
    intro hxa
    have hxa' : x = a := by simpa using hxa
    have h1 : ‖c x - c a‖ = r := by
      have h := hx.2
      simp only [Set.mem_preimage, Metric.mem_sphere, dist_eq_norm] at h
      exact h
    rw [hxa'] at h1
    simp at h1
    linarith [hrpos]
  obtain ⟨C₀, hC₀⟩ := hbdd (Submission.chartSphere c (c a) r) hKcpt hKsub
  let M : ℝ := C₀ + |Real.log r|
  -- ## 4. A bound, uniform in `n`, on the punctured chart ball of radius `r`
  have hbound : ∀ n : ℕ, ∀ z : ℂ, ‖z - c a‖ < r → z ≠ c a →
      |G n (c.symm z) - G n x₁ + Real.log ‖z - c a‖| ≤ M := by
    intro n z hzr hzne
    -- harmonicity on the punctured chart ball of radius `ρ`
    have hharm : ∀ w : ℂ, ‖w - c a‖ < ρ → w ≠ c a →
        InnerProductSpace.HarmonicAt
          (fun u : ℂ => G n (c.symm u) - G n x₁ + Real.log ‖u - c a‖) w := by
      intro w hw hwne
      have hGharm : Submission.HarmonicOnX (G n)
          (Submission.chartBall (chartAt ℂ a) ((chartAt ℂ a) a) ρ \ {a}) := by
        intro y hy
        exact (hG n).2.1 y ⟨hballn n hy.1, hy.2⟩
      have h1 : InnerProductSpace.HarmonicAt (fun u : ℂ => G n (c.symm u)) w :=
        Work.SimplyConnected.ABS.harmonicAt_chartSymm_of_punctured_chartBall
          (ζ := a) (ρ := ρ) (u := G n) hbtgt hGharm w hw hwne
      have h2 : InnerProductSpace.HarmonicAt (fun u : ℂ => Real.log ‖u - c a‖) w :=
        Submission.harmonicAt_log_norm_sub hwne
      exact (h1.sub (InnerProductSpace.harmonicAt_const (G n x₁))).add h2
    -- local boundedness at the puncture, from the log pole of `G n` in `Ω n`
    obtain ⟨C_n, V_n, hV_n_mem, hV_n_bd⟩ := (hG n).2.2.2
    obtain ⟨U_n, hUnV, hU_n_open, haU_n⟩ := mem_nhds_iff.mp hV_n_mem
    obtain ⟨ρ_n, hρ_n_pos, hρ_n_sub⟩ :=
      Work.Analysis.RiemannSurface.exists_chartBall_subset_of_mem_isOpen
        (hU_n_open.inter c.open_source) ⟨haU_n, mem_chart_source ℂ a⟩
    have hbcrux : ∃ C : ℝ, ∃ ε : ℝ, 0 < ε ∧ ε < r ∧
        ∀ z : ℂ, 0 < ‖z - c a‖ → ‖z - c a‖ < ε →
          |G n (c.symm z) - G n x₁ + Real.log ‖z - c a‖| ≤ C := by
      have hεr : min ρ_n (r / 2) ≤ r := by
        have h := min_le_right ρ_n (r / 2)
        linarith [hrpos]
      refine ⟨C_n + |G n x₁|, min ρ_n (r / 2), ?_, ?_, ?_⟩
      · exact lt_min hρ_n_pos (half_pos hrpos)
      · exact lt_of_le_of_lt (min_le_right _ _) (half_lt_self hrpos)
      · intro z hz1 hz2
        have hzr' : ‖z - c a‖ < r := lt_of_lt_of_le hz2 hεr
        have hzρ : ‖z - c a‖ < ρ := lt_trans hzr' hrρ
        have hztgt : z ∈ c.target :=
          htgr (Metric.mem_closedBall.mpr (by rw [dist_eq_norm]; exact le_of_lt hzr'))
        have hxsrc : c.symm z ∈ c.source := c.map_target hztgt
        have hcx : c (c.symm z) = z := c.right_inv hztgt
        have hxne : c.symm z ≠ a := by
          intro h
          have hzc : z = c a := by rw [← hcx, h]
          have h0 : ‖z - c a‖ = 0 := by rw [hzc, sub_self, norm_zero]
          rw [h0] at hz1
          exact lt_irrefl 0 hz1
        have hxballn : c.symm z ∈ Submission.chartBall c (c a) ρ_n := by
          refine ⟨hxsrc, ?_⟩
          show c (c.symm z) ∈ Metric.ball (c a) ρ_n
          rw [hcx]
          exact Metric.mem_ball.mpr (by rw [dist_eq_norm]; exact lt_of_lt_of_le hz2 (min_le_left _ _))
        have hxV : c.symm z ∈ V_n := hUnV (hρ_n_sub hxballn).1
        have hxΩ : c.symm z ∈ Ω n := hballn n (by
          refine ⟨hxsrc, ?_⟩
          show c (c.symm z) ∈ Metric.ball (c a) ρ
          rw [hcx]
          exact Metric.mem_ball.mpr (by rw [dist_eq_norm]; exact hzρ))
        have hbd := hV_n_bd (c.symm z) hxV hxΩ hxne
        rw [hcx] at hbd
        have hA : G n (c.symm z) - G n x₁ + Real.log ‖z - c a‖
            = (G n (c.symm z) + Real.log ‖z - c a‖) - G n x₁ := by ring
        rw [hA]
        exact le_trans (abs_sub _ _) (by linarith)
    -- the bound on the sphere of radius `r`
    have hscrux : ∀ z : ℂ, ‖z - c a‖ = r →
        |G n (c.symm z) - G n x₁ + Real.log ‖z - c a‖| ≤ M := by
      intro z hz
      have hzsp : z ∈ Metric.sphere (c a) r := by
        rw [Metric.mem_sphere, dist_eq_norm]; exact hz
      have hztgt : z ∈ c.target := htgr (Metric.sphere_subset_closedBall hzsp)
      have hxt : c.symm z ∈ Submission.chartSphere c (c a) r := by
        refine ⟨c.map_target hztgt, ?_⟩
        show c (c.symm z) ∈ Metric.sphere (c a) r
        rw [c.right_inv hztgt]
        exact hzsp
      have hb := hC₀ n (c.symm z) hxt
      have hlog : Real.log ‖z - c a‖ = Real.log r := by rw [hz]
      rw [hlog]
      calc |G n (c.symm z) - G n x₁ + Real.log r|
          ≤ |G n (c.symm z) - G n x₁| + |Real.log r| := abs_add_le _ _
        _ ≤ C₀ + |Real.log r| := by linarith [hb]
    exact Work.Potential.punctured_ball_abs_le_of_bounded_near hρpos hrpos hrρ hharm hbcrux hscrux z hzr hzne
  -- ## 5. Pass to the limit along the subsequence `φ`
  refine ⟨M, Submission.chartBall c (c a) r, ?_, ?_⟩
  · exact (Submission.chartBall_isOpen c (c a) r).mem_nhds
      ⟨mem_chart_source ℂ a, Metric.mem_ball_self hrpos⟩
  · intro x hx hxu hxne
    have hxr : ‖c x - c a‖ < r := by
      have h := hx.2
      simp only [Set.mem_preimage, Metric.mem_ball, dist_eq_norm] at h
      exact h
    have hxcne : c x ≠ c a := by
      intro h
      exact hxne (c.injOn hx.1 (mem_chart_source ℂ a) h)
    have hk : ∀ k : ℕ, |(G (φ k) x - G (φ k) x₁) + Real.log ‖c x - c a‖| ≤ M := by
      intro k
      have h := hbound (φ k) (c x) hxr hxcne
      rwa [c.left_inv hx.1] at h
    have hlim : Filter.Tendsto (fun k : ℕ => (G (φ k) x - G (φ k) x₁) + Real.log ‖c x - c a‖)
        Filter.atTop (𝓝 (E x + Real.log ‖c x - c a‖)) :=
      (hconv.tendsto_at hxu).add tendsto_const_nhds
    exact le_of_tendsto' hlim.abs hk

end Work.Drive
