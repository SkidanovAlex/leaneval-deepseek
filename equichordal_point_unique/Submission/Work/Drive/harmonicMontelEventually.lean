import Mathlib
import Submission.Work.SimplyConnected.ABS.Defs
import Submission.Work.Drive.chartBallCover
import Submission.Commons.Analysis.Complex.Montel.exists_subseq_tendstoLocallyUniformlyOn_ball
import Submission.Commons.Analysis.Complex.Harmonic.harmonic_of_circleAverage
import Submission.Commons.Analysis.Complex.Harmonic.circleAverage_tendsto_of_tendstoUniformlyOn
import Submission.Commons.Analysis.InnerProductSpace.harmonicAt_comp_analytic

namespace Work.Drive

open Filter Set Metric Topology Interval
open scoped Topology


/-! ### Auxiliary analytic lemmas -/

/-- Translation invariance of the circle average. -/
private lemma circleAverage_comp_add (g : ℂ → ℝ) (c p : ℂ) (r : ℝ) :
    Real.circleAverage (fun z => g (c + z)) p r = Real.circleAverage g (c + p) r := by
  rw [Real.circleAverage_def, Real.circleAverage_def]
  congr 1
  apply intervalIntegral.integral_congr
  intro θ _
  show g (c + circleMap p r θ) = g (circleMap (c + p) r θ)
  congr 1
  simp only [circleMap]
  ring

/-- The elementary Lipschitz estimate for the logarithm away from `0`. -/
private lemma log_sub_log_le {a b δ : ℝ} (hδ : 0 < δ) (ha : δ ≤ a) (hb : δ ≤ b) :
    Real.log a - Real.log b ≤ |a - b| / δ := by
  have ha0 : 0 < a := lt_of_lt_of_le hδ ha
  have hb0 : 0 < b := lt_of_lt_of_le hδ hb
  rcases lt_or_ge a b with hab | hba
  · have hneg : Real.log a - Real.log b ≤ 0 := by
      have := Real.log_lt_log ha0 hab
      linarith
    have h0 : 0 ≤ |a - b| / δ := by positivity
    linarith
  · have hkey : Real.log a - Real.log b = Real.log (a / b) := by
      rw [Real.log_div ha0.ne' hb0.ne']
    rw [hkey]
    have h1 : Real.log (a / b) ≤ a / b - 1 := Real.log_le_sub_one_of_pos (div_pos ha0 hb0)
    have h2 : a / b - 1 = (a - b) / b := by
      rw [sub_div, div_self hb0.ne']
    have h3 : (a - b) / b ≤ (a - b) / δ :=
      div_le_div_of_nonneg_left (by linarith) hδ hb
    have h4 : |a - b| = a - b := abs_of_nonneg (by linarith)
    rw [h4]
    linarith

private lemma abs_log_sub_log_le {a b δ : ℝ} (hδ : 0 < δ) (ha : δ ≤ a) (hb : δ ≤ b) :
    |Real.log a - Real.log b| ≤ |a - b| / δ := by
  refine abs_le.mpr ⟨?_, log_sub_log_le hδ ha hb⟩
  have h := log_sub_log_le hδ hb ha
  rw [abs_sub_comm b a] at h
  linarith

/-- `z ↦ log ‖z‖ + M` is Lipschitz on the annulus `{e^{-2M} ≤ ‖z‖ ≤ 1}`. -/
private lemma log_norm_add_lipschitzOn (M : ℝ) :
    LipschitzOnWith (Real.toNNReal (Real.exp (2 * M)))
      (fun z : ℂ => Real.log ‖z‖ + M) {z : ℂ | Real.exp (-2 * M) ≤ ‖z‖ ∧ ‖z‖ ≤ 1} := by
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro x hx y hy
  have hδpos : 0 < Real.exp (-2 * M) := Real.exp_pos _
  have hcoe : ((Real.exp (2 * M)).toNNReal : ℝ) = Real.exp (2 * M) :=
    Real.coe_toNNReal _ (Real.exp_nonneg _)
  have hdist : dist (Real.log ‖x‖ + M) (Real.log ‖y‖ + M) = |Real.log ‖x‖ - Real.log ‖y‖| := by
    rw [Real.dist_eq]
    congr 1
    ring
  have hbound : |Real.log ‖x‖ - Real.log ‖y‖| ≤ ‖x - y‖ / Real.exp (-2 * M) := by
    refine (abs_log_sub_log_le hδpos hx.1 hy.1).trans ?_
    have h2 : |‖x‖ - ‖y‖| ≤ ‖x - y‖ := abs_norm_sub_norm_le x y
    exact div_le_div_of_nonneg_right h2 (le_of_lt hδpos)
  rw [hdist, hcoe, dist_eq_norm]
  rw [div_eq_inv_mul] at hbound
  have hinv : (Real.exp (-2 * M))⁻¹ = Real.exp (2 * M) := by
    rw [← Real.exp_neg]
    congr 1
    ring
  rw [hinv] at hbound
  simpa [mul_comm] using hbound

/-- **The mean value criterion, for a disc with an arbitrary centre.** -/
private theorem harmonicOnNhd_of_circleAverage_center {g : ℂ → ℝ} {c : ℂ} {R : ℝ}
    (hcont : ContinuousOn g (Metric.ball c R))
    (hMV : ∀ p ∈ Metric.ball c R, ∀ r : ℝ, 0 < r → ‖p - c‖ + r < R →
      Real.circleAverage g p r = g p) :
    InnerProductSpace.HarmonicOnNhd g (Metric.ball c R) := by
  have hucont : ContinuousOn (fun w : ℂ => g (c + w)) (Metric.ball 0 R) := by
    refine hcont.comp (continuous_const.add continuous_id).continuousOn ?_
    intro w hw
    have hwR : ‖w‖ < R := by
      have := Metric.mem_ball.mp hw
      simpa [dist_eq_norm] using this
    simpa [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left] using hwR
  have huMV : ∀ p : ℂ, ‖p‖ < R → ∀ r : ℝ, 0 < r → ‖p‖ + r < R →
      Real.circleAverage (fun w : ℂ => g (c + w)) p r = g (c + p) := by
    intro p hp r hr hpr
    rw [circleAverage_comp_add]
    refine hMV (c + p) ?_ r hr ?_
    · simpa [Metric.mem_ball, dist_eq_norm] using hp
    · have : ‖(c + p) - c‖ = ‖p‖ := by rw [add_sub_cancel_left]
      rw [this]
      exact hpr
  have hu := Commons.Analysis.Complex.Harmonic.harmonic_of_circleAverage hucont huMV
  intro z hz
  have hzR : ‖z - c‖ < R := by
    have := Metric.mem_ball.mp hz
    simpa [dist_eq_norm] using this
  have hzc : z - c ∈ Metric.ball (0 : ℂ) R := by
    simpa [Metric.mem_ball, dist_eq_norm, sub_zero] using hzR
  have h1 : InnerProductSpace.HarmonicAt (fun w : ℂ => g (c + w)) (z - c) := hu (z - c) hzc
  have h2 : AnalyticAt ℂ (fun ζ : ℂ => ζ - c) z := by fun_prop
  have h3 : InnerProductSpace.HarmonicAt (fun ζ : ℂ => g (c + (ζ - c))) z :=
    Commons.Analysis.InnerProductSpace.harmonicAt_comp_analytic
      (u := fun w : ℂ => g (c + w)) (f := fun ζ : ℂ => ζ - c) (x := z) h2 h1
  refine (InnerProductSpace.harmonicAt_congr_nhds ?_).mp h3
  filter_upwards with ζ
  congr 1
  ring

/-! ### Montel compactness on a disc -/

/-- **Montel compactness for harmonic functions on a disc, with a uniform bound on the whole
disc.** -/
private theorem montelHarmonicBallBdd {c : ℂ} {R M : ℝ} (hR : 0 < R)
    {v : ℕ → ℂ → ℝ} (hv : ∀ n, InnerProductSpace.HarmonicOnNhd (v n) (Metric.ball c R))
    (hb : ∀ n, ∀ z ∈ Metric.ball c R, |v n z| ≤ M) :
    ∃ (φ : ℕ → ℕ) (g : ℂ → ℝ), StrictMono φ ∧
      InnerProductSpace.HarmonicOnNhd g (Metric.ball c R) ∧
      TendstoLocallyUniformlyOn (fun n => v (φ n)) g Filter.atTop (Metric.ball c R) := by
  classical
  have hconj : ∀ n, ∃ F : ℂ → ℂ, AnalyticOnNhd ℂ F (Metric.ball c R) ∧
      Set.EqOn (fun z => (F z).re) (v n) (Metric.ball c R) :=
    fun n => (hv n).exists_analyticOnNhd_ball_re_eq
  choose F hFana hFre using hconj
  let G : ℕ → ℂ → ℂ := fun n z => Complex.exp (F n z - (M : ℂ))
  have hG_ana : ∀ n, ∀ z ∈ Metric.ball c R, AnalyticAt ℂ (G n) z := by
    intro n z hz
    have h := ((hFana n z hz).sub (analyticAt_const (v := (M : ℂ)))).cexp
    simpa [G, Function.comp_def] using h
  have hG_norm : ∀ n z, z ∈ Metric.ball c R → ‖G n z‖ = Real.exp (v n z - M) := by
    intro n z hz
    have h1 : (F n z - (M : ℂ)).re = v n z - M := by
      rw [Complex.sub_re, Complex.ofReal_re]
      congr 1
      exact hFre n hz
    simp only [G, Complex.norm_exp, h1]
  have hG_le : ∀ n, ∀ z ∈ Metric.ball c R, ‖G n z‖ ≤ 1 := by
    intro n z hz
    rw [hG_norm n z hz, Real.exp_le_one_iff]
    have := (abs_le.mp (hb n z hz)).2
    linarith
  have hG_ge : ∀ n, ∀ z ∈ Metric.ball c R, Real.exp (-2 * M) ≤ ‖G n z‖ := by
    intro n z hz
    rw [hG_norm n z hz, Real.exp_le_exp]
    have := (abs_le.mp (hb n z hz)).1
    linarith
  obtain ⟨φ, H, hφ, hconv, hHana⟩ :=
    Commons.Analysis.Complex.Montel.exists_subseq_tendstoLocallyUniformlyOn_ball hR hG_ana hG_le
  have hH_ge : ∀ z ∈ Metric.ball c R, Real.exp (-2 * M) ≤ ‖H z‖ := by
    intro z hz
    have h1 : Filter.Tendsto (fun n => ‖G (φ n) z‖) Filter.atTop (𝓝 ‖H z‖) :=
      (hconv.tendsto_at hz).norm
    exact ge_of_tendsto h1 (Filter.Eventually.of_forall fun n => hG_ge (φ n) z hz)
  have hH_le : ∀ z ∈ Metric.ball c R, ‖H z‖ ≤ 1 := by
    intro z hz
    have h1 : Filter.Tendsto (fun n => ‖G (φ n) z‖) Filter.atTop (𝓝 ‖H z‖) :=
      (hconv.tendsto_at hz).norm
    exact le_of_tendsto h1 (Filter.Eventually.of_forall fun n => hG_le (φ n) z hz)
  have huc : UniformContinuousOn (fun z : ℂ => Real.log ‖z‖ + M)
      {z : ℂ | Real.exp (-2 * M) ≤ ‖z‖ ∧ ‖z‖ ≤ 1} :=
    (log_norm_add_lipschitzOn M).uniformContinuousOn
  have hMapsH : Set.MapsTo H (Metric.ball c R)
      {z : ℂ | Real.exp (-2 * M) ≤ ‖z‖ ∧ ‖z‖ ≤ 1} :=
    fun z hz => ⟨hH_ge z hz, hH_le z hz⟩
  have hMapsG : ∀ᶠ n in Filter.atTop, Set.MapsTo (G (φ n)) (Metric.ball c R)
      {z : ℂ | Real.exp (-2 * M) ≤ ‖z‖ ∧ ‖z‖ ≤ 1} :=
    Filter.Eventually.of_forall fun n z hz => ⟨hG_ge (φ n) z hz, hG_le (φ n) z hz⟩
  have hlog := huc.comp_tendstoLocallyUniformlyOn hconv hMapsH hMapsG
  have hlim : TendstoLocallyUniformlyOn (fun n => v (φ n))
      (fun z => Real.log ‖H z‖ + M) Filter.atTop (Metric.ball c R) := by
    have h1 : TendstoLocallyUniformlyOn
        (fun n => fun z => Real.log ‖G (φ n) z‖ + M) (fun z => Real.log ‖H z‖ + M)
        Filter.atTop (Metric.ball c R) := by
      simpa [Function.comp_def] using hlog
    refine h1.congr fun n => ?_
    intro z hz
    show Real.log ‖G (φ n) z‖ + M = v (φ n) z
    rw [hG_norm (φ n) z hz, Real.log_exp]
    ring
  have hne : ∀ z ∈ Metric.ball c R, ‖H z‖ ≠ 0 := by
    intro z hz
    have hge := hH_ge z hz
    have hpos : 0 < Real.exp (-2 * M) := Real.exp_pos _
    linarith [norm_nonneg (H z)]
  have hcont_g : ContinuousOn (fun z => Real.log ‖H z‖ + M) (Metric.ball c R) :=
    ((hHana.continuousOn.norm).log hne).add_const M
  have hMV : ∀ p ∈ Metric.ball c R, ∀ r : ℝ, 0 < r → ‖p - c‖ + r < R →
      Real.circleAverage (fun z => Real.log ‖H z‖ + M) p r = Real.log ‖H p‖ + M := by
    intro p hp r hr hpr
    have hsub : Metric.closedBall p |r| ⊆ Metric.ball c R := by
      intro z hz
      have hzp : ‖z - p‖ ≤ r := by
        have h1 := Metric.mem_closedBall.mp hz
        rw [dist_eq_norm, abs_of_pos hr] at h1
        exact h1
      have htri : ‖z - c‖ ≤ ‖z - p‖ + ‖p - c‖ := by
        have h2 := norm_add_le (z - p) (p - c)
        rwa [sub_add_sub_cancel] at h2
      have h3 : ‖z - c‖ < R := by linarith
      simpa [Metric.mem_ball, dist_eq_norm] using h3
    have hca : ∀ n, Real.circleAverage (v (φ n)) p r = v (φ n) p := by
      intro n
      exact InnerProductSpace.HarmonicOnNhd.circleAverage_eq ((hv (φ n)).mono hsub)
    have hsphere_sub : Metric.sphere p r ⊆ Metric.ball c R := fun z hz =>
      hsub (by rw [abs_of_pos hr]; exact Metric.sphere_subset_closedBall hz)
    have huni : TendstoUniformlyOn (fun n => v (φ n)) (fun z => Real.log ‖H z‖ + M)
        Filter.atTop (Metric.sphere p r) :=
      (tendstoLocallyUniformlyOn_iff_forall_isCompact Metric.isOpen_ball).mp hlim
        (Metric.sphere p r) hsphere_sub (isCompact_sphere p r)
    have hcont_sphere : ∀ n, ContinuousOn (v (φ n)) (Metric.sphere p r) := by
      intro n
      exact ((hv (φ n)).mono hsphere_sub).contDiffOn.continuousOn
    have h1 := Commons.Analysis.Complex.Harmonic.circleAverage_tendsto_of_tendstoUniformlyOn
      hr hcont_sphere huni
    have h2 : Filter.Tendsto (fun n => Real.circleAverage (v (φ n)) p r) Filter.atTop
        (𝓝 (Real.log ‖H p‖ + M)) :=
      (hlim.tendsto_at hp).congr' (Filter.Eventually.of_forall fun n => (hca n).symm)
    exact tendsto_nhds_unique h1 h2
  exact ⟨φ, fun z => Real.log ‖H z‖ + M, hφ,
    harmonicOnNhd_of_circleAverage_center hcont_g hMV, hlim⟩

/-! ### The diagonal argument -/

/-- Composition of a locally uniformly convergent family with an index map tending to `atTop`. -/
private lemma tluo_comp_tendsto_atTop {α : Type*} [TopologicalSpace α] {β : Type*}
    [UniformSpace β] {G : ℕ → α → β} {f : α → β} {s : Set α} {Θ : ℕ → ℕ}
    (h : TendstoLocallyUniformlyOn G f Filter.atTop s)
    (hΘ : Tendsto Θ Filter.atTop Filter.atTop) :
    TendstoLocallyUniformlyOn (fun n => G (Θ n)) f Filter.atTop s := by
  intro u hu x hx
  obtain ⟨t, ht, H⟩ := h u hu x hx
  exact ⟨t, ht, hΘ.eventually H⟩

/-- Shifting the index of a sequence by a constant does not affect locally uniform convergence. -/
private lemma tluo_shift {α : Type*} [TopologicalSpace α] {β : Type*} [UniformSpace β]
    {G : ℕ → α → β} {f : α → β} {s : Set α} (c : ℕ) :
    TendstoLocallyUniformlyOn (fun n => G (n + c)) f Filter.atTop s ↔
      TendstoLocallyUniformlyOn G f Filter.atTop s := by
  refine ⟨fun h => ?_, fun h => tluo_comp_tendsto_atTop h (tendsto_add_atTop_nat c)⟩
  intro u hu x hx
  obtain ⟨t, ht, H⟩ := h u hu x hx
  rw [Filter.eventually_atTop] at H
  obtain ⟨N, hN⟩ := H
  refine ⟨t, ht, ?_⟩
  rw [Filter.eventually_atTop]
  refine ⟨N + c, fun m hm y hy => ?_⟩
  have hcm : c ≤ m := le_trans (Nat.le_add_left c N) hm
  have hsub : (m - c) + c = m := Nat.sub_add_cancel hcm
  have hN' : N ≤ m - c := by omega
  simpa [hsub] using hN (m - c) hN' y hy

/-- **Montel for harmonic functions, eventual form.** A sequence of functions which is *eventually*
harmonic on a neighbourhood of each compact subset of an open set `Y`, and locally uniformly bounded
on the compact subsets of `Y`, has a subsequence converging locally uniformly on `Y` to a function
harmonic on `Y`.

This is the form needed when the `n`-th function is harmonic only on the `n`-th set of an
exhaustion: for every compact `K ⊆ Y` there is an open `O` with `K ⊆ O ⊆ Y` and an index `N` such
that every `u n`, `n ≥ N`, is harmonic on `O`.  It follows from
`Work.Drive.harmonicMontel` by restricting at each diagonal step to the tail `n ≥ N_k`. -/
theorem harmonicMontelEventually {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    [SecondCountableTopology X] [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    {Y : Set X} (hY : IsOpen Y) {u : ℕ → X → ℝ}
    (h : ∀ K : Set X, K ⊆ Y → IsCompact K → ∃ O : Set X, IsOpen O ∧ K ⊆ O ∧ O ⊆ Y ∧
        ∃ N : ℕ, ∀ n ≥ N, Submission.HarmonicOnX (u n) O)
    (hbdd : ∀ K : Set X, K ⊆ Y → IsCompact K → ∃ C : ℝ, ∀ n : ℕ, ∀ x ∈ K, |u n x| ≤ C) :
    ∃ (φ : ℕ → ℕ) (g : X → ℝ), StrictMono φ ∧ Submission.HarmonicOnX g Y ∧
      TendstoLocallyUniformlyOn (fun k : ℕ => u (φ k)) g Filter.atTop Y := by
  classical
  by_cases hYne : Y.Nonempty
  · obtain ⟨xs, rad, hrad, htgt, hKcpt, hKY, hcover⟩ := chartBallCover hY hYne
    let c : ℕ → ℂ := fun k => (chartAt ℂ (xs k)) (xs k)
    let B : ℕ → Set X := fun k => (chartAt ℂ (xs k)).symm '' Metric.ball (c k) (rad k)
    have hB_src : ∀ k, B k = (chartAt ℂ (xs k)).source ∩
        (chartAt ℂ (xs k)) ⁻¹' Metric.ball (c k) (rad k) :=
      fun k => OpenPartialHomeomorph.symm_image_eq_source_inter_preimage _ (htgt k)
    have hB_sub_src : ∀ k, B k ⊆ (chartAt ℂ (xs k)).source := by
      intro k
      rw [hB_src k]
      exact inter_subset_left
    have hB_sub_Y : ∀ k, B k ⊆ Y := fun k => subset_trans subset_closure (hKY k)
    have hB_open : ∀ k, IsOpen (B k) := fun k =>
      OpenPartialHomeomorph.isOpen_image_symm_of_subset_target _ isOpen_ball (htgt k)
    have hcoverB : (⋃ k, B k) = Y := hcover
    -- ## The eventual data attached to each chart ball
    have hO : ∀ k, ∃ (O : Set X) (N : ℕ), IsOpen O ∧ closure (B k) ⊆ O ∧ O ⊆ Y ∧
        ∀ n ≥ N, Submission.HarmonicOnX (u n) O := by
      intro k
      obtain ⟨O, hOo, hKO, hOY, N, hN⟩ := h (closure (B k)) (hKY k) (hKcpt k)
      exact ⟨O, N, hOo, hKO, hOY, hN⟩
    choose O N hOo hKO hOY hN using hO
    have hB_sub_O : ∀ k, B k ⊆ O k := fun k => subset_closure.trans (hKO k)
    -- ## Extraction on each chart ball
    have hex : ∀ (k : ℕ) (σ : ℕ → ℕ), StrictMono σ → ∃ (ψ : ℕ → ℕ) (G : ℂ → ℝ),
        StrictMono ψ ∧
        InnerProductSpace.HarmonicOnNhd G (Metric.ball (c k) (rad k)) ∧
        TendstoLocallyUniformlyOn
          (fun m => (u (σ (N k + ψ m))) ∘ (chartAt ℂ (xs k)).symm) G
          Filter.atTop (Metric.ball (c k) (rad k)) := by
      intro k σ hσ
      obtain ⟨C, hC⟩ := hbdd (closure (B k)) (hKY k) (hKcpt k)
      have hv : ∀ m, InnerProductSpace.HarmonicOnNhd
          ((u (σ (N k + m))) ∘ (chartAt ℂ (xs k)).symm) (Metric.ball (c k) (rad k)) := by
        intro m z hz
        have hzB : (chartAt ℂ (xs k)).symm z ∈ B k := ⟨z, hz, rfl⟩
        have hsrc := hB_sub_src k hzB
        have hge : N k ≤ σ (N k + m) := le_trans (Nat.le_add_right _ _) (hσ.id_le _)
        have hh := hN k (σ (N k + m)) hge ((chartAt ℂ (xs k)).symm z) (hB_sub_O k hzB)
        have h2 := (Submission.HarmonicOnXAt_iff_chart (u := u (σ (N k + m)))
          (x := (chartAt ℂ (xs k)).symm z) (y := xs k) hsrc).mp hh
        rwa [(chartAt ℂ (xs k)).right_inv (htgt k hz)] at h2
      have hb : ∀ m, ∀ z ∈ Metric.ball (c k) (rad k),
          |((u (σ (N k + m))) ∘ (chartAt ℂ (xs k)).symm) z| ≤ C := by
        intro m z hz
        exact hC _ _ (subset_closure ⟨z, hz, rfl⟩)
      exact montelHarmonicBallBdd (hrad k) hv hb
    -- ## The diagonal recursion
    let psi : (k : ℕ) → (σ : ℕ → ℕ) → StrictMono σ → (ℕ → ℕ) :=
      fun k σ hσ => Classical.choose (hex k σ hσ)
    let GOf : (k : ℕ) → (σ : ℕ → ℕ) → StrictMono σ → (ℂ → ℝ) :=
      fun k σ hσ => Classical.choose (Classical.choose_spec (hex k σ hσ))
    have psi_strict : ∀ k σ (hσ : StrictMono σ), StrictMono (psi k σ hσ) :=
      fun k σ hσ => (Classical.choose_spec (Classical.choose_spec (hex k σ hσ))).1
    have GOf_harm : ∀ k σ (hσ : StrictMono σ),
        InnerProductSpace.HarmonicOnNhd (GOf k σ hσ) (Metric.ball (c k) (rad k)) :=
      fun k σ hσ => (Classical.choose_spec (Classical.choose_spec (hex k σ hσ))).2.1
    have GOf_conv : ∀ k σ (hσ : StrictMono σ),
        TendstoLocallyUniformlyOn
          (fun m => (u (σ (N k + psi k σ hσ m))) ∘ (chartAt ℂ (xs k)).symm) (GOf k σ hσ)
          Filter.atTop (Metric.ball (c k) (rad k)) :=
      fun k σ hσ => (Classical.choose_spec (Classical.choose_spec (hex k σ hσ))).2.2
    let Phi : ℕ → {v : ℕ → ℕ // StrictMono v} :=
      Nat.rec (motive := fun _ => {v : ℕ → ℕ // StrictMono v}) ⟨id, strictMono_id⟩
        fun k rec => ⟨fun m => rec.1 (N k + psi k rec.1 rec.2 m),
          rec.2.comp fun a b hab => Nat.add_lt_add_left ((psi_strict k rec.1 rec.2) hab) (N k)⟩
    let U : ℕ → (ℕ → ℕ) := fun k => (Phi k).1
    have U_strict : ∀ k, StrictMono (U k) := fun k => (Phi k).2
    have U_succ : ∀ k, U (k + 1) = U k ∘ fun m => N k + psi k (U k) (U_strict k) m := fun k => rfl
    have range_succ : ∀ k, Set.range (U (k + 1)) ⊆ Set.range (U k) := by
      intro k
      rw [U_succ k]
      rintro y ⟨m, rfl⟩
      exact ⟨N k + psi k (U k) (U_strict k) m, rfl⟩
    have range_mono : ∀ k n, k ≤ n → Set.range (U n) ⊆ Set.range (U k) := by
      intro k n hkn
      induction hkn with
      | refl => exact subset_rfl
      | step h ih => exact (range_succ _).trans ih
    let diag : ℕ → ℕ := fun n => U n n
    have diag_strict : StrictMono diag := by
      apply strictMono_nat_of_lt_succ
      intro n
      have h1 : diag (n + 1) = U n (N n + psi n (U n) (U_strict n) (n + 1)) := by
        simp only [diag]
        rw [U_succ n]
        rfl
      have h2 : diag n = U n n := rfl
      rw [h1, h2]
      refine (U_strict n) (lt_of_lt_of_le (Nat.lt_succ_self n) ?_)
      exact le_trans ((psi_strict n (U n) (U_strict n)).id_le (n + 1))
        (Nat.le_add_left _ (N n))
    have diag_mem : ∀ k n, k + 1 ≤ n → diag n ∈ Set.range (U (k + 1)) :=
      fun k n hn => range_mono (k + 1) n hn ⟨n, rfl⟩
    have ThetaSpec : ∀ k n, ∃ m, U (k + 1) m = diag (n + (k + 1)) :=
      fun k n => diag_mem k (n + (k + 1)) (Nat.le_add_left _ _)
    let Theta : ℕ → ℕ → ℕ := fun k n => Classical.choose (ThetaSpec k n)
    have Theta_eq : ∀ k n, U (k + 1) (Theta k n) = diag (n + (k + 1)) :=
      fun k n => Classical.choose_spec (ThetaSpec k n)
    have Theta_strict : ∀ k, StrictMono (Theta k) := by
      intro k
      apply strictMono_nat_of_lt_succ
      intro n
      have hlt : diag (n + (k + 1)) < diag (n + 1 + (k + 1)) :=
        diag_strict (show n + (k + 1) < n + 1 + (k + 1) by omega)
      rw [← Theta_eq k n, ← Theta_eq k (n + 1)] at hlt
      exact (U_strict (k + 1)).lt_iff_lt.mp hlt
    have Theta_tendsto : ∀ k, Tendsto (Theta k) Filter.atTop Filter.atTop := by
      intro k
      rw [Filter.tendsto_atTop_atTop]
      exact fun b => ⟨b, fun a ha => le_trans ha ((Theta_strict k).id_le a)⟩
    -- ## Convergence in coordinates on each chart ball
    have hconv_ball : ∀ k, TendstoLocallyUniformlyOn
        (fun n => (u (diag n)) ∘ (chartAt ℂ (xs k)).symm) (GOf k (U k) (U_strict k))
        Filter.atTop (Metric.ball (c k) (rad k)) := by
      intro k
      have h2 : TendstoLocallyUniformlyOn
          (fun m => (u (U (k + 1) m)) ∘ (chartAt ℂ (xs k)).symm) (GOf k (U k) (U_strict k))
          Filter.atTop (Metric.ball (c k) (rad k)) := by
        have hh := GOf_conv k (U k) (U_strict k)
        rw [U_succ k]
        simpa only [Function.comp_apply] using hh
      have h3 := tluo_comp_tendsto_atTop h2 (Theta_tendsto k)
      have h4 : TendstoLocallyUniformlyOn
          (fun n => (u (diag (n + (k + 1)))) ∘ (chartAt ℂ (xs k)).symm)
          (GOf k (U k) (U_strict k)) Filter.atTop (Metric.ball (c k) (rad k)) :=
        h3.congr fun n => fun z _ => by simp only [Theta_eq k n]
      exact (tluo_shift (k + 1)).mp h4
    -- ## Convergence on the chart balls themselves
    have hconv_B : ∀ k, TendstoLocallyUniformlyOn (fun n => u (diag n))
        (fun x => GOf k (U k) (U_strict k) ((chartAt ℂ (xs k)) x)) Filter.atTop (B k) := by
      intro k
      have hmap : Set.MapsTo (↑(chartAt ℂ (xs k)) : X → ℂ) (B k) (Metric.ball (c k) (rad k)) := by
        intro x hx
        obtain ⟨z, hz, rfl⟩ := hx
        rw [OpenPartialHomeomorph.right_inv _ (htgt k hz)]
        exact hz
      have hcont : ContinuousOn (↑(chartAt ℂ (xs k)) : X → ℂ) (B k) :=
        (OpenPartialHomeomorph.continuousOn _).mono (hB_sub_src k)
      have h1 := (hconv_ball k).comp (↑(chartAt ℂ (xs k)) : X → ℂ) hmap hcont
      refine h1.congr fun n => fun x hx => ?_
      simp only [Function.comp_apply]
      rw [OpenPartialHomeomorph.left_inv _ (hB_sub_src k hx)]
    -- ## The limit function
    let g : X → ℝ := fun x => Filter.limUnder Filter.atTop (fun n => u (diag n) x)
    have hg_eq : ∀ k, Set.EqOn
        (fun x => GOf k (U k) (U_strict k) ((chartAt ℂ (xs k)) x)) g (B k) := by
      intro k x hx
      have htend : Tendsto (fun n => u (diag n) x) Filter.atTop
          (𝓝 (GOf k (U k) (U_strict k) ((chartAt ℂ (xs k)) x))) := (hconv_B k).tendsto_at hx
      show GOf k (U k) (U_strict k) ((chartAt ℂ (xs k)) x) = g x
      rw [show g x = Filter.limUnder Filter.atTop (fun n => u (diag n) x) from rfl]
      exact (Filter.Tendsto.limUnder_eq htend).symm
    have hconv_all : TendstoLocallyUniformlyOn (fun n => u (diag n)) g Filter.atTop (⋃ k, B k) :=
      tendstoLocallyUniformlyOn_iUnion hB_open fun k => (hconv_B k).congr_right (hg_eq k)
    have hconvY : TendstoLocallyUniformlyOn (fun n => u (diag n)) g Filter.atTop Y := by
      rw [← hcoverB]
      exact hconv_all
    -- ## The limit is harmonic
    have hg_harm : Submission.HarmonicOnX g Y := by
      intro p hp
      obtain ⟨k, hk⟩ : ∃ k, p ∈ B k := by
        have : p ∈ ⋃ k, B k := by rw [hcoverB]; exact hp
        exact Set.mem_iUnion.mp this
      obtain ⟨w, hw, hwe⟩ := hk
      have hsrc : p ∈ (chartAt ℂ (xs k)).source := by
        rw [← hwe]
        exact hB_sub_src k ⟨w, hw, rfl⟩
      have hwp : (chartAt ℂ (xs k)) p = w := by
        rw [← hwe]
        exact (chartAt ℂ (xs k)).right_inv (htgt k hw)
      have hwball : (chartAt ℂ (xs k)) p ∈ Metric.ball (c k) (rad k) := by
        rw [hwp]
        exact hw
      refine (Submission.HarmonicOnXAt_iff_chart (u := g) (x := p) (y := xs k) hsrc).mpr ?_
      have hEq : (fun z => g ((chartAt ℂ (xs k)).symm z)) =ᶠ[𝓝 ((chartAt ℂ (xs k)) p)]
          (GOf k (U k) (U_strict k)) := by
        filter_upwards [Metric.isOpen_ball.mem_nhds hwball] with z hz
        have hzB : (chartAt ℂ (xs k)).symm z ∈ B k := ⟨z, hz, rfl⟩
        have h1 := hg_eq k hzB
        simp only at h1
        rw [← h1, (chartAt ℂ (xs k)).right_inv (htgt k hz)]
      exact (InnerProductSpace.harmonicAt_congr_nhds hEq).mpr
        (GOf_harm k (U k) (U_strict k) _ hwball)
    exact ⟨diag, g, diag_strict, hg_harm, hconvY⟩
  · refine ⟨id, fun _ => 0, strictMono_id, ?_, ?_⟩
    · intro x hx
      exact absurd ⟨x, hx⟩ hYne
    · intro uu huu x hx
      exact absurd ⟨x, hx⟩ hYne

end Work.Drive
