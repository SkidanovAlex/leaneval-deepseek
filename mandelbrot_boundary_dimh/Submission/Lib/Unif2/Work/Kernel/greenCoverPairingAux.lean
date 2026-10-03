import Mathlib
import Submission.Lib.Unif2.Work.Kernel.GreenCover
import Submission.Lib.Unif2.Work.Kernel.exists_modelBump_chartBall
import Submission.Lib.Unif2.Work.Kernel.transferV2_local
import Submission.Lib.Unif2.Work.Drive.greenEnergyGlue
import Submission.Lib.Unif2.Work.Drive.greenEnergyPairing
import Submission.Lib.Unif2.Work.Drive.energyGreenRung
import Submission.Lib.Unif2.Work.Drive.chartPoleIdentity
import Submission.Lib.Unif2.Work.Analysis.Harmonic.integrable_inner_gradient_logNorm_sub

open Set Metric MeasureTheory Filter
open scoped Manifold Topology Gradient

noncomputable section

set_option linter.unusedSectionVars false

namespace Work.Kernel

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]


variable {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]

/-- Every point of `K` lies in one of the chart balls of the `s`-radii. -/
theorem K_subset_iUnion_chartBall {Ω K : Set X} {a b : X} {N : ℕ}
    (E : GreenCover (Fin N) Ω K a b) :
    K ⊆ ⋃ (t : Fin N), Submission.chartBall (chartAt ℂ (E.y t)) ((chartAt ℂ (E.y t)) (E.y t)) (E.s t) := by
  intro x hx
  have hne : ∃ i : Fin N, E.ψ i x ≠ 0 := by
    by_contra h
    push_neg at h
    have := E.hsum x hx
    simp only [h, Finset.sum_const_zero] at this
    exact absurd this.symm one_ne_zero
  obtain ⟨i, hi⟩ := hne
  exact Set.mem_iUnion.mpr ⟨i, E.hψsupp i (subset_tsupport _ (Function.mem_support.mpr hi))⟩

open scoped ContDiff

theorem exists_theta_pou {Ω K : Set X} {a b : X} {N : ℕ}
    [IsManifold (modelWithCornersSelf ℝ ℂ) ⊤ X]
    (E : GreenCover (Fin N) Ω K a b) :
    ∃ θ : Fin N → X → ℝ,
      (∀ t, ContMDiff (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℝ)
        (((⊤ : ℕ∞) : WithTop ℕ∞)) (θ t)) ∧
      (∀ t x, 0 ≤ θ t x) ∧ (∀ t x, θ t x ≤ 1) ∧
      (∀ t, tsupport (θ t) ⊆
        Submission.chartBall (chartAt ℂ (E.y t)) ((chartAt ℂ (E.y t)) (E.y t)) (E.σ t)) ∧
      (∀ x ∈ K, ∑ t, θ t x = 1) := by
  classical
  have hbump : ∀ t : Fin N, ∃ (η : X → ℝ),
      ContMDiff (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℝ)
        (((⊤ : ℕ∞) : WithTop ℕ∞)) η ∧
      (∀ x, 0 ≤ η x) ∧ (∀ x, η x ≤ 1) ∧
      (∀ x, x ∈ (chartAt ℂ (E.y t)).source →
        (chartAt ℂ (E.y t)) x ∈ Metric.closedBall ((chartAt ℂ (E.y t)) (E.y t)) (E.s t) → η x = 1) ∧
      tsupport η ⊆ Submission.chartBall (chartAt ℂ (E.y t)) ((chartAt ℂ (E.y t)) (E.y t)) (E.σ t) := by
    intro t
    exact exists_modelBump_chartBall (y := E.y t)
      (p := (chartAt ℂ (E.y t)) (E.y t)) (r₁ := E.s t) (r₂ := E.σ t)
      (E.hsσ t) (lt_trans (E.hspos t) (E.hsσ t))
      ((Metric.ball_subset_ball (E.hσρ t).le).trans (E.htgt t))
  choose η hη using hbump
  let ηc : ℕ → X → ℝ := fun n => if h : n < N then η ⟨n, h⟩ else 1
  have hηc : ∀ n, ContMDiff (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℝ)
      (((⊤ : ℕ∞) : WithTop ℕ∞)) (ηc n) := by
    intro n
    by_cases h : n < N
    · simp only [ηc, dif_pos h]
      exact (hη ⟨n, h⟩).1
    · simp only [ηc, dif_neg h]
      exact contMDiff_const
  have hηcb : ∀ n x, 0 ≤ ηc n x ∧ ηc n x ≤ 1 := by
    intro n x
    by_cases h : n < N
    · simp only [ηc, dif_pos h]
      exact ⟨(hη ⟨n, h⟩).2.1 x, (hη ⟨n, h⟩).2.2.1 x⟩
    · simp [ηc, dif_neg h]
  let θc : ℕ → X → ℝ := fun n x => ηc n x * ∏ i ∈ Finset.range n, (1 - ηc i x)
  have hθc_smooth : ∀ n, ContMDiff (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℝ)
      (((⊤ : ℕ∞) : WithTop ℕ∞)) (θc n) := by
    intro n
    have hprod : ContMDiff (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℝ)
        (((⊤ : ℕ∞) : WithTop ℕ∞)) (fun x => ∏ i ∈ Finset.range n, (1 - ηc i x)) :=
      ContMDiff.prod (fun i _ => contMDiff_const.sub (hηc i))
    exact (hηc n).mul hprod
  have hθc_nn : ∀ n x, 0 ≤ θc n x := by
    intro n x
    have h1 := hηcb n x
    have h2 : 0 ≤ ∏ i ∈ Finset.range n, (1 - ηc i x) :=
      Finset.prod_nonneg (fun i _ => by linarith [(hηcb i x).2])
    exact mul_nonneg h1.1 h2
  have hθc_le : ∀ n x, θc n x ≤ 1 := by
    intro n x
    have h1 := hηcb n x
    have h2 : (∏ i ∈ Finset.range n, (1 - ηc i x)) ≤ 1 := by
      apply Finset.prod_le_one₀
      · intro i _; linarith [(hηcb i x).2]
      · intro i _; linarith [(hηcb i x).1]
    have h2nn : 0 ≤ ∏ i ∈ Finset.range n, (1 - ηc i x) :=
      Finset.prod_nonneg (fun i _ => by linarith [(hηcb i x).2])
    calc θc n x = ηc n x * ∏ i ∈ Finset.range n, (1 - ηc i x) := rfl
      _ ≤ 1 * 1 := mul_le_mul h1.2 h2 h2nn zero_le_one
      _ = 1 := mul_one 1
  have htelescope : ∀ n x, ∑ i ∈ Finset.range n, θc i x = 1 - ∏ i ∈ Finset.range n, (1 - ηc i x) := by
    intro n
    induction n with
    | zero => intro x; simp [θc]
    | succ n ih =>
      intro x
      rw [Finset.sum_range_succ, ih x, Finset.prod_range_succ]
      simp only [θc]
      ring
  have hηc_eq : ∀ t : Fin N, ηc (t : ℕ) = η t := by
    intro t
    ext x
    simp only [ηc, dif_pos t.2]
  have hcover : ∀ x ∈ K, ∃ t : Fin N, η t x = 1 := by
    intro x hx
    have hmem : x ∈ ⋃ (t : Fin N), Submission.chartBall (chartAt ℂ (E.y t))
        ((chartAt ℂ (E.y t)) (E.y t)) (E.s t) := K_subset_iUnion_chartBall E hx
    rw [Set.mem_iUnion] at hmem
    obtain ⟨t, ht⟩ := hmem
    exact ⟨t, (hη t).2.2.2.1 x ht.1 (Metric.ball_subset_closedBall ht.2)⟩
  refine ⟨fun t => θc (t : ℕ), fun t => hθc_smooth (t : ℕ), fun t => hθc_nn (t : ℕ),
    fun t => hθc_le (t : ℕ), ?_, ?_⟩
  · intro t
    have h1 : tsupport (θc (t : ℕ)) ⊆ tsupport (ηc (t : ℕ)) := tsupport_mul_subset_left
    rw [hηc_eq t] at h1
    exact h1.trans (hη t).2.2.2.2
  · intro x hx
    obtain ⟨t₀, ht₀⟩ := hcover x hx
    have hz : (∏ i ∈ Finset.range N, (1 - ηc i x)) = 0 := by
      refine Finset.prod_eq_zero (Finset.mem_range.mpr t₀.2) ?_
      have : ηc (t₀ : ℕ) x = 1 := by
        simp only [ηc, dif_pos t₀.2]
        exact ht₀
      simp [this]
    rw [Fin.sum_univ_eq_sum_range (f := fun n => θc n x) N,
      htelescope N x, hz, sub_zero]



section Bridge

variable {N : ℕ}

/-- A real-smooth function on the manifold has a `C¹` chart representative in every chart. -/
theorem contDiffAt_chart_of_contMDiff {f : X → ℝ}
    [IsManifold (modelWithCornersSelf ℝ ℂ) ⊤ X]
    (hf : ContMDiff (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℝ)
      (((⊤ : ℕ∞) : WithTop ℕ∞)) f) (y : X) :
    ∀ x ∈ (chartAt ℂ y).source,
      ContDiffAt ℝ 1 (f ∘ (chartAt ℂ y).symm) ((chartAt ℂ y) x) := by
  intro x hx
  have hI : IsManifold (modelWithCornersSelf ℝ ℂ) (((⊤ : ℕ∞) : WithTop ℕ∞)) X := inferInstance
  have hG : HasGroupoid X
      (contDiffGroupoid (((⊤ : ℕ∞) : WithTop ℕ∞)) (modelWithCornersSelf ℝ ℂ)) := inferInstance
  have hcmax : chartAt ℂ y ∈ IsManifold.maximalAtlas (modelWithCornersSelf ℝ ℂ)
      (((⊤ : ℕ∞) : WithTop ℕ∞)) X := by
    intro e' he'
    exact ⟨hG.compatible (chart_mem_atlas ℂ y) he', hG.compatible he' (chart_mem_atlas ℂ y)⟩
  have hwit := (contMDiffWithinAt_iff_source_of_mem_maximalAtlas (I := modelWithCornersSelf ℝ ℂ)
      (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) (s := Set.univ) hcmax hx).mp
      ((hf.contMDiffAt (x := x)).contMDiffWithinAt)
  simp only [show ((modelWithCornersSelf ℝ ℂ : ModelWithCorners ℝ ℂ ℂ) : ℂ → ℂ) = id from rfl,
    show (((modelWithCornersSelf ℝ ℂ : ModelWithCorners ℝ ℂ ℂ).symm : ℂ → ℂ)) = id from rfl,
    OpenPartialHomeomorph.extend_coe, OpenPartialHomeomorph.extend_coe_symm, Function.comp_apply,
    Function.comp_id, Set.range_id, Set.inter_univ, Set.preimage_univ] at hwit
  rw [contMDiffWithinAt_univ] at hwit
  exact (hwit.contDiffAt).of_le (by norm_num)

end Bridge

section AE

/-- A clamped pullback whose chart representative is differentiable on the clamping ball is
differentiable almost everywhere. -/
theorem clampedPullback_differentiableAt_ae_of_differentiableOn {y : X} {ρ : ℝ} {u : X → ℝ}
    (htgt : Metric.ball ((chartAt ℂ y) y) ρ ⊆ (chartAt ℂ y).target)
    (hu : ∀ z ∈ Metric.ball ((chartAt ℂ y) y) ρ,
      DifferentiableAt ℝ (fun w : ℂ => u ((chartAt ℂ y).symm w)) z) :
    ∀ᵐ z ∂(volume : Measure ℂ), DifferentiableAt ℝ (Work.Drive.clampedPullback y ρ u) z := by
  rw [ae_iff]
  refine measure_mono_null (fun z hz => ?_)
    (MeasureTheory.Measure.addHaar_sphere volume ((chartAt ℂ y) y) ρ)
  by_cases hb : z ∈ Metric.ball ((chartAt ℂ y) y) ρ
  · have hev : (fun w : ℂ => u ((chartAt ℂ y).symm w)) =ᶠ[𝓝 z]
        Work.Drive.clampedPullback y ρ u := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hb] with w hw
      rw [Work.Drive.clampedPullback_apply_of_mem hw]
    exact absurd ((hev.differentiableAt_iff).mp (hu z hb)) hz
  · by_cases hc : z ∈ Metric.closedBall ((chartAt ℂ y) y) ρ
    · rw [Metric.mem_sphere]
      exact le_antisymm (Metric.mem_closedBall.mp hc) (not_lt.mp hb)
    · have hev : Work.Drive.clampedPullback y ρ u =ᶠ[𝓝 z] 0 := by
        filter_upwards [(Metric.isClosed_closedBall.isOpen_compl).mem_nhds hc] with w hw
        exact Work.Drive.clampedPullback_eq_zero_of_notMem_ball
          (fun h => hw (Metric.ball_subset_closedBall h))
      exact absurd ((hev.differentiableAt_iff).mpr (differentiableAt_const 0)) hz

end AE


section Analytic

/-- The gradient of a clamped pullback is bounded on the inner ball, for a chart-wise `C¹` function. -/
theorem gradient_clampedPullback_le {y : X} {ρ σ : ℝ} {Φ : X → ℝ} (hσρ : σ < ρ)
    (htgt : Metric.ball ((chartAt ℂ y) y) ρ ⊆ (chartAt ℂ y).target)
    (hΦ : ∀ x ∈ (chartAt ℂ y).source,
      ContDiffAt ℝ 1 (Φ ∘ (chartAt ℂ y).symm) ((chartAt ℂ y) x)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ Metric.ball ((chartAt ℂ y) y) σ,
      ‖gradient (Work.Drive.clampedPullback y ρ Φ) z‖ ≤ C := by
  have hA : ContinuousOn (fun z : ℂ => gradient (fun w : ℂ => Φ ((chartAt ℂ y).symm w)) z)
      (Metric.closedBall ((chartAt ℂ y) y) σ) := by
    intro z hz
    have hzρ : z ∈ Metric.ball ((chartAt ℂ y) y) ρ :=
      lt_of_le_of_lt (Metric.mem_closedBall.mp hz) hσρ
    have hzsrc : (chartAt ℂ y).symm z ∈ (chartAt ℂ y).source :=
      (chartAt ℂ y).map_target (htgt hzρ)
    have hright : (chartAt ℂ y) ((chartAt ℂ y).symm z) = z :=
      (chartAt ℂ y).right_inv (htgt hzρ)
    have hF : ContDiffAt ℝ 1 (fun w : ℂ => Φ ((chartAt ℂ y).symm w)) z := by
      have h := hΦ ((chartAt ℂ y).symm z) hzsrc
      rwa [hright] at h
    have h1 : ContinuousAt
        (fun w : ℂ => fderiv ℝ (fun u : ℂ => Φ ((chartAt ℂ y).symm u)) w) z :=
      hF.continuousAt_fderiv (by norm_num)
    have h2 : ContinuousAt (fun w : ℂ => gradient (fun u : ℂ => Φ ((chartAt ℂ y).symm u)) w) z := by
      simpa only [gradient, Function.comp_def] using
        (InnerProductSpace.toDual ℝ ℂ).symm.continuous.continuousAt.comp h1
    exact h2.continuousWithinAt
  have hB : ∀ z ∈ Metric.closedBall ((chartAt ℂ y) y) σ,
      gradient (Work.Drive.clampedPullback y ρ Φ) z
        = gradient (fun w : ℂ => Φ ((chartAt ℂ y).symm w)) z := by
    intro z hz
    refine Filter.EventuallyEq.gradient_eq ?_
    filter_upwards [Metric.isOpen_ball.mem_nhds
      (lt_of_le_of_lt (Metric.mem_closedBall.mp hz) hσρ)] with w hw
    rw [Work.Drive.clampedPullback_apply_of_mem hw]
  have hcont : ContinuousOn (fun z : ℂ => gradient (Work.Drive.clampedPullback y ρ Φ) z)
      (Metric.closedBall ((chartAt ℂ y) y) σ) := hA.congr hB
  obtain ⟨C, hC⟩ := (isCompact_closedBall ((chartAt ℂ y) y) σ).exists_bound_of_continuousOn hcont
  exact ⟨max C 0, le_max_right _ _, fun z hz =>
    le_trans (hC z (Metric.ball_subset_closedBall hz)) (le_max_left _ _)⟩

/-- **Local boundedness of the chart pullback of a function that is harmonic up to the pole.** -/
theorem gradient_chartPull_bdd_of_avoid {Ω : Set X} {c : X} {gC : X → ℝ}
    [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    (hgC : ∀ x ∈ Ω, x ≠ c →
      InnerProductSpace.HarmonicAt (gC ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x))
    {y : X} {σ ρ : ℝ} (hσ : 0 ≤ σ) (hσρ : σ < ρ)
    (htgt : Metric.ball ((chartAt ℂ y) y) ρ ⊆ (chartAt ℂ y).target)
    (hΩ : (chartAt ℂ y).source ∩ (chartAt ℂ y) ⁻¹' Metric.ball ((chartAt ℂ y) y) ρ ⊆ Ω)
    (hav : ∀ z ∈ Metric.closedBall ((chartAt ℂ y) y) σ, (chartAt ℂ y).symm z ≠ c) :
    ∃ C : ℝ, 0 < C ∧ ∀ z ∈ Metric.ball ((chartAt ℂ y) y) σ,
      ‖gradient (fun w : ℂ => gC ((chartAt ℂ y).symm w)) z‖ ≤ C := by
  have hA : ContinuousOn (fun z : ℂ => gradient (fun w : ℂ => gC ((chartAt ℂ y).symm w)) z)
      (Metric.closedBall ((chartAt ℂ y) y) σ) := by
    intro z hz
    have hzρ : z ∈ Metric.ball ((chartAt ℂ y) y) ρ :=
      lt_of_le_of_lt (Metric.mem_closedBall.mp hz) hσρ
    have hzsrc : (chartAt ℂ y).symm z ∈ (chartAt ℂ y).source :=
      (chartAt ℂ y).map_target (htgt hzρ)
    have hzpre : (chartAt ℂ y).symm z ∈ (chartAt ℂ y) ⁻¹' Metric.ball ((chartAt ℂ y) y) ρ := by
      rw [Set.mem_preimage, (chartAt ℂ y).right_inv (htgt hzρ)]
      exact hzρ
    have hharm : Submission.HarmonicOnXAt gC ((chartAt ℂ y).symm z) :=
      hgC _ (hΩ ⟨hzsrc, hzpre⟩) (hav z hz)
    have hright : (chartAt ℂ y) ((chartAt ℂ y).symm z) = z :=
      (chartAt ℂ y).right_inv (htgt hzρ)
    have hH : InnerProductSpace.HarmonicAt (fun w : ℂ => gC ((chartAt ℂ y).symm w)) z := by
      have h := (Submission.HarmonicOnXAt_iff_chart (u := gC)
        (x := (chartAt ℂ y).symm z) (y := y) hzsrc).mp hharm
      rwa [hright] at h
    have h1 : ContinuousAt (fun w : ℂ => fderiv ℝ (fun u : ℂ => gC ((chartAt ℂ y).symm u)) w) z :=
      hH.1.continuousAt_fderiv (by norm_num)
    have h2 : ContinuousAt (fun w : ℂ => gradient (fun u : ℂ => gC ((chartAt ℂ y).symm u)) w) z := by
      simpa only [gradient, Function.comp_def] using
        (InnerProductSpace.toDual ℝ ℂ).symm.continuous.continuousAt.comp h1
    exact h2.continuousWithinAt
  obtain ⟨C, hC⟩ := (isCompact_closedBall ((chartAt ℂ y) y) σ).exists_bound_of_continuousOn hA
  exact ⟨max C 0 + 1, by positivity, fun z hz =>
    le_trans (hC z (Metric.ball_subset_closedBall hz))
      (le_trans (le_max_left _ _) (le_add_of_nonneg_right zero_le_one))⟩

end Analytic



variable {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- **The transfer of the `(i,t)`-term to the chart of `t`.** -/
theorem theta_transfer {Ω K : Set X} {a b c : X} {N : ℕ} (E : GreenCover (Fin N) Ω K a b)
    (i₀ : Fin N)
    (hi₀nmem : ∀ i, i ≠ i₀ → c ∉ (chartAt ℂ (E.y i)) ⁻¹'
      Metric.closedBall ((chartAt ℂ (E.y i)) (E.y i)) (E.σ i))
    {θ : Fin N → X → ℝ}
    (hθsupp : ∀ t, tsupport (θ t) ⊆
      Submission.chartBall (chartAt ℂ (E.y t)) ((chartAt ℂ (E.y t)) (E.y t)) (E.σ t))
    {ψ : X → ℝ} (hψsupp : tsupport ψ ⊆ K)
    {gC : X → ℝ} (hgC : ∀ x ∈ Ω, x ≠ c → Submission.HarmonicOnXAt gC x)
    (hC1 : ∀ (t k : Fin N), ∀ x ∈ (chartAt ℂ (E.y k)).source,
      ContDiffAt ℝ 1 ((θ t) ∘ (chartAt ℂ (E.y k)).symm) ((chartAt ℂ (E.y k)) x))
    (hψC1 : ∀ k, ∀ x ∈ (chartAt ℂ (E.y k)).source,
      ContDiffAt ℝ 1 (ψ ∘ (chartAt ℂ (E.y k)).symm) ((chartAt ℂ (E.y k)) x))
    {i t : Fin N} (hit : i ≠ t) :
    Work.Drive.pairTerm (E.y i) (E.ρ i) (E.s i) (E.ψ i) gC (θ t * ψ)
      = Work.Drive.pairTerm (E.y t) (E.ρ t) (E.σ t) (E.ψ i) gC (θ t * ψ) := by
  classical
  -- the auxiliary open set
  set V : Set X := Submission.chartBall (chartAt ℂ (E.y i)) ((chartAt ℂ (E.y i)) (E.y i)) (E.s i)
    ∩ Submission.chartBall (chartAt ℂ (E.y t)) ((chartAt ℂ (E.y t)) (E.y t)) (E.σ t)
    ∩ ({c}ᶜ : Set X) with hVdef
  have hVopen : IsOpen V := by
    rw [hVdef]
    exact ((Submission.chartBall_isOpen _ _ _).inter (Submission.chartBall_isOpen _ _ _)).inter
      isOpen_compl_singleton
  have hVsub_i : V ⊆ (chartAt ℂ (E.y i)).source :=
    fun x hx => (Submission.chartBall_subset_source _ _ _) hx.1.1
  have hVsub_t : V ⊆ (chartAt ℂ (E.y t)).source :=
    fun x hx => (Submission.chartBall_subset_source _ _ _) hx.1.2
  have hVσ_i : ∀ x ∈ V, (chartAt ℂ (E.y i)) x ∈
      Metric.ball ((chartAt ℂ (E.y i)) (E.y i)) (E.s i) :=
    fun x hx => (Submission.mem_chartBall.mp hx.1.1).2
  have hVσ_t : ∀ x ∈ V, (chartAt ℂ (E.y t)) x ∈
      Metric.ball ((chartAt ℂ (E.y t)) (E.y t)) (E.σ t) :=
    fun x hx => (Submission.mem_chartBall.mp hx.1.2).2
  have hVc : ∀ x ∈ V, x ≠ c := fun x hx => hx.2
  -- the interaction points lie in `V`
  have hθmul_supp : tsupport (θ t * ψ) ⊆
      Submission.chartBall (chartAt ℂ (E.y t)) ((chartAt ℂ (E.y t)) (E.y t)) (E.σ t) :=
    (tsupport_mul_subset_left).trans (hθsupp t)
  have hint_supp : ∀ x ∈ tsupport (E.ψ i), x ∈ tsupport (θ t * ψ) →
      (chartAt ℂ (E.y i)) x ∈ Metric.ball ((chartAt ℂ (E.y i)) (E.y i)) (E.s i) → x ∈ V := by
    intro x hxw hxg hxball
    have hxi : x ∈ Submission.chartBall (chartAt ℂ (E.y i)) ((chartAt ℂ (E.y i)) (E.y i)) (E.s i) :=
      E.hψsupp i hxw
    have hxt : x ∈ Submission.chartBall (chartAt ℂ (E.y t)) ((chartAt ℂ (E.y t)) (E.y t)) (E.σ t) :=
      hθmul_supp hxg
    have hxc : x ≠ c := by
      intro hcon
      by_cases ht : t = i₀
      · subst ht
        have hmem : (chartAt ℂ (E.y i)) x ∈
            Metric.closedBall ((chartAt ℂ (E.y i)) (E.y i)) (E.σ i) :=
          Metric.ball_subset_closedBall (Metric.ball_subset_ball (le_of_lt (E.hsσ i)) hxball)
        rw [hcon] at hmem
        exact hi₀nmem i hit hmem
      · have hmem : (chartAt ℂ (E.y t)) x ∈
            Metric.closedBall ((chartAt ℂ (E.y t)) (E.y t)) (E.σ t) :=
          Metric.ball_subset_closedBall hxt.2
        rw [hcon] at hmem
        exact hi₀nmem t ht hmem
    exact ⟨⟨hxi, hxt⟩, hxc⟩
  have hint_supp' : ∀ x ∈ tsupport (E.ψ i), x ∈ tsupport (θ t * ψ) →
      (chartAt ℂ (E.y t)) x ∈ Metric.ball ((chartAt ℂ (E.y t)) (E.y t)) (E.σ t) → x ∈ V := by
    intro x hxw hxg hxball
    have hxi : x ∈ Submission.chartBall (chartAt ℂ (E.y i)) ((chartAt ℂ (E.y i)) (E.y i)) (E.s i) :=
      E.hψsupp i hxw
    have hxt : x ∈ Submission.chartBall (chartAt ℂ (E.y t)) ((chartAt ℂ (E.y t)) (E.y t)) (E.σ t) :=
      hθmul_supp hxg
    have hxc : x ≠ c := by
      intro hcon
      by_cases ht : t = i₀
      · subst ht
        have hmem : (chartAt ℂ (E.y i)) x ∈
            Metric.closedBall ((chartAt ℂ (E.y i)) (E.y i)) (E.σ i) :=
          Metric.ball_subset_closedBall (Metric.ball_subset_ball (le_of_lt (E.hsσ i)) hxi.2)
        rw [hcon] at hmem
        exact hi₀nmem i hit hmem
      · rw [hcon] at hxball
        exact hi₀nmem t ht (Metric.ball_subset_closedBall hxball)
    exact ⟨⟨hxi, hxt⟩, hxc⟩
  -- differentiability
  have hf₂ : ∀ x ∈ V, DifferentiableAt ℝ (fun w : ℂ => gC ((chartAt ℂ (E.y t)).symm w))
      ((chartAt ℂ (E.y t)) x) := by
    intro x hx
    have hxsrc : x ∈ (chartAt ℂ (E.y t)).source := hVsub_t hx
    have hxΩ : x ∈ Ω := E.hballΩ i ⟨hVsub_i hx, Metric.ball_subset_ball
      (le_of_lt (lt_trans (E.hsσ i) (E.hσρ i))) (hVσ_i x hx)⟩
    have hharm := hgC x hxΩ (hVc x hx)
    have h := (Submission.HarmonicOnXAt_iff_chart (u := gC) (x := x) (y := E.y t) hxsrc).mp hharm
    exact h.1.differentiableAt (by norm_num)
  have hg₂ : ∀ x ∈ V, DifferentiableAt ℝ (fun w : ℂ => (θ t * ψ) ((chartAt ℂ (E.y t)).symm w))
      ((chartAt ℂ (E.y t)) x) := by
    intro x hx
    have h1 := hC1 t t x (hVsub_t hx)
    have h2 := hψC1 t x (hVsub_t hx)
    have : (fun w : ℂ => (θ t * ψ) ((chartAt ℂ (E.y t)).symm w))
        = (fun w : ℂ => (θ t) ((chartAt ℂ (E.y t)).symm w)
            * ψ ((chartAt ℂ (E.y t)).symm w)) := rfl
    rw [this]
    exact (h1.mul h2).differentiableAt (by norm_num)
  exact Work.Kernel.TransferLocal.pairTerm_transfer_v2 (x := E.y i) (x' := E.y t) (ρ := E.ρ i) (σ := E.s i)
    (ρ' := E.ρ t) (σ' := E.σ t) (V := V) hVopen hVsub_i hVsub_t (E.htgt i) (E.htgt t)
    (lt_trans (E.hsσ i) (E.hσρ i)) (E.hσρ t) hint_supp hint_supp' hVσ_i hVσ_t hf₂ hg₂

/-- **The harmonic case: the `t`-th chart-local term vanishes when the pole is outside.** -/
theorem theta_harmonic_zero {Ω K : Set X} {a b c : X} {N : ℕ} (E : GreenCover (Fin N) Ω K a b)
    (i₀ : Fin N)
    (hi₀nmem : ∀ i, i ≠ i₀ → c ∉ (chartAt ℂ (E.y i)) ⁻¹'
      Metric.closedBall ((chartAt ℂ (E.y i)) (E.y i)) (E.σ i))
    {θ : Fin N → X → ℝ}
    (hθsupp : ∀ t, tsupport (θ t) ⊆
      Submission.chartBall (chartAt ℂ (E.y t)) ((chartAt ℂ (E.y t)) (E.y t)) (E.σ t))
    {ψ : X → ℝ} (hψsupp : tsupport ψ ⊆ K) (hψΩ : K ⊆ Ω)
    {gC : X → ℝ} (hgC : ∀ x ∈ Ω, x ≠ c → Submission.HarmonicOnXAt gC x)
    (hC1 : ∀ (t k : Fin N), ∀ x ∈ (chartAt ℂ (E.y k)).source,
      ContDiffAt ℝ 1 ((θ t) ∘ (chartAt ℂ (E.y k)).symm) ((chartAt ℂ (E.y k)) x))
    (hψC1 : ∀ k, ∀ x ∈ (chartAt ℂ (E.y k)).source,
      ContDiffAt ℝ 1 (ψ ∘ (chartAt ℂ (E.y k)).symm) ((chartAt ℂ (E.y k)) x))
    {t : Fin N} (ht : t ≠ i₀) :
    Work.Drive.pairTerm (E.y t) (E.ρ t) (E.σ t) (fun _ => (1 : ℝ)) gC (θ t * ψ) = 0 := by
  classical
  refine Work.Drive.GreenRung.integral_inner_gradient_eq_zero_weight_one (x₀ := E.y t) (h := gC)
    (φ := θ t * ψ) (ρ := E.ρ t) (σ := E.σ t) ?_ (E.hσρ t) (E.htgt t) ?_ ?_ ?_
  · exact le_of_lt (lt_trans (E.hspos t) (E.hsσ t))
  · intro x hx
    have this : ((θ t * ψ) ∘ (chartAt ℂ (E.y t)).symm)
        = (fun w : ℂ => (θ t) ((chartAt ℂ (E.y t)).symm w)
            * ψ ((chartAt ℂ (E.y t)).symm w)) := rfl
    rw [this]
    exact ((hC1 t t x hx).mul (hψC1 t x hx))
  · intro x hx
    have h1 : x ∈ tsupport (θ t) := tsupport_mul_subset_left hx
    exact (Submission.mem_chartBall.mp (hθsupp t h1)).2
  · intro x hx
    have hxK : x ∈ K := hψsupp (tsupport_mul_subset_right hx)
    have hxc : x ≠ c := by
      intro hcon
      have h1 : x ∈ tsupport (θ t) := tsupport_mul_subset_left hx
      have h2 := (Submission.mem_chartBall.mp (hθsupp t h1)).2
      have hmem : (chartAt ℂ (E.y t)) x ∈
          Metric.closedBall ((chartAt ℂ (E.y t)) (E.y t)) (E.σ t) :=
        Metric.ball_subset_closedBall h2
      rw [hcon] at hmem
      exact hi₀nmem t ht hmem
    exact hgC x (hψΩ hxK) hxc



/-! ## Analytic inputs (to be proved) -/

/-- **The logarithmic expansion in an arbitrary chart through the pole.** -/
theorem greenExpansion_chart {Ω : Set X} {c y : X} {gC : X → ℝ}
    (hΩo : IsOpen Ω) (hcΩ : c ∈ Ω)
    (hgC : Work.SimplyConnected.ABS.IsGreenOn Ω c gC)
    (hy : c ∈ (chartAt ℂ y).source) :
    ∃ r : ℝ, 0 < r ∧ ∃ H : ℂ → ℝ,
      Metric.ball ((chartAt ℂ y) c) r ⊆ (chartAt ℂ y).target ∧
      InnerProductSpace.HarmonicOnNhd H (Metric.ball ((chartAt ℂ y) c) r) ∧
      (∀ z ∈ Metric.ball ((chartAt ℂ y) c) r, z ≠ (chartAt ℂ y) c →
        gC ((chartAt ℂ y).symm z) = -Real.log ‖z - (chartAt ℂ y) c‖ + H z) := by
  classical
  obtain ⟨ρ₀, hρ₀pos, H₀, hH₀harm, hH₀eq⟩ :=
    Work.SimplyConnected.ABS.localPoleExpansion_of_hasLogPoleOn
      (x₀ := c) (U := Ω) (E := gC) (hΩo.mem_nhds hcΩ) hgC.2.1 hgC.2.2.2
  set p : ℂ := (chartAt ℂ c) c with hp
  set q : ℂ := (chartAt ℂ y) c with hq
  set τ : ℂ → ℂ := fun z => (chartAt ℂ c) ((chartAt ℂ y).symm z) with hτ
  set σ : ℂ → ℂ := fun w => (chartAt ℂ y) ((chartAt ℂ c).symm w) with hσ
  have hcy_tgt : q ∈ (chartAt ℂ y).target := by
    rw [hq]; exact (chartAt ℂ y).map_source hy
  have hcc_tgt : p ∈ (chartAt ℂ c).target := by
    rw [hp]; exact (chartAt ℂ c).map_source (mem_chart_source ℂ c)
  have hsymm_q : (chartAt ℂ y).symm q = c := by
    rw [hq]; exact (chartAt ℂ y).left_inv hy
  have hsymm_p : (chartAt ℂ c).symm p = c := by
    rw [hp]; exact (chartAt ℂ c).left_inv (mem_chart_source ℂ c)
  have hτq : τ q = p := by
    simp only [hτ, hsymm_q, hp]
  have hσp : σ p = q := by
    simp only [hσ, hsymm_p, hq]
  have hτan : AnalyticAt ℂ τ q :=
    Submission.analyticAt_transition_of_mem_atlas (chart_mem_atlas ℂ c) (chart_mem_atlas ℂ y)
      q hcy_tgt (by rw [hsymm_q]; exact mem_chart_source ℂ c)
  have hσan : AnalyticAt ℂ σ p :=
    Submission.analyticAt_transition_of_mem_atlas (chart_mem_atlas ℂ y) (chart_mem_atlas ℂ c)
      p hcc_tgt (by rw [hsymm_p]; exact hy)
  obtain ⟨A, hAfd⟩ : ∃ A : ℂ →L[ℂ] ℂ, HasFDerivAt τ A q :=
    ⟨fderiv ℂ τ q, hτan.differentiableAt.hasFDerivAt⟩
  obtain ⟨B, hBfd⟩ : ∃ B : ℂ →L[ℂ] ℂ, HasFDerivAt σ B p :=
    ⟨fderiv ℂ σ p, hσan.differentiableAt.hasFDerivAt⟩
  -- Lipschitz-type bounds from differentiability
  have hτlin : ∃ δ : ℝ, 0 < δ ∧ ∀ z, ‖z - q‖ < δ →
      ‖τ z - τ q - A (z - q)‖ ≤ 1 * ‖z - q‖ := by
    have hlit : (fun z : ℂ => τ z - τ q - A (z - q)) =o[nhds q] (fun z : ℂ => z - q) :=
      hasFDerivAt_iff_isLittleO.mp hAfd
    have h1 : ∀ᶠ z in nhds q, ‖τ z - τ q - A (z - q)‖ ≤ 1 * ‖z - q‖ :=
      hlit.def (c := 1) one_pos
    obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp h1
    exact ⟨ε, hε, fun z hz => hεsub (Metric.mem_ball.mpr (by rw [dist_eq_norm]; exact hz))⟩
  have hσlin : ∃ δ : ℝ, 0 < δ ∧ ∀ w, ‖w - p‖ < δ →
      ‖σ w - σ p - B (w - p)‖ ≤ 1 * ‖w - p‖ := by
    have hlit : (fun w : ℂ => σ w - σ p - B (w - p)) =o[nhds p] (fun w : ℂ => w - p) :=
      hasFDerivAt_iff_isLittleO.mp hBfd
    have h1 : ∀ᶠ w in nhds p, ‖σ w - σ p - B (w - p)‖ ≤ 1 * ‖w - p‖ :=
      hlit.def (c := 1) one_pos
    obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp h1
    exact ⟨ε, hε, fun w hw => hεsub (Metric.mem_ball.mpr (by rw [dist_eq_norm]; exact hw))⟩
  obtain ⟨δ₁, hδ₁pos, hδ₁⟩ := hτlin
  obtain ⟨δ₂, hδ₂pos, hδ₂⟩ := hσlin
  have hb₁ : ∀ z, ‖z - q‖ < δ₁ → ‖τ z - p‖ ≤ (1 + ‖A‖) * ‖z - q‖ := by
    intro z hz
    have h1 := hδ₁ z hz
    have heq : τ z - p = (τ z - τ q - A (z - q)) + A (z - q) := by
      rw [← hτq]; abel
    calc ‖τ z - p‖ = ‖(τ z - τ q - A (z - q)) + A (z - q)‖ := by rw [heq]
      _ ≤ ‖τ z - τ q - A (z - q)‖ + ‖A (z - q)‖ := norm_add_le _ _
      _ ≤ 1 * ‖z - q‖ + ‖A‖ * ‖z - q‖ := add_le_add h1 (A.le_opNorm (z - q))
      _ = (1 + ‖A‖) * ‖z - q‖ := by ring
  have hb₂ : ∀ w, ‖w - p‖ < δ₂ → ‖σ w - σ p‖ ≤ (1 + ‖B‖) * ‖w - p‖ := by
    intro w hw
    have h1 := hδ₂ w hw
    have h2 : ‖σ w - σ p‖ ≤ ‖σ w - σ p - B (w - p)‖ + ‖B (w - p)‖ := by
      have h3 := norm_add_le (σ w - σ p - B (w - p)) (B (w - p))
      rwa [sub_add_cancel] at h3
    calc ‖σ w - σ p‖ ≤ ‖σ w - σ p - B (w - p)‖ + ‖B (w - p)‖ := h2
      _ ≤ 1 * ‖w - p‖ + ‖B‖ * ‖w - p‖ := add_le_add h1 (B.le_opNorm (w - p))
      _ = (1 + ‖B‖) * ‖w - p‖ := by ring
  -- σ ∘ τ = id near q
  have hστ : ∀ z, z ∈ (chartAt ℂ y).target → (chartAt ℂ y).symm z ∈ (chartAt ℂ c).source →
      σ (τ z) = z := by
    intro z hzt hzs
    show (chartAt ℂ y) ((chartAt ℂ c).symm (τ z)) = z
    rw [show τ z = (chartAt ℂ c) ((chartAt ℂ y).symm z) from rfl,
      (chartAt ℂ c).left_inv hzs, (chartAt ℂ y).right_inv hzt]
  have hτcont : Tendsto τ (nhds q) (nhds p) := by
    rw [show p = τ q from hτq.symm]
    exact hAfd.continuousAt
  -- the eventual set
  have hmem1 : (chartAt ℂ y).target ∈ nhds q := (chartAt ℂ y).open_target.mem_nhds hcy_tgt
  have hmem2 : (chartAt ℂ y).symm ⁻¹' (chartAt ℂ c).source ∈ nhds q :=
    ((chartAt ℂ y).continuousAt_symm hcy_tgt).preimage_mem_nhds
      ((chartAt ℂ c).open_source.mem_nhds (by rw [hsymm_q]; exact mem_chart_source ℂ c))
  have hmem3 : (chartAt ℂ y).symm ⁻¹' Ω ∈ nhds q :=
    ((chartAt ℂ y).continuousAt_symm hcy_tgt).preimage_mem_nhds
      (hΩo.mem_nhds (by rw [hsymm_q]; exact hcΩ))
  have h4 : ∀ᶠ z in nhds q, ‖τ z - p‖ ≤ (1 + ‖A‖) * ‖z - q‖ := by
    have hb : ∀ᶠ z in nhds q, ‖z - q‖ < δ₁ := by
      have h := Metric.ball_mem_nhds q hδ₁pos
      filter_upwards [h] with z hz
      rwa [Metric.mem_ball, dist_eq_norm] at hz
    filter_upwards [hb] with z hz
    exact hb₁ z hz
  have h5c : ∀ᶠ z in nhds q, ‖τ z - p‖ < δ₂ := by
    have h := hτcont (Metric.ball_mem_nhds p hδ₂pos)
    filter_upwards [h] with z hz
    rwa [Set.mem_preimage, Metric.mem_ball, dist_eq_norm] at hz
  have h6 : ∀ᶠ z in nhds q, ‖τ z - p‖ < ρ₀ := by
    have h := hτcont (Metric.ball_mem_nhds p hρ₀pos)
    filter_upwards [h] with z hz
    rwa [Set.mem_preimage, Metric.mem_ball, dist_eq_norm] at hz
  have h7 : ∀ᶠ z in nhds q, |H₀ (τ z)| ≤ |H₀ p| + 1 := by
    have hτCA : ContinuousAt τ q := hAfd.continuousAt
    have hH₀cont : ContinuousAt H₀ (τ q) := by
      rw [hτq]
      exact hH₀harm.continuousOn.continuousAt (Metric.ball_mem_nhds p hρ₀pos)
    have hcont : ContinuousAt (fun z => H₀ (τ z)) q := hH₀cont.comp hτCA
    have hcont' : Tendsto (fun z => H₀ (τ z)) (nhds q) (nhds (H₀ (τ q))) := hcont
    have h1 : ∀ᶠ z in nhds q, dist (H₀ (τ z)) (H₀ (τ q)) < 1 :=
      (Metric.tendsto_nhds.mp hcont') 1 one_pos
    filter_upwards [h1] with z hz
    rw [Real.dist_eq, hτq] at hz
    have h2 := abs_add_le (H₀ (τ z) - H₀ p) (H₀ p)
    rw [sub_add_cancel] at h2
    linarith
  have h5 : ∀ᶠ z in nhds q, ‖z - q‖ ≤ (1 + ‖B‖) * ‖τ z - p‖ := by
    filter_upwards [h5c, hmem1, hmem2] with z hz hzt hzs
    have hστz : σ (τ z) = z := hστ z hzt hzs
    have heq : σ (τ z) - σ p = z - q := by rw [hστz, hσp]
    calc ‖z - q‖ = ‖σ (τ z) - σ p‖ := by rw [heq]
      _ ≤ (1 + ‖B‖) * ‖τ z - p‖ := hb₂ (τ z) hz
  have hev : ∀ᶠ z in nhds q,
      z ∈ (chartAt ℂ y).target ∧ (chartAt ℂ y).symm z ∈ (chartAt ℂ c).source ∧
      (chartAt ℂ y).symm z ∈ Ω ∧ ‖τ z - p‖ ≤ (1 + ‖A‖) * ‖z - q‖ ∧
      ‖z - q‖ ≤ (1 + ‖B‖) * ‖τ z - p‖ ∧ ‖τ z - p‖ < ρ₀ ∧
      |H₀ (τ z)| ≤ |H₀ p| + 1 := by
    filter_upwards [hmem1, hmem2, hmem3, h4, h5, h6, h7] with z h1 h2 h3 h4' h5' h6' h7'
    exact ⟨h1, h2, h3, h4', h5', h6', h7'⟩
  obtain ⟨δ, hδpos, hδ⟩ := Metric.mem_nhds_iff.mp hev
  have hneq_c : ∀ z : ℂ, z ∈ (chartAt ℂ y).target → z ≠ q → (chartAt ℂ y).symm z ≠ c := by
    intro z hzt hzq hcon
    have h1 : (chartAt ℂ y) c = z := by rw [← hcon]; exact (chartAt ℂ y).right_inv hzt
    exact hzq (by rw [hq, ← h1])
  have hharm : ∀ z : ℂ, ‖z - q‖ < δ → z ≠ q → InnerProductSpace.HarmonicAt
      (fun z : ℂ => gC ((chartAt ℂ y).symm z) + Real.log ‖z - q‖) z := by
    intro z hz hzne
    have hzball : z ∈ Metric.ball q δ := Metric.mem_ball.mpr (by rwa [dist_eq_norm])
    obtain ⟨hzt, hzs, hzΩ, -, -, -, -⟩ := hδ hzball
    have hxc : (chartAt ℂ y).symm z ≠ c := hneq_c z hzt hzne
    have hY : Submission.HarmonicOnXAt gC ((chartAt ℂ y).symm z) := hgC.2.1 _ ⟨hzΩ, hxc⟩
    have hiff := (Submission.HarmonicOnXAt_iff_chart (u := gC)
      (x := (chartAt ℂ y).symm z) (y := y) ((chartAt ℂ y).map_target hzt)).mp hY
    rw [(chartAt ℂ y).right_inv hzt] at hiff
    have hlog : InnerProductSpace.HarmonicAt (fun v : ℂ => Real.log ‖v - q‖) z :=
      AnalyticAt.harmonicAt_log_norm (f := fun v : ℂ => v - q)
        (analyticAt_id.sub analyticAt_const) (sub_ne_zero.mpr hzne)
    exact hiff.add hlog
  have hbnd : ∀ z : ℂ, ‖z - q‖ < δ → z ≠ q →
      |gC ((chartAt ℂ y).symm z) + Real.log ‖z - q‖| ≤
        |H₀ p| + 1 + Real.log (max (1 + ‖A‖) (1 + ‖B‖)) := by
    intro z hz hzne
    have hzball : z ∈ Metric.ball q δ := Metric.mem_ball.mpr (by rwa [dist_eq_norm])
    obtain ⟨hzt, hzs, hzΩ, h4', h5', h6', h7'⟩ := hδ hzball
    have hxc : (chartAt ℂ y).symm z ≠ c := hneq_c z hzt hzne
    have hxball : (chartAt ℂ y).symm z ∈ Submission.chartBall (chartAt ℂ c) p ρ₀ := by
      refine Submission.mem_chartBall.mpr ⟨hzs, ?_⟩
      rw [Metric.mem_ball, dist_eq_norm]
      exact h6'
    have hval := hH₀eq _ hzΩ hxball hxc
    have hPpos : 0 < ‖τ z - p‖ := by
      rw [← dist_eq_norm]
      refine dist_pos.mpr ?_
      intro hcon
      have hστz : σ (τ z) = z := hστ z hzt hzs
      exact hzne (by rw [← hστz, hcon, hσp])
    have hQpos : 0 < ‖z - q‖ := by rw [← dist_eq_norm]; exact dist_pos.mpr hzne
    have hMpos : 0 < max (1 + ‖A‖) (1 + ‖B‖) := by
      have hle : (1 : ℝ) ≤ 1 + ‖A‖ := le_add_of_nonneg_right (norm_nonneg A)
      exact lt_of_lt_of_le one_pos (le_trans hle (le_max_left _ _))
    have hQle : ‖z - q‖ / ‖τ z - p‖ ≤ max (1 + ‖A‖) (1 + ‖B‖) := by
      rw [div_le_iff₀ hPpos]
      calc ‖z - q‖ ≤ (1 + ‖B‖) * ‖τ z - p‖ := h5'
        _ ≤ max (1 + ‖A‖) (1 + ‖B‖) * ‖τ z - p‖ :=
            mul_le_mul_of_nonneg_right (le_max_right _ _) (le_of_lt hPpos)
    have hPle : ‖τ z - p‖ ≤ max (1 + ‖A‖) (1 + ‖B‖) * ‖z - q‖ :=
      le_trans h4' (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
    have hQge : 1 / max (1 + ‖A‖) (1 + ‖B‖) ≤ ‖z - q‖ / ‖τ z - p‖ := by
      rw [div_le_div_iff₀ hMpos hPpos, one_mul, mul_comm]
      exact hPle
    have hlogb : |Real.log (‖z - q‖ / ‖τ z - p‖)| ≤
        Real.log (max (1 + ‖A‖) (1 + ‖B‖)) := by
      have hQpos' : 0 < ‖z - q‖ / ‖τ z - p‖ := div_pos hQpos hPpos
      refine abs_le.mpr ⟨?_, Real.log_le_log hQpos' hQle⟩
      have h1 : Real.log ((max (1 + ‖A‖) (1 + ‖B‖))⁻¹) ≤ Real.log (‖z - q‖ / ‖τ z - p‖) :=
        Real.log_le_log (by positivity) (by simpa [one_div] using hQge)
      rwa [Real.log_inv] at h1
    have hkey : gC ((chartAt ℂ y).symm z) + Real.log ‖z - q‖
        = H₀ (τ z) + Real.log (‖z - q‖ / ‖τ z - p‖) := by
      rw [hval, Real.log_div (ne_of_gt hQpos) (ne_of_gt hPpos)]
      ring
    rw [hkey]
    calc |H₀ (τ z) + Real.log (‖z - q‖ / ‖τ z - p‖)|
        ≤ |H₀ (τ z)| + |Real.log (‖z - q‖ / ‖τ z - p‖)| := abs_add_le _ _
      _ ≤ (|H₀ p| + 1) + Real.log (max (1 + ‖A‖) (1 + ‖B‖)) := add_le_add h7' hlogb
  obtain ⟨U, hUharm, hUeq⟩ := Work.Potential.removable_singularity_ball_center
    (u := fun z : ℂ => gC ((chartAt ℂ y).symm z) + Real.log ‖z - q‖)
    (a := q) (R := δ) (M := |H₀ p| + 1 + Real.log (max (1 + ‖A‖) (1 + ‖B‖)))
    hδpos hharm hbnd
  refine ⟨δ / 2, by linarith, U, ?_, ?_, ?_⟩
  · intro z hz
    have hzδ : z ∈ Metric.ball q δ := Metric.ball_subset_ball (by linarith) hz
    exact (hδ hzδ).1
  · intro z hz
    have hz' : ‖z - q‖ < δ / 2 := by rwa [Metric.mem_ball, dist_eq_norm] at hz
    exact hUharm z hz'
  · intro z hz hzne
    have hz' : ‖z - q‖ < δ / 2 := by rwa [Metric.mem_ball, dist_eq_norm] at hz
    have h1 := hUeq z hz' hzne
    rw [h1]; ring



/-- **Continuity and boundedness of the cover weights.** -/
theorem continuous_cover_weight {Ω K : Set X} {a b : X} {N : ℕ}
    (E : GreenCover (Fin N) Ω K a b) (i : Fin N) : Continuous (E.ψ i) := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x ∈ tsupport (E.ψ i)
  · have hxball : x ∈ Submission.chartBall (chartAt ℂ (E.y i)) ((chartAt ℂ (E.y i)) (E.y i)) (E.s i) :=
      E.hψsupp i hx
    have hxsrc : x ∈ (chartAt ℂ (E.y i)).source := hxball.1
    have hxΩ : x ∈ Ω := E.hballΩ i
      ⟨hxball.1, Metric.ball_subset_ball (le_of_lt (lt_trans (E.hsσ i) (E.hσρ i))) hxball.2⟩
    have hdiff : DifferentiableAt ℝ (fun w : ℂ => E.ψ i ((chartAt ℂ (E.y i)).symm w))
        ((chartAt ℂ (E.y i)) x) := E.hψdiff i i x ⟨hxΩ, hxsrc⟩
    have hcomp : ContinuousAt
        (fun y : X => E.ψ i ((chartAt ℂ (E.y i)).symm ((chartAt ℂ (E.y i)) y))) x :=
      hdiff.continuousAt.comp ((chartAt ℂ (E.y i)).continuousAt hxsrc)
    have hev : (fun y : X => E.ψ i ((chartAt ℂ (E.y i)).symm ((chartAt ℂ (E.y i)) y)))
        =ᶠ[𝓝 x] E.ψ i := by
      filter_upwards [(chartAt ℂ (E.y i)).open_source.mem_nhds hxsrc] with y hy
      rw [(chartAt ℂ (E.y i)).left_inv hy]
    exact hcomp.congr hev
  · have hev : E.ψ i =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
      filter_upwards [(isClosed_tsupport (E.ψ i)).isOpen_compl.mem_nhds hx] with y hy
      exact image_eq_zero_of_notMem_tsupport hy
    exact continuousAt_const.congr_of_eventuallyEq hev


/-! ## Growth bounds for the pairing integrand (packaged) -/

/-- **Growth bound for the pairing integrand in a chart that avoids the pole.** -/
theorem growth_bound_away {Ω K : Set X} {a b c : X} {N : ℕ} (E : GreenCover (Fin N) Ω K a b)
    {gC : X → ℝ}
    (hgC : ∀ x ∈ Ω, x ≠ c → Submission.HarmonicOnXAt gC x)
    (hΩo : IsOpen Ω)
    {i : Fin N} (hav : ∀ z ∈ Metric.closedBall ((chartAt ℂ (E.y i)) (E.y i)) (E.σ i),
      (chartAt ℂ (E.y i)).symm z ≠ c)
    {Φ : X → ℝ} (hΦc1 : ∀ x ∈ (chartAt ℂ (E.y i)).source,
      ContDiffAt ℝ 1 (Φ ∘ (chartAt ℂ (E.y i)).symm) ((chartAt ℂ (E.y i)) x)) :
    ∃ C₂ : ℝ, 0 ≤ C₂ ∧
      ContinuousOn (fun z : ℂ => inner (𝕜 := ℝ)
        (gradient (fun w : ℂ => gC ((chartAt ℂ (E.y i)).symm w)) z)
        (gradient (fun w : ℂ => Φ ((chartAt ℂ (E.y i)).symm w)) z))
        (Metric.ball ((chartAt ℂ (E.y i)) (E.y i)) (E.σ i)) ∧
      ∀ z ∈ Metric.ball ((chartAt ℂ (E.y i)) (E.y i)) (E.σ i),
        z ≠ (chartAt ℂ (E.y i)) (E.y i) →
        ‖inner (𝕜 := ℝ) (gradient (fun w : ℂ => gC ((chartAt ℂ (E.y i)).symm w)) z)
          (gradient (fun w : ℂ => Φ ((chartAt ℂ (E.y i)).symm w)) z)‖
          ≤ C₂ / ‖z - (chartAt ℂ (E.y i)) (E.y i)‖ := by
  obtain ⟨B, hB, hBbound⟩ := gradient_chartPull_bdd_of_avoid (Ω := Ω) (c := c) (gC := gC)
    (fun x hx hxc => hgC x hx hxc) (y := E.y i) (σ := E.σ i) (ρ := E.ρ i)
    (le_of_lt (lt_trans (E.hspos i) (E.hsσ i))) (E.hσρ i) (E.htgt i) (E.hballΩ i) hav
  obtain ⟨C, hC, hCbound⟩ := gradient_clampedPullback_le (y := E.y i) (ρ := E.ρ i) (σ := E.σ i)
    (Φ := Φ) (E.hσρ i) (E.htgt i) hΦc1
  have hcont_grad_gC : ContinuousOn
      (fun z : ℂ => gradient (fun w : ℂ => gC ((chartAt ℂ (E.y i)).symm w)) z)
      (Metric.ball ((chartAt ℂ (E.y i)) (E.y i)) (E.σ i)) := by
    intro z hz
    have hzρ : z ∈ Metric.ball ((chartAt ℂ (E.y i)) (E.y i)) (E.ρ i) :=
      Metric.ball_subset_ball (le_of_lt (E.hσρ i)) hz
    have hzsrc : (chartAt ℂ (E.y i)).symm z ∈ (chartAt ℂ (E.y i)).source :=
      (chartAt ℂ (E.y i)).map_target (E.htgt i hzρ)
    have hzΩ : (chartAt ℂ (E.y i)).symm z ∈ Ω := E.hballΩ i ⟨hzsrc, by
      rw [Set.mem_preimage, (chartAt ℂ (E.y i)).right_inv (E.htgt i hzρ)]; exact hzρ⟩
    have hzc : (chartAt ℂ (E.y i)).symm z ≠ c := hav z (Metric.ball_subset_closedBall hz)
    have hharm : InnerProductSpace.HarmonicAt
        (fun w : ℂ => gC ((chartAt ℂ (E.y i)).symm w)) z := by
      have h := (Submission.HarmonicOnXAt_iff_chart (u := gC)
        (x := (chartAt ℂ (E.y i)).symm z) (y := E.y i) hzsrc).mp (hgC _ hzΩ hzc)
      rwa [(chartAt ℂ (E.y i)).right_inv (E.htgt i hzρ)] at h
    have h1 := hharm.1.continuousAt_fderiv (by norm_num)
    have h2 : ContinuousAt
        (fun w : ℂ => gradient (fun u : ℂ => gC ((chartAt ℂ (E.y i)).symm u)) w) z := by
      simpa only [gradient, Function.comp_def] using
        (InnerProductSpace.toDual ℝ ℂ).symm.continuous.continuousAt.comp h1
    exact h2.continuousWithinAt
  have hcont_grad_Φ : ContinuousOn
      (fun z : ℂ => gradient (fun w : ℂ => Φ ((chartAt ℂ (E.y i)).symm w)) z)
      (Metric.ball ((chartAt ℂ (E.y i)) (E.y i)) (E.σ i)) := by
    intro z hz
    have hzρ : z ∈ Metric.ball ((chartAt ℂ (E.y i)) (E.y i)) (E.ρ i) :=
      Metric.ball_subset_ball (le_of_lt (E.hσρ i)) hz
    have hzsrc : (chartAt ℂ (E.y i)).symm z ∈ (chartAt ℂ (E.y i)).source :=
      (chartAt ℂ (E.y i)).map_target (E.htgt i hzρ)
    have h := hΦc1 _ hzsrc
    rw [(chartAt ℂ (E.y i)).right_inv (E.htgt i hzρ)] at h
    have h1 := h.continuousAt_fderiv (by norm_num)
    have h2 : ContinuousAt
        (fun w : ℂ => gradient (fun u : ℂ => Φ ((chartAt ℂ (E.y i)).symm u)) w) z := by
      simpa only [gradient, Function.comp_def] using
        (InnerProductSpace.toDual ℝ ℂ).symm.continuous.continuousAt.comp h1
    exact h2.continuousWithinAt
  refine ⟨B * C * E.σ i, mul_nonneg (mul_nonneg hB.le hC)
    (le_of_lt (lt_trans (E.hspos i) (E.hsσ i))), hcont_grad_gC.inner hcont_grad_Φ, ?_⟩
  intro z hz hzne
  have hzρ : z ∈ Metric.ball ((chartAt ℂ (E.y i)) (E.y i)) (E.ρ i) :=
    Metric.ball_subset_ball (le_of_lt (E.hσρ i)) hz
  have hclamp_eq : gradient (fun w : ℂ => Φ ((chartAt ℂ (E.y i)).symm w)) z
      = gradient (Work.Drive.clampedPullback (E.y i) (E.ρ i) Φ) z :=
    (Filter.EventuallyEq.gradient_eq (by
      filter_upwards [Metric.isOpen_ball.mem_nhds hzρ] with w hw
      rw [Work.Drive.clampedPullback_apply_of_mem hw])).symm
  have h1 : ‖gradient (fun w : ℂ => gC ((chartAt ℂ (E.y i)).symm w)) z‖ ≤ B := hBbound z hz
  have h2 : ‖gradient (fun w : ℂ => Φ ((chartAt ℂ (E.y i)).symm w)) z‖ ≤ C := by
    rw [hclamp_eq]; exact hCbound z hz
  have h3 : ‖inner (𝕜 := ℝ) (gradient (fun w : ℂ => gC ((chartAt ℂ (E.y i)).symm w)) z)
      (gradient (fun w : ℂ => Φ ((chartAt ℂ (E.y i)).symm w)) z)‖ ≤ B * C :=
    (norm_inner_le_norm _ _).trans (mul_le_mul h1 h2 (norm_nonneg _) (le_trans (norm_nonneg _) h1))
  have h4 : ‖z - (chartAt ℂ (E.y i)) (E.y i)‖ ≤ E.σ i := by
    rw [← dist_eq_norm]; exact le_of_lt (Metric.mem_ball.mp hz)
  have h5 : 0 ≤ B * C := mul_nonneg hB.le hC
  have h6 : 0 < ‖z - (chartAt ℂ (E.y i)) (E.y i)‖ := by
    rw [← dist_eq_norm]; exact dist_pos.mpr hzne
  rw [le_div_iff₀ h6]
  calc ‖inner (𝕜 := ℝ) (gradient (fun w : ℂ => gC ((chartAt ℂ (E.y i)).symm w)) z)
        (gradient (fun w : ℂ => Φ ((chartAt ℂ (E.y i)).symm w)) z)‖
        * ‖z - (chartAt ℂ (E.y i)) (E.y i)‖
      ≤ (B * C) * E.σ i := mul_le_mul h3 h4 (norm_nonneg _) h5
    _ = B * C * E.σ i := rfl



/-! ## The chart-local pole identity with a *punctured* expansion hypothesis -/

/-- **The planar pole identity, with the expansion required only off the pole.** -/
theorem integral_inner_gradient_of_logExpansion_punctured {u H : ℂ → ℝ} {p : ℂ} {ρ : ℝ}
    (hH : InnerProductSpace.HarmonicOnNhd H (Metric.ball p ρ))
    {Φ : ℂ → ℝ} (hΦ : ContDiff ℝ 1 Φ) (hΦc : HasCompactSupport Φ)
    (hΦsupp : tsupport Φ ⊆ Metric.ball p ρ)
    (hueq : ∀ z ∈ tsupport Φ, z ≠ p →
      u =ᶠ[𝓝 z] fun w => -Real.log ‖w - p‖ + H w)
    (hi1 : Integrable (fun z : ℂ =>
      inner (𝕜 := ℝ) (gradient (fun y : ℂ => -Real.log ‖y - p‖) z) (gradient Φ z)))
    (hi2 : Integrable (fun z : ℂ =>
      inner (𝕜 := ℝ) (gradient H z) (gradient Φ z))) :
    ∫ z : ℂ, inner (𝕜 := ℝ) (gradient u z) (gradient Φ z) = 2 * Real.pi * Φ p := by
  have hae : ∀ᵐ z ∂(volume : Measure ℂ), inner (𝕜 := ℝ) (gradient u z) (gradient Φ z)
      = inner (𝕜 := ℝ) (gradient (fun y : ℂ => -Real.log ‖y - p‖) z) (gradient Φ z)
        + inner (𝕜 := ℝ) (gradient H z) (gradient Φ z) := by
    filter_upwards [compl_mem_ae_iff.mpr (measure_singleton p)] with z hzp
    by_cases hzs : z ∈ tsupport Φ
    · by_cases hz : z ∈ Metric.ball p ρ
      · have hev : u =ᶠ[𝓝 z] fun w => -Real.log ‖w - p‖ + H w := hueq z hzs hzp
        have hdiff : DifferentiableAt ℝ (fun w : ℂ => -Real.log ‖w - p‖) z :=
          (Work.Drive.hasFDerivAt_neg_log_norm_sub hzp).differentiableAt
        have hHdiff : DifferentiableAt ℝ H z := (hH z hz).1.differentiableAt (by norm_num)
        have h1 : gradient u z
            = gradient (fun w : ℂ => -Real.log ‖w - p‖) z + gradient H z := by
          rw [Filter.EventuallyEq.gradient_eq hev]
          exact Work.Drive.gradient_add_of_differentiableAt hdiff hHdiff
        rw [h1, inner_add_left]
      · exact absurd (hΦsupp hzs) hz
    · have hΦz : gradient Φ z = 0 :=
        Work.Analysis.Harmonic.gradient_eq_zero_of_notMem_tsupport hzs
      simp [hΦz]
  rw [integral_congr_ae hae, integral_add hi1 hi2,
    Work.Drive.integral_inner_gradient_logNorm_eq hΦ hΦc]
  have hzero : (∫ z : ℂ, inner (𝕜 := ℝ) (gradient H z) (gradient Φ z)) = 0 :=
    Work.Analysis.Harmonic.integral_inner_gradient_eq_zero
      (fun z hz => hH z (hΦsupp hz)) hΦ hΦc
  rw [hzero, add_zero]

/-- **The chart-local pole term, with the expansion required only off the pole.** -/
theorem pairTerm_pole_punctured {x₀ : X} {f χ : X → ℝ} {H : ℂ → ℝ} {p : ℂ} {ρ r σ : ℝ}
    (hσ : 0 ≤ σ) (hσρ : σ < ρ) (hrρ : r ≤ ρ)
    (htgt : Metric.ball ((chartAt ℂ x₀) x₀) ρ ⊆ (chartAt ℂ x₀).target)
    (hχsupp : tsupport χ ⊆ (chartAt ℂ x₀) ⁻¹' Metric.ball ((chartAt ℂ x₀) x₀) σ)
    (hH : InnerProductSpace.HarmonicOnNhd H (Metric.ball p r))
    (hueq : ∀ z ∈ Metric.ball ((chartAt ℂ x₀) x₀) ρ, z ≠ p →
      f ((chartAt ℂ x₀).symm z) = -Real.log ‖z - p‖ + H z)
    (hχc1 : ContDiff ℝ 1 (Work.Drive.clampedPullback x₀ ρ χ))
    (hχcs : HasCompactSupport (Work.Drive.clampedPullback x₀ ρ χ))
    (hχball : tsupport (Work.Drive.clampedPullback x₀ ρ χ) ⊆ Metric.ball p r)
    (hi1 : Integrable (fun z : ℂ =>
      inner (𝕜 := ℝ) (gradient (fun y : ℂ => -Real.log ‖y - p‖) z)
        (gradient (Work.Drive.clampedPullback x₀ ρ χ) z)))
    (hi2 : Integrable (fun z : ℂ =>
      inner (𝕜 := ℝ) (gradient H z) (gradient (Work.Drive.clampedPullback x₀ ρ χ) z)))
    (hint : Integrable (fun z : ℂ =>
      inner (𝕜 := ℝ) (gradient (Work.Drive.clampedPullback x₀ ρ f) z)
        (gradient (Work.Drive.clampedPullback x₀ ρ χ) z))) :
    Work.Drive.pairTerm x₀ ρ σ (fun _ : X => (1 : ℝ)) f χ
      = 2 * Real.pi * Work.Drive.clampedPullback x₀ ρ χ p := by
  classical
  have hsuppσ : tsupport (Work.Drive.clampedPullback x₀ ρ χ) ⊆
      Metric.closedBall ((chartAt ℂ x₀) x₀) σ := by
    refine closure_minimal ?_ Metric.isClosed_closedBall
    intro z hz
    rw [Function.mem_support] at hz
    have hzρ : z ∈ Metric.ball ((chartAt ℂ x₀) x₀) ρ := by
      by_contra hcon
      exact hz (Work.Drive.clampedPullback_eq_zero_of_notMem_ball (u := χ) hcon)
    rw [Metric.mem_closedBall]
    have hχne : χ ((chartAt ℂ x₀).symm z) ≠ 0 := by
      rw [← Work.Drive.clampedPullback_apply_of_mem (u := χ) hzρ]
      exact hz
    have hy : (chartAt ℂ x₀).symm z ∈ tsupport χ :=
      subset_tsupport _ (Function.mem_support.mpr hχne)
    have hball := hχsupp hy
    rw [Set.mem_preimage, (chartAt ℂ x₀).right_inv (htgt hzρ)] at hball
    exact le_of_lt hball
  have hae : (fun z : ℂ => Work.Drive.clampedPullback x₀ σ (fun _ : X => (1 : ℝ)) z *
        inner (𝕜 := ℝ) (gradient (Work.Drive.clampedPullback x₀ ρ f) z)
          (gradient (Work.Drive.clampedPullback x₀ ρ χ) z))
      =ᵐ[volume] fun z : ℂ =>
        inner (𝕜 := ℝ) (gradient (Work.Drive.clampedPullback x₀ ρ f) z)
          (gradient (Work.Drive.clampedPullback x₀ ρ χ) z) := by
    filter_upwards [compl_mem_ae_iff.mpr (MeasureTheory.Measure.addHaar_sphere volume
      ((chartAt ℂ x₀) x₀) σ)] with z hz
    have hzne : dist z ((chartAt ℂ x₀) x₀) ≠ σ := fun hcon =>
      hz (by rw [Metric.mem_sphere]; exact hcon)
    rcases lt_or_gt_of_ne hzne with hlt | hgt
    · rw [Work.Drive.clampedPullback_apply_of_mem (u := fun _ : X => (1 : ℝ))
        (Metric.mem_ball.mpr hlt), one_mul]
    · have hw : Work.Drive.clampedPullback x₀ σ (fun _ : X => (1 : ℝ)) z = 0 :=
        Work.Drive.clampedPullback_eq_zero_of_notMem_ball (u := fun _ : X => (1 : ℝ))
          (fun hcon => absurd (Metric.mem_ball.mp hcon) (not_lt.mpr (le_of_lt hgt)))
      have hnot : z ∉ tsupport (Work.Drive.clampedPullback x₀ ρ χ) := fun hcon =>
        (not_le.mpr hgt) (Metric.mem_closedBall.mp (hsuppσ hcon))
      rw [hw, zero_mul,
        Work.Analysis.Harmonic.gradient_eq_zero_of_notMem_tsupport hnot, inner_zero_right]
  have hloc : ∀ z ∈ tsupport (Work.Drive.clampedPullback x₀ ρ χ), z ≠ p →
      Work.Drive.clampedPullback x₀ ρ f
        =ᶠ[𝓝 z] fun w => -Real.log ‖w - p‖ + H w := by
    intro z hz hzp
    have hzρ : z ∈ Metric.ball ((chartAt ℂ x₀) x₀) ρ := by
      rw [Metric.mem_ball]
      exact lt_of_le_of_lt (Metric.mem_closedBall.mp (hsuppσ hz)) hσρ
    have hzr : z ∈ Metric.ball p r := hχball hz
    have hopen : Metric.ball p r ∩ Metric.ball ((chartAt ℂ x₀) x₀) ρ ∈ 𝓝 z :=
      Filter.inter_mem (Metric.isOpen_ball.mem_nhds hzr) (Metric.isOpen_ball.mem_nhds hzρ)
    filter_upwards [hopen, isOpen_compl_singleton.mem_nhds hzp] with w hw hwne
    rw [Work.Drive.clampedPullback_apply_of_mem (u := f) hw.2, hueq w hw.2 hwne]
  rw [Work.Drive.pairTerm, integral_congr_ae hae]
  exact integral_inner_gradient_of_logExpansion_punctured (u := Work.Drive.clampedPullback x₀ ρ f)
    hH hχc1 hχcs hχball hloc hi1 hi2


/-- **Changing the clamping radius of the weight.** -/
theorem pairTerm_clamp_weight {Ω K : Set X} {a b : X} {N : ℕ} (E : GreenCover (Fin N) Ω K a b)
    (t : Fin N) {gC χ : X → ℝ} :
    Work.Drive.pairTerm (E.y t) (E.ρ t) (E.s t) (E.ψ t) gC χ
      = Work.Drive.pairTerm (E.y t) (E.ρ t) (E.σ t) (E.ψ t) gC χ := by
  have hclamp : Work.Drive.clampedPullback (E.y t) (E.s t) (E.ψ t)
      = Work.Drive.clampedPullback (E.y t) (E.σ t) (E.ψ t) := by
    funext z
    by_cases hz : z ∈ Metric.ball ((chartAt ℂ (E.y t)) (E.y t)) (E.s t)
    · rw [Work.Drive.clampedPullback_apply_of_mem hz,
        Work.Drive.clampedPullback_apply_of_mem (Metric.ball_subset_ball (le_of_lt (E.hsσ t)) hz)]
    · rw [Work.Drive.clampedPullback_eq_zero_of_notMem_ball hz]
      by_cases hzσ : z ∈ Metric.ball ((chartAt ℂ (E.y t)) (E.y t)) (E.σ t)
      · rw [Work.Drive.clampedPullback_apply_of_mem hzσ]
        by_contra hne
        have hmem : (chartAt ℂ (E.y t)).symm z ∈ tsupport (E.ψ t) :=
          subset_tsupport _ (Function.mem_support.mpr (Ne.symm hne))
        have hball := (Submission.mem_chartBall.mp (E.hψsupp t hmem)).2
        rw [(chartAt ℂ (E.y t)).right_inv (E.htgt t
          (Metric.ball_subset_ball (le_of_lt (E.hσρ t)) hzσ))] at hball
        exact hz (Metric.mem_ball.mpr hball)
      · rw [Work.Drive.clampedPullback_eq_zero_of_notMem_ball hzσ]
  rw [Work.Drive.pairTerm, Work.Drive.pairTerm, hclamp]






/-- **Continuity and boundedness of a weight read in a chart ball.**  If `W` is continuous on `X`,
then `z ↦ W ((chartAt ℂ x).symm z)` is continuous on the `σ`-ball of the chart at `x` (for
`σ < ρ` and the `ρ`-ball inside the chart target) and bounded there by a nonnegative constant. -/
theorem weight_continuous_bounded {x : X} {ρ σ : ℝ} {W : X → ℝ} (hW : Continuous W)
    (hσ : 0 ≤ σ) (hσρ : σ < ρ)
    (htgt : Metric.ball ((chartAt ℂ x) x) ρ ⊆ (chartAt ℂ x).target) :
    ContinuousOn (fun z : ℂ => W ((chartAt ℂ x).symm z))
      (Metric.ball ((chartAt ℂ x) x) σ) ∧
    ∃ C₁ : ℝ, 0 ≤ C₁ ∧ ∀ z ∈ Metric.ball ((chartAt ℂ x) x) σ,
      ‖W ((chartAt ℂ x).symm z)‖ ≤ C₁ := by
  have hsub : Metric.closedBall ((chartAt ℂ x) x) σ ⊆ (chartAt ℂ x).target :=
    (Metric.closedBall_subset_ball hσρ).trans htgt
  have hsymm : ContinuousOn (fun z : ℂ => (chartAt ℂ x).symm z)
      (Metric.closedBall ((chartAt ℂ x) x) σ) :=
    ((chartAt ℂ x).continuousOn_symm).mono hsub
  have hcont_closed : ContinuousOn (fun z : ℂ => W ((chartAt ℂ x).symm z))
      (Metric.closedBall ((chartAt ℂ x) x) σ) :=
    hW.continuousOn.comp hsymm (fun z _ => Set.mem_univ _)
  obtain ⟨C₁, hC₁⟩ :=
    (isCompact_closedBall ((chartAt ℂ x) x) σ).exists_bound_of_continuousOn hcont_closed
  refine ⟨hcont_closed.mono (Metric.ball_subset_closedBall), C₁, ?_, ?_⟩
  · exact le_trans (norm_nonneg _)
      (hC₁ _ (Metric.mem_closedBall_self hσ))
  · intro z hz
    exact hC₁ z (Metric.ball_subset_closedBall hz)


/-! ## Pole identities with a *localised* expansion hypothesis -/

/-- **The planar pole identity, with harmonicity of the regular part assumed only on the support.** -/
theorem integral_inner_gradient_of_logExpansion_local {u H : ℂ → ℝ} {p : ℂ}
    {Φ : ℂ → ℝ} (hΦ : ContDiff ℝ 1 Φ) (hΦc : HasCompactSupport Φ)
    (hH : ∀ z ∈ tsupport Φ, InnerProductSpace.HarmonicAt H z)
    (hueq : ∀ z ∈ tsupport Φ, z ≠ p →
      u =ᶠ[𝓝 z] fun w => -Real.log ‖w - p‖ + H w)
    (hi1 : Integrable (fun z : ℂ =>
      inner (𝕜 := ℝ) (gradient (fun y : ℂ => -Real.log ‖y - p‖) z) (gradient Φ z)))
    (hi2 : Integrable (fun z : ℂ =>
      inner (𝕜 := ℝ) (gradient H z) (gradient Φ z))) :
    ∫ z : ℂ, inner (𝕜 := ℝ) (gradient u z) (gradient Φ z) = 2 * Real.pi * Φ p := by
  have hae : ∀ᵐ z ∂(volume : Measure ℂ), inner (𝕜 := ℝ) (gradient u z) (gradient Φ z)
      = inner (𝕜 := ℝ) (gradient (fun y : ℂ => -Real.log ‖y - p‖) z) (gradient Φ z)
        + inner (𝕜 := ℝ) (gradient H z) (gradient Φ z) := by
    filter_upwards [compl_mem_ae_iff.mpr (measure_singleton p)] with z hzp
    by_cases hzs : z ∈ tsupport Φ
    · have hev : u =ᶠ[𝓝 z] fun w => -Real.log ‖w - p‖ + H w := hueq z hzs hzp
      have hdiff : DifferentiableAt ℝ (fun w : ℂ => -Real.log ‖w - p‖) z :=
        (Work.Drive.hasFDerivAt_neg_log_norm_sub hzp).differentiableAt
      have hHdiff : DifferentiableAt ℝ H z := (hH z hzs).1.differentiableAt (by norm_num)
      have h1 : gradient u z
          = gradient (fun w : ℂ => -Real.log ‖w - p‖) z + gradient H z := by
        rw [Filter.EventuallyEq.gradient_eq hev]
        exact Work.Drive.gradient_add_of_differentiableAt hdiff hHdiff
      rw [h1, inner_add_left]
    · have hΦz : gradient Φ z = 0 :=
        Work.Analysis.Harmonic.gradient_eq_zero_of_notMem_tsupport hzs
      simp [hΦz]
  rw [integral_congr_ae hae, integral_add hi1 hi2,
    Work.Drive.integral_inner_gradient_logNorm_eq hΦ hΦc]
  have hzero : (∫ z : ℂ, inner (𝕜 := ℝ) (gradient H z) (gradient Φ z)) = 0 :=
    Work.Analysis.Harmonic.integral_inner_gradient_eq_zero (fun z hz => hH z hz) hΦ hΦc
  rw [hzero, add_zero]

/-- **The chart-local pole term, with a *localised* expansion hypothesis.**  Only the behaviour of
the regular part `H` and of the expansion on the support of the clamped weight is used. -/
theorem pairTerm_pole_local {x₀ : X} {f χ : X → ℝ} {H : ℂ → ℝ} {p : ℂ} {ρ σ : ℝ}
    (hσ : 0 ≤ σ) (hσρ : σ < ρ)
    (htgt : Metric.ball ((chartAt ℂ x₀) x₀) ρ ⊆ (chartAt ℂ x₀).target)
    (hχsupp : tsupport χ ⊆ (chartAt ℂ x₀) ⁻¹' Metric.ball ((chartAt ℂ x₀) x₀) σ)
    (hH : ∀ z ∈ tsupport (Work.Drive.clampedPullback x₀ ρ χ),
      InnerProductSpace.HarmonicAt H z)
    (hueq : ∀ z, z ∈ Metric.ball ((chartAt ℂ x₀) x₀) ρ → z ≠ p →
      f ((chartAt ℂ x₀).symm z) = -Real.log ‖z - p‖ + H z)
    (hχc1 : ContDiff ℝ 1 (Work.Drive.clampedPullback x₀ ρ χ))
    (hχcs : HasCompactSupport (Work.Drive.clampedPullback x₀ ρ χ))
    (hi1 : Integrable (fun z : ℂ =>
      inner (𝕜 := ℝ) (gradient (fun y : ℂ => -Real.log ‖y - p‖) z)
        (gradient (Work.Drive.clampedPullback x₀ ρ χ) z)))
    (hi2 : Integrable (fun z : ℂ =>
      inner (𝕜 := ℝ) (gradient H z) (gradient (Work.Drive.clampedPullback x₀ ρ χ) z)))
    (hint : Integrable (fun z : ℂ =>
      inner (𝕜 := ℝ) (gradient (Work.Drive.clampedPullback x₀ ρ f) z)
        (gradient (Work.Drive.clampedPullback x₀ ρ χ) z))) :
    Work.Drive.pairTerm x₀ ρ σ (fun _ : X => (1 : ℝ)) f χ
      = 2 * Real.pi * Work.Drive.clampedPullback x₀ ρ χ p := by
  classical
  have hsuppσ : tsupport (Work.Drive.clampedPullback x₀ ρ χ) ⊆
      Metric.closedBall ((chartAt ℂ x₀) x₀) σ := by
    refine closure_minimal ?_ Metric.isClosed_closedBall
    intro z hz
    rw [Function.mem_support] at hz
    have hzρ : z ∈ Metric.ball ((chartAt ℂ x₀) x₀) ρ := by
      by_contra hcon
      exact hz (Work.Drive.clampedPullback_eq_zero_of_notMem_ball (u := χ) hcon)
    rw [Metric.mem_closedBall]
    have hχne : χ ((chartAt ℂ x₀).symm z) ≠ 0 := by
      rw [← Work.Drive.clampedPullback_apply_of_mem (u := χ) hzρ]
      exact hz
    have hy : (chartAt ℂ x₀).symm z ∈ tsupport χ :=
      subset_tsupport _ (Function.mem_support.mpr hχne)
    have hball := hχsupp hy
    rw [Set.mem_preimage, (chartAt ℂ x₀).right_inv (htgt hzρ)] at hball
    exact le_of_lt hball
  have hae : (fun z : ℂ => Work.Drive.clampedPullback x₀ σ (fun _ : X => (1 : ℝ)) z *
        inner (𝕜 := ℝ) (gradient (Work.Drive.clampedPullback x₀ ρ f) z)
          (gradient (Work.Drive.clampedPullback x₀ ρ χ) z))
      =ᵐ[volume] fun z : ℂ =>
        inner (𝕜 := ℝ) (gradient (Work.Drive.clampedPullback x₀ ρ f) z)
          (gradient (Work.Drive.clampedPullback x₀ ρ χ) z) := by
    filter_upwards [compl_mem_ae_iff.mpr (MeasureTheory.Measure.addHaar_sphere volume
      ((chartAt ℂ x₀) x₀) σ)] with z hz
    have hzne : dist z ((chartAt ℂ x₀) x₀) ≠ σ := fun hcon =>
      hz (by rw [Metric.mem_sphere]; exact hcon)
    rcases lt_or_gt_of_ne hzne with hlt | hgt
    · rw [Work.Drive.clampedPullback_apply_of_mem (u := fun _ : X => (1 : ℝ))
        (Metric.mem_ball.mpr hlt), one_mul]
    · have hw : Work.Drive.clampedPullback x₀ σ (fun _ : X => (1 : ℝ)) z = 0 :=
        Work.Drive.clampedPullback_eq_zero_of_notMem_ball (u := fun _ : X => (1 : ℝ))
          (fun hcon => absurd (Metric.mem_ball.mp hcon) (not_lt.mpr (le_of_lt hgt)))
      have hnot : z ∉ tsupport (Work.Drive.clampedPullback x₀ ρ χ) := fun hcon =>
        (not_le.mpr hgt) (Metric.mem_closedBall.mp (hsuppσ hcon))
      rw [hw, zero_mul,
        Work.Analysis.Harmonic.gradient_eq_zero_of_notMem_tsupport hnot, inner_zero_right]
  have hloc : ∀ z ∈ tsupport (Work.Drive.clampedPullback x₀ ρ χ), z ≠ p →
      Work.Drive.clampedPullback x₀ ρ f
        =ᶠ[𝓝 z] fun w => -Real.log ‖w - p‖ + H w := by
    intro z hz hzp
    have hzρ : z ∈ Metric.ball ((chartAt ℂ x₀) x₀) ρ := by
      rw [Metric.mem_ball]
      exact lt_of_le_of_lt (Metric.mem_closedBall.mp (hsuppσ hz)) hσρ
    have hopen : Metric.ball ((chartAt ℂ x₀) x₀) ρ ∈ 𝓝 z :=
      Metric.isOpen_ball.mem_nhds hzρ
    filter_upwards [hopen, isOpen_compl_singleton.mem_nhds hzp] with w hw hwne
    rw [Work.Drive.clampedPullback_apply_of_mem (u := f) hw, hueq w hw hwne]
  rw [Work.Drive.pairTerm, integral_congr_ae hae]
  exact integral_inner_gradient_of_logExpansion_local hχc1 hχcs (fun z hz => hH z hz) hloc hi1 hi2


/-- The clamped pullback of a chart-`C¹` function whose support sits in a smaller ball is `C¹` and
has compact support. -/
theorem clampedPullback_contDiff_hasCompactSupport {x : X} {u : X → ℝ} {ρ σ : ℝ}
    (hρ : 0 < ρ) (hσ : 0 ≤ σ) (hσρ : σ < ρ)
    (htgt : Metric.ball ((chartAt ℂ x) x) ρ ⊆ (chartAt ℂ x).target)
    (hu : ∀ y ∈ (chartAt ℂ x).source,
      ContDiffAt ℝ 1 (u ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) y))
    (hsupp : tsupport u ⊆ (chartAt ℂ x) ⁻¹' Metric.ball ((chartAt ℂ x) x) σ) :
    ContDiff ℝ 1 (Work.Drive.clampedPullback x ρ u) ∧
      HasCompactSupport (Work.Drive.clampedPullback x ρ u) :=
  Work.Drive.GreenRung.contDiff_clampedPullback_hasCompactSupport hρ hσ hσρ htgt hu hsupp

/-- **Integrability of `⟪∇H, ∇Φ⟫`**: `Φ` is `C¹` with compact support and `H` is harmonic at every
point of the support of `Φ`. -/
theorem integrable_inner_gradient_of_harmonicOnSupport {H Φ : ℂ → ℝ}
    (hH : ∀ z ∈ tsupport Φ, InnerProductSpace.HarmonicAt H z)
    (hΦ : ContDiff ℝ 1 Φ) (hΦc : HasCompactSupport Φ) :
    Integrable (fun z : ℂ => inner (𝕜 := ℝ) (gradient H z) (gradient Φ z)) := by
  obtain ⟨CΦ, hCΦ⟩ := Work.Drive.GreenRung.exists_norm_gradient_le_of_hasCompactSupport hΦ hΦc
  have hgradΦ : Continuous (fun z : ℂ => gradient Φ z) := by
    have h1 : Continuous (fderiv ℝ Φ) := hΦ.continuous_fderiv (by norm_num)
    have h2 : Continuous fun z : ℂ => (InnerProductSpace.toDual ℝ ℂ).symm (fderiv ℝ Φ z) :=
      (InnerProductSpace.toDual ℝ ℂ).symm.continuous.comp h1
    simpa only [gradient, Function.comp_def] using h2
  have hHc : ContinuousOn (fun z : ℂ => gradient H z) (tsupport Φ) := by
    intro z hz
    have h1 := (hH z hz).1.continuousAt_fderiv (by norm_num)
    have h2 : ContinuousAt (fun w : ℂ => gradient H w) z := by
      simpa only [gradient, Function.comp_def] using
        (InnerProductSpace.toDual ℝ ℂ).symm.continuous.continuousAt.comp h1
    exact h2.continuousWithinAt
  obtain ⟨CH, hCH⟩ := hΦc.isCompact.exists_bound_of_continuousOn hHc
  have hsub : Function.support (fun z : ℂ => inner (𝕜 := ℝ) (gradient H z) (gradient Φ z)) ⊆
      tsupport Φ := by
    intro z hz
    by_contra hcon
    rw [Function.mem_support] at hz
    rw [Work.Analysis.Harmonic.gradient_eq_zero_of_notMem_tsupport hcon, inner_zero_right] at hz
    exact hz rfl
  have hbound : ∀ z : ℂ,
      ‖inner (𝕜 := ℝ) (gradient H z) (gradient Φ z)‖ ≤ max CH 0 * CΦ := by
    intro z
    by_cases hz : z ∈ tsupport Φ
    · rw [Real.norm_eq_abs]
      exact (abs_real_inner_le_norm _ _).trans
        (mul_le_mul (le_trans (hCH z hz) (le_max_left _ _)) (hCΦ z) (norm_nonneg _)
          (le_max_right _ _))
    · rw [Work.Analysis.Harmonic.gradient_eq_zero_of_notMem_tsupport hz, inner_zero_right,
        norm_zero]
      exact mul_nonneg (le_max_right _ _) (le_trans (norm_nonneg _) (hCΦ 0))
  rw [← integrableOn_iff_integrable_of_support_subset hsub]
  refine IntegrableOn.of_bound hΦc.isCompact.measure_lt_top ?_ (max CH 0 * CΦ) ?_
  · exact (ContinuousOn.inner (𝕜 := ℝ) hHc hgradΦ.continuousOn).aestronglyMeasurable
      (isClosed_tsupport Φ).measurableSet
  · filter_upwards with z
    exact hbound z

end Work.Kernel
