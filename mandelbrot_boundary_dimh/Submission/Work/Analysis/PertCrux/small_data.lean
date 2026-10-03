import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Pert.small_of_nearOn
import Submission.Work.Analysis.PertCrux.deriv_dslope_same
import Submission.Work.Analysis.PertCrux.germ_cubic_bound
import Submission.Work.Analysis.PertCrux.normalForm_apply_sigma

namespace Work.Analysis.PertCrux

open Complex Metric Filter Set
open scoped Topology

/-- Derivative at `0` of the normal form `z ↦ z + z (z - σ) u z`. -/
theorem normalForm_deriv {f u : ℂ → ℂ} {σ : ℂ} {rr : ℝ} (hrr : 0 < rr)
    (hu : DifferentiableOn ℂ u (Metric.ball (0 : ℂ) rr))
    (hform : ∀ z ∈ Metric.ball (0 : ℂ) rr, f z = z + z * (z - σ) * u z) :
    deriv f 0 = 1 - σ * u 0 := by
  have heq : f =ᶠ[𝓝 (0 : ℂ)] fun z => z + z * (z - σ) * u z :=
    Filter.eventually_of_mem (Metric.ball_mem_nhds 0 hrr) hform
  rw [heq.deriv_eq]
  have hud : DifferentiableAt ℂ u 0 := hu.differentiableAt (Metric.ball_mem_nhds 0 hrr)
  rw [Work.Pert.deriv_quad_mul hud]
  ring

theorem small_data {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (hd : MandelDim.IsParabolicGerm f₀ D₀) :
    ∃ r₁ M₀ : ℝ, 0 < r₁ ∧ 0 ≤ M₀ ∧
    ∀ {f : ℂ → ℂ} {Df : Set ℂ} {ρ δ₀ rr : ℝ} {u : ℂ → ℂ} {σ α : ℂ},
      0 < ρ → ρ ≤ r₁ → 0 < δ₀ → δ₀ ≤ ρ ^ 2 / 20 → δ₀ * (20 * (M₀ + 1)) ≤ ρ →
      0 < rr → ‖σ‖ ≤ rr →
      MandelDim.NearOn f₀ f Df (Metric.closedBall (0 : ℂ) ρ) δ₀ → f 0 = 0 →
      DifferentiableOn ℂ u (Metric.ball 0 rr) →
      (∀ z ∈ Metric.ball 0 rr, 1 / 2 ≤ ‖u z‖ ∧ ‖u z‖ ≤ 2) →
      (∀ z ∈ Metric.ball 0 rr, f z = z + z * (z - σ) * u z) →
      1 - σ * u 0 = Complex.exp (2 * Real.pi * Complex.I * α) →
      ‖σ‖ ≤ Real.sqrt (2 * δ₀) ∧ ‖u 0 - 1‖ ≤ 4 * δ₀ / ρ ^ 2 + M₀ * Real.sqrt (2 * δ₀) := by
  obtain ⟨C, hCnn, rC, hrCpos, hCbound⟩ := germ_cubic_bound hd
  obtain ⟨hD₀open, h0D₀, hf₀diff, hf₀0, hdf₀0, hddf₀0⟩ := hd
  obtain ⟨ε, hεpos, hεsub⟩ := Metric.mem_nhds_iff.mp (hD₀open.mem_nhds h0D₀)
  have hε4pos : 0 < ε / 4 := by linarith
  refine ⟨min rC (ε / 4), C, lt_min hrCpos hε4pos, hCnn, ?_⟩
  intro f Df ρ δ₀ rr u σ α hρ hρr hδ0 hδ20 hδρ hrr hσrr hnear hf0 hudiff hub hform hexp
  obtain ⟨hDfopen, hDfsub, hfdiff, hclose⟩ := hnear
  have hrC : ρ ≤ rC := le_trans hρr (min_le_left _ _)
  have hε4 : ρ ≤ ε / 4 := le_trans hρr (min_le_right _ _)
  have hρε : ρ < ε := by linarith
  have hεD₀ : Metric.closedBall (0 : ℂ) ρ ⊆ D₀ := fun z hz => by
    apply hεsub
    rw [Metric.mem_ball, dist_zero_right]
    rw [Metric.mem_closedBall, dist_zero_right] at hz
    linarith
  have hball_sub : Metric.ball (0 : ℂ) ρ ⊆ Df := fun z hz => hDfsub (Metric.ball_subset_closedBall hz)
  have hball_sub₀ : Metric.ball (0 : ℂ) ρ ⊆ D₀ := fun z hz => hεD₀ (Metric.ball_subset_closedBall hz)
  have h0ρ : (0 : ℂ) ∈ Metric.closedBall (0 : ℂ) ρ := Metric.mem_closedBall_self hρ.le
  have h0Df : (0 : ℂ) ∈ Df := hDfsub h0ρ
  have h0D₀ : (0 : ℂ) ∈ D₀ := hεD₀ h0ρ
  have hf_at : DifferentiableAt ℂ f 0 := hfdiff.differentiableAt (hDfopen.mem_nhds h0Df)
  have hf₀_at : DifferentiableAt ℂ f₀ 0 := hf₀diff.differentiableAt (hD₀open.mem_nhds h0D₀)
  have hf_an : AnalyticAt ℂ f 0 := hfdiff.analyticAt (hDfopen.mem_nhds h0Df)
  have hf₀_an : AnalyticAt ℂ f₀ 0 := hf₀diff.analyticAt (hD₀open.mem_nhds h0D₀)
  -- ## Cauchy estimate on `f - f₀`
  have hh_diff : DifferentiableOn ℂ (fun z => f z - f₀ z) (Metric.ball (0 : ℂ) ρ) :=
    (hfdiff.mono hball_sub).sub (hf₀diff.mono hball_sub₀)
  have hh_cont : ContinuousOn (fun z => f z - f₀ z) (closure (Metric.ball (0 : ℂ) ρ)) := by
    have h1 : ContinuousOn f (Df ∩ D₀) := hfdiff.continuousOn.mono (fun z hz => hz.1)
    have h2 : ContinuousOn f₀ (Df ∩ D₀) := hf₀diff.continuousOn.mono (fun z hz => hz.2)
    exact (h1.sub h2).mono (fun z hz =>
      ⟨hDfsub (Metric.closure_ball_subset_closedBall hz),
       hεD₀ (Metric.closure_ball_subset_closedBall hz)⟩)
  have hDC : DiffContOnCl ℂ (fun z => f z - f₀ z) (Metric.ball (0 : ℂ) ρ) := ⟨hh_diff, hh_cont⟩
  have hsphere : ∀ z ∈ Metric.sphere (0 : ℂ) ρ, ‖f z - f₀ z‖ ≤ δ₀ :=
    fun z hz => le_of_lt (hclose z (Metric.sphere_subset_closedBall hz))
  have hC1 : ‖iteratedDeriv 1 (fun z => f z - f₀ z) 0‖ ≤ δ₀ / ρ := by
    rw [iteratedDeriv_one]
    exact Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hρ hDC hsphere
  have hderiv_sub : deriv (fun z => f z - f₀ z) 0 = deriv f 0 - deriv f₀ 0 :=
    (hf_at.hasDerivAt.sub hf₀_at.hasDerivAt).deriv
  have hfderiv : deriv f 0 = 1 - σ * u 0 := normalForm_deriv hrr hudiff hform
  have hσu : ‖σ * u 0‖ ≤ δ₀ / ρ := by
    have h := hC1
    rw [iteratedDeriv_one, hderiv_sub, hfderiv, hdf₀0] at h
    have h2 : (1 - σ * u 0) - 1 = -(σ * u 0) := by ring
    rw [h2, norm_neg] at h
    exact h
  have h0ballrr : (0 : ℂ) ∈ Metric.ball (0 : ℂ) rr := Metric.mem_ball_self hrr
  have hu0lo : (1 / 2 : ℝ) ≤ ‖u 0‖ := (hub 0 h0ballrr).1
  have hucont : ContinuousAt u 0 := (hudiff.differentiableAt (Metric.ball_mem_nhds 0 hrr)).continuousAt
  have hσ2 : ‖σ‖ ≤ 2 * δ₀ / ρ := by
    have h1 : (1 / 2) * ‖σ‖ ≤ δ₀ / ρ := by
      refine le_trans ?_ hσu
      rw [norm_mul]
      calc (1 / 2) * ‖σ‖ ≤ ‖u 0‖ * ‖σ‖ := mul_le_mul_of_nonneg_right hu0lo (norm_nonneg σ)
        _ = ‖σ‖ * ‖u 0‖ := by ring
    have h3 : 2 * ((1 / 2) * ‖σ‖) ≤ 2 * (δ₀ / ρ) := by linarith
    have h4 : 2 * ((1 / 2) * ‖σ‖) = ‖σ‖ := by ring
    have h5 : 2 * (δ₀ / ρ) = 2 * δ₀ / ρ := by ring
    linarith [h3, h4.symm.le, h4.le, h5.symm.le, h5.le]
  have hσ10 : ‖σ‖ ≤ ρ / 10 := by
    have h1 : 2 * δ₀ / ρ ≤ ρ / 10 := by
      rw [div_le_div_iff₀ hρ (by norm_num : (0 : ℝ) < 10)]
      nlinarith [hδ20]
    linarith
  have hσρ : ‖σ‖ < ρ := by linarith
  -- ## first conclusion
  have hσsqrt : ‖σ‖ ≤ Real.sqrt (2 * δ₀) := by
    have hsq : ‖σ‖ ^ 2 ≤ 2 * δ₀ := by
      rcases le_or_gt rr ρ with hrrρ | hρrr
      · have h1 : ‖σ‖ ^ 2 ≤ rr * (2 * δ₀ / ρ) := by
          rw [sq]
          exact mul_le_mul hσrr hσ2 (norm_nonneg σ) (le_trans (norm_nonneg σ) hσrr)
        have h2 : rr * (2 * δ₀ / ρ) ≤ 2 * δ₀ := by
          have h3 : rr * (2 * δ₀ / ρ) ≤ ρ * (2 * δ₀ / ρ) :=
            mul_le_mul_of_nonneg_right hrrρ (by positivity)
          have h4 : ρ * (2 * δ₀ / ρ) = 2 * δ₀ := by field_simp
          linarith [h3, h4.le]
        linarith
      · have h1 : ‖σ‖ ^ 2 ≤ (2 * δ₀ / ρ) ^ 2 := by
          rw [sq, sq]
          exact mul_le_mul hσ2 hσ2 (norm_nonneg σ) (by positivity)
        have h2 : (2 * δ₀ / ρ) ^ 2 ≤ 2 * δ₀ := by
          rw [div_pow, sq]
          rw [div_le_iff₀ (by positivity)]
          nlinarith [hδ20, hρ, hδ0]
        linarith
    rw [Real.le_sqrt (norm_nonneg σ) (by linarith)]
    exact hsq
  refine ⟨hσsqrt, ?_⟩
  -- ## the `F`/`G` split of `P = dslope (f - id - id²) 0`
  set F : ℂ → ℂ := dslope (fun z : ℂ => f z - f₀ z) 0 with hF
  set G : ℂ → ℂ := dslope (fun z : ℂ => f₀ z - z - z ^ 2) 0 with hG
  have hF0 : F 0 = deriv f 0 - deriv f₀ 0 := by
    rw [hF, dslope_same]
    exact (hf_at.hasDerivAt.sub hf₀_at.hasDerivAt).deriv
  have hG0 : G 0 = 0 := by
    rw [hG, dslope_same]
    have hd : deriv (fun z : ℂ => f₀ z - z - z ^ 2) 0 = deriv f₀ 0 - 1 := by
      have h := ((hf₀_at.hasDerivAt.sub (hasDerivAt_id 0)).sub (hasDerivAt_pow 2 0)).deriv
      have h' : deriv (fun z : ℂ => f₀ z - z - z ^ 2) 0
          = (deriv f₀ 0 - 1) - (2 * (0:ℂ) ^ (2 - 1)) := h
      simpa using h'
    rw [hd, hdf₀0]
    ring
  -- ## bounds for `F`
  have hFdiff_ball : DifferentiableOn ℂ F (Metric.ball (0 : ℂ) ρ) := by
    rw [hF]
    exact (Complex.differentiableOn_dslope (Metric.ball_mem_nhds 0 hρ)).mpr hh_diff
  have hFdiff_U : DifferentiableOn ℂ F (Df ∩ D₀) := by
    rw [hF]
    refine (Complex.differentiableOn_dslope ?_).mpr ?_
    · exact hDfopen.inter hD₀open |>.mem_nhds ⟨h0Df, h0D₀⟩
    · exact (hfdiff.mono (fun z hz => hz.1)).sub (hf₀diff.mono (fun z hz => hz.2))
  have hFbound_sphere : ∀ z ∈ Metric.sphere (0 : ℂ) ρ, ‖F z‖ ≤ δ₀ / ρ := by
    intro z hz
    have hzn : ‖z‖ = ρ := by
      rw [Metric.mem_sphere, dist_zero_right] at hz
      exact hz
    have hz0 : z ≠ 0 := by
      intro h
      rw [h] at hzn
      simp at hzn
      linarith
    have hval : F z = (f z - f₀ z) / z := by
      rw [hF, dslope_of_ne _ hz0, slope_def_module]
      simp only [smul_eq_mul, sub_zero, hf0, hf₀0, sub_zero]
      rw [div_eq_mul_inv]; ring
    rw [hval, norm_div, hzn, div_le_div_iff₀ hρ hρ]
    exact le_of_lt (mul_lt_mul_of_pos_right (hclose z (Metric.sphere_subset_closedBall hz)) hρ)
  have hFbound : ∀ z ∈ Metric.ball (0 : ℂ) ρ, ‖F z‖ ≤ δ₀ / ρ := by
    intro z hz
    have hcont : ContinuousOn F (closure (Metric.ball (0 : ℂ) ρ)) :=
      hFdiff_U.continuousOn.mono (fun w hw =>
        ⟨hDfsub (Metric.closure_ball_subset_closedBall hw),
         hεD₀ (Metric.closure_ball_subset_closedBall hw)⟩)
    have hDC' : DiffContOnCl ℂ F (Metric.ball (0 : ℂ) ρ) := ⟨hFdiff_ball, hcont⟩
    refine Complex.norm_le_of_forall_mem_frontier_norm_le Metric.isBounded_ball hDC' ?_
      (subset_closure hz)
    intro w hw
    rw [frontier_ball _ hρ.ne'] at hw
    exact hFbound_sphere w hw
  have hFmaps : Set.MapsTo F (Metric.ball (0 : ℂ) ρ) (Metric.closedBall (F 0) (2 * δ₀ / ρ)) := by
    intro z hz
    have h0 : (0 : ℂ) ∈ Metric.ball (0 : ℂ) ρ := Metric.mem_ball_self hρ
    rw [Metric.mem_closedBall, dist_eq_norm]
    calc ‖F z - F 0‖ ≤ ‖F z‖ + ‖F 0‖ := norm_sub_le _ _
      _ ≤ δ₀ / ρ + δ₀ / ρ := add_le_add (hFbound z hz) (hFbound 0 h0)
      _ = 2 * δ₀ / ρ := by ring
  -- ## case σ = 0
  rcases eq_or_ne σ 0 with rfl | hσ0
  · have hfderiv0 : deriv f 0 = 1 := by
      have h := hfderiv
      simpa using h
    set K : ℂ → ℂ := dslope (dslope f 0) 0 with hK
    have hKval : ∀ z ∈ Metric.ball (0 : ℂ) rr, z ≠ 0 → K z = u z := by
      intro z hz hz0
      have hfz : f z = z + z * (z - 0) * u z := hform z hz
      simp only [sub_zero] at hfz
      have hA : dslope f 0 z = f z / z := by
        rw [dslope_of_ne _ hz0, slope_def_module]
        simp only [smul_eq_mul, sub_zero, hf0, sub_zero]
        rw [div_eq_mul_inv]; ring
      have hB : dslope f 0 0 = 1 := by rw [dslope_same, hfderiv0]
      rw [hK, dslope_of_ne _ hz0, slope_def_module, hA, hB, smul_eq_mul, sub_zero]
      rw [hfz]
      field_simp
      ring
    have hKcont : ContinuousAt K 0 := by
      rw [hK]
      have hd : DifferentiableOn ℂ (dslope (dslope f 0) 0) Df := by
        refine (Complex.differentiableOn_dslope (hDfopen.mem_nhds h0Df)).mpr ?_
        exact (Complex.differentiableOn_dslope (hDfopen.mem_nhds h0Df)).mpr hfdiff
      exact (hd.differentiableAt (hDfopen.mem_nhds h0Df)).continuousAt
    have hKu : K 0 = u 0 := by
      have heq : K =ᶠ[𝓝[≠] (0:ℂ)] u := by
        rw [eventuallyEq_nhdsWithin_iff]
        filter_upwards [Metric.ball_mem_nhds (0:ℂ) hrr] with z hz hz0
        exact hKval z hz hz0
      have h1 : Tendsto K (𝓝[≠] (0:ℂ)) (𝓝 (K 0)) := hKcont.tendsto.mono_left nhdsWithin_le_nhds
      have h2 : Tendsto u (𝓝[≠] (0:ℂ)) (𝓝 (u 0)) := hucont.tendsto.mono_left nhdsWithin_le_nhds
      exact tendsto_nhds_unique (h1.congr' heq) h2
    have hK0 : K 0 = deriv (deriv f) 0 / 2 := by
      rw [hK, dslope_same]
      exact deriv_dslope_same hDfopen h0Df hfdiff hf_an.deriv.differentiableAt
    have hf2 : iteratedDeriv 2 f 0 = deriv (deriv f) 0 := by
      rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
    have hu0 : u 0 = iteratedDeriv 2 f 0 / 2 := by
      rw [hf2, ← hK0, hKu]
    have hC2 : ‖iteratedDeriv 2 (fun z => f z - f₀ z) 0‖ ≤ 2 * (δ₀ / ρ ^ 2) := by
      have h := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le 2 hρ hDC hsphere
      have hval : ((Nat.factorial 2 : ℕ) : ℝ) * δ₀ / ρ ^ 2 = 2 * (δ₀ / ρ ^ 2) := by
        norm_num
        ring
      rw [hval] at h
      exact h
    have hsplit : iteratedDeriv 2 (fun z => f z - f₀ z) 0
        = iteratedDeriv 2 f 0 - iteratedDeriv 2 f₀ 0 :=
      iteratedDeriv_sub hf_an.contDiffAt hf₀_an.contDiffAt
    have hf₀2 : iteratedDeriv 2 f₀ 0 = 2 := by
      rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
      exact hddf₀0
    have hbound : ‖u 0 - 1‖ ≤ δ₀ / ρ ^ 2 := by
      have h1 : ‖iteratedDeriv 2 f 0 - 2‖ ≤ 2 * (δ₀ / ρ ^ 2) := by
        have hh := hC2
        rw [hsplit, hf₀2] at hh
        exact hh
      have h2 : u 0 - 1 = (iteratedDeriv 2 f 0 - 2) / 2 := by
        rw [hu0]; ring
      rw [h2, norm_div]
      have h3 : ‖(2 : ℂ)‖ = 2 := by norm_num
      rw [h3]
      linarith
    have hfin : ‖u 0 - 1‖ ≤ 4 * δ₀ / ρ ^ 2 + C * Real.sqrt (2 * δ₀) := by
      have h4 : δ₀ / ρ ^ 2 ≤ 4 * δ₀ / ρ ^ 2 := by
        have h5 : (0:ℝ) ≤ 3 * δ₀ / ρ ^ 2 := by positivity
        have h6 : (4:ℝ) * δ₀ / ρ ^ 2 = δ₀ / ρ ^ 2 + 3 * δ₀ / ρ ^ 2 := by ring
        linarith
      have h6 : (0:ℝ) ≤ C * Real.sqrt (2 * δ₀) := by positivity
      linarith
    exact hfin
  · -- ## case σ ≠ 0
    have hσ_ball : σ ∈ Metric.ball (0 : ℂ) ρ := by
      rw [Metric.mem_ball, dist_zero_right]; exact hσρ
    have hfσ : f σ = σ :=
      normalForm_apply_sigma (ρ := ‖σ‖) (norm_pos_iff.mpr hσ0) hrr hσrr le_rfl hDfopen
        (fun z hz => hDfsub (Metric.closedBall_subset_closedBall (le_of_lt hσρ) hz))
        hfdiff (fun z hz => (hub z hz).2) hform
    have hFσ : F σ = (f σ - f₀ σ) / σ := by
      rw [hF, dslope_of_ne _ hσ0, slope_def_module]
      simp only [smul_eq_mul, sub_zero, hf0, hf₀0, sub_zero]
      rw [div_eq_mul_inv]; ring
    have hGσ : G σ = (f₀ σ - σ - σ ^ 2) / σ := by
      rw [hG, dslope_of_ne _ hσ0, slope_def_module]
      simp only [smul_eq_mul, sub_zero, hf₀0, sub_zero]
      rw [div_eq_mul_inv]; ring
    have hident : ((F σ - F 0) + (G σ - G 0)) / σ = u 0 - 1 := by
      rw [hFσ, hGσ, hF0, hG0, hfσ, hdf₀0, hfderiv]
      field_simp
      ring
    have hFdiffbound : ‖F σ - F 0‖ ≤ 2 * δ₀ * ‖σ‖ / ρ ^ 2 := by
      have h := Complex.dist_le_div_mul_dist_of_mapsTo_ball hFdiff_ball hFmaps hσ_ball
      rw [dist_eq_norm, dist_eq_norm, sub_zero] at h
      calc ‖F σ - F 0‖ ≤ (2 * δ₀ / ρ) / ρ * ‖σ‖ := h
        _ = 2 * δ₀ * ‖σ‖ / ρ ^ 2 := by ring
    have hGdiffbound : ‖G σ - G 0‖ ≤ C * ‖σ‖ ^ 2 := by
      rw [hG0, sub_zero, hGσ, norm_div]
      rw [div_le_iff₀ (norm_pos_iff.mpr hσ0)]
      have hb := hCbound σ (le_of_lt (by linarith : ‖σ‖ < rC))
      calc ‖f₀ σ - σ - σ ^ 2‖ ≤ C * ‖σ‖ ^ 3 := hb
        _ = C * ‖σ‖ ^ 2 * ‖σ‖ := by ring
    have h5 : (2 * δ₀ * ‖σ‖ / ρ ^ 2) / ‖σ‖ = 2 * δ₀ / ρ ^ 2 := by
      field_simp
    have h6 : (C * ‖σ‖ ^ 2) / ‖σ‖ = C * ‖σ‖ := by
      field_simp
    have hfin : ‖u 0 - 1‖ ≤ 4 * δ₀ / ρ ^ 2 + C * Real.sqrt (2 * δ₀) := by
      have hgoal : ‖u 0 - 1‖ = ‖(F σ - F 0) + (G σ - G 0)‖ / ‖σ‖ := by
        rw [← hident, norm_div]
      rw [hgoal]
      have hA : ‖(F σ - F 0) + (G σ - G 0)‖ ≤ ‖F σ - F 0‖ + ‖G σ - G 0‖ := norm_add_le _ _
      have hB : (‖F σ - F 0‖ + ‖G σ - G 0‖) / ‖σ‖
          ≤ (2 * δ₀ * ‖σ‖ / ρ ^ 2 + C * ‖σ‖ ^ 2) / ‖σ‖ := by
        apply div_le_div_of_nonneg_right _ (norm_nonneg σ)
        linarith [hFdiffbound, hGdiffbound]
      have hC : (2 * δ₀ * ‖σ‖ / ρ ^ 2 + C * ‖σ‖ ^ 2) / ‖σ‖
          = 2 * δ₀ / ρ ^ 2 + C * ‖σ‖ := by
        rw [add_div, h5, h6]
      have hD : 2 * δ₀ / ρ ^ 2 + C * ‖σ‖ ≤ 4 * δ₀ / ρ ^ 2 + C * Real.sqrt (2 * δ₀) := by
        have h7 : 2 * δ₀ / ρ ^ 2 ≤ 4 * δ₀ / ρ ^ 2 := by
          have h8 : (0:ℝ) ≤ 2 * δ₀ / ρ ^ 2 := by positivity
          have h8' : (4:ℝ) * δ₀ / ρ ^ 2 = 2 * (2 * δ₀ / ρ ^ 2) := by ring
          linarith
        have h9 : C * ‖σ‖ ≤ C * Real.sqrt (2 * δ₀) :=
          mul_le_mul_of_nonneg_left hσsqrt hCnn
        linarith
      calc ‖(F σ - F 0) + (G σ - G 0)‖ / ‖σ‖
          ≤ (‖F σ - F 0‖ + ‖G σ - G 0‖) / ‖σ‖ := by
            apply div_le_div_of_nonneg_right hA (norm_nonneg σ)
        _ ≤ (2 * δ₀ * ‖σ‖ / ρ ^ 2 + C * ‖σ‖ ^ 2) / ‖σ‖ := hB
        _ = 2 * δ₀ / ρ ^ 2 + C * ‖σ‖ := hC
        _ ≤ 4 * δ₀ / ρ ^ 2 + C * Real.sqrt (2 * δ₀) := hD
    exact hfin

end Work.Analysis.PertCrux
