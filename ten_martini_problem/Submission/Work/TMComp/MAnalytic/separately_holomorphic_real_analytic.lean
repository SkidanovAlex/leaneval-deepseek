import Mathlib
import Submission.Work.TMComp.MAnalytic.hasSum_range_regroup
import Submission.Work.TMComp.MAnalytic.summable_double_of_bound
import Submission.Work.TMComp.MAnalytic.continuousOn_circleIntegral_parameter
import Submission.Work.TMComp.MAnalytic.formalMultilinearSeries_diagonal

open Complex MeasureTheory
open scoped Real Topology ENNReal NNReal
open Filter Set

namespace Work.TMComp.MAnalytic

/-! ## Elementary facts -/

noncomputable def mcoeff (F : ℂ → ℂ → ℂ) (r : ℝ) (η : ℂ) (m : ℕ) : ℂ :=
  (cauchyPowerSeries (fun ζ => F ζ η) 0 r m) (fun _ => 1)

noncomputable def acoeff (F : ℂ → ℂ → ℂ) (r : ℝ) (m n : ℕ) : ℂ :=
  (cauchyPowerSeries (fun η => mcoeff F r η m) 0 r n) (fun _ => 1)

lemma mul_aux (w z : ℂ) (m : ℕ) : (w / z) ^ m * z⁻¹ = w ^ m * ((1 / z) ^ m * z⁻¹) := by
  simp only [div_eq_mul_inv, mul_pow, inv_pow]
  ring

lemma cauchyPowerSeries_apply_one_mul (φ : ℂ → ℂ) {r : ℝ} (hr : 0 ≤ r) (m : ℕ) (w : ℂ) :
    (cauchyPowerSeries φ 0 r m) (fun _ => w)
      = w ^ m * ((cauchyPowerSeries φ 0 r m) (fun _ => 1)) := by
  rw [cauchyPowerSeries_apply, cauchyPowerSeries_apply]
  have h1 : (∮ z in C(0, r), (w / (z - 0)) ^ m • (z - 0)⁻¹ • φ z)
      = ∮ z in C(0, r), w ^ m • ((1 / (z - 0)) ^ m • (z - 0)⁻¹ • φ z) := by
    apply circleIntegral.integral_congr hr
    intro z hz
    show (w / (z - 0)) ^ m • (z - 0)⁻¹ • φ z
        = w ^ m • ((1 / (z - 0)) ^ m • (z - 0)⁻¹ • φ z)
    rw [smul_eq_mul, smul_eq_mul, smul_eq_mul]
    rw [← mul_assoc, mul_aux w (z - 0) m]
    ring
  rw [h1, circleIntegral.integral_smul, smul_comm, smul_eq_mul]

lemma mcoeff_eq_integral (F : ℂ → ℂ → ℂ) (r : ℝ) (η : ℂ) (m : ℕ) :
    mcoeff F r η m = (2 * Real.pi * Complex.I : ℂ)⁻¹ •
      ∮ z in C(0, r), (1 / z) ^ m • z⁻¹ • F z η := by
  unfold mcoeff
  rw [cauchyPowerSeries_apply]
  simp only [sub_zero]

lemma mcoeff_eq_integral' {F : ℂ → ℂ → ℂ} {r : ℝ} (hr : 0 ≤ r) (η : ℂ) (m : ℕ) :
    mcoeff F r η m = (2 * Real.pi * Complex.I : ℂ)⁻¹ •
      ∮ z in C(0, r), (z ^ (m + 1))⁻¹ • F z η := by
  rw [mcoeff_eq_integral]
  congr 1
  apply circleIntegral.integral_congr hr
  intro z hz
  have hkey : (1 / z) ^ m * z⁻¹ = (z ^ (m + 1))⁻¹ := by
    rw [one_div, inv_pow, ← mul_inv, ← pow_succ]
  show (1 / z) ^ m • z⁻¹ • F z η = (z ^ (m + 1))⁻¹ • F z η
  rw [smul_eq_mul, smul_eq_mul, smul_eq_mul]
  rw [← mul_assoc, hkey]

lemma acoeff_eq_integral {F : ℂ → ℂ → ℂ} {r : ℝ} (hr : 0 ≤ r) (m n : ℕ) :
    acoeff F r m n = (2 * Real.pi * Complex.I : ℂ)⁻¹ •
      ∮ η in C(0, r), (η ^ (n + 1))⁻¹ • mcoeff F r η m := by
  unfold acoeff
  rw [cauchyPowerSeries_apply]
  simp only [sub_zero]
  congr 1
  apply circleIntegral.integral_congr hr
  intro z hz
  have hkey : (1 / z) ^ n * z⁻¹ = (z ^ (n + 1))⁻¹ := by
    rw [one_div, inv_pow, ← mul_inv, ← pow_succ]
  show (1 / z) ^ n • z⁻¹ • mcoeff F r z m = (z ^ (n + 1))⁻¹ • mcoeff F r z m
  rw [smul_eq_mul, smul_eq_mul, smul_eq_mul]
  rw [← mul_assoc, hkey]

lemma inv_pow_mul_self {r : ℝ} (hr : 0 < r) (m : ℕ) : r * r⁻¹ ^ (m + 1) = r⁻¹ ^ m := by
  have h : r * r⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hr)
  rw [inv_pow, pow_succ, mul_inv_rev, ← mul_assoc, h, one_mul, ← inv_pow]

lemma arith1 {r : ℝ} (hr : 0 < r) (M : ℝ) (m : ℕ) :
    r * (r⁻¹ ^ m * r⁻¹ * M) = M * r⁻¹ ^ m := by
  calc r * (r⁻¹ ^ m * r⁻¹ * M) = (r * r⁻¹ ^ (m + 1)) * M := by rw [pow_succ]; ring
    _ = r⁻¹ ^ m * M := by rw [inv_pow_mul_self hr m]
    _ = M * r⁻¹ ^ m := by ring

lemma arith2 {r : ℝ} (hr : 0 < r) (M : ℝ) (p q : ℕ) :
    r * (r⁻¹ ^ (p + 1) * (M * r⁻¹ ^ q)) = M * r⁻¹ ^ (p + q) := by
  calc r * (r⁻¹ ^ (p + 1) * (M * r⁻¹ ^ q))
      = (r * r⁻¹ ^ (p + 1)) * (M * r⁻¹ ^ q) := by ring
    _ = r⁻¹ ^ p * (M * r⁻¹ ^ q) := by rw [inv_pow_mul_self hr p]
    _ = M * (r⁻¹ ^ p * r⁻¹ ^ q) := by ring
    _ = M * r⁻¹ ^ (p + q) := by rw [pow_add]



/-- `cauchyPowerSeries` evaluated at `z`, in terms of `mcoeff` (opaque RHS: safe as a simp lemma). -/
lemma mcoeff_spec (F : ℂ → ℂ → ℂ) {r : ℝ} (hr : 0 ≤ r) (η : ℂ) (m : ℕ) (z : ℂ) :
    (cauchyPowerSeries (fun ζ => F ζ η) 0 r m) (fun _ => z) = z ^ m * mcoeff F r η m :=
  cauchyPowerSeries_apply_one_mul (fun ζ => F ζ η) hr m z

/-- Cauchy power series of `η ↦ mcoeff F r η m`, evaluated at `w`, in terms of `acoeff`. -/
lemma acoeff_spec (F : ℂ → ℂ → ℂ) {r : ℝ} (hr : 0 ≤ r) (m : ℕ) (n : ℕ) (w : ℂ) :
    (cauchyPowerSeries (fun η => mcoeff F r η m) 0 r n) (fun _ => w) = w ^ n * acoeff F r m n :=
  cauchyPowerSeries_apply_one_mul (fun η => mcoeff F r η m) hr n w

theorem analyticAt_zero_aux {F : ℂ → ℂ → ℂ} {U V : Set ℂ}
    (hU : IsOpen U) (hV : IsOpen V) (h0U : (0 : ℂ) ∈ U) (h0V : (0 : ℂ) ∈ V)
    (hcont : ContinuousOn (fun p : ℂ × ℂ => F p.1 p.2) (U ×ˢ V))
    (hz : ∀ z ∈ U, DifferentiableOn ℂ (F z) V)
    (hw : ∀ w ∈ V, DifferentiableOn ℂ (fun z => F z w) U) :
    AnalyticAt ℂ (fun p : ℂ × ℂ => F p.1 p.2) 0 := by
  obtain ⟨r, hr, hrU, hrV⟩ :
      ∃ r : ℝ, 0 < r ∧ Metric.closedBall 0 r ⊆ U ∧ Metric.closedBall 0 r ⊆ V := by
    obtain ⟨r₁, hr₁, h₁⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds h0U)
    obtain ⟨r₂, hr₂, h₂⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds h0V)
    refine ⟨min r₁ r₂ / 2, by positivity, ?_, ?_⟩
    · exact (Metric.closedBall_subset_ball (by have := min_le_left r₁ r₂; linarith)).trans h₁
    · exact (Metric.closedBall_subset_ball (by have := min_le_right r₁ r₂; linarith)).trans h₂
  set R : ℝ≥0 := Real.toNNReal r with hRdef
  have hRval : (R : ℝ) = r := by rw [hRdef, Real.coe_toNNReal r hr.le]
  have hK : IsCompact (Metric.closedBall (0 : ℂ) r ×ˢ Metric.closedBall (0 : ℂ) r) :=
    IsCompact.prod (isCompact_closedBall (x := (0:ℂ)) (r := r))
      (isCompact_closedBall (x := (0:ℂ)) (r := r))
  have hKne : (Metric.closedBall (0 : ℂ) r ×ˢ Metric.closedBall (0 : ℂ) r).Nonempty :=
    ⟨(0, 0), by simp [Metric.mem_closedBall, hr.le]⟩
  have hcontK : ContinuousOn (fun p : ℂ × ℂ => F p.1 p.2)
      (Metric.closedBall 0 r ×ˢ Metric.closedBall 0 r) := hcont.mono (Set.prod_mono hrU hrV)
  obtain ⟨x₀, hx₀K, hx₀max⟩ := hK.exists_isMaxOn hKne hcontK.norm
  obtain ⟨M, hM0, hMb⟩ : ∃ M : ℝ, 0 ≤ M ∧
      ∀ ζ ∈ Metric.closedBall (0:ℂ) r, ∀ η ∈ Metric.closedBall (0:ℂ) r, ‖F ζ η‖ ≤ M :=
    ⟨‖F x₀.1 x₀.2‖, norm_nonneg _, fun ζ hζ η hη =>
      hx₀max (show (ζ, η) ∈ Metric.closedBall (0:ℂ) r ×ˢ Metric.closedBall (0:ℂ) r
        from ⟨hζ, hη⟩)⟩
  have hmcoeff_bound : ∀ η ∈ Metric.closedBall (0:ℂ) r, ∀ m : ℕ,
      ‖mcoeff F r η m‖ ≤ M * r⁻¹ ^ m := by
    intro η hη m
    rw [mcoeff_eq_integral]
    have hf : ∀ z ∈ Metric.sphere (0:ℂ) r,
        ‖(1 / z) ^ m • z⁻¹ • F z η‖ ≤ r⁻¹ ^ m * r⁻¹ * M := by
      intro z hz
      have hzr : ‖z‖ = r := by rwa [Metric.mem_sphere, dist_zero_right] at hz
      have h1 : ‖(1 / z) ^ m‖ = r⁻¹ ^ m := by
        rw [norm_pow, norm_div, norm_one, hzr, one_div]
      have h2 : ‖z⁻¹‖ = r⁻¹ := by rw [norm_inv, hzr]
      rw [norm_smul, norm_smul, ← mul_assoc, h1, h2]
      exact mul_le_mul_of_nonneg_left (hMb z (Metric.sphere_subset_closedBall hz) η hη)
        (by positivity)
    calc ‖(2 * Real.pi * Complex.I : ℂ)⁻¹ •
            ∮ z in C(0, r), (1 / z) ^ m • z⁻¹ • F z η‖
        ≤ r * (r⁻¹ ^ m * r⁻¹ * M) :=
          circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const hr.le hf
      _ = M * r⁻¹ ^ m := arith1 hr M m
  have hmcoeff_cont : ∀ m, ContinuousOn (fun η : ℂ => mcoeff F r η m) (Metric.closedBall 0 r) := by
    intro m
    have hc := continuousOn_circleIntegral_parameter (r := r) (r₁ := r) hr le_rfl hcontK m
    have hcs : ContinuousOn ((fun _ : ℂ => (2 * Real.pi * Complex.I : ℂ)⁻¹) •
        fun η : ℂ => ∮ ζ in C(0, r), (ζ ^ (m + 1))⁻¹ • F ζ η) (Metric.closedBall 0 r) :=
      (continuousOn_const (c := (2 * Real.pi * Complex.I : ℂ)⁻¹)).smul hc
    exact hcs.congr (fun η _ => mcoeff_eq_integral' hr.le η m)
  have hacoeff_bound : ∀ m n : ℕ, ‖acoeff F r m n‖ * r ^ (m + n) ≤ M := by
    intro m n
    rw [acoeff_eq_integral hr.le m n]
    have hf : ∀ z ∈ Metric.sphere (0:ℂ) r,
        ‖(z ^ (n+1))⁻¹ • mcoeff F r z m‖ ≤ r⁻¹ ^ (n+1) * (M * r⁻¹ ^ m) := by
      intro z hz
      have hzr : ‖z‖ = r := by rwa [Metric.mem_sphere, dist_zero_right] at hz
      rw [norm_smul]
      have h1 : ‖(z ^ (n+1))⁻¹‖ = r⁻¹ ^ (n+1) := by rw [norm_inv, norm_pow, hzr, inv_pow]
      rw [h1]
      exact mul_le_mul_of_nonneg_left
        (hmcoeff_bound z (Metric.sphere_subset_closedBall hz) m) (by positivity)
    calc ‖(2 * Real.pi * Complex.I : ℂ)⁻¹ •
            ∮ z in C(0, r), (z ^ (n+1))⁻¹ • mcoeff F r z m‖ * r ^ (m + n)
        ≤ (r * (r⁻¹ ^ (n+1) * (M * r⁻¹ ^ m))) * r ^ (m + n) := by
          gcongr
          exact circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const hr.le hf
      _ = (M * r⁻¹ ^ (m + n)) * r ^ (m + n) := by rw [arith2 hr M n m, Nat.add_comm]
      _ = M * (r⁻¹ * r) ^ (m + n) := by rw [mul_pow]; ring
      _ = M := by rw [inv_mul_cancel₀ (ne_of_gt hr), one_pow, mul_one]
  have hA : ∀ (η : ℂ), η ∈ Metric.closedBall (0:ℂ) r → ∀ z : ℂ, ‖z‖ < r →
      HasSum (fun m => z ^ m * mcoeff F r η m) (F z η) := by
    intro η hη z hzr
    have hηV : η ∈ V := hrV hη
    have hfps := hasFPowerSeriesOnBall_of_differentiable_off_countable (R := R) (s := ∅)
      (f := fun ζ => F ζ η) (c := 0)
      (by simp)
      (hcont.comp ((Continuous.prodMk continuous_id continuous_const).continuousOn)
        (fun ζ hζ => ⟨hrU (by rw [hRval] at hζ; exact hζ), hηV⟩))
      (fun ζ hζ => by
        rw [hRval] at hζ
        exact (hw η hηV).differentiableAt
          (hU.mem_nhds (hrU (Metric.ball_subset_closedBall hζ.1))))
      (by rw [hRdef, Real.toNNReal_pos]; exact hr)
    have hb := hfps.hasSum (y := z)
      (by rw [Metric.eball_coe, Metric.mem_ball, dist_zero_right, hRval]; exact hzr)
    rw [hRval] at hb
    simpa only [zero_add, mcoeff_spec (F := F) hr.le η] using hb
  have hstep0 : ∀ z ∈ U, ∀ w : ℂ, ‖w‖ < r →
      F z w = (2 * Real.pi * Complex.I : ℂ)⁻¹ • ∮ η in C(0, r), (η - w)⁻¹ • F z η := by
    intro z hzU w hwr
    refine (two_pi_I_inv_smul_circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
      (s := ∅) (by simp) ?_ ?_ ?_).symm
    · rw [Metric.mem_ball, dist_zero_right]; exact hwr
    · exact hcont.comp ((Continuous.prodMk continuous_const continuous_id).continuousOn)
        (fun η hη => ⟨hzU, hrV hη⟩)
    · intro x hx
      exact (hz z hzU).differentiableAt (hV.mem_nhds (hrV (Metric.ball_subset_closedBall hx.1)))
  have hstepB : ∀ z ∈ U, ∀ w : ℂ, ‖w‖ < r → ‖z‖ < r →
      HasSum (fun m => z ^ m * ((2 * Real.pi * Complex.I : ℂ)⁻¹ •
        ∮ η in C(0, r), (η - w)⁻¹ • mcoeff F r η m)) (F z w) := by
    intro z hzU w hwr hzr
    set q : ℝ := ‖z‖ * r⁻¹ with hqdef
    have hq0 : 0 ≤ q := by positivity
    have hq1 : q < 1 := by
      rw [hqdef, ← div_eq_mul_inv]
      exact (div_lt_one hr).mpr hzr
    set Kc : ℝ := r * (r - ‖w‖)⁻¹ * M with hKdef
    have hrw2 : 0 < r - ‖w‖ := sub_pos.mpr hwr
    have hne2 : ∀ θ : ℝ, circleMap 0 r θ - w ≠ 0 := by
      intro θ hzero
      have h1 : ‖circleMap 0 r θ‖ = r := by rw [norm_circleMap_zero, abs_of_pos hr]
      rw [sub_eq_zero] at hzero
      rw [← hzero, h1] at hwr
      exact lt_irrefl _ hwr
    have hmain := intervalIntegral.hasSum_integral_of_dominated_convergence
      (μ := volume) (a := 0) (b := 2 * Real.pi)
      (F := fun m θ => deriv (circleMap 0 r) θ •
          ((circleMap 0 r θ - w)⁻¹ • (z ^ m * mcoeff F r (circleMap 0 r θ) m)))
      (f := fun θ => deriv (circleMap 0 r) θ •
          ((circleMap 0 r θ - w)⁻¹ • F z (circleMap 0 r θ)))
      (bound := fun m _ => Kc * q ^ m)
      (fun m => by
        have hcθ : Continuous fun θ : ℝ => mcoeff F r (circleMap 0 r θ) m :=
          (hmcoeff_cont m).comp_continuous (continuous_circleMap 0 r)
            (fun θ => circleMap_mem_closedBall 0 hr.le θ)
        have hbase : Continuous fun θ : ℝ => deriv (circleMap 0 r) θ •
            ((circleMap 0 r θ - w)⁻¹ • (z ^ m * mcoeff F r (circleMap 0 r θ) m)) := by
          simp only [deriv_circleMap]
          fun_prop
        exact hbase.measurable.aestronglyMeasurable)
      (fun m => by
        refine Filter.Eventually.of_forall fun θ _ => ?_
        have hnorm : ‖deriv (circleMap 0 r) θ‖ = r := by
          rw [deriv_circleMap, norm_mul, Complex.norm_I, mul_one, norm_circleMap_zero, abs_of_pos hr]
        have hcirc : ‖circleMap 0 r θ‖ = r := by rw [norm_circleMap_zero, abs_of_pos hr]
        have hsub : r - ‖w‖ ≤ ‖circleMap 0 r θ - w‖ := by
          have ha : |r - ‖w‖| ≤ ‖circleMap 0 r θ - w‖ := by
            simpa only [hcirc] using abs_norm_sub_norm_le (circleMap 0 r θ) w
          exact (le_abs_self _).trans ha
        have hposη : 0 < ‖circleMap 0 r θ - w‖ := lt_of_lt_of_le hrw2 hsub
        have hden : ‖(circleMap 0 r θ - w)⁻¹‖ ≤ (r - ‖w‖)⁻¹ := by
          rw [norm_inv]
          exact (inv_le_inv₀ hposη hrw2).mpr hsub
        have hmc : ‖mcoeff F r (circleMap 0 r θ) m‖ ≤ M * r⁻¹ ^ m :=
          hmcoeff_bound _ (circleMap_mem_closedBall 0 hr.le θ) m
        rw [hKdef, hqdef, norm_smul, norm_smul, norm_mul, hnorm]
        have hstep : ‖(circleMap 0 r θ - w)⁻¹‖ * (‖z ^ m‖ * ‖mcoeff F r (circleMap 0 r θ) m‖)
            ≤ (r - ‖w‖)⁻¹ * (‖z‖ ^ m * (M * r⁻¹ ^ m)) := by
          refine mul_le_mul hden (mul_le_mul ?_ hmc (by positivity) (by positivity))
            (by positivity) (by positivity)
          exact le_of_eq (norm_pow z m)
        calc r * (‖(circleMap 0 r θ - w)⁻¹‖ * (‖z ^ m‖ * ‖mcoeff F r (circleMap 0 r θ) m‖))
            ≤ r * ((r - ‖w‖)⁻¹ * (‖z‖ ^ m * (M * r⁻¹ ^ m))) :=
              mul_le_mul_of_nonneg_left hstep hr.le
          _ = (r * (r - ‖w‖)⁻¹ * M) * (‖z‖ * r⁻¹) ^ m := by rw [mul_pow]; ring)
      (by
        refine Filter.Eventually.of_forall fun θ _ => ?_
        exact (summable_geometric_of_lt_one hq0 hq1).mul_left Kc)
      (by
        rw [show (fun t : ℝ => ∑' n : ℕ, Kc * q ^ n) = fun _ => Kc * (1 - q)⁻¹ from
          funext fun t => by rw [tsum_mul_left, tsum_geometric_of_lt_one hq0 hq1]]
        exact intervalIntegrable_const)
      (by
        refine Filter.Eventually.of_forall fun θ _ => ?_
        have h := (hA (circleMap 0 r θ) (circleMap_mem_closedBall 0 hr.le θ) z hzr).const_smul
          (deriv (circleMap 0 r) θ * (circleMap 0 r θ - w)⁻¹)
        simpa only [mul_smul] using h)
    have hh := hmain.const_smul (2 * Real.pi * Complex.I : ℂ)⁻¹
    have hpair : (2 * Real.pi * Complex.I : ℂ)⁻¹ • (∫ t in (0:ℝ)..2 * Real.pi,
        deriv (circleMap 0 r) t • ((circleMap 0 r t - w)⁻¹ • F z (circleMap 0 r t))
        ∂volume) = F z w := by
      change (2 * Real.pi * Complex.I : ℂ)⁻¹ •
        (∮ η in C(0, r), (η - w)⁻¹ • F z η) = F z w
      exact (hstep0 z hzU w hwr).symm
    rw [hpair] at hh
    have hmain2 : HasSum (fun m : ℕ => (2 * Real.pi * Complex.I : ℂ)⁻¹ •
          ∮ η in C(0, r), (η - w)⁻¹ • (z ^ m * mcoeff F r η m)) (F z w) := by
      simpa only [circleIntegral] using hh
    have hterm : ∀ m : ℕ, (2 * Real.pi * Complex.I : ℂ)⁻¹ •
          ∮ η in C(0, r), (η - w)⁻¹ • (z ^ m * mcoeff F r η m)
        = z ^ m * ((2 * Real.pi * Complex.I : ℂ)⁻¹ •
          ∮ η in C(0, r), (η - w)⁻¹ • mcoeff F r η m) := by
      intro m
      have hfuneq : (fun η : ℂ => (η - w)⁻¹ • (z ^ m * mcoeff F r η m))
          = fun η => z ^ m • ((η - w)⁻¹ • mcoeff F r η m) := by
        funext η
        rw [← smul_eq_mul, smul_comm]
      rw [hfuneq, circleIntegral.integral_smul, smul_comm]
      simp only [smul_eq_mul]
    simpa only [hterm] using hmain2
  have hstepC : ∀ m : ℕ, ∀ w : ℂ, ‖w‖ < r →
      HasSum (fun n => w ^ n * acoeff F r m n)
        ((2 * Real.pi * Complex.I : ℂ)⁻¹ • ∮ η in C(0, r), (η - w)⁻¹ • mcoeff F r η m) := by
    intro m w hwr
    have hci : CircleIntegrable (fun η => mcoeff F r η m) 0 r :=
      ((hmcoeff_cont m).mono Metric.sphere_subset_closedBall).circleIntegrable hr.le
    have h := hasSum_cauchyPowerSeries_integral (f := fun η => mcoeff F r η m) (c := 0)
      (R := r) hci hwr
    simpa only [zero_add, acoeff_spec (F := F) hr.le m] using h
  have hfinal : ∀ z ∈ U, ∀ w : ℂ, ‖w‖ < r → ‖z‖ < r →
      HasSum (fun N : ℕ => ∑ k ∈ Finset.range (N + 1),
          acoeff F r k (N - k) * z ^ k * w ^ (N - k)) (F z w) := by
    intro z hzU w hwr hzr
    set g : ℕ × ℕ → ℂ := fun p => acoeff F r p.1 p.2 * z ^ p.1 * w ^ p.2 with hgdef
    have hgsum : Summable g := summable_double_of_bound hr hM0 hacoeff_bound hzr hwr
    have hwq : ‖w‖ * r⁻¹ < 1 := by
      rw [← div_eq_mul_inv]
      exact (div_lt_one hr).mpr hwr
    have hsummand : ∀ m, Summable (fun n => g (m, n)) := by
      intro m
      refine Summable.of_norm_bounded (f := fun n => g (m, n))
        (g := fun n => (M * r⁻¹ ^ m * ‖z‖ ^ m) * (‖w‖ * r⁻¹) ^ n) ?_ ?_
      · exact (summable_geometric_of_lt_one (by positivity) hwq).mul_left _
      · intro n
        have hle : ‖acoeff F r m n‖ ≤ M * r⁻¹ ^ (m + n) := by
          have h' := mul_le_mul_of_nonneg_right (hacoeff_bound m n)
            (by positivity : (0:ℝ) ≤ r⁻¹ ^ (m + n))
          rwa [mul_assoc, ← mul_pow, mul_inv_cancel₀ (ne_of_gt hr), one_pow, mul_one] at h'
        rw [hgdef, norm_mul, norm_mul, norm_pow, norm_pow]
        calc ‖acoeff F r m n‖ * ‖z‖ ^ m * ‖w‖ ^ n
            ≤ (M * r⁻¹ ^ (m + n)) * ‖z‖ ^ m * ‖w‖ ^ n :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right hle (by positivity)) (by positivity)
          _ = (M * r⁻¹ ^ m * ‖z‖ ^ m) * (‖w‖ * r⁻¹) ^ n := by
              rw [mul_pow, pow_add]; ring
    have h1 : HasSum (fun m => z ^ m * ((2 * Real.pi * Complex.I : ℂ)⁻¹ •
        ∮ η in C(0, r), (η - w)⁻¹ • mcoeff F r η m)) (F z w) := hstepB z hzU w hwr hzr
    have h2 : ∀ m, (∑' n : ℕ, g (m, n)) = z ^ m * ((2 * Real.pi * Complex.I : ℂ)⁻¹ •
        ∮ η in C(0, r), (η - w)⁻¹ • mcoeff F r η m) := by
      intro m
      have hC := (hstepC m w hwr).mul_left (z ^ m)
      have hC' : HasSum (fun n : ℕ => g (m, n)) (z ^ m * ((2 * Real.pi * Complex.I : ℂ)⁻¹ •
          ∮ η in C(0, r), (η - w)⁻¹ • mcoeff F r η m)) := by
        simpa only [hgdef, mul_comm, mul_left_comm, mul_assoc] using hC
      exact hC'.tsum_eq
    have h3 : (∑' p : ℕ × ℕ, g p) = F z w := by
      rw [hgsum.tsum_prod' hsummand]
      rw [show (fun m => ∑' n : ℕ, g (m, n)) = fun m => z ^ m *
          ((2 * Real.pi * Complex.I : ℂ)⁻¹ •
          ∮ η in C(0, r), (η - w)⁻¹ • mcoeff F r η m) from funext h2]
      exact h1.tsum_eq
    have hreg := hasSum_range_regroup hgsum
    rw [h3] at hreg
    simpa only [hgdef] using hreg
  obtain ⟨p, hpdiag, hpnorm⟩ :=
    formalMultilinearSeries_diagonal (acoeff F r) hr hM0 hacoeff_bound
  set R2 : ℝ≥0 := Real.toNNReal (r / 2) with hR2def
  have hR2val : (R2 : ℝ) = r / 2 := by rw [hR2def, Real.coe_toNNReal (r / 2) (by positivity)]
  have hfpso : HasFPowerSeriesOnBall (fun q : ℂ × ℂ => F q.1 q.2) p 0 (R2 : ℝ≥0∞) := by
    refine ⟨?_, ?_, ?_⟩
    · refine p.le_radius_of_bound M ?_
      intro N
      simpa only [hR2val] using hpnorm N
    · have hpos : (0 : ℝ≥0) < R2 := by
        rw [hR2def, Real.toNNReal_pos]
        exact show (0:ℝ) < r / 2 by positivity
      exact ENNReal.coe_pos.mpr hpos
    · intro y hy
      rw [Metric.eball_coe, Metric.mem_ball, dist_zero_right, hR2val] at hy
      have hy1 : ‖y.1‖ < r := lt_of_le_of_lt (norm_fst_le y) (by linarith)
      have hy2 : ‖y.2‖ < r := lt_of_le_of_lt (norm_snd_le y) (by linarith)
      have hy1U : y.1 ∈ U :=
        hrU (by rw [Metric.mem_closedBall, dist_zero_right]; exact le_of_lt hy1)
      have h := hfinal y.1 hy1U y.2 hy2 hy1
      simpa only [zero_add, hpdiag] using h
  exact ⟨p, ⟨_, hfpso⟩⟩

theorem separately_holomorphic_real_analytic {U V : Set ℂ} (hU : IsOpen U) (hV : IsOpen V)
    {F : ℂ → ℂ → ℂ}
    (hcont : ContinuousOn (fun p : ℂ × ℂ => F p.1 p.2) (U ×ˢ V))
    (hz : ∀ z ∈ U, DifferentiableOn ℂ (F z) V)
    (hw : ∀ w ∈ V, DifferentiableOn ℂ (fun z => F z w) U) :
    AnalyticOnNhd ℝ (fun p : ℂ × ℂ => F p.1 p.2) (U ×ˢ V) := by
  intro x hx
  rw [Set.mem_prod] at hx
  obtain ⟨hx1, hx2⟩ := hx
  set G : ℂ → ℂ → ℂ := fun s t => F (x.1 + s) (x.2 + t) with hGdef
  set U' : Set ℂ := {s | x.1 + s ∈ U} with hU'def
  set V' : Set ℂ := {t | x.2 + t ∈ V} with hV'def
  have hU'open : IsOpen U' := by
    rw [hU'def]
    exact hU.preimage (continuous_const.add continuous_id)
  have hV'open : IsOpen V' := by
    rw [hV'def]
    exact hV.preimage (continuous_const.add continuous_id)
  have h0U' : (0:ℂ) ∈ U' := by
    simp only [hU'def, Set.mem_ofPred_eq, add_zero]; exact hx1
  have h0V' : (0:ℂ) ∈ V' := by
    simp only [hV'def, Set.mem_ofPred_eq, add_zero]; exact hx2
  have hG' : (fun q : ℂ × ℂ => G q.1 q.2) = fun q => F (x.1 + q.1) (x.2 + q.2) := by
    funext q; simp only [hGdef]
  have hcont' : ContinuousOn (fun q : ℂ × ℂ => G q.1 q.2) (U' ×ˢ V') := by
    rw [hG']
    refine hcont.comp (f := fun q : ℂ × ℂ => (x.1 + q.1, x.2 + q.2)) ?_ ?_
    · exact (Continuous.prodMk (continuous_const.add continuous_fst)
        (continuous_const.add continuous_snd)).continuousOn
    · intro q hq; exact ⟨hq.1, hq.2⟩
  have hz' : ∀ s ∈ U', DifferentiableOn ℂ (G s) V' := by
    intro s hs
    have he : G s = fun t : ℂ => F (x.1 + s) (x.2 + t) := by funext t; simp only [hGdef]
    rw [he]
    exact (hz (x.1 + s) hs).comp
      ((differentiableOn_const (c := x.2)).add differentiableOn_id)
      (fun t ht => ht)
  have hw' : ∀ t ∈ V', DifferentiableOn ℂ (fun s => G s t) U' := by
    intro t ht
    have he : (fun s : ℂ => G s t) = fun s : ℂ => F (x.1 + s) (x.2 + t) := by
      funext s; simp only [hGdef]
    rw [he]
    exact (hw (x.2 + t) ht).comp
      ((differentiableOn_const (c := x.1)).add differentiableOn_id)
      (fun s hs => hs)
  have hloc := analyticAt_zero_aux hU'open hV'open h0U' h0V' hcont' hz' hw'
  have hf : AnalyticOnNhd ℂ (fun q : ℂ × ℂ => G q.1 q.2) ({0} : Set (ℂ × ℂ)) :=
    fun y hy => by rw [Set.mem_singleton_iff] at hy; rwa [hy]
  have h2 := (hf.comp_sub x) x (by
    simpa using Set.add_mem_add (Set.mem_singleton (0 : ℂ × ℂ)) (Set.mem_singleton x))
  have h3 : AnalyticAt ℂ (fun q : ℂ × ℂ => F q.1 q.2) x :=
    h2.congr (Filter.Eventually.of_forall fun z => by
      simp only [hGdef, Prod.fst_sub, Prod.snd_sub]
      congr 1 <;> ring)
  exact h3.restrictScalars

end Work.TMComp.MAnalytic
