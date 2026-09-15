import Mathlib.Analysis.Complex.LocallyUniformLimit
import Submission.Commons.Analysis.Complex.Montel.exists_subseq_tendstoLocallyUniformlyOn

noncomputable section
open Set Metric Filter Topology
open scoped Topology

namespace Commons.Analysis.Complex.Montel

theorem exists_subseq_tendstoLocallyUniformlyOn_ball {c : ℂ} {R : ℝ} (hR : 0 < R)
    {f : ℕ → ℂ → ℂ} (hf : ∀ n, ∀ z ∈ Metric.ball c R, AnalyticAt ℂ (f n) z)
    (hb : ∀ n z, z ∈ Metric.ball c R → ‖f n z‖ ≤ 1) :
    ∃ (φ : ℕ → ℕ) (g : ℂ → ℂ), StrictMono φ ∧
      TendstoLocallyUniformlyOn (fun n => f (φ n)) g Filter.atTop (Metric.ball c R) ∧
      AnalyticOnNhd ℂ g (Metric.ball c R) := by
  classical
  have hRne : R ≠ 0 := ne_of_gt hR
  have hRc : (R : ℂ) ≠ 0 := by exact_mod_cast hRne
  -- ## The affine change of variables sending `ball 0 1` onto `ball c R`
  have hscale : ∀ w : ℂ, c + (R : ℂ) * w ∈ Metric.ball c R ↔ w ∈ Metric.ball 0 1 := by
    intro w
    simp only [Metric.mem_ball, dist_eq_norm, sub_zero]
    have h1 : c + (R : ℂ) * w - c = (R : ℂ) * w := by ring
    rw [h1, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
    simpa using (mul_lt_mul_iff_right₀ hR : R * ‖w‖ < R * 1 ↔ ‖w‖ < 1)
  have hscale' : ∀ z : ℂ, (z - c) / (R : ℂ) ∈ Metric.ball 0 1 ↔ z ∈ Metric.ball c R := by
    intro z
    simp only [Metric.mem_ball, dist_eq_norm, sub_zero]
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR, div_lt_iff₀ hR]
    simp
  have hαβ : ∀ z : ℂ, c + (R : ℂ) * ((z - c) / (R : ℂ)) = z := by
    intro z
    rw [div_eq_inv_mul, ← mul_assoc, mul_inv_cancel₀ hRc, one_mul]
    ring
  -- ## The reparametrised family on the unit ball
  have hFan : ∀ n, AnalyticOnNhd ℂ (fun w : ℂ => f n (c + (R : ℂ) * w)) (Metric.ball 0 1) := by
    intro n w hw
    have hw' : c + (R : ℂ) * w ∈ Metric.ball c R := (hscale w).mpr hw
    have hα : AnalyticAt ℂ (fun w : ℂ => c + (R : ℂ) * w) w := by
      rw [Complex.analyticAt_iff_eventually_differentiableAt]
      filter_upwards with z
      have h1 : DifferentiableAt ℂ (fun z : ℂ => c + (R : ℂ) * z) z :=
        (differentiableAt_const c).add ((differentiableAt_const (R : ℂ)).mul differentiableAt_id)
      simpa using h1
    have hcomp : AnalyticAt ℂ ((f n) ∘ (fun y : ℂ => c + (R : ℂ) * y)) w :=
      AnalyticAt.comp (g := f n) (f := fun y : ℂ => c + (R : ℂ) * y) (x := w)
        (hf n (c + (R : ℂ) * w) hw') hα
    simpa [Function.comp_def] using hcomp
  have hFb : ∀ n, ∀ w ∈ Metric.ball 0 1, ‖f n (c + (R : ℂ) * w)‖ ≤ 1 := by
    intro n w hw
    exact hb n (c + (R : ℂ) * w) ((hscale w).mpr hw)
  -- ## Montel on the unit ball
  obtain ⟨g₀, φ, hφ, hconv₀⟩ := exists_subseq_tendstoLocallyUniformlyOn hFan hFb
  -- ## Push the convergence forward along `z ↦ (z - c) / R`
  have hβcont : ContinuousOn (fun z : ℂ => (z - c) / (R : ℂ)) (Metric.ball c R) := by
    have hcont : Continuous (fun z : ℂ => (z - c) / (R : ℂ)) :=
      (continuous_id.sub continuous_const).div_const (R : ℂ)
    exact hcont.continuousOn
  have hβmap : MapsTo (fun z : ℂ => (z - c) / (R : ℂ)) (Metric.ball c R) (Metric.ball 0 1) :=
    fun z hz => (hscale' z).mpr hz
  have hconv : TendstoLocallyUniformlyOn (fun n => f (φ n))
      (fun z : ℂ => g₀ ((z - c) / (R : ℂ))) Filter.atTop (Metric.ball c R) := by
    have hcomp := hconv₀.comp (fun z : ℂ => (z - c) / (R : ℂ)) hβmap hβcont
    refine hcomp.congr (fun n z hz => ?_)
    simp only [Function.comp_apply]
    rw [hαβ]
  -- ## The limit is analytic
  have hdiff : DifferentiableOn ℂ (fun z : ℂ => g₀ ((z - c) / (R : ℂ))) (Metric.ball c R) :=
    hconv.differentiableOn
      (Eventually.of_forall fun n => fun z hz =>
        ((hf (φ n) z hz).differentiableAt).differentiableWithinAt)
      Metric.isOpen_ball
  have hAnalytic : AnalyticOnNhd ℂ (fun z : ℂ => g₀ ((z - c) / (R : ℂ))) (Metric.ball c R) := by
    intro z hz
    rw [Complex.analyticAt_iff_eventually_differentiableAt]
    exact Filter.eventually_of_mem (Metric.isOpen_ball.mem_nhds hz) fun w hw =>
      (hdiff w hw).differentiableAt (Metric.isOpen_ball.mem_nhds hw)
  exact ⟨φ, fun z => g₀ ((z - c) / (R : ℂ)), hφ, hconv, hAnalytic⟩

end Commons.Analysis.Complex.Montel