import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Submission.Commons.NumberTheory.Linnik.tentF1_laplace
import Submission.Commons.NumberTheory.Linnik.tentF1_boundary
import Submission.Commons.NumberTheory.Linnik.tentF1_decay
import Submission.Commons.NumberTheory.Linnik.tentF2_decay
import Submission.Commons.Analysis.Complex.re_ge_norm_of_boundary

open Complex MeasureTheory Filter
open scoped Interval Topology

namespace Commons.NumberTheory.Linnik

/-- `Re(−w) ≤ ‖w‖` for complex `w`. -/
private lemma re_neg_le_norm (w : ℂ) : (-w).re ≤ ‖w‖ := by
  calc
    (-w).re ≤ ‖-w‖ := Complex.re_le_norm (-w)
    _ = ‖w‖ := by simp

/-- A point in the unit ball around `x₀` has norm at most `‖x₀‖ + 1`. -/
private lemma norm_le_of_mem_ball (x x₀ : ℂ) (h : x ∈ Metric.ball x₀ 1) : ‖x‖ ≤ ‖x₀‖ + 1 := by
  have hd : ‖x - x₀‖ < 1 := by simpa [dist_eq_norm] using h
  have htri : ‖x‖ ≤ ‖x₀‖ + ‖x - x₀‖ := by
    have h := norm_add_le x₀ (x - x₀)
    simpa [sub_eq_add_neg] using h
  linarith

/-- Derivative of `z ↦ e^{−zt}` (complex variable `z`, parameter `t`). -/
private lemma exp_neg_mul_deriv (x t : ℂ) :
    HasDerivAt (fun z : ℂ => Complex.exp (-(z * t))) (Complex.exp (-(x * t)) * (-t)) x := by
  have hinner : HasDerivAt (fun z : ℂ => (-t) * z) (-t) x := by
    simpa using (hasDerivAt_id x).const_mul (-t)
  have hCe : HasDerivAt (fun z : ℂ => Complex.exp ((-t) * z)) (Complex.exp ((-t) * x) * (-t)) x := by
    exact hinner.cexp
  convert hCe using 1
  · ext z
    congr 1
    ring_nf
  · congr 1
    ring_nf

/-- A Laplace-type integral `z ↦ ∫ g(u) e^{−zu}` over a finite interval is holomorphic
everywhere (for any continuous `g`). -/
private lemma hasDerivAt_laplace {a b : ℝ} {g : ℝ → ℂ} (hg : Continuous g) (x₀ : ℂ) :
    HasDerivAt (fun z : ℂ => ∫ u in a..b, Complex.exp (-(z * (u : ℂ))) * g u)
      (∫ u in a..b, Complex.exp (-(x₀ * (u : ℂ))) * (-(u : ℂ)) * g u) x₀ := by
  let F : ℂ → ℝ → ℂ := fun z u => Complex.exp (-(z * (u : ℂ))) * g u
  let F' : ℂ → ℝ → ℂ := fun z u => Complex.exp (-(z * (u : ℂ))) * (-(u : ℂ)) * g u
  let s : Set ℂ := Metric.ball x₀ 1
  let bound : ℝ → ℝ := fun u => Real.exp ((‖x₀‖ + 1) * ‖(u : ℂ)‖) * ‖(u : ℂ)‖ * ‖g u‖
  have hs : s ∈ 𝓝 x₀ := Metric.ball_mem_nhds x₀ (by norm_num)
  have hF_meas : ∀ᶠ x in 𝓝 x₀, AEStronglyMeasurable (F x) (volume.restrict (Ι a b)) := by
    refine Filter.Eventually.of_forall ?_
    intro x
    exact (by fun_prop : Continuous (fun u : ℝ => F x u)).aestronglyMeasurable
  have hF_int : IntervalIntegrable (F x₀) volume a b := by
    exact (by fun_prop : Continuous (fun u : ℝ => F x₀ u)).intervalIntegrable a b
  have hF'_meas : AEStronglyMeasurable (F' x₀) (volume.restrict (Ι a b)) := by
    exact (by fun_prop : Continuous (fun u : ℝ => F' x₀ u)).aestronglyMeasurable
  have h_bound : ∀ᵐ u ∂volume, u ∈ Ι a b → ∀ x ∈ s, ‖F' x u‖ ≤ bound u := by
    refine Filter.Eventually.of_forall ?_
    intro u hu x hx
    have hxnorm : ‖x‖ ≤ ‖x₀‖ + 1 := norm_le_of_mem_ball x x₀ (by simpa [s] using hx)
    have hre : (-(x * (u : ℂ))).re ≤ (‖x₀‖ + 1) * ‖(u : ℂ)‖ := by
      calc
        (-(x * (u : ℂ))).re ≤ ‖x * (u : ℂ)‖ := re_neg_le_norm (x * (u : ℂ))
        _ = ‖x‖ * ‖(u : ℂ)‖ := norm_mul x (u : ℂ)
        _ ≤ (‖x₀‖ + 1) * ‖(u : ℂ)‖ := by
          exact mul_le_mul_of_nonneg_right hxnorm (norm_nonneg (u : ℂ))
    have hexp : Real.exp (-(x * (u : ℂ))).re ≤ Real.exp ((‖x₀‖ + 1) * ‖(u : ℂ)‖) :=
      Real.exp_le_exp.mpr hre
    dsimp [F', bound]
    calc
      ‖Complex.exp (-(x * (u : ℂ))) * (-(u : ℂ)) * g u‖
          = Real.exp (-(x * (u : ℂ))).re * ‖(u : ℂ)‖ * ‖g u‖ := by
            simp [Complex.norm_exp]
      _ ≤ Real.exp ((‖x₀‖ + 1) * ‖(u : ℂ)‖) * ‖(u : ℂ)‖ * ‖g u‖ := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hexp (norm_nonneg (u : ℂ))) (norm_nonneg (g u))
  have bound_cont : Continuous bound := by
    dsimp [bound]
    fun_prop
  have bound_integrable : IntervalIntegrable bound volume a b := by
    exact bound_cont.intervalIntegrable a b
  have h_diff : ∀ᵐ u ∂volume, u ∈ Ι a b → ∀ x ∈ s, HasDerivAt (fun z : ℂ => F z u) (F' x u) x := by
    refine Filter.Eventually.of_forall ?_
    intro u hu x hx
    dsimp [F, F']
    exact (exp_neg_mul_deriv x (u : ℂ)).mul_const (g u)
  have hmain := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (𝕜 := ℂ) (μ := volume) (E := ℂ) (a := a) (b := b) (F := F) (F' := F') (x₀ := x₀)
    (s := s) (bound := bound) hs hF_meas hF_int hF'_meas h_bound bound_integrable h_diff
  simpa [F, F'] using hmain.2

/-- `‖(c : ℂ)‖ = c` for `0 ≤ c`. -/
private lemma norm_ofReal_nonneg {c : ℝ} (hc : 0 ≤ c) : ‖(c : ℂ)‖ = c := by
  rw [Complex.norm_real]
  rw [Real.norm_eq_abs]
  exact abs_of_nonneg hc

/-- `‖w ^ 2‖ = ‖w‖ ^ 2` for complex `w`. -/
private lemma norm_sq_of_complex (w : ℂ) : ‖w ^ 2‖ = ‖w‖ ^ 2 := by
  rw [norm_pow]

/-- `‖(c : ℂ) * w ^ 2‖ = c * ‖w ^ 2‖` for real `c ≥ 0`. -/
private lemma norm_mul_pow_two {c : ℝ} (hc : 0 ≤ c) (w : ℂ) : ‖(c : ℂ) * w ^ 2‖ = c * ‖w ^ 2‖ := by
  rw [norm_mul, norm_ofReal_nonneg hc]

theorem tentF1_re_ge {K : ℝ} (hK : 0 < K) (x : ℝ) (hx : 0 < x) (z : ℂ) (hz : 0 ≤ z.re) :
    (x / 2) * Real.exp (x * K) *
        ‖(((1 - Complex.exp (-((K : ℂ) * ((x : ℂ) + z)))) / ((x : ℂ) + z)) ^ 2)‖ ≤
      (∫ u in (0 : ℝ)..(K : ℝ),
          Complex.exp (-(z * (u : ℂ))) * ((Real.sinh ((K - u) * x) : ℝ) : ℂ)).re := by
  let L : ℂ → ℂ := fun w => ∫ u in (0 : ℝ)..(K : ℝ),
      Complex.exp (-(w * (u : ℂ))) * ((Real.sinh ((K - u) * x) : ℝ) : ℂ)
  let c : ℝ := (x / 2) * Real.exp (x * K)
  let F2 : ℂ → ℂ := fun w =>
      (c : ℂ) * (((1 - Complex.exp (-((K : ℂ) * ((x : ℂ) + w)))) / ((x : ℂ) + w)) ^ 2)
  have hcpos : 0 < c := by
    dsimp [c]
    exact mul_pos (div_pos hx (by norm_num)) (Real.exp_pos (x * K))
  have hcnn : 0 ≤ c := le_of_lt hcpos
  have hg : Continuous (fun u : ℝ => ((Real.sinh ((K - u) * x) : ℝ) : ℂ)) := by fun_prop
  have hderiv (w : ℂ) :
      HasDerivAt (fun v : ℂ => ∫ u in (0 : ℝ)..(K : ℝ),
          Complex.exp (-(v * (u : ℂ))) * ((Real.sinh ((K - u) * x) : ℝ) : ℂ))
        (∫ u in (0 : ℝ)..(K : ℝ),
          Complex.exp (-(w * (u : ℂ))) * (-(u : ℂ)) * ((Real.sinh ((K - u) * x) : ℝ) : ℂ)) w := by
    exact hasDerivAt_laplace (a := 0) (b := K) hg w
  have hdL : DifferentiableOn ℂ L {z : ℂ | 0 < z.re} := by
    intro w hw
    dsimp [L]
    exact (hderiv w).differentiableAt.differentiableWithinAt
  have hcL : ContinuousOn L {z : ℂ | 0 ≤ z.re} := by
    intro w hw
    dsimp [L]
    exact (hderiv w).continuousAt.continuousWithinAt
  have hden_ne (w : ℂ) (hw : 0 ≤ w.re) : (x : ℂ) + w ≠ 0 := by
    intro hz0
    have hrew : ((x : ℂ) + w).re = 0 := by rw [hz0]; simp
    have hrew' : ((x : ℂ) + w).re = x + w.re := by simp
    rw [hrew'] at hrew
    nlinarith
  have hdF2 : DifferentiableOn ℂ F2 {z : ℂ | 0 < z.re} := by
    intro w hw
    have hwne : (x : ℂ) + w ≠ 0 := hden_ne w (le_of_lt hw)
    dsimp [F2]
    fun_prop
  have hcF2 : ContinuousOn F2 {z : ℂ | 0 ≤ z.re} := by
    intro w hw
    have hwne : (x : ℂ) + w ≠ 0 := hden_ne w hw
    dsimp [F2]
    fun_prop
  have hbounded_axis : ∀ t : ℝ, 0 ≤ (L (Complex.I * (t : ℂ))).re - ‖F2 (Complex.I * (t : ℂ))‖ := by
    intro t
    have hLeq : (L (Complex.I * (t : ℂ))).re =
        (x / 2) * Real.exp (x * K) *
          ‖((1 - Complex.exp (-((K : ℂ) * ((x : ℂ) + Complex.I * (t : ℂ))))) /
              ((x : ℂ) + Complex.I * (t : ℂ)))‖ ^ 2 := by
      dsimp [L]
      exact tentF1_boundary hK x hx t
    have hF2eq : ‖F2 (Complex.I * (t : ℂ))‖ =
        (x / 2) * Real.exp (x * K) *
          ‖((1 - Complex.exp (-((K : ℂ) * ((x : ℂ) + Complex.I * (t : ℂ))))) /
              ((x : ℂ) + Complex.I * (t : ℂ)))‖ ^ 2 := by
      dsimp [F2, c]
      rw [norm_mul_pow_two hcnn]
      rw [norm_sq_of_complex]
    linarith
  have hdec : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ w : ℂ, 0 ≤ w.re → R ≤ ‖w‖ →
      ‖L w‖ < ε ∧ ‖F2 w‖ < ε := by
    intro ε hε
    rcases tentF1_decay hK x hx ε hε with ⟨R1, hR1⟩
    have hεc : 0 < ε / c := div_pos hε hcpos
    rcases tentF2_decay hK hx (ε / c) hεc with ⟨R2, hR2⟩
    refine ⟨max R1 R2, ?_⟩
    intro w hw hRw
    have hw1 : R1 ≤ ‖w‖ := le_trans (le_max_left R1 R2) hRw
    have hw2 : R2 ≤ ‖w‖ := le_trans (le_max_right R1 R2) hRw
    have hLw : ‖L w‖ < ε := hR1 w hw hw1
    have hF2w : ‖F2 w‖ < ε := by
      have hG2 : ‖(((1 - Complex.exp (-((K : ℂ) * ((x : ℂ) + w)))) / ((x : ℂ) + w)) ^ 2)‖ < ε / c :=
        hR2 w hw hw2
      have hnorm : ‖F2 w‖ = c * ‖(((1 - Complex.exp (-((K : ℂ) * ((x : ℂ) + w)))) / ((x : ℂ) + w)) ^ 2)‖ := by
        dsimp [F2]
        exact norm_mul_pow_two hcnn (((1 - Complex.exp (-((K : ℂ) * ((x : ℂ) + w)))) / ((x : ℂ) + w)))
      rw [hnorm]
      exact (mul_lt_mul_of_pos_left hG2 hcpos).trans_eq (by
        field_simp [ne_of_gt hcpos])
    exact ⟨hLw, hF2w⟩
  have hmain := Commons.Analysis.Complex.re_ge_norm_of_boundary (F1 := L) (F2 := F2)
    hdL hdF2 hcL hcF2 hbounded_axis hdec z hz
  have hF2norm : ‖F2 z‖ =
      (x / 2) * Real.exp (x * K) *
        ‖(((1 - Complex.exp (-((K : ℂ) * ((x : ℂ) + z)))) / ((x : ℂ) + z)) ^ 2)‖ := by
    dsimp [F2, c]
    rw [norm_mul_pow_two hcnn]
  have hLz : (L z).re =
      (∫ u in (0 : ℝ)..(K : ℝ),
          Complex.exp (-(z * (u : ℂ))) * ((Real.sinh ((K - u) * x) : ℝ) : ℂ)).re := by
    rfl
  rwa [hF2norm, hLz] at hmain

end Commons.NumberTheory.Linnik