import Mathlib
import Submission.Work.CPull.defs
import Submission.Work.CPull.exists_poly_mul_holo_div
import Submission.Work.CPull.exists_summable_majorant
import Submission.Work.CPull.hasSum_deriv_series_of_majorant

open Filter Metric
open scoped Topology

namespace Work.CPull

/-! ## Auxiliary facts -/

/-- Coefficients of the formal derivative, cast to `ℂ`. -/
lemma coeff_derivative_cast (f : PowerSeries ℚ) (n : ℕ) :
    ((PowerSeries.coeff n ((PowerSeries.derivative (R := ℚ)) f) : ℚ) : ℂ)
      = ((PowerSeries.coeff (n + 1) f : ℚ) : ℂ) * ((n : ℂ) + 1) := by
  rw [PowerSeries.coeff_derivative]
  push_cast
  ring

/-! ## The derivative step -/

theorem pullbackMero_deriv_step {f : PowerSeries ℚ} {Ψ : ℂ → ℂ} (S : Finset ℂ)
    (hΨ : DifferentiableOn ℂ Ψ (Metric.ball 0 1)) (hΨ'0 : deriv Ψ 0 ≠ 0)
    (hS : ∀ z ∈ Metric.ball (0:ℂ) 1, deriv Ψ z = 0 → z ∈ S)
    (h : Submission.CDTPlan.PullbackMero f Ψ) :
    Submission.CDTPlan.PullbackMero ((PowerSeries.derivative (R := ℚ)) f) Ψ := by
  classical
  obtain ⟨P, N, hP0, hNd, hgerm⟩ := h
  obtain ⟨W, u, hW0, hud, huW⟩ :=
    exists_poly_mul_holo_div S (hΨ.deriv Metric.isOpen_ball) hΨ'0 hS
  set F : ℂ → ℂ := fun z => N z / P.eval z with hFdef
  set A : ℂ → ℂ := fun z => deriv N z * P.eval z - N z * P.derivative.eval z with hAdef
  set Ñ : ℂ → ℂ := u * A with hÑdef
  refine ⟨P ^ 2 * W, Ñ, ?_, ?_, ?_⟩
  · simp only [Polynomial.eval_mul, Polynomial.eval_pow]
    exact mul_ne_zero (pow_ne_zero 2 hP0) hW0
  · have hN' : DifferentiableOn ℂ (deriv N) (Metric.ball 0 1) := hNd.deriv Metric.isOpen_ball
    have hp : DifferentiableOn ℂ (fun z : ℂ => P.eval z) (Metric.ball 0 1) := by fun_prop
    have hp' : DifferentiableOn ℂ (fun z : ℂ => P.derivative.eval z) (Metric.ball 0 1) := by
      fun_prop
    have h1 : DifferentiableOn ℂ (fun z => deriv N z * P.eval z) (Metric.ball 0 1) := hN'.mul hp
    have h2 : DifferentiableOn ℂ (fun z => N z * P.derivative.eval z) (Metric.ball 0 1) :=
      hNd.mul hp'
    have hAd : DifferentiableOn ℂ A (Metric.ball 0 1) := by
      rw [hAdef]
      exact h1.sub h2
    simpa only [hÑdef] using hud.mul hAd
  · obtain ⟨δ₀, hδ₀pos, hδ₀⟩ := Metric.eventually_nhds_iff.mp hgerm
    set U : Set ℂ := Metric.ball 0 (min δ₀ 1) ∩ {z : ℂ | P.eval z ≠ 0} with hUdef
    have hUmem : ∀ z ∈ U, z ∈ Metric.ball (0:ℂ) (min δ₀ 1) := by
      intro z hz; rw [hUdef] at hz; exact hz.1
    have hUP : ∀ z ∈ U, P.eval z ≠ 0 := by
      intro z hz; rw [hUdef] at hz; exact hz.2
    have hUsub : U ⊆ Metric.ball (0:ℂ) 1 := fun z hz =>
      Metric.ball_subset_ball (min_le_right _ _) (hUmem z hz)
    have hPne_open : IsOpen {z : ℂ | P.eval z ≠ 0} :=
      isOpen_ne.preimage (by fun_prop : Continuous fun z : ℂ => P.eval z)
    have hUopen : IsOpen U := by rw [hUdef]; exact Metric.isOpen_ball.inter hPne_open
    have hU0 : U ∈ nhds (0 : ℂ) := by
      rw [hUdef]
      exact inter_mem (Metric.ball_mem_nhds 0 (lt_min hδ₀pos one_pos)) (hPne_open.mem_nhds hP0)
    have hgermU : ∀ z ∈ U, HasSum (fun n : ℕ => ((PowerSeries.coeff n f : ℚ) : ℂ) * Ψ z ^ n)
        (N z / P.eval z) := by
      intro z hz
      have hz' : dist z 0 < δ₀ := by
        have h1 := Metric.ball_subset_ball (min_le_left _ _) (hUmem z hz)
        rw [Metric.mem_ball, dist_zero_right] at h1
        rwa [dist_zero_right]
      simpa using hδ₀ hz'
    have hFd : DifferentiableOn ℂ F U := by
      rw [hFdef]
      exact (hNd.mono hUsub).div (by fun_prop) (fun z hz => hUP z hz)
    -- the majorant
    obtain ⟨s, hs_gt, hsum⟩ :=
      exists_summable_majorant hUopen hU0 hΨ hΨ'0 (fun z hz => (hgermU z hz).summable)
    obtain ⟨ε₁, hε₁pos, hε₁⟩ := Metric.mem_nhds_iff.mp hU0
    have hΨc : ContinuousAt Ψ 0 :=
      (hΨ.differentiableAt (Metric.ball_mem_nhds 0 one_pos)).continuousAt
    have hs0 : 0 < s - ‖Ψ 0‖ := sub_pos.mpr hs_gt
    obtain ⟨ε₂, hε₂pos, hε₂⟩ := Metric.continuousAt_iff.mp hΨc (s - ‖Ψ 0‖) hs0
    have hcont' : ContinuousAt (deriv Ψ) 0 :=
      ((hΨ.deriv Metric.isOpen_ball).differentiableAt
        (Metric.ball_mem_nhds 0 one_pos)).continuousAt
    obtain ⟨ε₃, hε₃pos, hε₃⟩ :=
      Metric.eventually_nhds_iff.mp (hcont'.eventually_ne hΨ'0)
    set δ : ℝ := min (min ε₁ ε₂) (min ε₃ 1) with hδdef
    have hδpos : 0 < δ := lt_min (lt_min hε₁pos hε₂pos) (lt_min hε₃pos one_pos)
    have hδ1 : δ ≤ 1 := (min_le_right _ _).trans (min_le_right _ _)
    have hδε₁ : δ ≤ ε₁ := (min_le_left _ _).trans (min_le_left _ _)
    have hδε₂ : δ ≤ ε₂ := (min_le_left _ _).trans (min_le_right _ _)
    have hδε₃ : δ ≤ ε₃ := (min_le_right _ _).trans (min_le_left _ _)
    have hδU : ∀ z : ℂ, ‖z‖ < δ → z ∈ U := by
      intro z hz
      exact hε₁ (by rw [Metric.mem_ball, dist_zero_right]; exact lt_of_lt_of_le hz hδε₁)
    have hδΨb : ∀ z : ℂ, ‖z‖ < δ → ‖Ψ z‖ < s := by
      intro z hz
      have h1 : dist z (0:ℂ) < ε₂ := by
        rw [dist_zero_right]; exact lt_of_lt_of_le hz hδε₂
      have h2 := hε₂ h1
      rw [dist_eq_norm] at h2
      have h3 : ‖Ψ z‖ ≤ ‖Ψ z - Ψ 0‖ + ‖Ψ 0‖ := by
        have := norm_add_le (Ψ z - Ψ 0) (Ψ 0)
        simpa using this
      linarith
    have hδΨ'ne : ∀ z : ℂ, ‖z‖ < δ → deriv Ψ z ≠ 0 := by
      intro z hz
      exact hε₃ (by rw [dist_zero_right]; exact lt_of_lt_of_le hz hδε₃)
    have hderiv := hasSum_deriv_series_of_majorant hδpos (lt_of_le_of_lt (norm_nonneg _) hs_gt) hδ1
      hUopen hδU hΨ hδΨb hδΨ'ne hsum hFd hgermU
    -- the eventual statement
    have hWop : IsOpen {z : ℂ | W.eval z ≠ 0} :=
      isOpen_ne.preimage (by fun_prop : Continuous fun z : ℂ => W.eval z)
    filter_upwards [Metric.ball_mem_nhds 0 hδpos, hWop.mem_nhds hW0, hU0] with z hzd hzW hzU
    rw [Metric.mem_ball, dist_zero_right] at hzd
    have hz1 : z ∈ Metric.ball (0:ℂ) 1 := hUsub hzU
    have hzuW : u z * deriv Ψ z = W.eval z := huW z hz1
    have hPz : P.eval z ≠ 0 := hUP z hzU
    have hΨ'z : deriv Ψ z ≠ 0 := hδΨ'ne z hzd
    have hHS := hderiv z hzd
    -- the value identity
    have hdF : deriv F z
        = (deriv N z * P.eval z - N z * P.derivative.eval z) / P.eval z ^ 2 := by
      rw [hFdef]
      rw [show (fun z : ℂ => N z / P.eval z) = N / (fun x : ℂ => P.eval x) from rfl]
      rw [deriv_div (hNd.differentiableAt (Metric.isOpen_ball.mem_nhds hz1))
        ((Polynomial.differentiable P).differentiableAt) hPz]
      simp
    have huz : u z = W.eval z / deriv Ψ z := by
      rw [eq_div_iff hΨ'z]
      exact hzuW
    have hAeq : deriv N z * P.eval z - N z * P.derivative.eval z
        = deriv F z * P.eval z ^ 2 := by
      rw [hdF]
      field_simp
    have hval : Ñ z / (P ^ 2 * W).eval z = deriv F z / deriv Ψ z := by
      simp only [hÑdef, hAdef, Pi.mul_apply, Polynomial.eval_mul, Polynomial.eval_pow]
      rw [hAeq, huz]
      field_simp
    have hsummand : (fun n : ℕ =>
          ((PowerSeries.coeff n ((PowerSeries.derivative (R := ℚ)) f) : ℚ) : ℂ) * Ψ z ^ n)
        = fun n : ℕ => (n + 1 : ℂ) * ((PowerSeries.coeff (n + 1) f : ℚ) : ℂ) * Ψ z ^ n := by
      funext n
      rw [coeff_derivative_cast]
      ring
    rw [hsummand, hval]
    exact hHS

/-! ## The iterated statement -/

theorem pullbackMero_deriv_iter {f : PowerSeries ℚ} {Ψ N : ℂ → ℂ} (S : Finset ℂ) (k : ℕ)
    (hΨ : DifferentiableOn ℂ Ψ (Metric.ball 0 1)) (hΨ'0 : deriv Ψ 0 ≠ 0)
    (hS : ∀ z ∈ Metric.ball (0:ℂ) 1, deriv Ψ z = 0 → z ∈ S)
    (hN : DifferentiableOn ℂ N (Metric.ball 0 1))
    (hgerm : ∀ᶠ z in nhds (0:ℂ),
      HasSum (fun n : ℕ => ((PowerSeries.coeff n f : ℚ) : ℂ) * Ψ z ^ n) (N z)) :
    Submission.CDTPlan.PullbackMero ((PowerSeries.derivative (R := ℚ))^[k] f) Ψ := by
  have h0 : Submission.CDTPlan.PullbackMero f Ψ := by
    refine ⟨1, N, by simp, hN, ?_⟩
    filter_upwards [hgerm] with z hz
    simpa using hz
  have hstep : ∀ g : PowerSeries ℚ, Submission.CDTPlan.PullbackMero g Ψ →
      Submission.CDTPlan.PullbackMero ((PowerSeries.derivative (R := ℚ)) g) Ψ :=
    fun g hg => pullbackMero_deriv_step S hΨ hΨ'0 hS hg
  induction k with
  | zero => simpa using h0
  | succ k ih =>
    simpa [Function.iterate_succ_apply'] using hstep _ ih

end Work.CPull

/-!
# Area CPull — the pullback of the formal derivative is meromorphic

`Submission.CDTPlan.PullbackMero f Ψ` says that the germ at `0` of `z ↦ Σₙ (coeffₙ f) Ψ(z)ⁿ`
extends to a function of the form `N / P` on the unit disc, with `P` a polynomial with
`P.eval 0 ≠ 0` and `N` holomorphic.  Here we show that this property survives formal
differentiation (`Work.CPull.pullbackMero_deriv_step`), hence holds for all iterates
(`Work.CPull.pullbackMero_deriv_iter`).

The mathematics of the step: write `F = N / P` for the meromorphic function agreeing near `0` with
the pullback of `f`.  Then, near `0`,

* `deriv F z = deriv Ψ z · Σₙ (n+1) aₙ₊₁ Ψ(z)ⁿ` — term-by-term differentiation of the pullback
  series (this is the content of `Work.CPull.hasSum_deriv_series_of_majorant`, with the dominating
  radius supplied by `Work.CPull.exists_summable_majorant`);
* hence the germ of the pullback of the formal derivative `(PowerSeries.derivative (R := ℚ)) f` is
  `(deriv F) / (deriv Ψ) = A/(P²·deriv Ψ)` with `A = (deriv N)·P − N·(P.derivative)`;
* finally `Work.CPull.exists_poly_mul_holo_div` clears the zeros of `deriv Ψ` by a polynomial `W`
  (with `u·deriv Ψ = W` holomorphic `u`), giving the meromorphic presentation
  `A/(P²·deriv Ψ) = (u·A)/(P²·W)`.
-/
