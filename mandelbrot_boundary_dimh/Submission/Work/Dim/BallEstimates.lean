import Mathlib
import Submission.Unif.Commons.Analysis.Complex.Landau.landau_theorem
import Submission.Unif.Commons.Analysis.Complex.Koebe.weak_koebe_of_landau
import Submission.Unif.Commons.Analysis.Complex.Analytic.deriv_ne_zero_of_injOn

/-!
# Koebe-type estimates for univalent functions on a disc (area DIM)

Self-contained version of the three analytic estimates used by the conformal-IFS dimension
argument, with universal constants:

* `koebeCoverDisc`: Koebe's one-quarter covering theorem on the unit disc, derived from Landau's
  theorem and the weak Koebe inequality (`Submission.Unif`);
* `ballBounds'`: the rescaled consequences on a general disc `ball p ρ` — covering, lower
  derivative bound and mean-value (Lipschitz) bound.
-/

open Complex Metric Set
open scoped Topology

noncomputable section

namespace Work.Dim

/-- **Koebe covering on the disc.** There is `c > 0` such that every univalent normalised `f` on
the unit disc has `closedBall 0 c ⊆ f '' ball 0 1`. -/
theorem koebeCoverDisc : ∃ c : ℝ, 0 < c ∧ ∀ f : ℂ → ℂ,
    (∀ z ∈ ball (0 : ℂ) 1, AnalyticAt ℂ f z) → InjOn f (ball (0 : ℂ) 1) → f 0 = 0 →
    deriv f 0 = 1 → closedBall 0 c ⊆ f '' ball (0 : ℂ) 1 := by
  obtain ⟨c₀, hc₀, hlandau⟩ := Commons.Analysis.Complex.Landau.landau_theorem
  refine ⟨c₀ / (2 * Real.pi), by positivity, ?_⟩
  intro f hf hinj h0 h1 w hw
  have hwk := Commons.Analysis.Complex.Koebe.weak_koebe_of_landau hc₀ hlandau f hf hinj h0 h1
  rw [mem_closedBall, dist_eq_norm, sub_zero] at hw
  by_contra h
  have h2 : c₀ / Real.pi ≤ ‖w‖ := hwk w h
  have h4 : c₀ / (2 * Real.pi) < c₀ / Real.pi := by
    rw [div_lt_div_iff₀ (by positivity : (0:ℝ) < 2 * Real.pi) Real.pi_pos]
    nlinarith [hc₀, Real.pi_pos]
  linarith

/-- **Koebe-type estimates with universal constants.** Given two-sided derivative bounds for
normalised univalent functions on the unit disc, we obtain the covering, lower derivative and
mean-value estimates for univalent functions on an arbitrary disc `ball p ρ`. -/
theorem ballBounds' (Cup Clow : ℝ) (hCup : 0 < Cup) (hClow : 0 < Clow)
    (hdisc : ∀ f : ℂ → ℂ, (∀ z ∈ ball (0 : ℂ) 1, AnalyticAt ℂ f z) →
      InjOn f (ball (0 : ℂ) 1) → f 0 = 0 → deriv f 0 = 1 →
      ∀ z : ℂ, ‖z‖ ≤ 1 / 2 → Clow ≤ ‖deriv f z‖ ∧ ‖deriv f z‖ ≤ Cup) :
    ∃ Ci Cg Cd : ℝ, 0 < Ci ∧ 0 < Cg ∧ 0 < Cd ∧
      (∀ (g : ℂ → ℂ) (p : ℂ) (ρ : ℝ), 0 < ρ → (∀ z ∈ ball p ρ, AnalyticAt ℂ g z) →
        InjOn g (ball p ρ) → closedBall (g p) (Ci * ‖deriv g p‖ * ρ) ⊆ g '' ball p ρ) ∧
      (∀ (g : ℂ → ℂ) (p : ℂ) (ρ : ℝ), 0 < ρ → (∀ z ∈ ball p ρ, AnalyticAt ℂ g z) →
        InjOn g (ball p ρ) →
        ∀ z ∈ closedBall p (ρ / 2), ‖deriv g p‖ ≤ Cd * ‖deriv g z‖) ∧
      (∀ (g : ℂ → ℂ) (p : ℂ) (ρ : ℝ), 0 < ρ → (∀ z ∈ ball p ρ, AnalyticAt ℂ g z) →
        InjOn g (ball p ρ) →
        ∀ z ∈ closedBall p (ρ / 2), ‖g z - g p‖ ≤ Cg * ‖deriv g p‖ * ‖z - p‖) := by
  obtain ⟨c, hc, hcov⟩ := koebeCoverDisc
  refine ⟨c, Cup, 1 / Clow, hc, hCup, one_div_pos.mpr hClow, ?_, ?_, ?_⟩
  · -- covering
    intro g p ρ hρ hg hinj
    have hpmem : p ∈ ball p ρ := mem_ball_self hρ
    have hd : deriv g p ≠ 0 :=
      Commons.Analysis.Complex.Analytic.deriv_ne_zero_of_injOn hρ (hg p hpmem) hinj
    have hρc : ((ρ : ℂ)) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hρ)
    have hdne : ((ρ : ℂ) * deriv g p) ≠ 0 := mul_ne_zero hρc hd
    set F : ℂ → ℂ := fun u => (g (p + (ρ : ℂ) * u) - g p) / ((ρ : ℂ) * deriv g p) with hFdef
    have hmem : ∀ u : ℂ, u ∈ ball (0 : ℂ) 1 → p + (ρ : ℂ) * u ∈ ball p ρ := by
      intro u hu
      have hu' : ‖u‖ < 1 := by simpa [mem_ball, dist_eq_norm] using hu
      have hn : ‖(ρ : ℂ) * u‖ = ρ * ‖u‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ]
      rw [mem_ball, dist_eq_norm, show p + (ρ : ℂ) * u - p = (ρ : ℂ) * u by ring, hn]
      nlinarith
    have hFan : ∀ u ∈ ball (0 : ℂ) 1, AnalyticAt ℂ F u := by
      intro u hu
      have hφ : AnalyticAt ℂ (fun v : ℂ => p + (ρ : ℂ) * v) u :=
        AnalyticAt.add analyticAt_const (AnalyticAt.mul analyticAt_const analyticAt_id)
      have h1 : AnalyticAt ℂ (fun v : ℂ => g (p + (ρ : ℂ) * v)) u :=
        AnalyticAt.comp (hg (p + (ρ : ℂ) * u) (hmem u hu)) hφ
      simpa only [hFdef, Pi.sub_apply] using (h1.sub analyticAt_const).div_const
    have hFinj : InjOn F (ball (0 : ℂ) 1) := by
      intro u hu v hv huv
      rw [hFdef] at huv
      have huv1 : g (p + (ρ : ℂ) * u) - g p = g (p + (ρ : ℂ) * v) - g p :=
        (div_left_inj' hdne).mp huv
      have huv2 : g (p + (ρ : ℂ) * u) = g (p + (ρ : ℂ) * v) := by
        have hh := congrArg (fun z => z + g p) huv1
        simpa using hh
      have huv3 : p + (ρ : ℂ) * u = p + (ρ : ℂ) * v := hinj (hmem u hu) (hmem v hv) huv2
      exact mul_left_cancel₀ hρc (add_left_cancel huv3)
    have hF0 : F 0 = 0 := by simp [hFdef]
    have hF1 : deriv F 0 = 1 := by
      have hφ : HasDerivAt (fun v : ℂ => p + (ρ : ℂ) * v) (ρ : ℂ) (0 : ℂ) := by
        simpa using ((hasDerivAt_id (0 : ℂ)).const_mul (ρ : ℂ)).const_add p
      have hg0 : HasDerivAt g (deriv g p) (p + (ρ : ℂ) * 0) := by
        simpa using (hg p hpmem).differentiableAt.hasDerivAt
      have hcomp : HasDerivAt (fun v : ℂ => g (p + (ρ : ℂ) * v)) (deriv g p * (ρ : ℂ)) 0 := by
        simpa only [Function.comp_def] using hg0.comp 0 hφ
      have hFd : HasDerivAt F ((deriv g p * (ρ : ℂ)) / ((ρ : ℂ) * deriv g p)) 0 := by
        simpa only [hFdef, Function.comp_def] using
          (hcomp.sub_const (g p)).div_const ((ρ : ℂ) * deriv g p)
      rw [hFd.deriv, mul_comm (deriv g p) ((ρ : ℂ)), div_self hdne]
    have hcov' := hcov F hFan hFinj hF0 hF1
    intro w hw
    rw [mem_closedBall, dist_eq_norm] at hw
    have hmemw : (w - g p) / ((ρ : ℂ) * deriv g p) ∈ closedBall 0 c := by
      rw [mem_closedBall, dist_eq_norm, sub_zero, norm_div, norm_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hρ]
      rw [div_le_iff₀ (by positivity : (0:ℝ) < ρ * ‖deriv g p‖)]
      have h3 : c * ‖deriv g p‖ * ρ = c * (ρ * ‖deriv g p‖) := by ring
      linarith [hw]
    obtain ⟨u, hu, huw⟩ := hcov' hmemw
    refine ⟨p + (ρ : ℂ) * u, ?_, ?_⟩
    · rw [mem_ball, dist_eq_norm, show p + (ρ : ℂ) * u - p = (ρ : ℂ) * u by ring,
        norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ]
      have hu' : ‖u‖ < 1 := by simpa [mem_ball, dist_eq_norm] using hu
      nlinarith
    · simp only [hFdef] at huw
      have h1 : g (p + (ρ : ℂ) * u) - g p = w - g p := by
        have h2 := congrArg (fun z => z * ((ρ : ℂ) * deriv g p)) huw
        simpa only [div_mul_cancel₀ _ hdne] using h2
      have h1' := congrArg (fun z => z + g p) h1
      simpa using h1'
  · -- lower derivative bound
    intro g p ρ hρ hg hinj z hz
    have hpmem : p ∈ ball p ρ := mem_ball_self hρ
    have hd : deriv g p ≠ 0 :=
      Commons.Analysis.Complex.Analytic.deriv_ne_zero_of_injOn hρ (hg p hpmem) hinj
    have hρc : ((ρ : ℂ)) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hρ)
    set F : ℂ → ℂ := fun u => (g (p + (ρ : ℂ) * u) - g p) / ((ρ : ℂ) * deriv g p) with hFdef
    have hmem : ∀ u : ℂ, u ∈ ball (0 : ℂ) 1 → p + (ρ : ℂ) * u ∈ ball p ρ := by
      intro u hu
      have hu' : ‖u‖ < 1 := by simpa [mem_ball, dist_eq_norm] using hu
      have hn : ‖(ρ : ℂ) * u‖ = ρ * ‖u‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ]
      rw [mem_ball, dist_eq_norm, show p + (ρ : ℂ) * u - p = (ρ : ℂ) * u by ring, hn]
      nlinarith
    have hFan : ∀ u ∈ ball (0 : ℂ) 1, AnalyticAt ℂ F u := by
      intro u hu
      have hφ : AnalyticAt ℂ (fun v : ℂ => p + (ρ : ℂ) * v) u :=
        AnalyticAt.add analyticAt_const (AnalyticAt.mul analyticAt_const analyticAt_id)
      have h1 : AnalyticAt ℂ (fun v : ℂ => g (p + (ρ : ℂ) * v)) u :=
        AnalyticAt.comp (hg (p + (ρ : ℂ) * u) (hmem u hu)) hφ
      simpa only [hFdef, Pi.sub_apply] using (h1.sub analyticAt_const).div_const
    have hFinj : InjOn F (ball (0 : ℂ) 1) := by
      intro u hu v hv huv
      rw [hFdef] at huv
      have huv1 : g (p + (ρ : ℂ) * u) - g p = g (p + (ρ : ℂ) * v) - g p :=
        (div_left_inj' (mul_ne_zero hρc hd)).mp huv
      have huv2 : g (p + (ρ : ℂ) * u) = g (p + (ρ : ℂ) * v) := by
        have hh := congrArg (fun z => z + g p) huv1
        simpa using hh
      have huv3 : p + (ρ : ℂ) * u = p + (ρ : ℂ) * v := hinj (hmem u hu) (hmem v hv) huv2
      exact mul_left_cancel₀ hρc (add_left_cancel huv3)
    have hF0 : F 0 = 0 := by simp [hFdef]
    have hF1 : deriv F 0 = 1 := by
      have hφ : HasDerivAt (fun v : ℂ => p + (ρ : ℂ) * v) (ρ : ℂ) (0 : ℂ) := by
        simpa using ((hasDerivAt_id (0 : ℂ)).const_mul (ρ : ℂ)).const_add p
      have hg0 : HasDerivAt g (deriv g p) (p + (ρ : ℂ) * 0) := by
        simpa using (hg p hpmem).differentiableAt.hasDerivAt
      have hcomp : HasDerivAt (fun v : ℂ => g (p + (ρ : ℂ) * v)) (deriv g p * (ρ : ℂ)) 0 := by
        simpa only [Function.comp_def] using hg0.comp 0 hφ
      have hFd : HasDerivAt F ((deriv g p * (ρ : ℂ)) / ((ρ : ℂ) * deriv g p)) 0 := by
        simpa only [hFdef, Function.comp_def] using
          (hcomp.sub_const (g p)).div_const ((ρ : ℂ) * deriv g p)
      rw [hFd.deriv, mul_comm (deriv g p) ((ρ : ℂ)), div_self (mul_ne_zero hρc hd)]
    have hFder : ∀ u ∈ ball (0 : ℂ) 1, deriv F u = deriv g (p + (ρ : ℂ) * u) / deriv g p := by
      intro u hu
      have hφ : HasDerivAt (fun v : ℂ => p + (ρ : ℂ) * v) (ρ : ℂ) u := by
        simpa using ((hasDerivAt_id u).const_mul (ρ : ℂ)).const_add p
      have hgu : HasDerivAt g (deriv g (p + (ρ : ℂ) * u)) (p + (ρ : ℂ) * u) :=
        (hg _ (hmem u hu)).differentiableAt.hasDerivAt
      have hcomp : HasDerivAt (fun v : ℂ => g (p + (ρ : ℂ) * v))
          (deriv g (p + (ρ : ℂ) * u) * (ρ : ℂ)) u := by
        simpa only [Function.comp_def] using hgu.comp u hφ
      have hFd : HasDerivAt F ((deriv g (p + (ρ : ℂ) * u) * (ρ : ℂ)) / ((ρ : ℂ) * deriv g p)) u := by
        simpa only [hFdef, Function.comp_def] using
          (hcomp.sub_const (g p)).div_const ((ρ : ℂ) * deriv g p)
      rw [hFd.deriv]
      field_simp
    have hzp : ‖z - p‖ ≤ ρ / 2 := by
      have h := mem_closedBall.mp hz
      rwa [dist_eq_norm] at h
    set u : ℂ := (z - p) / (ρ : ℂ) with hudef
    have hun : ‖u‖ ≤ 1 / 2 := by
      rw [hudef, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ]
      rw [div_le_iff₀ hρ]
      linarith
    have humem : u ∈ ball (0 : ℂ) 1 := by
      rw [mem_ball, dist_eq_norm, sub_zero]
      linarith
    have hzu : z = p + (ρ : ℂ) * u := by
      rw [hudef]; field_simp; ring
    have hlow := (hdisc F hFan hFinj hF0 hF1 u hun).1
    rw [hFder u humem, ← hzu, norm_div] at hlow
    have h1 : Clow * ‖deriv g p‖ ≤ ‖deriv g z‖ :=
      (le_div_iff₀ (norm_pos_iff.mpr hd)).mp hlow
    have h2 : ‖deriv g p‖ * Clow ≤ ‖deriv g z‖ := by linarith [h1, mul_comm ‖deriv g p‖ Clow]
    have h3 : ‖deriv g p‖ = (1 / Clow) * (‖deriv g p‖ * Clow) := by field_simp
    rw [h3]
    exact mul_le_mul_of_nonneg_left h2 (by positivity)
  · -- mean value bound
    intro g p ρ hρ hg hinj z hz
    have hpmem : p ∈ ball p ρ := mem_ball_self hρ
    have hd : deriv g p ≠ 0 :=
      Commons.Analysis.Complex.Analytic.deriv_ne_zero_of_injOn hρ (hg p hpmem) hinj
    have hρc : ((ρ : ℂ)) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hρ)
    set F : ℂ → ℂ := fun u => (g (p + (ρ : ℂ) * u) - g p) / ((ρ : ℂ) * deriv g p) with hFdef
    have hmem : ∀ u : ℂ, u ∈ ball (0 : ℂ) 1 → p + (ρ : ℂ) * u ∈ ball p ρ := by
      intro u hu
      have hu' : ‖u‖ < 1 := by simpa [mem_ball, dist_eq_norm] using hu
      have hn : ‖(ρ : ℂ) * u‖ = ρ * ‖u‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ]
      rw [mem_ball, dist_eq_norm, show p + (ρ : ℂ) * u - p = (ρ : ℂ) * u by ring, hn]
      nlinarith
    have hFan : ∀ u ∈ ball (0 : ℂ) 1, AnalyticAt ℂ F u := by
      intro u hu
      have hφ : AnalyticAt ℂ (fun v : ℂ => p + (ρ : ℂ) * v) u :=
        AnalyticAt.add analyticAt_const (AnalyticAt.mul analyticAt_const analyticAt_id)
      have h1 : AnalyticAt ℂ (fun v : ℂ => g (p + (ρ : ℂ) * v)) u :=
        AnalyticAt.comp (hg (p + (ρ : ℂ) * u) (hmem u hu)) hφ
      simpa only [hFdef, Pi.sub_apply] using (h1.sub analyticAt_const).div_const
    have hFinj : InjOn F (ball (0 : ℂ) 1) := by
      intro u hu v hv huv
      rw [hFdef] at huv
      have huv1 : g (p + (ρ : ℂ) * u) - g p = g (p + (ρ : ℂ) * v) - g p :=
        (div_left_inj' (mul_ne_zero hρc hd)).mp huv
      have huv2 : g (p + (ρ : ℂ) * u) = g (p + (ρ : ℂ) * v) := by
        have hh := congrArg (fun z => z + g p) huv1
        simpa using hh
      have huv3 : p + (ρ : ℂ) * u = p + (ρ : ℂ) * v := hinj (hmem u hu) (hmem v hv) huv2
      exact mul_left_cancel₀ hρc (add_left_cancel huv3)
    have hF0 : F 0 = 0 := by simp [hFdef]
    have hF1 : deriv F 0 = 1 := by
      have hφ : HasDerivAt (fun v : ℂ => p + (ρ : ℂ) * v) (ρ : ℂ) (0 : ℂ) := by
        simpa using ((hasDerivAt_id (0 : ℂ)).const_mul (ρ : ℂ)).const_add p
      have hg0 : HasDerivAt g (deriv g p) (p + (ρ : ℂ) * 0) := by
        simpa using (hg p hpmem).differentiableAt.hasDerivAt
      have hcomp : HasDerivAt (fun v : ℂ => g (p + (ρ : ℂ) * v)) (deriv g p * (ρ : ℂ)) 0 := by
        simpa only [Function.comp_def] using hg0.comp 0 hφ
      have hFd : HasDerivAt F ((deriv g p * (ρ : ℂ)) / ((ρ : ℂ) * deriv g p)) 0 := by
        simpa only [hFdef, Function.comp_def] using
          (hcomp.sub_const (g p)).div_const ((ρ : ℂ) * deriv g p)
      rw [hFd.deriv, mul_comm (deriv g p) ((ρ : ℂ)), div_self (mul_ne_zero hρc hd)]
    have hFder : ∀ u ∈ ball (0 : ℂ) 1, deriv F u = deriv g (p + (ρ : ℂ) * u) / deriv g p := by
      intro u hu
      have hφ : HasDerivAt (fun v : ℂ => p + (ρ : ℂ) * v) (ρ : ℂ) u := by
        simpa using ((hasDerivAt_id u).const_mul (ρ : ℂ)).const_add p
      have hgu : HasDerivAt g (deriv g (p + (ρ : ℂ) * u)) (p + (ρ : ℂ) * u) :=
        (hg _ (hmem u hu)).differentiableAt.hasDerivAt
      have hcomp : HasDerivAt (fun v : ℂ => g (p + (ρ : ℂ) * v))
          (deriv g (p + (ρ : ℂ) * u) * (ρ : ℂ)) u := by
        simpa only [Function.comp_def] using hgu.comp u hφ
      have hFd : HasDerivAt F
          ((deriv g (p + (ρ : ℂ) * u) * (ρ : ℂ)) / ((ρ : ℂ) * deriv g p)) u := by
        simpa only [hFdef, Function.comp_def] using
          (hcomp.sub_const (g p)).div_const ((ρ : ℂ) * deriv g p)
      rw [hFd.deriv]
      field_simp
    -- derivative bound on the inner disc
    have hbound : ∀ ζ ∈ closedBall p (ρ / 2), ‖deriv g ζ‖ ≤ Cup * ‖deriv g p‖ := by
      intro ζ hζ
      have hζp : ‖ζ - p‖ ≤ ρ / 2 := by
        have h := mem_closedBall.mp hζ
        rwa [dist_eq_norm] at h
      set u : ℂ := (ζ - p) / (ρ : ℂ) with hudef
      have hun : ‖u‖ ≤ 1 / 2 := by
        rw [hudef, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ]
        rw [div_le_iff₀ hρ]
        linarith
      have humem : u ∈ ball (0 : ℂ) 1 := by
        rw [mem_ball, dist_eq_norm, sub_zero]
        linarith
      have hζu : ζ = p + (ρ : ℂ) * u := by
        rw [hudef]; field_simp; ring
      have hup := (hdisc F hFan hFinj hF0 hF1 u hun).2
      rw [hFder u humem, ← hζu, norm_div, div_le_iff₀ (norm_pos_iff.mpr hd)] at hup
      linarith
    have hdiff : ∀ ζ ∈ closedBall p (ρ / 2), DifferentiableAt ℂ g ζ := by
      intro ζ hζ
      have hζ' : ζ ∈ ball p ρ := by
        rw [mem_closedBall] at hζ
        rw [mem_ball]
        linarith [hζ, hρ]
      exact (hg ζ hζ').differentiableAt
    have hconv : Convex ℝ (closedBall p (ρ / 2)) := convex_closedBall _ _
    exact Convex.norm_image_sub_le_of_norm_deriv_le hdiff hbound hconv
      (mem_closedBall_self (by linarith : (0:ℝ) ≤ ρ / 2)) hz

end Work.Dim
