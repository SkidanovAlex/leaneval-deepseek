import Mathlib
import Submission.Work.Pert.small_of_nearOn

/-!
# `SmallOfNearOnConst`

The explicit-constant form of `Work.Pert.small_of_nearOn`: the germ relation
`f z = z + z (z - σ) u z` that `PertStatement` uses to *output* the parameters `(σ, u)`
of the perturbation, read at `z = 0`, forces `u 0 ≈ 1` and `σ` small, with the
quantitative bounds of §4.2/(4.2.x) of Shishikura.  Here the constant is fixed to `10`,
which is what the `(1/2, 1/32)`-form uses.

The analytic input is Cauchy's estimate applied to `f - f₀` on the ball of radius `ρ`
(supremum bound `δ₀`) and to `u` on the ball of radius `rr/2` (supremum bound `2`).
-/

namespace Work.Pert

open Complex Metric Filter Set

open scoped Topology

theorem SmallOfNearOnConst {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (h₀ : MandelDim.IsParabolicGerm f₀ D₀) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ Metric.closedBall (0 : ℂ) r₀ ⊆ D₀ ∧
    ∀ {f : ℂ → ℂ} {Df : Set ℂ} {ρ δ₀ rr : ℝ} {u : ℂ → ℂ} {σ : ℂ},
      0 < ρ → ρ ≤ r₀ → 0 < δ₀ → 2 * δ₀ ≤ ρ → 0 < rr →
      MandelDim.NearOn f₀ f Df (Metric.closedBall (0 : ℂ) ρ) δ₀ → f 0 = 0 →
      DifferentiableOn ℂ u (Metric.ball 0 rr) →
      (∀ z ∈ Metric.ball 0 rr, 1 / 2 ≤ ‖u z‖ ∧ ‖u z‖ ≤ 2) →
      (∀ z ∈ Metric.ball 0 rr, f z = z + z * (z - σ) * u z) →
      ‖u 0 - 1‖ ≤ 10 * (δ₀ / ρ ^ 2 + δ₀ / (ρ * rr)) ∧ ‖σ‖ ≤ 10 * δ₀ / ρ ∧
        ‖MandelDim.rotOf f‖ ≤ 10 * δ₀ / ρ := by
  obtain ⟨hD0open, h0mem, hf0diff, _hf00, hdf0, hddf0⟩ := h₀
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp (hD0open.mem_nhds h0mem)
  set R₀ : ℝ := min (ε / 2) 1 with hR₀def
  have hR₀pos : 0 < R₀ := by
    rw [hR₀def]
    exact lt_min (by linarith) one_pos
  have hR₀sub : Metric.closedBall (0 : ℂ) R₀ ⊆ D₀ := by
    rw [hR₀def]
    exact fun z hz =>
      hεsub (Metric.closedBall_subset_ball (by linarith [min_le_left (ε / 2) 1, hε]) hz)
  refine ⟨R₀, hR₀pos, hR₀sub, ?_⟩
  intro f Df ρ δ₀ rr u σ hρ hρr hδ h2δ hrr hnear _hf0eq hdiffu hbnd hform
  -- ## elementary memberships
  have h0clρ : (0 : ℂ) ∈ Metric.closedBall (0 : ℂ) ρ := Metric.mem_closedBall_self hρ.le
  have h0Df : (0 : ℂ) ∈ Df := hnear.2.1 h0clρ
  have hsubD0 : Metric.closedBall (0 : ℂ) ρ ⊆ D₀ :=
    (Metric.closedBall_subset_closedBall hρr).trans hR₀sub
  have h0D0 : (0 : ℂ) ∈ D₀ := hsubD0 h0clρ
  have hball_sub : Metric.ball (0 : ℂ) ρ ⊆ Df := fun z hz =>
    hnear.2.1 (Metric.ball_subset_closedBall hz)
  have hball_sub₀ : Metric.ball (0 : ℂ) ρ ⊆ D₀ := fun z hz =>
    hsubD0 (Metric.ball_subset_closedBall hz)
  have h0ballrr : (0 : ℂ) ∈ Metric.ball (0 : ℂ) rr := Metric.mem_ball_self hrr
  have h0nhdsrr : Metric.ball (0 : ℂ) rr ∈ 𝓝 (0 : ℂ) :=
    Metric.isOpen_ball.mem_nhds h0ballrr
  -- ## analyticity of `f` and `f₀` at `0`
  have hanal_f : AnalyticAt ℂ f 0 := hnear.2.2.1.analyticAt (hnear.1.mem_nhds h0Df)
  have hanal_f0 : AnalyticAt ℂ f₀ 0 := hf0diff.analyticAt (hD0open.mem_nhds h0mem)
  -- ## Cauchy estimates for `f - f₀`
  have hdiffg : DifferentiableOn ℂ (fun z : ℂ => f z - f₀ z) (Metric.ball (0 : ℂ) ρ) :=
    (hnear.2.2.1.mono hball_sub).sub (hf0diff.mono hball_sub₀)
  have hcontg : ContinuousOn (fun z : ℂ => f z - f₀ z)
      (closure (Metric.ball (0 : ℂ) ρ)) := by
    have h1 : ContinuousOn f (Df ∩ D₀) :=
      hnear.2.2.1.continuousOn.mono (fun z hz => hz.1)
    have h2 : ContinuousOn f₀ (Df ∩ D₀) :=
      hf0diff.continuousOn.mono (fun z hz => hz.2)
    exact (h1.sub h2).mono (fun z hz =>
      ⟨hnear.2.1 (Metric.closure_ball_subset_closedBall hz),
        hsubD0 (Metric.closure_ball_subset_closedBall hz)⟩)
  have hDCg : DiffContOnCl ℂ (fun z : ℂ => f z - f₀ z) (Metric.ball (0 : ℂ) ρ) :=
    ⟨hdiffg, hcontg⟩
  have hsphere_le : ∀ z ∈ Metric.sphere (0 : ℂ) ρ, ‖f z - f₀ z‖ ≤ δ₀ := fun z hz =>
    le_of_lt (hnear.2.2.2 z (Metric.sphere_subset_closedBall hz))
  have hC1 : ‖iteratedDeriv 1 (fun z : ℂ => f z - f₀ z) 0‖ ≤ δ₀ / ρ := by
    rw [iteratedDeriv_one]
    exact Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hρ hDCg hsphere_le
  have hC2 : ‖iteratedDeriv 2 (fun z : ℂ => f z - f₀ z) 0‖ ≤ 2 * (δ₀ / ρ ^ 2) := by
    have h := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le 2 hρ hDCg hsphere_le
    have hval : (↑(Nat.factorial 2) : ℝ) * δ₀ / ρ ^ 2 = 2 * (δ₀ / ρ ^ 2) := by
      norm_num
      ring
    rw [hval] at h
    exact h
  -- ## differentiability of `u` and of `deriv u`
  have hu_d0 : DifferentiableAt ℂ u 0 :=
    hdiffu.differentiableAt (Metric.isOpen_ball.mem_nhds h0ballrr)
  have hdu : DifferentiableOn ℂ (deriv u) (Metric.ball (0 : ℂ) rr) :=
    hdiffu.deriv Metric.isOpen_ball
  have hdu_d0 : DifferentiableAt ℂ (deriv u) 0 :=
    hdu.differentiableAt (Metric.isOpen_ball.mem_nhds h0ballrr)
  -- ## Cauchy estimate for `u'`
  have hu' : ‖deriv u 0‖ ≤ 4 / rr := by
    have hd : DifferentiableOn ℂ u (Metric.ball (0 : ℂ) (rr / 2)) :=
      hdiffu.mono (fun z hz => by
        rw [Metric.mem_ball] at hz ⊢
        linarith)
    have hc : ContinuousOn u (closure (Metric.ball (0 : ℂ) (rr / 2))) :=
      hdiffu.continuousOn.mono (fun z hz => by
        have hz' : ‖z‖ ≤ rr / 2 := by
          have h := Metric.mem_closedBall.mp (Metric.closure_ball_subset_closedBall hz)
          rwa [dist_zero_right] at h
        rw [Metric.mem_ball, dist_zero_right]
        linarith)
    have h := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (c := 0) (R := rr / 2)
      (C := 2) (by linarith) (⟨hd, hc⟩ : DiffContOnCl ℂ u (Metric.ball (0 : ℂ) (rr / 2)))
      (fun z hz => by
        have hz2 : z ∈ Metric.ball (0 : ℂ) rr := by
          have hz'' : ‖z‖ = rr / 2 := by
            have h := Metric.mem_sphere.mp hz
            rwa [dist_zero_right] at h
          rw [Metric.mem_ball, dist_zero_right]
          linarith
        exact (hbnd z hz2).2)
    have hval : (2 : ℝ) / (rr / 2) = 4 / rr := by
      field_simp
      ring
    rw [hval] at h
    exact h
  -- ## the explicit model map `F z = z + z (z - σ) u z`
  have hpt : ∀ y ∈ Metric.ball (0 : ℂ) rr,
      deriv (fun z : ℂ => z + z * (z - σ) * u z) y
        = 1 + (2 * y - σ) * u y + (y ^ 2 - σ * y) * deriv u y := fun y hy =>
    deriv_quad_mul (hdiffu.differentiableAt (Metric.isOpen_ball.mem_nhds hy))
  have hiter1F : iteratedDeriv 1 (fun z : ℂ => z + z * (z - σ) * u z) 0 = 1 - σ * u 0 := by
    rw [iteratedDeriv_one, hpt 0 h0ballrr]
    ring
  have hderivF_eq : deriv (fun z : ℂ => z + z * (z - σ) * u z) =ᶠ[𝓝 (0 : ℂ)]
      (fun z : ℂ => 1 + (2 * z - σ) * u z + (z ^ 2 - σ * z) * deriv u z) :=
    Filter.eventually_of_mem h0nhdsrr hpt
  have hiter2F : iteratedDeriv 2 (fun z : ℂ => z + z * (z - σ) * u z) 0
      = 2 * u 0 - 2 * σ * deriv u 0 := by
    have hd : deriv (deriv (fun z : ℂ => z + z * (z - σ) * u z)) 0
        = 2 * u 0 - 2 * σ * deriv u 0 :=
      ((hasDerivAt_deriv_quad_mul hu_d0 hdu_d0).congr_of_eventuallyEq hderivF_eq).deriv
    have h2 : iteratedDeriv 2 (fun z : ℂ => z + z * (z - σ) * u z)
        = deriv (deriv (fun z : ℂ => z + z * (z - σ) * u z)) := by
      rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
    rw [h2]
    exact hd
  -- ## transfer to `f` and `f₀`
  have hfeq : f =ᶠ[𝓝 (0 : ℂ)] (fun z : ℂ => z + z * (z - σ) * u z) :=
    Filter.eventually_of_mem h0nhdsrr hform
  have hf1 : iteratedDeriv 1 f 0 = 1 - σ * u 0 := by
    rw [Filter.EventuallyEq.iteratedDeriv_eq 1 hfeq, hiter1F]
  have hf2 : iteratedDeriv 2 f 0 = 2 * u 0 - 2 * σ * deriv u 0 := by
    rw [Filter.EventuallyEq.iteratedDeriv_eq 2 hfeq, hiter2F]
  have hf01 : iteratedDeriv 1 f₀ 0 = 1 := by
    rw [iteratedDeriv_one]
    exact hdf0
  have hf02 : iteratedDeriv 2 f₀ 0 = 2 := by
    have h2 : iteratedDeriv 2 f₀ = deriv (deriv f₀) := by
      rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
    rw [h2]
    exact hddf0
  have hsplit1 :
      iteratedDeriv 1 (fun z : ℂ => f z - f₀ z) 0 = (1 - σ * u 0) - 1 := by
    change iteratedDeriv 1 (f - f₀) 0 = (1 - σ * u 0) - 1
    rw [iteratedDeriv_sub hanal_f.contDiffAt hanal_f0.contDiffAt, hf1, hf01]
  have hsplit2 :
      iteratedDeriv 2 (fun z : ℂ => f z - f₀ z) 0 = (2 * u 0 - 2 * σ * deriv u 0) - 2 := by
    change iteratedDeriv 2 (f - f₀) 0 = (2 * u 0 - 2 * σ * deriv u 0) - 2
    rw [iteratedDeriv_sub hanal_f.contDiffAt hanal_f0.contDiffAt, hf2, hf02]
  -- ## first order information
  have hσu : ‖σ * u 0‖ ≤ δ₀ / ρ := by
    have h := hC1
    rw [hsplit1] at h
    have hval : (1 - σ * u 0) - 1 = -(σ * u 0) := by ring
    rw [hval, norm_neg] at h
    exact h
  have hsec : ‖2 * u 0 - 2 * σ * deriv u 0 - 2‖ ≤ 2 * (δ₀ / ρ ^ 2) := by
    have h := hC2
    rw [hsplit2] at h
    exact h
  have hu0lo : (1 / 2 : ℝ) ≤ ‖u 0‖ := (hbnd 0 h0ballrr).1
  have hσ : ‖σ‖ ≤ 2 * (δ₀ / ρ) := by
    have h1 : (1 / 2 : ℝ) * ‖σ‖ ≤ ‖σ * u 0‖ := by
      have h := mul_le_mul_of_nonneg_right hu0lo (norm_nonneg σ)
      rw [norm_mul]
      linarith [h, mul_comm ‖u 0‖ ‖σ‖]
    linarith [hσu, h1]
  -- ## the bound on `u 0 - 1`
  have hhalf : ‖u 0 - 1 - σ * deriv u 0‖ ≤ δ₀ / ρ ^ 2 := by
    have heq : (2 * u 0 - 2 * σ * deriv u 0) - 2 = 2 * (u 0 - 1 - σ * deriv u 0) := by
      ring
    have h2 : ‖(2 : ℂ) * (u 0 - 1 - σ * deriv u 0)‖ ≤ 2 * (δ₀ / ρ ^ 2) := by
      have h := hsec
      rw [heq] at h
      exact h
    rw [norm_mul, Complex.norm_ofNat] at h2
    linarith
  have hmain : ‖u 0 - 1‖ ≤ δ₀ / ρ ^ 2 + ‖σ‖ * (4 / rr) := by
    have htri : ‖u 0 - 1‖ ≤ ‖u 0 - 1 - σ * deriv u 0‖ + ‖σ * deriv u 0‖ := by
      have h := norm_add_le (u 0 - 1 - σ * deriv u 0) (σ * deriv u 0)
      have he : (u 0 - 1 - σ * deriv u 0) + σ * deriv u 0 = u 0 - 1 := by ring
      rwa [he] at h
    have hmul : ‖σ * deriv u 0‖ ≤ ‖σ‖ * (4 / rr) := by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left hu' (norm_nonneg σ)
    linarith
  have hfin1 : ‖u 0 - 1‖ ≤ 10 * (δ₀ / ρ ^ 2 + δ₀ / (ρ * rr)) := by
    have hb : ‖σ‖ * (4 / rr) ≤ (2 * (δ₀ / ρ)) * (4 / rr) :=
      mul_le_mul_of_nonneg_right hσ (by positivity)
    have hkey : (2 * (δ₀ / ρ)) * (4 / rr) = 8 * (δ₀ / (ρ * rr)) := by
      field_simp
      ring
    have hA : (0 : ℝ) ≤ δ₀ / ρ ^ 2 := by positivity
    have hB : (0 : ℝ) ≤ δ₀ / (ρ * rr) := by positivity
    have hmid : ‖u 0 - 1‖ ≤ δ₀ / ρ ^ 2 + 8 * (δ₀ / (ρ * rr)) := by
      linarith [hmain, hb, hkey]
    have hgoal : 10 * (δ₀ / ρ ^ 2 + δ₀ / (ρ * rr)) =
        10 * (δ₀ / ρ ^ 2) + 10 * (δ₀ / (ρ * rr)) := by ring
    rw [hgoal]
    linarith [hmid, hA, hB]
  -- ## the bounds on `σ` and on `rotOf f`
  have hfin2 : ‖σ‖ ≤ 10 * δ₀ / ρ := by
    have hX : (0 : ℝ) ≤ δ₀ / ρ := by positivity
    have h10 : (10 : ℝ) * δ₀ / ρ = 10 * (δ₀ / ρ) := by ring
    rw [h10]
    linarith [hσ, hX]
  have hderivf0 : deriv f 0 = 1 - σ * u 0 := by
    have h := hf1
    rwa [iteratedDeriv_one] at h
  have hfin3 : ‖MandelDim.rotOf f‖ ≤ 10 * δ₀ / ρ := by
    have hhw : ‖σ * u 0‖ ≤ 1 / 2 := by
      have hhalf' : δ₀ / ρ ≤ 1 / 2 := by
        rw [div_le_iff₀ hρ]
        linarith
      linarith [hσu, hhalf']
    have hlog : ‖Complex.log (1 - σ * u 0)‖ ≤ (3 / 2) * ‖σ * u 0‖ := by
      have hz : ‖-(σ * u 0)‖ ≤ 1 / 2 := by rwa [norm_neg]
      have h := Complex.norm_log_one_add_half_le_self (z := -(σ * u 0)) hz
      have heq : (1 : ℂ) + -(σ * u 0) = 1 - σ * u 0 := by ring
      rw [heq] at h
      calc ‖Complex.log (1 - σ * u 0)‖ ≤ 3 / 2 * ‖-(σ * u 0)‖ := h
        _ = 3 / 2 * ‖σ * u 0‖ := by rw [norm_neg]
    have hh : (0 : ℝ) < 2 * Real.pi := by positivity
    have hden : ‖(2 : ℂ) * (Real.pi : ℂ) * Complex.I‖ = 2 * Real.pi := by
      rw [norm_mul, norm_mul, Complex.norm_ofNat, Complex.norm_I, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos Real.pi_pos]
      ring
    have hX : (0 : ℝ) ≤ δ₀ / ρ := by positivity
    have hmult : (3 / 2) * (δ₀ / ρ) ≤ 10 * (δ₀ / ρ) * (2 * Real.pi) := by
      have hpi : (3 / 2 : ℝ) ≤ 10 * (2 * Real.pi) := by nlinarith [Real.pi_gt_three]
      have h := mul_le_mul_of_nonneg_right hpi hX
      nlinarith [h]
    have h10 : (10 : ℝ) * δ₀ / ρ = 10 * (δ₀ / ρ) := by ring
    rw [MandelDim.rotOf, hderivf0, norm_div, hden, h10, div_le_iff₀ hh]
    linarith [hlog, hσu, hmult]
  exact ⟨hfin1, hfin2, hfin3⟩

end Work.Pert
