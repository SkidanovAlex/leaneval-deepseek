import Mathlib
import Submission.Work.Pert.Basic
import Submission.Work.FatouCoord.Petal.reflected_inverse_germ
import Submission.Unif.Commons.Analysis.Complex.rouche_simple_zero

namespace Work.Pert

open Complex Set Metric Filter Topology
open scoped Topology

noncomputable section

/-! ## Auxiliary lemmas (general, reusable) -/

/-- **Division by `z - a` (removable singularity).**  If `g` is holomorphic on the open set `U`, with
`a ∈ U` and `g a = 0`, then `z ↦ g z / (z - a)` extends to a holomorphic function `S` on `U`:
`g z = (z - a) * S z` on `U`, `S z = g z / (z - a)` away from `a`, and `S a = deriv g a`. -/
theorem div_removable_aux {g : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) {a : ℂ} (ha : a ∈ U)
    (hg : DifferentiableOn ℂ g U) (hga : g a = 0) :
    ∃ S : ℂ → ℂ, DifferentiableOn ℂ S U ∧ (∀ z ∈ U, g z = (z - a) * S z) ∧
      (∀ z ∈ U, z ≠ a → S z = g z / (z - a)) ∧ S a = deriv g a := by
  have hgan : AnalyticAt ℂ g a := hg.analyticAt (hU.mem_nhds ha)
  refine ⟨dslope g a, ?_, ?_, ?_, dslope_same g a⟩
  · intro z hz
    rcases eq_or_ne z a with rfl | hne
    · exact (hgan.hasFPowerSeriesAt.has_fpower_series_dslope_fslope.analyticAt.differentiableAt).differentiableWithinAt
    · exact ((differentiableAt_dslope_of_ne hne).mpr
        ((hg z hz).differentiableAt (hU.mem_nhds hz))).differentiableWithinAt
  · intro z hz
    have h := sub_smul_dslope_of_zero hga z
    rw [smul_eq_mul] at h
    exact h.symm
  · intro z hz hne
    rw [dslope_of_ne g hne, slope]
    simp only [hga, vsub_eq_sub, sub_zero, smul_eq_mul, div_eq_mul_inv]
    ring

/-- **Maximum modulus principle, closed-ball form.**  If `u` is complex differentiable at every
point of `closedBall 0 R` and `‖u‖ ≤ M` on the sphere `sphere 0 R`, then `‖u z‖ ≤ M` for `z` in
`closedBall 0 R`. -/
theorem absmax_ball_aux {u : ℂ → ℂ} {R M : ℝ} (hR : 0 < R)
    (hu : ∀ z ∈ Metric.closedBall (0 : ℂ) R, DifferentiableAt ℂ u z)
    (hM : ∀ z ∈ Metric.sphere (0 : ℂ) R, ‖u z‖ ≤ M) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) R, ‖u z‖ ≤ M := by
  have hd : DiffContOnCl ℂ u (Metric.ball (0 : ℂ) R) := by
    refine ⟨fun z hz => (hu z (Metric.ball_subset_closedBall hz)).differentiableWithinAt, ?_⟩
    rw [closure_ball (0 : ℂ) hR.ne']
    exact fun z hz => (hu z hz).continuousAt.continuousWithinAt
  intro z hz
  refine Complex.norm_le_of_forall_mem_frontier_norm_le
    (Metric.isBounded_ball (x := (0 : ℂ)) (r := R)) hd (fun w hw => ?_) ?_
  · rw [frontier_ball (0 : ℂ) hR.ne'] at hw
    exact hM w hw
  · rwa [closure_ball (0 : ℂ) hR.ne']

/-! ## Shishikura A.1.2 -/

/-- **Shishikura Lemma A.1.2** (normal form of a small perturbation of a parabolic germ), with the
quantitative bounds used by the estimates of A.1.7.  (The `C⁰` closeness `NearOn` gives no control
of `u'`, hence no derivative clause here; the estimates only need `u'` on a strictly smaller ball,
which follows from `1/2 ≤ ‖u‖ ≤ 2` by Cauchy.) -/
theorem normalform {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (h₀ : MandelDim.IsParabolicGerm f₀ D₀) :
    ∃ ρ : ℝ, 0 < ρ ∧ Metric.closedBall 0 ρ ⊆ D₀ ∧ ∃ δ C : ℝ, 0 < δ ∧ 0 < C ∧
    ∀ {f : ℂ → ℂ} {Df : Set ℂ},
      MandelDim.NearOn f₀ f Df (Metric.closedBall 0 ρ) δ → f 0 = 0 →
      ∃ (σ : ℂ) (u : ℂ → ℂ),
        DifferentiableOn ℂ u (Metric.ball 0 ρ) ∧
        (∀ z ∈ Metric.ball 0 ρ, u z ≠ 0) ∧
        (∀ z ∈ Metric.ball 0 ρ, 1 / 2 ≤ ‖u z‖ ∧ ‖u z‖ ≤ 2) ∧
        (∀ z ∈ Metric.ball 0 ρ, f z = z + z * (z - σ) * u z) ∧
        deriv f 0 = 1 - σ * u 0 ∧
        ‖σ‖ ≤ C * ‖1 - deriv f 0‖ := by
  obtain ⟨hD0open, h0D0, hdiff0, hf00, hd1, hd2⟩ := h₀
  -- ## the unperturbed germ, in normal form
  have hFan : AnalyticAt ℂ f₀ 0 := hdiff0.analyticAt (hD0open.mem_nhds h0D0)
  have hF1 : iteratedDeriv 1 f₀ 0 = 1 := by rw [iteratedDeriv_one]; exact hd1
  have hF2 : iteratedDeriv 2 f₀ 0 = 2 := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
    exact hd2
  set b : ℂ := iteratedDeriv 3 f₀ 0 / 6 with hb
  obtain ⟨hF, r', A'', A''', hr'pos, hA''nn, -, hFeq, hFdiff, hFclose, -, -⟩ :=
    Work.FatouCoord.Petal.exists_parabolic_germ_bounds (b := b) hFan hf00 hF1 hF2
      (by rw [hb]; ring)
  obtain ⟨ε, hεpos, hεsub⟩ := Metric.mem_nhds_iff.mp (hD0open.mem_nhds h0D0)
  -- ## the two radii
  set ρ : ℝ := min (min r' ε / 2) (min (1 / 2) (1 / (64 * (‖b‖ + A'' + 1)))) with hρdef
  have hρpos : 0 < ρ := by
    rw [hρdef]
    have h1 : 0 < min r' ε := lt_min hr'pos hεpos
    have h2 : 0 < ‖b‖ + A'' + 1 := by positivity
    positivity
  have hρ_lt_r' : ρ < r' := by
    have h1 : ρ ≤ min r' ε / 2 := by rw [hρdef]; exact min_le_left _ _
    have h2 : min r' ε ≤ r' := min_le_left _ _
    linarith
  have hρ_lt_ε : ρ < ε := by
    have h1 : ρ ≤ min r' ε / 2 := by rw [hρdef]; exact min_le_left _ _
    have h2 : min r' ε ≤ ε := min_le_right _ _
    linarith
  have hρ_le_half : ρ ≤ 1 / 2 := by
    have h1 : ρ ≤ min (1 / 2) (1 / (64 * (‖b‖ + A'' + 1))) := by
      rw [hρdef]; exact min_le_right _ _
    have h2 := min_le_left (1 / 2 : ℝ) (1 / (64 * (‖b‖ + A'' + 1)))
    linarith
  have hρ_small : (‖b‖ + A'') * ρ ≤ 1 / 64 := by
    have h1 : ρ ≤ 1 / (64 * (‖b‖ + A'' + 1)) :=
      le_trans (by rw [hρdef]; exact min_le_right _ _) (min_le_right _ _)
    have hpos : 0 < 64 * (‖b‖ + A'' + 1) := by positivity
    have h2 : ρ * (64 * (‖b‖ + A'' + 1)) ≤ 1 := (le_div_iff₀ hpos).mp h1
    have h3 : 0 ≤ ‖b‖ + A'' := by positivity
    nlinarith [h2, h3, hρpos]
  set δ : ℝ := ρ ^ 3 / 32 with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; positivity
  have hδρ : δ / ρ = ρ ^ 2 / 32 := by
    rw [hδdef]
    field_simp
  refine ⟨ρ, hρpos, ?_, δ, 2, hδpos, by norm_num, ?_⟩
  · intro z hz
    exact hεsub (Metric.closedBall_subset_ball hρ_lt_ε hz)
  -- ## the perturbation
  intro f Df hnear hf0
  obtain ⟨hDfopen, hDfsub, hfdiff, hclose⟩ := hnear
  have h0Df : (0 : ℂ) ∈ Df := hDfsub (by rw [mem_closedBall_zero_iff, norm_zero]; exact hρpos.le)
  -- the cofactor `k` of `f - id`
  have hgdiff : DifferentiableOn ℂ (fun z : ℂ => f z - z) Df := hfdiff.sub differentiableOn_id
  have hg0 : (fun z : ℂ => f z - z) 0 = 0 := by simp [hf0]
  obtain ⟨k, hkdiff, -, hkeq0, hk0val⟩ := div_removable_aux hDfopen h0Df hgdiff hg0
  have hkeq : ∀ z ∈ Df, z ≠ 0 → k z = (f z - z) / z := fun z hz h => by simpa using hkeq0 z hz h
  have hk0 : k 0 = deriv f 0 - 1 := by
    have hdf : DifferentiableAt ℂ f 0 :=
      (hfdiff 0 h0Df).differentiableAt (hDfopen.mem_nhds h0Df)
    rw [hk0val]
    show deriv (f - id) 0 = deriv f 0 - 1
    rw [deriv_sub hdf differentiableAt_id]
    simp
  -- abbreviations
  have hclos : ∀ z ∈ Metric.closedBall (0 : ℂ) ρ, DifferentiableAt ℂ k z := fun z hz =>
    (hkdiff z (hDfsub hz)).differentiableAt (hDfopen.mem_nhds (hDfsub hz))
  have hkF_at : ∀ z ∈ Metric.closedBall (0 : ℂ) ρ, DifferentiableAt ℂ (fun w : ℂ => w * hF w) z := by
    intro z hz
    have hzr' : z ∈ Metric.ball (0 : ℂ) r' := Metric.closedBall_subset_ball hρ_lt_r' hz
    exact differentiableAt_id.mul (hFdiff.differentiableAt (Metric.isOpen_ball.mem_nhds hzr'))
  -- `hF ≈ 1`
  have hF_closed : ∀ z ∈ Metric.closedBall (0 : ℂ) ρ, ‖hF z - 1‖ ≤ 1 / 16 := by
    intro z hz
    have hzr' : z ∈ Metric.ball (0 : ℂ) r' := Metric.closedBall_subset_ball hρ_lt_r' hz
    have h1 : ‖hF z - 1 - b * z‖ ≤ A'' * ‖z‖ ^ 2 := hFclose z hzr'
    have hzρ : ‖z‖ ≤ ρ := mem_closedBall_zero_iff.mp hz
    have hznn : 0 ≤ ‖z‖ := norm_nonneg z
    have h2 : A'' * ‖z‖ ^ 2 ≤ A'' * ρ := by
      have h2a : ‖z‖ ^ 2 ≤ ρ := by nlinarith [hznn, hzρ, hρ_le_half]
      exact mul_le_mul_of_nonneg_left h2a hA''nn
    have h3 : ‖b * z‖ ≤ ‖b‖ * ρ := by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left hzρ (norm_nonneg b)
    have hsplit : hF z - 1 = (hF z - 1 - b * z) + b * z := by ring
    rw [hsplit]
    refine le_trans (norm_add_le _ _) ?_
    have h2' : ‖hF z - 1 - b * z‖ ≤ A'' * ρ := le_trans h1 h2
    refine le_trans (add_le_add h2' h3) ?_
    rw [show A'' * ρ + ‖b‖ * ρ = (A'' + ‖b‖) * ρ from by ring]
    nlinarith [hρ_small]
  -- ## the comparison `k ≈ id` on the sphere
  have hsphere : ∀ z ∈ Metric.sphere (0 : ℂ) ρ, ‖k z - z‖ < ‖z‖ := by
    intro z hz
    have hzρ : ‖z‖ = ρ := mem_sphere_zero_iff_norm.mp hz
    have hzDf : z ∈ Df := hDfsub (Metric.sphere_subset_closedBall hz)
    have hz0 : z ≠ 0 := by
      intro h; rw [h, norm_zero] at hzρ; linarith [hρpos]
    have hzr' : z ∈ Metric.ball (0 : ℂ) r' := by
      rw [Metric.mem_ball, dist_zero_right, hzρ]; exact hρ_lt_r'
    have hkey : k z - z = (f z - f₀ z) / z + (z * hF z - z) := by
      rw [hkeq z hzDf hz0, hFeq z hzr']
      field_simp
      ring
    have hb2 : ‖z * hF z - z‖ ≤ ρ / 16 := by
      have h1 : z * hF z - z = z * (hF z - 1) := by ring
      rw [h1, norm_mul, hzρ]
      calc ρ * ‖hF z - 1‖ ≤ ρ * (1 / 16) :=
            mul_le_mul_of_nonneg_left (hF_closed z (Metric.sphere_subset_closedBall hz)) hρpos.le
        _ = ρ / 16 := by ring
    have hbb : ‖f z - f₀ z‖ / ρ < δ / ρ := by
      rw [div_lt_div_iff_of_pos_right hρpos]
      exact hclose z (Metric.sphere_subset_closedBall hz)
    have hmid : ‖f z - f₀ z‖ / ρ + ρ / 16 < ρ := by
      have h2 : δ / ρ + ρ / 16 < ρ := by
        rw [hδρ]
        nlinarith [hρpos, hρ_le_half]
      linarith
    calc ‖k z - z‖ = ‖(f z - f₀ z) / z + (z * hF z - z)‖ := by rw [hkey]
      _ ≤ ‖(f z - f₀ z) / z‖ + ‖z * hF z - z‖ := norm_add_le _ _
      _ = ‖f z - f₀ z‖ / ρ + ‖z * hF z - z‖ := by rw [norm_div, hzρ]
      _ ≤ ‖f z - f₀ z‖ / ρ + ρ / 16 := add_le_add le_rfl hb2
      _ < ρ := hmid
      _ = ‖z‖ := hzρ.symm
  -- ## Rouché: a unique zero `σ` of `k` in the ball
  obtain ⟨σ, hσball, hσz, hσuniq⟩ :=
    Commons.Analysis.Complex.rouche_simple_zero (R := ρ) hρpos (f := fun z : ℂ => z)
      (g := fun z : ℂ => k z - z) (a := 0)
      (by simpa using hρpos) differentiableOn_id continuousOn_id
      (fun z hz => ((hclos z hz).sub differentiableAt_id).differentiableWithinAt)
      (fun z hz => ((hclos z hz).sub differentiableAt_id).continuousAt.continuousWithinAt)
      hsphere (by simp) (by simp) (fun z hz h0 => h0)
  have hkσ : k σ = 0 := by linear_combination hσz
  have hσDf : σ ∈ Df := hDfsub (Metric.ball_subset_closedBall hσball)
  -- the cofactor `u` of `k` at `σ`
  obtain ⟨u, hudiff, hufac, hueq, -⟩ := div_removable_aux hDfopen hσDf hkdiff hkσ
  -- ## `k` and `kF` are close on the whole ball
  have hkle : ∀ z ∈ Metric.closedBall (0 : ℂ) ρ, ‖k z - z * hF z‖ ≤ δ / ρ := by
    refine absmax_ball_aux hρpos (fun z hz => (hclos z hz).sub (hkF_at z hz)) ?_
    intro z hz
    have hzρ : ‖z‖ = ρ := mem_sphere_zero_iff_norm.mp hz
    have hzDf : z ∈ Df := hDfsub (Metric.sphere_subset_closedBall hz)
    have hz0 : z ≠ 0 := by
      intro h; rw [h, norm_zero] at hzρ; linarith [hρpos]
    have hzr' : z ∈ Metric.ball (0 : ℂ) r' := by
      rw [Metric.mem_ball, dist_zero_right, hzρ]; exact hρ_lt_r'
    have hkey : k z - z * hF z = (f z - f₀ z) / z := by
      rw [hkeq z hzDf hz0, hFeq z hzr']
      field_simp
      ring
    rw [hkey, norm_div, hzρ, div_le_div_iff_of_pos_right hρpos]
    exact le_of_lt (hclose z (Metric.sphere_subset_closedBall hz))
  -- ## the second fixed point is small
  have hσbd : ‖σ‖ ≤ ρ ^ 2 / 30 := by
    have h1 : ‖k σ - σ * hF σ‖ ≤ δ / ρ := hkle σ (Metric.ball_subset_closedBall hσball)
    have h2 : ‖σ * hF σ‖ ≤ δ / ρ := by
      have h2a : k σ - σ * hF σ = -(σ * hF σ) := by rw [hkσ]; ring
      rwa [h2a, norm_neg] at h1
    have h3 : (15 : ℝ) / 16 ≤ ‖hF σ‖ := by
      have h4 : ‖hF σ - 1‖ ≤ 1 / 16 := hF_closed σ (Metric.ball_subset_closedBall hσball)
      have h5 : |‖hF σ‖ - 1| ≤ 1 / 16 := by
        have := abs_norm_sub_norm_le (hF σ) (1 : ℂ)
        simpa using le_trans this h4
      linarith [(abs_le.mp h5).1]
    calc ‖σ‖ = ‖σ * hF σ‖ / ‖hF σ‖ := by
          rw [norm_mul, mul_div_cancel_right₀ _ (by linarith : ‖hF σ‖ ≠ 0)]
      _ ≤ (δ / ρ) / (15 / 16) :=
          div_le_div₀ (by positivity) h2 (by norm_num) h3
      _ = ρ ^ 2 / 30 := by rw [hδρ]; ring
  -- ## `u ≈ 1` on the sphere and hence on the ball
  have hu_sphere : ∀ z ∈ Metric.sphere (0 : ℂ) ρ, ‖u z - 1‖ ≤ 3 / 8 := by
    intro z hz
    have hzρ : ‖z‖ = ρ := mem_sphere_zero_iff_norm.mp hz
    have hzDf : z ∈ Df := hDfsub (Metric.sphere_subset_closedBall hz)
    have hσlt : ‖σ‖ < ρ := by nlinarith [hσbd, hρ_le_half, hρpos]
    have hzne : z ≠ σ := by
      intro h; rw [h] at hzρ; linarith
    have hnum : ‖k z - (z - σ)‖ ≤ ρ ^ 2 / 32 + ρ / 16 + ρ ^ 2 / 30 := by
      have h1 : ‖k z - z * hF z‖ ≤ δ / ρ := hkle z (Metric.sphere_subset_closedBall hz)
      have h2 : ‖z * hF z - z‖ ≤ ρ / 16 := by
        have h3 : z * hF z - z = z * (hF z - 1) := by ring
        rw [h3, norm_mul, hzρ]
        calc ρ * ‖hF z - 1‖ ≤ ρ * (1 / 16) :=
              mul_le_mul_of_nonneg_left (hF_closed z (Metric.sphere_subset_closedBall hz)) hρpos.le
          _ = ρ / 16 := by ring
      have h4 : k z - (z - σ) = (k z - z * hF z) + (z * hF z - z) + σ := by ring
      rw [h4]
      calc ‖(k z - z * hF z) + (z * hF z - z) + σ‖
          ≤ ‖(k z - z * hF z) + (z * hF z - z)‖ + ‖σ‖ := norm_add_le _ _
        _ ≤ (‖k z - z * hF z‖ + ‖z * hF z - z‖) + ‖σ‖ := by
              have := norm_add_le (k z - z * hF z) (z * hF z - z)
              linarith
        _ ≤ (δ / ρ + ρ / 16) + ρ ^ 2 / 30 := by linarith
        _ = ρ ^ 2 / 32 + ρ / 16 + ρ ^ 2 / 30 := by rw [hδρ]
    have hden : ρ / 2 ≤ ‖z - σ‖ := by
      have h1 : ‖z‖ - ‖σ‖ ≤ ‖z - σ‖ := by
        have := abs_norm_sub_norm_le z σ
        linarith [(abs_le.mp this).2]
      have h3 : ρ / 2 ≤ ρ - ρ ^ 2 / 30 := by nlinarith [hρpos, hρ_le_half]
      linarith [hσbd]
    calc ‖u z - 1‖ = ‖k z / (z - σ) - 1‖ := by rw [hueq z hzDf hzne]
      _ = ‖(k z - (z - σ)) / (z - σ)‖ := by rw [div_sub_one (sub_ne_zero.mpr hzne)]
      _ = ‖k z - (z - σ)‖ / ‖z - σ‖ := norm_div _ _
      _ ≤ (ρ ^ 2 / 32 + ρ / 16 + ρ ^ 2 / 30) / (ρ / 2) :=
          div_le_div₀ (by positivity) hnum (by positivity) hden
      _ ≤ 3 / 8 := by
          rw [div_le_iff₀ (by positivity : (0 : ℝ) < ρ / 2)]
          nlinarith [hρ_le_half, hρpos]
  have hu_closed : ∀ z ∈ Metric.closedBall (0 : ℂ) ρ, ‖u z - 1‖ ≤ 3 / 8 :=
    absmax_ball_aux hρpos (fun z hz =>
      ((hudiff z (hDfsub hz)).differentiableAt (hDfopen.mem_nhds (hDfsub hz))).sub_const 1)
      hu_sphere
  -- ## the derivative and the size of `σ`
  have hderiv : deriv f 0 = 1 - σ * u 0 := by
    have h1 : k 0 = (0 - σ) * u 0 := hufac 0 h0Df
    have h2 : deriv f 0 - 1 = (0 - σ) * u 0 := by rw [← hk0, h1]
    rw [sub_eq_iff_eq_add] at h2
    rw [h2]; ring
  have hu0 : (1 : ℝ) / 2 ≤ ‖u 0‖ := by
    have h1 : |‖u 0‖ - 1| ≤ 3 / 8 := by
      have := abs_norm_sub_norm_le (u 0) (1 : ℂ)
      simpa using le_trans this (hu_closed 0 (by rw [mem_closedBall_zero_iff, norm_zero]; exact hρpos.le))
    linarith [(abs_le.mp h1).1]
  refine ⟨σ, u, ?_, ?_, ?_, ?_, hderiv, ?_⟩
  · exact hudiff.mono (fun z hz => hDfsub (Metric.ball_subset_closedBall hz))
  · intro z hz
    have h1 : |‖u z‖ - 1| ≤ 3 / 8 := by
      have := abs_norm_sub_norm_le (u z) (1 : ℂ)
      simpa using le_trans this (hu_closed z (Metric.ball_subset_closedBall hz))
    exact norm_pos_iff.mp (by linarith [(abs_le.mp h1).1])
  · intro z hz
    have h1 : |‖u z‖ - 1| ≤ 3 / 8 := by
      have := abs_norm_sub_norm_le (u z) (1 : ℂ)
      simpa using le_trans this (hu_closed z (Metric.ball_subset_closedBall hz))
    exact ⟨by linarith [(abs_le.mp h1).1], by linarith [(abs_le.mp h1).2]⟩
  · intro z hz
    have hzDf : z ∈ Df := hDfsub (Metric.ball_subset_closedBall hz)
    rcases eq_or_ne z 0 with rfl | hz0
    · rw [hf0]; ring
    · have h1 : (f z - z) / z = (z - σ) * u z := by
        rw [← hkeq z hzDf hz0, hufac z hzDf]
      have h2 : f z - z = z * ((z - σ) * u z) := by
        rw [← h1, mul_comm, div_mul_cancel₀ _ hz0]
      rw [sub_eq_iff_eq_add] at h2
      rw [h2]; ring
  · have h1 : ‖1 - deriv f 0‖ = ‖σ * u 0‖ := by rw [hderiv]; ring_nf
    have h2 : ‖u 0‖ ≠ 0 := by linarith [hu0]
    calc ‖σ‖ = ‖σ * u 0‖ / ‖u 0‖ := by rw [norm_mul, mul_div_cancel_right₀ _ h2]
      _ ≤ ‖σ * u 0‖ / (1 / 2) :=
          div_le_div_of_nonneg_left (norm_nonneg _) (by norm_num) hu0
      _ = 2 * ‖1 - deriv f 0‖ := by rw [h1]; ring

end

end Work.Pert
