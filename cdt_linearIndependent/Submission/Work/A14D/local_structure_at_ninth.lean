import Mathlib
import Submission.Work.A14D.setup
import Submission.Work.A14D.local_structure_flip_v2
import Submission.Work.A14D.LZ_sub_const_mul

namespace Work.A14D

open Complex Metric Filter
open scoped Topology

noncomputable section

/-! ## helpers -/

lemma differentiable_PZ : Differentiable ℂ PZ := by unfold PZ; fun_prop
lemma differentiable_PZ' : Differentiable ℂ PZ' := by unfold PZ'; fun_prop
lemma differentiable_RZ : Differentiable ℂ RZ := by unfold RZ; fun_prop
lemma differentiable_qZ : Differentiable ℂ qZ := by unfold qZ; fun_prop

lemma differentiableOn_psiZ {y : ℂ → ℂ} {δ : ℝ}
    (hdy : DifferentiableOn ℂ (deriv y) (Metric.ball ninth δ))
    (hy : DifferentiableOn ℂ y (Metric.ball ninth δ)) :
    DifferentiableOn ℂ (psiZ y) (Metric.ball ninth δ) := by
  have hfun : psiZ y = fun w : ℂ => 2 * (qZ w * deriv y w) + (18 * w - 9) * y w := by
    funext w; rw [psiZ]; ring
  rw [hfun]
  have hq : DifferentiableOn ℂ (qZ * deriv y) (Metric.ball ninth δ) :=
    differentiable_qZ.differentiableOn.mul hdy
  exact (((differentiableOn_const (2 : ℂ)).mul hq).add
    ((((differentiableOn_const (18 : ℂ)).mul differentiableOn_id).sub
      (differentiableOn_const (9 : ℂ))).mul hy))

lemma deriv_PZ_local_structure_at_ninth (z : ℂ) : deriv PZ z = PZ' z := by
  have hfun : PZ = fun z : ℂ => z - 10 * z ^ 2 + 9 * z ^ 3 := by
    funext z; simp only [PZ]; ring
  have hd : HasDerivAt (fun z : ℂ => z - 10 * z ^ 2 + 9 * z ^ 3) (PZ' z) z := by
    have h1 : HasDerivAt (fun z : ℂ => z) 1 z := hasDerivAt_id z
    have h2 : HasDerivAt (fun z : ℂ => 10 * z ^ 2) (10 * (2 * z)) z := by
      simpa using (h1.pow 2).const_mul 10
    have h3 : HasDerivAt (fun z : ℂ => 9 * z ^ 3) (9 * (3 * z ^ 2)) z := by
      simpa using (h1.pow 3).const_mul 9
    have h4 : HasDerivAt (fun z : ℂ => z - 10 * z ^ 2 + 9 * z ^ 3)
        (1 - 10 * (2 * z) + 9 * (3 * z ^ 2)) z := (h1.sub h2).add h3
    convert h4 using 1
    simp only [PZ']
    ring
  rw [hfun]
  exact hd.deriv

lemma norm_ofReal' (r : ℝ) : ‖((r : ℝ) : ℂ)‖ = |r| := by
  have h1 : ‖((r : ℝ) : ℂ)‖ ^ 2 = |r| ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_ofReal, sq_abs]; ring
  nlinarith [h1, norm_nonneg (((r : ℝ) : ℂ)), abs_nonneg r]

lemma one_ninth_le_dist_zero : (1 : ℝ) / 9 ≤ dist (0 : ℂ) ninth := by
  have h := Complex.abs_re_le_norm ninth
  have hre : ninth.re = 1 / 9 := by norm_num [ninth]
  rw [hre, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 9)] at h
  rwa [Complex.dist_eq, zero_sub, norm_neg]

lemma eight_ninth_le_dist_one : (8 : ℝ) / 9 ≤ dist (1 : ℂ) ninth := by
  have h := Complex.abs_re_le_norm ((1 : ℂ) - ninth)
  have hre : ((1 : ℂ) - ninth).re = 8 / 9 := by
    rw [Complex.sub_re, Complex.one_re]; norm_num [ninth]
  rw [hre, abs_of_pos (by norm_num : (0 : ℝ) < 8 / 9)] at h
  rwa [Complex.dist_eq]

lemma qZ_ne_zero_of_mem_ball {ρ : ℝ} (hρ9 : ρ ≤ 1 / 9) {z : ℂ}
    (hz : z ∈ Metric.ball ninth ρ) : qZ z ≠ 0 := by
  intro h
  have hzd : dist z ninth < ρ := Metric.mem_ball.mp hz
  have h0 : z ≠ 0 := by
    intro h0
    rw [h0] at hzd
    linarith [one_ninth_le_dist_zero]
  have h1 : z ≠ 1 := by
    intro h1
    rw [h1] at hzd
    linarith [eight_ninth_le_dist_one]
  simp only [qZ] at h
  rcases mul_eq_zero.mp h with h' | h'
  · rcases mul_eq_zero.mp h' with h'' | h''
    · exact absurd h'' (by norm_num)
    · exact h0 h''
  · exact h1 (sub_eq_zero.mp h').symm

lemma ninth_not_mem_slitDisk (ρ : ℝ) : ninth ∉ slitDisk ρ := by
  intro h
  rcases h.2 with h2 | h2
  · exact h2 (by simp [ninth])
  · exact absurd h2 (by simp [ninth])

lemma slitDisk_mono {ρ δ : ℝ} (h : ρ ≤ δ) : slitDisk ρ ⊆ slitDisk δ := by
  intro z hz
  exact ⟨Metric.ball_subset_ball h hz.1, hz.2⟩

lemma LZ_congr_eqOn {Ω : Set ℂ} (hΩ : IsOpen Ω) {f g : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f Ω) (hg : DifferentiableOn ℂ g Ω) (h : Set.EqOn f g Ω)
    {z : ℂ} (hz : z ∈ Ω) : LZ f z = LZ g z := by
  have hz_nhds : Ω ∈ 𝓝 z := hΩ.mem_nhds hz
  have hdf : deriv f z = deriv g z := by
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards [hz_nhds] with w hw
    exact h hw
  have hderiv_eq : Set.EqOn (deriv f) (deriv g) Ω := by
    intro w hw
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards [hΩ.mem_nhds hw] with x hx
    exact h hx
  have hdd : deriv (deriv f) z = deriv (deriv g) z := by
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards [hz_nhds] with w hw
    exact hderiv_eq hw
  simp only [LZ_def]
  rw [hdf, hdd, h hz]

/-! ## the target -/

theorem local_structure_at_ninth {y9 : ℂ → ℂ} {δ : ℝ} (hY : Y9 y9 δ) {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F (slitDisk δ)) (hFL : ∀ z ∈ slitDisk δ, LZ F z = 0) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ δ ∧ ∃ κ : ℂ, ∃ hh : ℂ → ℂ,
      DifferentiableOn ℂ hh (Metric.ball ninth ρ) ∧
      (∀ z ∈ Metric.ball ninth ρ, z ≠ ninth → LZ hh z = -κ * psiZ y9 z) ∧
      (∀ z ∈ slitDisk δ ∩ Metric.ball ninth ρ,
        F z = κ * y9 z * Complex.log (z - ninth) + hh z) := by
  obtain ⟨hδpos, hδ20, hy9d, hy9ne9, hy9ode⟩ := hY
  have hcont : ContinuousAt y9 ninth :=
    (hy9d.differentiableAt (Metric.ball_mem_nhds ninth hδpos)).continuousAt
  obtain ⟨ρ₁, hρ₁pos, hρ₁sub⟩ := Metric.eventually_nhds_iff.mp (hcont.eventually_ne hy9ne9)
  set ρ : ℝ := min ρ₁ δ with hρdef
  have hρpos : 0 < ρ := by rw [hρdef]; exact lt_min hρ₁pos hδpos
  have hρδ : ρ ≤ δ := by rw [hρdef]; exact min_le_right _ _
  have hρρ₁ : ρ ≤ ρ₁ := by rw [hρdef]; exact min_le_left _ _
  have hρ9 : ρ ≤ 1 / 9 := by
    have h : (1 : ℝ) / 20 ≤ 1 / 9 := by norm_num
    linarith
  have hy9ne : ∀ z ∈ Metric.ball ninth ρ, y9 z ≠ 0 := fun z hz =>
    hρ₁sub (lt_of_lt_of_le (Metric.mem_ball.mp hz) hρρ₁)
  have hy9dρ : DifferentiableOn ℂ y9 (Metric.ball ninth ρ) :=
    hy9d.mono (Metric.ball_subset_ball hρδ)
  have hFdρ : DifferentiableOn ℂ F (slitDisk ρ) := hF.mono (slitDisk_mono hρδ)
  have hFodeρ : ∀ z ∈ slitDisk ρ,
      PZ z * deriv (deriv F) z + PZ' z * deriv F z + RZ z * F z = 0 := fun z hz =>
    (by simpa only [LZ_def] using hFL z (slitDisk_mono hρδ hz))
  have hy9odeρ : ∀ z ∈ Metric.ball ninth ρ,
      PZ z * deriv (deriv y9) z + PZ' z * deriv y9 z + RZ z * y9 z = 0 := fun z hz =>
    (by simpa only [LZ_def] using hy9ode z (Metric.ball_subset_ball hρδ hz))
  obtain ⟨κ, hh, hhd, hheq⟩ := local_structure_flip_v2 hρpos hy9dρ hy9ne hy9odeρ
    differentiable_PZ.differentiableOn (fun z _ => (deriv_PZ_local_structure_at_ninth z).symm)
    (fun z _ => PZ_eq_mul_qZ z) differentiable_qZ.differentiableOn
    (fun z hz => qZ_ne_zero_of_mem_ball hρ9 hz)
    (isOpen_slitDisk ρ) (isPreconnected_slitDisk hρpos) (fun z hz => hz.1)
    (ninth_not_mem_slitDisk ρ) (fun z hz => slitComp_slitPlane hz.2) hFdρ hFodeρ
  refine ⟨ρ, hρpos, hρδ, κ, hh, hhd, ?_, ?_⟩
  · intro z hzball hzne
    have hballo : IsOpen (Metric.ball ninth ρ) := Metric.isOpen_ball
    have hΩo : IsOpen (slitDisk ρ) := isOpen_slitDisk ρ
    have hlog_ρ : DifferentiableOn ℂ (logTerm y9) (slitDisk ρ) :=
      (differentiableOn_logTerm hy9d).mono (slitDisk_mono hρδ)
    have hGld : DifferentiableOn ℂ (fun x => F x - κ * logTerm y9 x) (slitDisk ρ) :=
      hFdρ.sub (hlog_ρ.const_mul κ)
    have heq : Set.EqOn hh (fun x => F x - κ * logTerm y9 x) (slitDisk ρ) := by
      intro w hw
      have h1 := hheq w hw
      show hh w = F w - κ * logTerm y9 w
      rw [show logTerm y9 w = y9 w * Complex.log (w - ninth) from rfl, h1]
      ring
    have hderivρ : DifferentiableOn ℂ (deriv hh) (Metric.ball ninth ρ) := hhd.deriv hballo
    have hderiv2ρ : DifferentiableOn ℂ (deriv (deriv hh)) (Metric.ball ninth ρ) :=
      hderivρ.deriv hballo
    have hLZhh_d : DifferentiableOn ℂ (fun w => LZ hh w) (Metric.ball ninth ρ) := by
      have he : (fun w => LZ hh w)
          = fun w => PZ w * deriv (deriv hh) w + PZ' w * deriv hh w + RZ w * hh w := by
        funext w; rw [LZ_def]
      rw [he]
      exact ((differentiable_PZ.differentiableOn.mul hderiv2ρ).add
        (differentiable_PZ'.differentiableOn.mul hderivρ)).add
        (differentiable_RZ.differentiableOn.mul hhd)
    have hy9deriv_d : DifferentiableOn ℂ (deriv y9) (Metric.ball ninth δ) :=
      hy9d.deriv Metric.isOpen_ball
    have hpsi_d : DifferentiableOn ℂ (fun w => psiZ y9 w) (Metric.ball ninth ρ) :=
      differentiableOn_psiZ (hy9deriv_d.mono (Metric.ball_subset_ball hρδ)) hy9dρ
    have hE_an : AnalyticOnNhd ℂ (fun w => LZ hh w + κ * psiZ y9 w) (Metric.ball ninth ρ) :=
      (hLZhh_d.add (hpsi_d.const_mul κ)).analyticOnNhd hballo
    have hE_zero : ∀ w ∈ slitDisk ρ, LZ hh w + κ * psiZ y9 w = 0 := by
      intro w hw
      have hcongr : LZ hh w = LZ (fun x => F x - κ * logTerm y9 x) w :=
        LZ_congr_eqOn hΩo (hhd.mono (fun z hz => hz.1)) hGld heq hw
      have hlin : LZ (fun x => F x - κ * logTerm y9 x) w
          = LZ F w - κ * LZ (logTerm y9) w :=
        LZ_sub_const_mul hΩo κ hFdρ hlog_ρ hw
      have hLF : LZ F w = 0 := hFL w (slitDisk_mono hρδ hw)
      have hLlog : LZ (logTerm y9) w = psiZ y9 w :=
        LZ_logTerm (y := y9) (hy9d.mono (fun z hz => hz.1))
          ((hy9d.deriv Metric.isOpen_ball).mono (fun z hz => hz.1))
          (fun w hw => hy9ode w hw.1)
          (slitDisk_mono hρδ hw)
      rw [hcongr, hlin, hLF, hLlog]
      ring
    set z0 : ℂ := ninth + (((ρ / 2 : ℝ)) : ℂ) * Complex.I with hz0def
    have hz0sub : z0 - ninth = (((ρ / 2 : ℝ)) : ℂ) * Complex.I := by
      rw [hz0def]; ring
    have hz0norm : ‖z0 - ninth‖ = ρ / 2 := by
      rw [hz0sub, norm_mul, Complex.norm_I, mul_one, norm_ofReal',
        abs_of_pos (by linarith : (0 : ℝ) < ρ / 2)]
    have hz0ball : z0 ∈ Metric.ball ninth ρ := by
      rw [Metric.mem_ball, Complex.dist_eq, hz0norm]; linarith
    have hz0slit : z0 ∈ slitDisk ρ := by
      refine ⟨hz0ball, Or.inl ?_⟩
      have hninth : ninth = ((1 / 9 : ℝ) : ℂ) := by norm_num [ninth]
      have him : z0.im = ρ / 2 := by
        rw [hz0def, hninth]
        simp [Complex.add_im, Complex.mul_im]
      rw [him]; linarith
    have hevE : (fun w => LZ hh w + κ * psiZ y9 w) =ᶠ[𝓝 z0] (fun _ => 0) := by
      filter_upwards [hΩo.mem_nhds hz0slit] with w hw
      exact hE_zero w hw
    have hEqOn := AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq hE_an
      ((differentiableOn_const (0 : ℂ)).analyticOnNhd hballo) isPreconnected_ball hz0ball hevE
    have hEz : LZ hh z + κ * psiZ y9 z = 0 := hEqOn hzball
    linear_combination hEz
  · intro z hz
    exact hheq z ⟨hz.2, hz.1.2⟩

end

end Work.A14D
