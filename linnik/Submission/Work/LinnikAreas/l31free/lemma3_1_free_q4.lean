import Mathlib
import Submission.Commons.Analysis.Complex.jensenCarleman
import Submission.Commons.NumberTheory.DirichletCharacter.completedL_divisor_le_L
import Submission.Commons.NumberTheory.DirichletCharacter.LFunction_norm_le_inv_sub_one
import Submission.Commons.NumberTheory.DirichletCharacter.LFunction_norm_ge_near_one
import Submission.Commons.NumberTheory.DirichletCharacter.diskZeroCount_two_half
import Submission.Commons.NumberTheory.Linnik.completedL_zero_strip

open Complex DirichletCharacter Metric MeasureTheory Filter
open scoped Real Topology BigOperators Interval

set_option autoImplicit false
set_option maxHeartbeats 16000000

noncomputable section

namespace Work.LinnikAreas.l31free

/-! ## A. The cosine-weighted logarithmic integral (Heath-Brown's `J`). -/

private theorem cosWeighted_logIntegral_lower {f : ℂ → ℂ} {a : ℂ} {R P Q V : ℝ} (hR : 0 < R)
    (hint : IntervalIntegrable (fun θ : ℝ => Real.cos θ *
      Real.log ‖f (a + (R : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))‖) MeasureTheory.volume 0 (2 * Real.pi))
    (hright : ∀ θ : ℝ, 0 ≤ Real.cos θ → -V ≤ Real.log ‖f (a + (R : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))‖)
    (hleft : ∀ θ : ℝ, Real.cos θ ≤ 0 →
      Real.log ‖f (a + (R : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))‖ ≤ P - Q * Real.cos θ) :
    -(2 * V) - 2 * P - (Real.pi / 2) * Q ≤
      ∫ θ in (0 : ℝ)..(2 * Real.pi),
        Real.cos θ * Real.log ‖f (a + (R : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))‖ := by
  set F : ℝ → ℝ := fun θ => Real.cos θ *
    Real.log ‖f (a + (R : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))‖ with hF
  set G : ℝ → ℝ := fun θ => max (Real.cos θ) 0 * (-V) + min (Real.cos θ) 0 * (P - Q * Real.cos θ)
    with hG
  have hπ : (0:ℝ) < Real.pi := Real.pi_pos
  have h1 : (0:ℝ) ≤ Real.pi / 2 := by positivity
  have h2 : Real.pi / 2 ≤ 3 * Real.pi / 2 := by linarith
  have h3 : 3 * Real.pi / 2 ≤ 2 * Real.pi := by linarith
  have h4 : (0:ℝ) ≤ 2 * Real.pi := by positivity
  have hpt : ∀ θ : ℝ, G θ ≤ F θ := by
    intro θ
    rcases le_or_gt 0 (Real.cos θ) with hc | hc
    · rw [hG]
      simp only [max_eq_left hc, min_eq_right hc, zero_mul, add_zero]
      simp only [hF]
      have := hright θ hc
      nlinarith
    · rw [hG]
      have hle : Real.cos θ ≤ 0 := hc.le
      simp only [max_eq_right hle, min_eq_left hle, zero_mul, zero_add]
      simp only [hF]
      have := hleft θ hle
      nlinarith
  have I1 : IntervalIntegrable F volume 0 (Real.pi / 2) :=
    hint.mono_set (by
      rw [Set.uIcc_of_le h1, Set.uIcc_of_le h4]
      exact Set.Icc_subset_Icc le_rfl (by linarith))
  have I2 : IntervalIntegrable F volume (Real.pi / 2) (3 * Real.pi / 2) :=
    hint.mono_set (by
      rw [Set.uIcc_of_le h2, Set.uIcc_of_le h4]
      exact Set.Icc_subset_Icc (by linarith) (by linarith))
  have I3 : IntervalIntegrable F volume (3 * Real.pi / 2) (2 * Real.pi) :=
    hint.mono_set (by
      rw [Set.uIcc_of_le h3, Set.uIcc_of_le h4]
      exact Set.Icc_subset_Icc (by linarith) le_rfl)
  have hcontG : Continuous G := by
    rw [hG]
    exact (Real.continuous_cos.max continuous_const).mul continuous_const |>.add
      ((Real.continuous_cos.min continuous_const).mul
        (continuous_const.sub (continuous_const.mul Real.continuous_cos)))
  have J1 : IntervalIntegrable G volume 0 (Real.pi / 2) := hcontG.intervalIntegrable _ _
  have J2 : IntervalIntegrable G volume (Real.pi / 2) (3 * Real.pi / 2) := hcontG.intervalIntegrable _ _
  have J3 : IntervalIntegrable G volume (3 * Real.pi / 2) (2 * Real.pi) := hcontG.intervalIntegrable _ _
  have J12 : IntervalIntegrable G volume (Real.pi / 2) (2 * Real.pi) := J2.trans J3
  have g1 : (∫ θ in (0:ℝ)..(Real.pi / 2), G θ) = -V := by
    have hcongr : (∫ θ in (0:ℝ)..(Real.pi / 2), G θ)
        = ∫ θ in (0:ℝ)..(Real.pi / 2), (-V * Real.cos θ) := by
      apply intervalIntegral.integral_congr
      intro θ hθ
      rw [Set.uIcc_of_le h1] at hθ
      have hc : 0 ≤ Real.cos θ :=
        Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
      rw [hG]
      simp only [max_eq_left hc, min_eq_right hc, zero_mul, add_zero]
      ring
    rw [hcongr, intervalIntegral.integral_const_mul, integral_cos, Real.sin_pi_div_two,
      Real.sin_zero, sub_zero, mul_one]
  have g3 : (∫ θ in (3 * Real.pi / 2)..(2 * Real.pi), G θ) = -V := by
    have hcongr : (∫ θ in (3 * Real.pi / 2)..(2 * Real.pi), G θ)
        = ∫ θ in (3 * Real.pi / 2)..(2 * Real.pi), (-V * Real.cos θ) := by
      apply intervalIntegral.integral_congr
      intro θ hθ
      rw [Set.uIcc_of_le h3] at hθ
      have hmem : θ - 2 * Real.pi ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) :=
        ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
      have hc : 0 ≤ Real.cos θ := by
        have hh := Real.cos_nonneg_of_mem_Icc hmem
        rwa [Real.cos_sub_two_pi] at hh
      rw [hG]
      simp only [max_eq_left hc, min_eq_right hc, zero_mul, add_zero]
      ring
    rw [hcongr, intervalIntegral.integral_const_mul, integral_cos]
    have hsin : Real.sin (3 * Real.pi / 2) = -1 := by
      have h : (3:ℝ) * Real.pi / 2 = 2 * Real.pi - Real.pi / 2 := by ring
      rw [h, Real.sin_two_pi_sub, Real.sin_pi_div_two]
    rw [hsin, Real.sin_two_pi, sub_neg_eq_add, zero_add, mul_one]
  have g2 : (∫ θ in (Real.pi / 2)..(3 * Real.pi / 2), G θ) = -2 * P - (Real.pi / 2) * Q := by
    have hcongr : (∫ θ in (Real.pi / 2)..(3 * Real.pi / 2), G θ)
        = ∫ θ in (Real.pi / 2)..(3 * Real.pi / 2),
            (P * Real.cos θ - Q * Real.cos θ ^ 2) := by
      apply intervalIntegral.integral_congr
      intro θ hθ
      rw [Set.uIcc_of_le h2] at hθ
      have hc : Real.cos θ ≤ 0 := by
        have hmem : θ - Real.pi ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) :=
          ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
        have hh := Real.cos_nonneg_of_mem_Icc hmem
        rw [Real.cos_sub_pi] at hh
        linarith
      rw [hG]
      simp only [max_eq_right hc, min_eq_left hc, zero_mul, zero_add]
      ring
    rw [hcongr]
    have hsub : (∫ θ in (Real.pi / 2)..(3 * Real.pi / 2), (P * Real.cos θ - Q * Real.cos θ ^ 2))
        = (∫ θ in (Real.pi / 2)..(3 * Real.pi / 2), P * Real.cos θ)
          - ∫ θ in (Real.pi / 2)..(3 * Real.pi / 2), Q * Real.cos θ ^ 2 :=
      intervalIntegral.integral_sub
        (f := fun θ => P * Real.cos θ) (g := fun θ => Q * Real.cos θ ^ 2)
        ((continuous_const.mul Real.continuous_cos).intervalIntegrable _ _)
        ((continuous_const.mul (Real.continuous_cos.pow 2)).intervalIntegrable _ _)
    rw [hsub]
    rw [intervalIntegral.integral_const_mul, integral_cos, intervalIntegral.integral_const_mul,
      integral_cos_sq]
    have hsin1 : Real.sin (Real.pi / 2) = 1 := Real.sin_pi_div_two
    have hsin2 : Real.sin (3 * Real.pi / 2) = -1 := by
      have h : (3:ℝ) * Real.pi / 2 = 2 * Real.pi - Real.pi / 2 := by ring
      rw [h, Real.sin_two_pi_sub, Real.sin_pi_div_two]
    have hcos1 : Real.cos (Real.pi / 2) = 0 := Real.cos_pi_div_two
    have hcos2 : Real.cos (3 * Real.pi / 2) = 0 := by
      have h : (3:ℝ) * Real.pi / 2 = 2 * Real.pi - Real.pi / 2 := by ring
      rw [h, Real.cos_two_pi_sub, Real.cos_pi_div_two]
    rw [hsin2, hsin1, hcos2, hcos1]
    ring
  have hsplitG : (∫ θ in (0:ℝ)..(2 * Real.pi), G θ)
      = (∫ θ in (0:ℝ)..(Real.pi / 2), G θ) + (∫ θ in (Real.pi / 2)..(3 * Real.pi / 2), G θ)
        + (∫ θ in (3 * Real.pi / 2)..(2 * Real.pi), G θ) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals J1 J12]
    rw [← intervalIntegral.integral_add_adjacent_intervals J2 J3]
    ring
  have hmono : (∫ θ in (0:ℝ)..(2 * Real.pi), G θ) ≤ ∫ θ in (0:ℝ)..(2 * Real.pi), F θ :=
    intervalIntegral.integral_mono h4 (hcontG.intervalIntegrable _ _) hint hpt
  have hval : (∫ θ in (0:ℝ)..(2 * Real.pi), G θ) = -V + -V + (-2 * P - (Real.pi / 2) * Q) := by
    rw [hsplitG, g1, g2, g3]
    ring
  simp only [hF] at hmono
  linarith [hmono, hval]

/-! ## B. Thresholds. -/

private lemma exists_log_threshold (K η : ℝ) (hη : 0 < η) (hK : 3 ≤ K) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      K ≤ Real.log (N:ℝ) ∧ Real.log (Real.log (N:ℝ)) ≤ η * Real.log (N:ℝ) := by
  have h1 : ∀ᶠ N : ℕ in atTop, K ≤ Real.log (N:ℝ) := by
    have h : Tendsto (fun N : ℕ => Real.log (N:ℝ)) atTop atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    exact (tendsto_atTop.1 h) K
  have h2 : ∀ᶠ N : ℕ in atTop, Real.log (Real.log (N:ℝ)) ≤ η * Real.log (N:ℝ) := by
    have hb : ∀ᶠ x : ℝ in atTop, ‖Real.log x‖ ≤ η * ‖x‖ :=
      Real.isLittleO_log_id_atTop.bound hη
    have hc : ∀ᶠ x : ℝ in atTop, ‖Real.log (Real.log x)‖ ≤ η * ‖Real.log x‖ :=
      Real.tendsto_log_atTop.eventually hb
    have hd : ∀ᶠ N : ℕ in atTop, ‖Real.log (Real.log (N:ℝ))‖ ≤ η * ‖Real.log (N:ℝ)‖ :=
      tendsto_natCast_atTop_atTop.eventually hc
    filter_upwards [hd, h1] with N hN hKN
    have hlogN : 0 ≤ Real.log (N:ℝ) := by linarith
    have h2N : Real.log (N:ℝ) ≤ ‖Real.log (N:ℝ)‖ := le_abs_self _
    have : Real.log (Real.log (N:ℝ)) ≤ η * Real.log (N:ℝ) := by
      calc Real.log (Real.log (N:ℝ)) ≤ ‖Real.log (Real.log (N:ℝ))‖ := le_abs_self _
        _ ≤ η * ‖Real.log (N:ℝ)‖ := hN
        _ = η * Real.log (N:ℝ) := by rw [Real.norm_eq_abs, abs_of_nonneg hlogN]
    exact this
  exact Filter.eventually_atTop.mp (h1.and h2)

/-! ## C. A zero-free radius. -/

private lemma divisor_eq_orderNat {f : ℂ → ℂ} {U : Set ℂ} {u : ℂ}
    (hf : AnalyticOnNhd ℂ f U) (hu : u ∈ U) :
    MeromorphicOn.divisor f U u = (analyticOrderNatAt f u : ℤ) := by
  rw [MeromorphicOn.divisor_apply (fun z hz => (hf z hz).meromorphicAt) hu,
    (hf u hu).meromorphicOrderAt_eq]
  rcases eq_or_ne (analyticOrderAt f u) ⊤ with h | h
  · rw [h]; simp [analyticOrderNatAt, h]
  · obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp h
    have h2 : analyticOrderNatAt f u = n := by rw [analyticOrderNatAt, ← hn]; simp
    rw [h2, ← hn]; simp

private lemma divisor_ne_zero_imp_eq_zero {f : ℂ → ℂ} {U : Set ℂ} {u : ℂ}
    (hf : AnalyticOnNhd ℂ f U) (hu : u ∈ U)
    (h : MeromorphicOn.divisor f U u ≠ 0) : f u = 0 := by
  rw [divisor_eq_orderNat hf hu] at h
  by_contra hne
  apply h
  have h2 : analyticOrderNatAt f u = 0 := by
    rw [analyticOrderNatAt, analyticOrderAt_eq_zero.mpr (Or.inr hne)]
    rfl
  rw [h2]; simp

private lemma GammaR_analyticAt_of_re_pos {z : ℂ} (hz : 0 < z.re) :
    AnalyticAt ℂ Complex.Gammaℝ z := by
  have hinv : Differentiable ℂ (fun s : ℂ => s.Gammaℝ⁻¹) := Complex.differentiable_Gammaℝ_inv
  have hinvz : (fun s : ℂ => s.Gammaℝ⁻¹) z ≠ 0 := by
    dsimp
    exact inv_ne_zero (Complex.Gammaℝ_ne_zero_of_re_pos hz)
  have han0 : AnalyticAt ℂ (fun s : ℂ => (s.Gammaℝ⁻¹)⁻¹) z := (hinv.analyticAt z).inv hinvz
  convert han0 with s
  · rw [inv_inv]

private lemma gammaFactor_analyticAt_of_re_pos {N : ℕ} (χ : DirichletCharacter ℂ N) {z : ℂ}
    (hz : 0 < z.re) : AnalyticAt ℂ (DirichletCharacter.gammaFactor χ) z := by
  rcases χ.even_or_odd with hE | hO
  · have hγ : DirichletCharacter.gammaFactor χ = Complex.Gammaℝ := funext fun s => hE.gammaFactor_def s
    rw [hγ]
    exact GammaR_analyticAt_of_re_pos hz
  · have hγ : DirichletCharacter.gammaFactor χ = (fun s : ℂ => Complex.Gammaℝ (s + 1)) :=
      funext fun s => hO.gammaFactor_def s
    rw [hγ]
    change AnalyticAt ℂ (fun s : ℂ => Complex.Gammaℝ (s + 1)) z
    refine AnalyticAt.comp (g := Complex.Gammaℝ) (f := fun s : ℂ => s + 1) (x := z) ?_ ?_
    · have hz1 : 0 < (z + 1).re := by simp; linarith
      exact GammaR_analyticAt_of_re_pos hz1
    · fun_prop

private lemma gammaFactor_ne_zero_of_re_pos {N : ℕ} (χ : DirichletCharacter ℂ N) {z : ℂ}
    (hz : 0 < z.re) : DirichletCharacter.gammaFactor χ z ≠ 0 := by
  rcases χ.even_or_odd with hE | hO
  · rw [hE.gammaFactor_def]
    exact Complex.Gammaℝ_ne_zero_of_re_pos hz
  · rw [hO.gammaFactor_def]
    have hz1 : 0 < (z + 1).re := by simp; linarith
    exact Complex.Gammaℝ_ne_zero_of_re_pos hz1

private lemma completedL_eq_mul_gammaFactor_of_re_pos {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {s : ℂ} (hs : 0 < s.re) :
    DirichletCharacter.completedLFunction χ s =
      DirichletCharacter.LFunction χ s * DirichletCharacter.gammaFactor χ s := by
  have hs0 : s ≠ 0 := by intro h; rw [h] at hs; simp at hs
  have h := DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ s (Or.inl hs0)
  have hG : DirichletCharacter.gammaFactor χ s ≠ 0 := gammaFactor_ne_zero_of_re_pos χ hs
  calc DirichletCharacter.completedLFunction χ s
      = (DirichletCharacter.completedLFunction χ s / DirichletCharacter.gammaFactor χ s) *
          DirichletCharacter.gammaFactor χ s := by rw [div_mul_cancel₀ _ hG]
    _ = DirichletCharacter.LFunction χ s * DirichletCharacter.gammaFactor χ s := by rw [h]

private lemma divisor_eq_divisorCompleted {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) {U : Set ℂ} {u : ℂ} (hu : u ∈ U) (hre : 0 < u.re) :
    MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) U u =
      MeromorphicOn.divisor (DirichletCharacter.LFunction χ) U u := by
  have hΛan : AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ) U :=
    fun z _ => (differentiable_completedLFunction hχ).analyticAt z
  have hLan : AnalyticOnNhd ℂ (DirichletCharacter.LFunction χ) U :=
    fun z _ => (differentiable_LFunction hχ).analyticAt z
  by_cases h0 : DirichletCharacter.completedLFunction χ u = 0
  · have hγan : AnalyticAt ℂ (DirichletCharacter.gammaFactor χ) u := gammaFactor_analyticAt_of_re_pos χ hre
    have hγ0 : DirichletCharacter.gammaFactor χ u ≠ 0 := gammaFactor_ne_zero_of_re_pos χ hre
    have hev' : {z : ℂ | 0 < z.re} ∈ 𝓝[≠] u := by
      simpa [nhdsWithin] using
        (Filter.mem_inf_of_left ((isOpen_lt continuous_const continuous_re).mem_nhds hre))
    have hfun : (fun z : ℂ => DirichletCharacter.completedLFunction χ z) =ᶠ[𝓝[≠] u]
        fun z : ℂ => DirichletCharacter.gammaFactor χ z * DirichletCharacter.LFunction χ z := by
      filter_upwards [hev'] with z hz
      rw [completedL_eq_mul_gammaFactor_of_re_pos χ hz]
      ring
    have hord : meromorphicOrderAt (DirichletCharacter.completedLFunction χ) u =
        meromorphicOrderAt (DirichletCharacter.LFunction χ) u := by
      calc meromorphicOrderAt (fun z : ℂ => DirichletCharacter.completedLFunction χ z) u
          = meromorphicOrderAt
              (fun z : ℂ => DirichletCharacter.gammaFactor χ z * DirichletCharacter.LFunction χ z) u :=
            meromorphicOrderAt_congr hfun
        _ = meromorphicOrderAt (DirichletCharacter.LFunction χ) u :=
            meromorphicOrderAt_mul_of_ne_zero hγan hγ0
    rw [MeromorphicOn.divisor_apply (fun z hz => (hΛan z hz).meromorphicAt) hu,
      MeromorphicOn.divisor_apply (fun z hz => (hLan z hz).meromorphicAt) hu, hord]
  · have hL0 : DirichletCharacter.LFunction χ u ≠ 0 := by
      intro hL
      exact h0 (by rw [completedL_eq_mul_gammaFactor_of_re_pos (s := u) χ hre, hL, zero_mul])
    have hdΛ : MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) U u = 0 := by
      rw [divisor_eq_orderNat hΛan hu]
      have h1 : analyticOrderNatAt (DirichletCharacter.completedLFunction χ) u = 0 := by
        rw [analyticOrderNatAt, analyticOrderAt_eq_zero.mpr (Or.inr h0)]
        rfl
      rw [h1]; simp
    have hdL : MeromorphicOn.divisor (DirichletCharacter.LFunction χ) U u = 0 := by
      rw [divisor_eq_orderNat hLan hu]
      have h1 : analyticOrderNatAt (DirichletCharacter.LFunction χ) u = 0 := by
        rw [analyticOrderNatAt, analyticOrderAt_eq_zero.mpr (Or.inr hL0)]
        rfl
      rw [h1]; simp
    rw [hdΛ, hdL]

private lemma LF_disc_zeroCount : ∃ c : ℝ, 0 < c ∧
    ∀ {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N), χ ≠ 1 → χ.IsPrimitive →
      ∀ (a : ℂ) (ρ : ℝ), 0 < ρ → ρ < 1 → 1 ≤ a.re → a.re ≤ 3 →
        (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.LFunction χ)
          (Metric.closedBall a ρ)) u : ℤ) : ℝ))
          ≤ c * (Real.log (‖a‖ + 3) + Real.log (N : ℝ) + 2) := by
  refine ⟨64, by norm_num, ?_⟩
  intro N _ χ hχ hχprim a ρ hρ0 hρ1 ha ha3
  have hdisk := Commons.NumberTheory.DirichletCharacter.diskZeroCount_two_half χ hχ hχprim a.im
  have hpt : ∀ u : ℂ,
      (((MeromorphicOn.divisor (DirichletCharacter.LFunction χ) (Metric.closedBall a ρ)) u : ℤ) : ℝ)
      ≤ (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
            (Metric.closedBall ((2 : ℂ) + Complex.I * (a.im : ℂ)) (5 / 2))) u : ℤ) : ℝ) := by
    intro u
    by_cases hmem : u ∈ Metric.closedBall a ρ
    · have hunorm : ‖u - a‖ ≤ ρ := by
        rw [Metric.mem_closedBall, dist_eq_norm] at hmem
        exact hmem
      have hure : 0 < u.re := by
        have h1 : |u.re - a.re| ≤ ‖u - a‖ := by
          have h := Complex.abs_re_le_norm (u - a)
          simpa [Complex.sub_re] using h
        rw [abs_le] at h1
        linarith [h1.1, hunorm, ha, hρ1]
      have hbig : u ∈ Metric.closedBall ((2 : ℂ) + Complex.I * (a.im : ℂ)) (5 / 2) := by
        have h1 : ‖u - ((2 : ℂ) + Complex.I * (a.im : ℂ))‖
            ≤ ‖u - a‖ + ‖a - ((2 : ℂ) + Complex.I * (a.im : ℂ))‖ := by
          have h := norm_add_le (u - a) (a - ((2 : ℂ) + Complex.I * (a.im : ℂ)))
          have heq : (u - a) + (a - ((2 : ℂ) + Complex.I * (a.im : ℂ)))
              = u - ((2 : ℂ) + Complex.I * (a.im : ℂ)) := by ring
          rwa [heq] at h
        have h2 : ‖a - ((2 : ℂ) + Complex.I * (a.im : ℂ))‖ = |a.re - 2| := by
          have heq : a - ((2 : ℂ) + Complex.I * (a.im : ℂ)) = ((a.re - 2 : ℝ) : ℂ) := by
            apply Complex.ext <;> simp
          rw [heq, show ‖((a.re - 2 : ℝ) : ℂ)‖ = |a.re - 2| from RCLike.norm_ofReal _]
        have h3 : |a.re - 2| ≤ 1 := by
          rw [abs_le]
          constructor <;> linarith
        rw [Metric.mem_closedBall, dist_eq_norm]
        linarith
      have h1 : ((MeromorphicOn.divisor (DirichletCharacter.LFunction χ) (Metric.closedBall a ρ)) u : ℤ)
          = ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
              (Metric.closedBall a ρ)) u : ℤ) := by
        rw [(divisor_eq_divisorCompleted χ hχ hmem hure).symm]
      have h2 : ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
            (Metric.closedBall a ρ)) u : ℤ)
          = ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
              (Metric.closedBall ((2 : ℂ) + Complex.I * (a.im : ℂ)) (5 / 2))) u : ℤ) := by
        rw [divisor_eq_orderNat (fun z _ => (differentiable_completedLFunction hχ).analyticAt z) hmem,
          divisor_eq_orderNat (fun z _ => (differentiable_completedLFunction hχ).analyticAt z) hbig]
      rw [h1, h2]
    · have h0 : ((MeromorphicOn.divisor (DirichletCharacter.LFunction χ) (Metric.closedBall a ρ)) u : ℤ) = 0 :=
        (MeromorphicOn.divisor _ _).apply_eq_zero_of_notMem hmem
      have hnn : (0:ℤ) ≤ MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (Metric.closedBall ((2 : ℂ) + Complex.I * (a.im : ℂ)) (5 / 2)) u :=
        MeromorphicOn.AnalyticOnNhd.divisor_nonneg
          (f := DirichletCharacter.completedLFunction χ)
          (U := Metric.closedBall ((2 : ℂ) + Complex.I * (a.im : ℂ)) (5 / 2))
          (fun z _ => (differentiable_completedLFunction hχ).analyticAt z) u
      rw [h0]
      exact_mod_cast hnn
  have hfin1 : Function.HasFiniteSupport (fun u : ℂ =>
      (((MeromorphicOn.divisor (DirichletCharacter.LFunction χ) (Metric.closedBall a ρ)) u : ℤ) : ℝ)) :=
    (MeromorphicOn.divisor_support_finite_of_subset
      (fun z _ => ((differentiable_LFunction hχ).analyticAt z).meromorphicAt)
      (isCompact_closedBall a ρ) subset_rfl).subset (by
        intro u hu
        rw [Function.mem_support] at hu ⊢
        intro h0
        exact hu (by rw [h0]; simp))
  have hfin2 : Function.HasFiniteSupport (fun u : ℂ =>
      (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (Metric.closedBall ((2 : ℂ) + Complex.I * (a.im : ℂ)) (5 / 2))) u : ℤ) : ℝ)) :=
    (MeromorphicOn.divisor_support_finite_of_subset
      (fun z _ => ((differentiable_completedLFunction hχ).analyticAt z).meromorphicAt)
      (isCompact_closedBall _ (5/2)) subset_rfl).subset (by
        intro u hu
        rw [Function.mem_support] at hu ⊢
        intro h0
        exact hu (by rw [h0]; simp))
  have hmain := finsum_le_finsum' hfin1 hfin2 hpt
  refine hmain.trans ?_
  have hlog1 : Real.log (2 + |a.im| + 2) ≤ Real.log (‖a‖ + 3) + Real.log 2 := by
    have h1 : 2 + |a.im| + 2 ≤ 2 * (‖a‖ + 3) := by
      have h2 : |a.im| ≤ ‖a‖ := Complex.abs_im_le_norm a
      have h5 : 0 ≤ ‖a‖ := norm_nonneg a
      linarith
    have hpos : (0:ℝ) < 2 + |a.im| + 2 := by positivity
    have h3 := Real.log_le_log hpos h1
    have h4 : Real.log (2 * (‖a‖ + 3)) = Real.log 2 + Real.log (‖a‖ + 3) :=
      Real.log_mul (by norm_num) (by positivity)
    linarith [h3, h4]
  have hlogN : 0 ≤ Real.log (N:ℝ) := by
    have h1 : (1:ℝ) ≤ (N:ℝ) := by
      exact_mod_cast (Nat.succ_le_of_lt (Nat.pos_of_ne_zero (NeZero.ne N)))
    exact Real.log_nonneg h1
  have hlogA : 0 ≤ Real.log (‖a‖ + 3) := Real.log_nonneg (by linarith [norm_nonneg a])
  have hlog2 : Real.log 2 ≤ 2 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
    linarith
  have h3h : (3/2 : ℝ) * (Real.log (N:ℝ) + Real.log (2 + |a.im| + 2)) ≤
      2 * (Real.log (N:ℝ) + Real.log (‖a‖ + 3) + 2) := by
    linarith [hlog1, hlogN, hlogA]
  linarith [hdisk, h3h, hlogN, hlogA]

/-- A zero of an entire function that is not locally zero has nonzero vanishing order. -/
private lemma analyticOrderNatAt_ne_zero_of_eq_zero {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f Set.univ) (hnz : ∃ w, f w ≠ 0) {u : ℂ} (h : f u = 0) :
    analyticOrderNatAt f u ≠ 0 := by
  intro hnat
  have hAn : AnalyticAt ℂ f u := hf u (Set.mem_univ u)
  have htop : analyticOrderAt f u ≠ ⊤ := by
    intro htop'
    rw [analyticOrderAt_eq_top] at htop'
    obtain ⟨w, hw⟩ := hnz
    exact hw (hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
      (Set.mem_univ u) htop' (Set.mem_univ w))
  rw [hAn.analyticOrderNatAt_eq_iff htop] at hnat
  obtain ⟨g, _, hgn, hge⟩ := hnat
  have hgu : f u = g u := by
    have h1 := hge.self_of_nhds
    simpa using h1
  exact hgn (hgu ▸ h)

/-- There is a radius `R' ∈ [R/2, R]` with `L(·,χ)` zero-free on the circle of radius `R'`. -/
private lemma exists_good_radius {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    (s : ℂ) {R : ℝ} (hR : 0 < R) :
    ∃ R' : ℝ, R / 2 ≤ R' ∧ R' ≤ R ∧ ∀ u : ℂ, ‖u - s‖ = R' → DirichletCharacter.LFunction χ u ≠ 0 := by
  set f : ℂ → ℂ := DirichletCharacter.LFunction χ with hfdef
  have hfan : AnalyticOnNhd ℂ f Set.univ :=
    fun z _ => (differentiable_LFunction hχ).analyticAt z
  have hnz2 : ∃ w, f w ≠ 0 :=
    ⟨2, by rw [hfdef]; exact LFunction_ne_zero_of_one_le_re χ (Or.inr (by norm_num)) (by norm_num)⟩
  have hmer : MeromorphicOn f (Metric.closedBall s R) := fun z _ => (hfan z (Set.mem_univ z)).meromorphicAt
  have hfin : (MeromorphicOn.divisor f (Metric.closedBall s R)).support.Finite :=
    MeromorphicOn.divisor_support_finite_of_subset hmer (isCompact_closedBall s R) subset_rfl
  have hzsub : ∀ u : ℂ, f u = 0 → u ∈ Metric.closedBall s R →
      u ∈ (MeromorphicOn.divisor f (Metric.closedBall s R)).support := by
    intro u hu hmem
    rw [Function.mem_support]
    rw [divisor_eq_orderNat (hfan.mono (Set.subset_univ _)) hmem]
    have hne := analyticOrderNatAt_ne_zero_of_eq_zero hfan hnz2 hu
    exact_mod_cast hne
  have himg_fin : ((fun u : ℂ => ‖u - s‖) ''
      ((MeromorphicOn.divisor f (Metric.closedBall s R)).support : Set ℂ)).Finite :=
    hfin.image _
  have hIcc_inf : (Set.Icc (R/2) R).Infinite := Set.Icc_infinite (by linarith)
  obtain ⟨R', hR'mem, hR'notmem⟩ := hIcc_inf.exists_notMem_finite himg_fin
  refine ⟨R', hR'mem.1, hR'mem.2, ?_⟩
  intro u hu henz
  have hmem : u ∈ Metric.closedBall s R := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    exact le_trans hu.le hR'mem.2
  exact hR'notmem ⟨u, hzsub u henz hmem, hu⟩

/-- Lower bound for `‖L(s,χ)‖` for `1 < Re s ≤ 2`, from the shared commons. -/
private theorem LFunction_norm_ge_near_one_aux {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {s : ℂ} (hs : 1 < s.re) (hs2 : s.re ≤ 2) :
    (s.re - 1) / 2 ≤ ‖DirichletCharacter.LFunction χ s‖ :=
  Commons.NumberTheory.DirichletCharacter.LFunction_norm_ge_near_one χ hs hs2

/-- Zero count for `L(·,χ)` in a small disc inside the half-plane `Re ≥ 1`. -/
private theorem exists_LFunction_disc_zeroCount_aux : ∃ c : ℝ, 0 < c ∧
    ∀ {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N), χ ≠ 1 → χ.IsPrimitive →
      ∀ (a : ℂ) (ρ : ℝ), 0 < ρ → ρ < 1 → 1 ≤ a.re → a.re ≤ 3 →
        (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.LFunction χ) (Metric.closedBall a ρ)) u : ℤ) : ℝ))
          ≤ c * (Real.log (‖a‖ + 3) + Real.log (N : ℝ) + 2) :=
  LF_disc_zeroCount

private lemma exists_L_threshold (K η C τ : ℝ) (hη : 0 < η) (hτ : 0 < τ) (hC : 0 ≤ C)
    (hK : 3 ≤ K) :
    ∃ L₀ : ℝ, 11 ≤ L₀ ∧ ∀ L : ℝ, L₀ ≤ L →
      K ≤ L ∧ C ≤ η * L ∧ Real.log L ≤ η * L ∧ Real.log L / L ≤ τ := by
  have hη' : 0 < min η τ := lt_min hη hτ
  have h1 : ∀ᶠ L : ℝ in atTop, K ≤ L := eventually_ge_atTop K
  have h2 : ∀ᶠ L : ℝ in atTop, C ≤ η * L := by
    have ht : Tendsto (fun L : ℝ => η * L) atTop atTop :=
      Tendsto.const_mul_atTop hη tendsto_id
    exact (tendsto_atTop.1 ht) C
  have h3 : ∀ᶠ L : ℝ in atTop, Real.log L ≤ (min η τ) * L := by
    have hb : ∀ᶠ x : ℝ in atTop, ‖Real.log x‖ ≤ (min η τ) * ‖x‖ :=
      Real.isLittleO_log_id_atTop.bound hη'
    filter_upwards [hb, eventually_ge_atTop (Real.exp 1)] with L hL hL1
    have hpos : 0 < L := lt_of_lt_of_le (Real.exp_pos 1) hL1
    have hexp1 : (1:ℝ) ≤ Real.exp 1 := by
      have h := Real.exp_le_exp.mpr (show (0:ℝ) ≤ 1 by norm_num)
      rwa [Real.exp_zero] at h
    have hlogpos : 0 ≤ Real.log L := Real.log_nonneg (le_trans hexp1 hL1)
    rw [Real.norm_eq_abs, abs_of_nonneg hlogpos, Real.norm_eq_abs, abs_of_nonneg hpos.le] at hL
    exact hL
  obtain ⟨a, ha⟩ := eventually_atTop.mp (h1.and (h2.and h3))
  refine ⟨max a 11, le_max_right _ _, ?_⟩
  intro L hL
  have haL : a ≤ L := le_trans (le_max_left _ _) hL
  have h11 : (11:ℝ) ≤ L := le_trans (le_max_right _ _) hL
  obtain ⟨hKL, hCL, hlog⟩ := ha L haL
  have hLpos : 0 < L := by linarith
  refine ⟨hKL, hCL, le_trans hlog (mul_le_mul_of_nonneg_right (min_le_left _ _) hLpos.le), ?_⟩
  rw [div_le_iff₀ hLpos]
  exact le_trans hlog (mul_le_mul_of_nonneg_right (min_le_right _ _) hLpos.le)

private lemma three_le_of_char_ne_one {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) : (3 : ℝ) ≤ (N : ℝ) := by
  have hN : 3 ≤ N := by
    by_contra h
    have hN2 : N ≤ 2 := by omega
    have hχne : ¬ (∀ a : (ZMod N)ˣ, χ ↑a = (1 : DirichletCharacter ℂ N) ↑a) := by
      intro hh
      exact hχ (MulChar.ext hh)
    push Not at hχne
    rcases hχne with ⟨a, hne⟩
    have hs : Subsingleton (ZMod N)ˣ := by
      have hN1 : 1 ≤ N := by exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne N))
      interval_cases N <;> infer_instance
    have ha : a = 1 := Subsingleton.elim a 1
    subst a
    simp at hne
  exact_mod_cast hN

/-- **Heath-Brown's Lemma 3.1, restricted to characters of order dividing `4`.**

This is verbatim `Submission/Work/LinnikAreas/l31free/lemma3_1_free_gen_real.lean` (itself the
proved `Work.LinnikAreas.l31free.lemma3_1_free_gen` with the extra hypothesis `χ ^ 2 = 1` threaded
through the single use of `hbound`), except that the hypothesis is `χ ^ 4 = 1` instead of
`χ ^ 2 = 1` — again added in exactly two places, the `hbound` slot and the conclusion (plus the
localized helper `hCbb`, which is applied exactly once, at the concluding `χ`).

The need for this variant: HB Lemma 2.5 with exponent `φ = 1/4` holds for every character of order
dividing `4` (order `≤ 4` is an absolute constant, so the order factor `(orderOf χ)^{3/(2k)}` of
HB §2 is bounded), whereas `lemma3_1_free_gen` insists on the hypothesis `χ ^ 2 = 1` (order `≤ 2`).
The proof is unchanged because the hypothesis is only threaded through; see
`lemma3_1_free_gen_real` for the identical construction with `2` in place of `4`. -/
theorem lemma3_1_free_q4 {φ : ℝ} (hφ : 0 < φ) {ε : ℝ} (hε : 0 < ε)
    (hbound : ∀ k : ℕ, 3 ≤ k → ∀ ε' : ℝ, 0 < ε' → ∃ Cb : ℝ, 0 < Cb ∧
      ∀ {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N), χ ≠ 1 → χ ^ 4 = 1 →
        ∀ σ t : ℝ, 1 - 1/(k:ℝ) ≤ σ → σ ≤ 1 + Real.log (Real.log (N:ℝ)) / Real.log (N:ℝ) →
          ‖DirichletCharacter.LFunction χ ((σ:ℂ) + (t:ℂ) * Complex.I)‖
            ≤ Cb * (N:ℝ) ^ (φ * (1 - σ) * (1 + 1/(k:ℝ)) + ε') * (1 + |t|)) :
    ∃ L₀ : ℝ, ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧
      ∀ {N : ℕ} [NeZero N], 3 ≤ N →
          ∀ (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive), χ ^ 4 = 1 →
        ∀ {L : ℝ}, L₀ ≤ L → Real.log (N:ℝ) ≤ L →
        ∀ s : ℂ, 1 + 1 / (L * Real.log L) ≤ s.re →
          s.re ≤ 1 + Real.log L / L → |s.im| ≤ 10 * L →
          (-logDeriv (DirichletCharacter.LFunction χ) s).re
            + (∑ᶠ u : ℂ, ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) (Metric.closedBall 0 (|s.im| + 2))) u : ℤ) *
                (if ‖(1:ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ then ((1/(s-u)).re) else 0))
            ≤ (φ/2 + ε) * L := by
  have hφpos : 0 < φ := hφ
  -- choose k
  obtain ⟨k, hk3, hk⟩ : ∃ k : ℕ, 3 ≤ k ∧ 4 * φ / ε ≤ (k:ℝ) := by
    obtain ⟨n, hn⟩ := exists_nat_ge (max (3:ℝ) (4 * φ / ε))
    refine ⟨n, ?_, ?_⟩
    · have h : (3:ℝ) ≤ (n:ℝ) := le_trans (le_max_left _ _) hn
      exact_mod_cast h
    · exact le_trans (le_max_right _ _) hn
  have hkR3 : (3:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk3
  have hkRpos : (0:ℝ) < (k:ℝ) := by linarith
  set ε' : ℝ := ε / (64 * (k:ℝ)) with hε'def
  have hε'pos : 0 < ε' := by rw [hε'def]; positivity
  obtain ⟨Cb₀, hCb₀pos, hCb₀⟩ := hbound k hk3 ε' hε'pos
  set Cb : ℝ := max Cb₀ 1 with hCbdef
  have hCb1 : 1 ≤ Cb := le_max_right _ _
  have hCbpos : 0 < Cb := lt_of_lt_of_le one_pos hCb1
  have hCbb : ∀ {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N), χ ≠ 1 → χ ^ 4 = 1 →
      ∀ σ t : ℝ, 1 - 1/(k:ℝ) ≤ σ → σ ≤ 1 + Real.log (Real.log (N:ℝ)) / Real.log (N:ℝ) →
        ‖DirichletCharacter.LFunction χ ((σ:ℂ) + (t:ℂ) * Complex.I)‖
          ≤ Cb * (N:ℝ) ^ (φ * (1 - σ) * (1 + 1/(k:ℝ)) + ε') * (1 + |t|) := by
    intro N _ χ hχ hχ2 σ t h1 h2
    have h := hCb₀ χ hχ hχ2 σ t h1 h2
    have hle : Cb₀ ≤ Cb := le_max_left _ _
    have h3 : 0 ≤ (N:ℝ) ^ (φ * (1 - σ) * (1 + 1/(k:ℝ)) + ε') * (1 + |t|) := by positivity
    have h4 : Cb₀ * (N:ℝ) ^ (φ * (1 - σ) * (1 + 1/(k:ℝ)) + ε') * (1 + |t|)
        ≤ Cb * (N:ℝ) ^ (φ * (1 - σ) * (1 + 1/(k:ℝ)) + ε') * (1 + |t|) := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hle (by positivity)) (by positivity)
    linarith only [h, h4]
  obtain ⟨c0, hc0pos, hc0⟩ := exists_LFunction_disc_zeroCount_aux
  -- constants
  set η : ℝ := min (1/(8*(k:ℝ)))
      (min 1 (min (ε/(1024*(c0+1)*((k:ℝ)+1)^2)) (Real.pi*ε/(4096*(k:ℝ))))) with hηdef
  have hηpos : 0 < η := by
    rw [hηdef]
    refine lt_min (by positivity) (lt_min one_pos (lt_min (by positivity) (by positivity)))
  have hη_k : η ≤ 1/(8*(k:ℝ)) := by rw [hηdef]; exact min_le_left _ _
  have hη_1 : η ≤ 1 := le_trans (min_le_right _ _) (min_le_left _ _)
  have hη_a : η ≤ ε/(1024*(c0+1)*((k:ℝ)+1)^2) :=
    le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hη_b : η ≤ Real.pi*ε/(4096*(k:ℝ)) :=
    le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  set K : ℝ := max 5 (max (Real.log 2 / η) (max (Real.log Cb / η) (1/η))) with hKdef
  have hK5 : 5 ≤ K := by rw [hKdef]; exact le_max_left _ _
  have hK3 : 3 ≤ K := le_trans (by norm_num) hK5
  have hK_log2 : Real.log 2 ≤ η * K := by
    have h : Real.log 2 / η ≤ K := le_trans (le_max_left _ _) (le_max_right _ _)
    rw [div_le_iff₀ hηpos] at h; linarith
  have hK_Cb : Real.log Cb ≤ η * K := by
    have h : Real.log Cb / η ≤ K := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
    rw [div_le_iff₀ hηpos] at h; linarith
  have hK_1 : 1 ≤ η * K := by
    have h : 1 / η ≤ K :=
      le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
    rw [div_le_iff₀ hηpos] at h; linarith
  set R : ℝ := 1/(k:ℝ) with hRdef
  have hRpos : 0 < R := by rw [hRdef]; positivity
  have hRle : R ≤ 1/3 := by
    rw [hRdef, div_le_div_iff₀ hkRpos (by norm_num : (0:ℝ) < 3)]
    linarith
  have hphiRpos : 0 < φ * (1 + R) := by positivity
  have hd0pos : 0 < Real.log (Real.log 3) := by
    apply Real.log_pos
    rw [← Real.log_exp 1]
    exact Real.log_lt_log (Real.exp_pos 1) (by linarith only [Real.exp_one_lt_three])
  set C₀ : ℝ := Real.log (1 + 1 / Real.log (Real.log 3)) with hC₀def
  have hC₀nn : 0 ≤ C₀ := by
    rw [hC₀def]
    apply Real.log_nonneg
    have : 0 ≤ 1 / Real.log (Real.log 3) := by positivity
    linarith
  obtain ⟨L₀, hL₀11, hL₀⟩ := exists_L_threshold K η C₀ (ε' / (φ * (1 + R))) hηpos
    (div_pos hε'pos hphiRpos) hC₀nn hK3
  set δ : ℝ := min (R/4) (ε/(256*c0*(k:ℝ)^2)) with hδdef
  have hδpos : 0 < δ := by
    rw [hδdef]; exact lt_min (by positivity) (by positivity)
  have hδ_R : δ ≤ R/4 := by rw [hδdef]; exact min_le_left _ _
  have hδ_ε : δ ≤ ε/(256*c0*(k:ℝ)^2) := by rw [hδdef]; exact min_le_right _ _
  have hδ_lt1 : δ < 1 := by
    have h1 : R/4 < 1 := by linarith only [hRle]
    linarith
  refine ⟨L₀, δ, hδpos, hδ_lt1, ?_⟩
  intro N hNe hN3 χ hχ hχprim hχ2 L hL₀le hNL s hs1 hs2 hs3
  -- thresholds in `L`
  obtain ⟨hK_le_L, hC₀le, hlogL, hlogLdivτ⟩ := hL₀ L hL₀le
  have hL11 : (11:ℝ) ≤ L := le_trans hL₀11 hL₀le
  have hL5 : (5:ℝ) ≤ L := by linarith
  have hL3 : 3 ≤ L := by linarith
  have hLpos : 0 < L := by linarith
  have hL1 : 1 ≤ L := by linarith
  have hlog2 : Real.log 2 ≤ η * L := le_trans hK_log2 (by
    have := mul_le_mul_of_nonneg_left hK_le_L hηpos.le; linarith)
  have hlogCb : Real.log Cb ≤ η * L := le_trans hK_Cb (by
    have := mul_le_mul_of_nonneg_left hK_le_L hηpos.le; linarith)
  have hone : 1 ≤ η * L := le_trans hK_1 (by
    have := mul_le_mul_of_nonneg_left hK_le_L hηpos.le; linarith)
  have hlogLdiv : Real.log L / L ≤ 1/(8*(k:ℝ)) := by
    rw [div_le_iff₀ hLpos]
    exact le_trans hlogL (mul_le_mul_of_nonneg_right hη_k hLpos.le)
  have hlog3 : 0 < Real.log L := Real.log_pos (by linarith)
  -- conduit / threshold constants
  have hNpos : (0:ℝ) < (N:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hlog3gt1 : (1:ℝ) < Real.log 3 := by
    rw [← Real.log_exp 1]
    exact Real.log_lt_log (Real.exp_pos 1) (by linarith only [Real.exp_one_lt_three])
  have hlogN1 : 1 < Real.log (N:ℝ) := by
    have h1 : Real.log 3 ≤ Real.log (N:ℝ) :=
      Real.log_le_log (by norm_num) (by exact_mod_cast hN3)
    linarith
  have hlogMpos : 0 < Real.log (Real.log (N:ℝ)) := Real.log_pos hlogN1
  set cN : ℝ := Real.log (Real.log (N:ℝ)) / Real.log (N:ℝ) with hcNdef
  have hcNpos : 0 < cN := by
    rw [hcNdef]; exact div_pos hlogMpos (by linarith)
  set K₀ : ℝ := Real.log (1 + 1 / cN) with hK₀def
  have hK₀nn : 0 ≤ K₀ := by
    rw [hK₀def]
    apply Real.log_nonneg
    have : 0 ≤ 1 / cN := by positivity
    linarith
  have hK₀bound : K₀ ≤ Real.log L + C₀ := by
    have hd0pos' : 0 < Real.log (Real.log 3) := hd0pos
    have hMge3 : Real.log 3 ≤ Real.log (N:ℝ) :=
      Real.log_le_log (by norm_num) (by exact_mod_cast hN3)
    have hlogMge : Real.log (Real.log 3) ≤ Real.log (Real.log (N:ℝ)) :=
      Real.log_le_log (by linarith only [hlog3gt1]) hMge3
    have hM1 : 1 ≤ Real.log (N:ℝ) := le_of_lt hlogN1
    have h1 : 1 + 1 / cN ≤ 1 + Real.log (N:ℝ) / Real.log (Real.log 3) := by
      rw [hcNdef]
      have hinv : 1 / Real.log (Real.log (N:ℝ)) ≤ 1 / Real.log (Real.log 3) :=
        one_div_le_one_div_of_le hd0pos' hlogMge
      have hmul := mul_le_mul_of_nonneg_left hinv (by linarith : (0:ℝ) ≤ Real.log (N:ℝ))
      have heq1 : (Real.log (N:ℝ)) * (1 / Real.log (Real.log 3))
          = Real.log (N:ℝ) / Real.log (Real.log 3) := by ring
      have heq2 : (Real.log (N:ℝ)) * (1 / Real.log (Real.log (N:ℝ)))
          = Real.log (N:ℝ) / Real.log (Real.log (N:ℝ)) := by ring
      have hdiv : 1 / (Real.log (Real.log (N:ℝ)) / Real.log (N:ℝ))
          = Real.log (N:ℝ) / Real.log (Real.log (N:ℝ)) := by rw [one_div_div]
      rw [hdiv, heq1.symm, heq2.symm] at *
      linarith only [hmul]
    have h2 : 1 + Real.log (N:ℝ) / Real.log (Real.log 3)
        ≤ (1 + 1 / Real.log (Real.log 3)) * Real.log (N:ℝ) := by
      have h3 : (1 + 1 / Real.log (Real.log 3)) * Real.log (N:ℝ)
          = Real.log (N:ℝ) + Real.log (N:ℝ) / Real.log (Real.log 3) := by ring
      rw [h3]; linarith only [hM1]
    have h4 : Real.log (1 + 1 / cN)
        ≤ Real.log ((1 + 1 / Real.log (Real.log 3)) * Real.log (N:ℝ)) :=
      Real.log_le_log (by positivity) (by linarith only [h1, h2])
    have h5 : Real.log ((1 + 1 / Real.log (Real.log 3)) * Real.log (N:ℝ))
        = Real.log (1 + 1 / Real.log (Real.log 3)) + Real.log (Real.log (N:ℝ)) :=
      Real.log_mul (by positivity) (ne_of_gt (by linarith : (0:ℝ) < Real.log (N:ℝ)))
    have h6 : Real.log (Real.log (N:ℝ)) ≤ Real.log L :=
      Real.log_le_log (by linarith : (0:ℝ) < Real.log (N:ℝ)) hNL
    rw [hK₀def, hC₀def]
    linarith only [h4, h5, h6]
  set σ : ℝ := s.re with hσdef
  set t : ℝ := s.im with htdef
  have hσ1 : 1 < σ := by
    have hden : 0 < L * Real.log L := mul_pos hLpos hlog3
    have hpos : 0 < 1 / (L * Real.log L) := by positivity
    linarith only [hs1, hpos]
  have hσle : σ ≤ 1 + Real.log L / L := hs2
  have htabs : |t| ≤ 10 * L := hs3
  -- good radius and Carleman's formula
  obtain ⟨R', hR'ge, hR'le, hR'good⟩ := exists_good_radius χ hχ s hRpos
  have hR'pos : 0 < R' := lt_of_lt_of_le (by positivity : (0:ℝ) < R/2) hR'ge
  have hR'le1 : R' ≤ 1 := by
    have h1 : R ≤ 1 := by linarith only [hRle]
    linarith only [hR'le, h1]
  have hR'few : (R')⁻¹ ≤ 2 * R⁻¹ := by
    have hR2 : 0 < R / 2 := by positivity
    have h1 : (R')⁻¹ ≤ (R / 2)⁻¹ := (inv_le_inv₀ hR'pos hR2).mpr (by linarith only [hR'ge])
    have h2 : (R / 2)⁻¹ = 2 * R⁻¹ := by rw [inv_div]; ring
    linarith only [h1, h2]
  have hfan : AnalyticOnNhd ℂ (DirichletCharacter.LFunction χ) (Metric.closedBall s |R'|) :=
    fun z _ => (differentiable_LFunction hχ).analyticAt z
  have hsne : s ≠ 1 := by
    intro h
    have h1 : σ = 1 := by rw [hσdef, h]; simp
    linarith only [hσ1, h1]
  have hfs : DirichletCharacter.LFunction χ s ≠ 0 :=
    LFunction_ne_zero_of_one_le_re χ (Or.inr hsne) hσ1.le
  have hJC := Commons.Analysis.Complex.jensenCarleman (a := s) (R := R') hR'pos hfan hfs hR'good
  -- the circle point
  have hexp : ∀ θ : ℝ, Complex.exp (Complex.I * (θ:ℂ)) = (Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I := by
    intro θ
    have h : Complex.I * (θ:ℂ) = ((θ:ℝ):ℂ) * Complex.I := by push_cast; ring
    rw [h, Complex.exp_ofReal_mul_I]
  have hexp_re : ∀ θ : ℝ, (Complex.exp (Complex.I * (θ:ℂ))).re = Real.cos θ := by
    intro θ
    rw [hexp θ]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.I_re,
      Complex.I_im, mul_zero, mul_one, sub_zero, add_zero]
  have hexp_im : ∀ θ : ℝ, (Complex.exp (Complex.I * (θ:ℂ))).im = Real.sin θ := by
    intro θ
    rw [hexp θ]
    simp only [Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_im, Complex.I_re,
      Complex.I_im, mul_zero, mul_one, zero_add, add_zero, zero_sub, sub_zero]
  have hcirc_re : ∀ θ : ℝ, (s + (R':ℂ) * Complex.exp (Complex.I * (θ:ℂ))).re = σ + R' * Real.cos θ := by
    intro θ
    rw [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, hexp_re θ, hexp_im θ,
      hσdef]
    ring
  have hcirc_im : ∀ θ : ℝ, (s + (R':ℂ) * Complex.exp (Complex.I * (θ:ℂ))).im = t + R' * Real.sin θ := by
    intro θ
    rw [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, hexp_re θ, hexp_im θ,
      htdef]
    ring
  have hcirc_eq : ∀ θ : ℝ, s + (R':ℂ) * Complex.exp (Complex.I * (θ:ℂ)) =
      ((σ + R' * Real.cos θ : ℝ) : ℂ) + ((t + R' * Real.sin θ : ℝ) : ℂ) * Complex.I := by
    intro θ
    apply Complex.ext
    · rw [hcirc_re θ]
      simp only [Complex.add_re, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.I_re,
        Complex.I_im, mul_zero, mul_one, sub_zero, add_zero]
    · rw [hcirc_im θ]
      simp only [Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_im, Complex.I_re,
        Complex.I_im, mul_zero, mul_one, zero_add, add_zero, sub_zero]
  have hcirc_norm : ∀ θ : ℝ, ‖s + (R':ℂ) * Complex.exp (Complex.I * (θ:ℂ)) - s‖ = R' := by
    intro θ
    have hexpnorm : ‖Complex.exp (Complex.I * (θ:ℂ))‖ = 1 := by
      rw [Complex.norm_exp]
      have h1 : (Complex.I * (θ:ℂ)).re = 0 := by simp [Complex.mul_re, Complex.I_re, Complex.I_im]
      rw [h1, Real.exp_zero]
    rw [add_sub_cancel_left, norm_mul, show ‖(R':ℂ)‖ = |R'| from RCLike.norm_ofReal R',
      abs_of_pos hR'pos, hexpnorm, mul_one]
  -- bounds needed for the weighted integral
  have hlogden_pos : 0 < 2 * L * Real.log L := by positivity
  set V : ℝ := Real.log (2 * L * Real.log L) with hVdef
  set Pc : ℝ := Real.log Cb + φ * (1 + 1/(k:ℝ)) * (1 - σ) * L + ε' * L + Real.log (10 * L + 2) with hPcdef
  set Qc : ℝ := φ * (1 + 1/(k:ℝ)) * R' * L with hQcdef
  have hLlog_pos : 0 < L * Real.log L := mul_pos hLpos hlog3
  have hsig1 : 1 / (L * Real.log L) ≤ σ - 1 := by linarith only [hs1]
  set Pstar : ℝ := max Pc K₀ with hPstardef
  have hInt : (∫ θ in (0:ℝ)..(2*Real.pi), Real.cos θ * Real.log ‖DirichletCharacter.LFunction χ (s + (R':ℂ) * Complex.exp (Complex.I * (θ:ℂ)))‖)
      ≥ -(2*V) - 2*Pstar - (Real.pi/2)*Qc := by
    refine cosWeighted_logIntegral_lower hR'pos ?hint ?hright ?hleft
    · have hcont : Continuous (fun θ : ℝ => DirichletCharacter.LFunction χ (s + (R':ℂ) * Complex.exp (Complex.I * (θ:ℂ)))) :=
        (differentiable_LFunction hχ).continuous.comp (by fun_prop)
      have hnz : ∀ θ : ℝ, DirichletCharacter.LFunction χ (s + (R':ℂ) * Complex.exp (Complex.I * (θ:ℂ))) ≠ 0 :=
        fun θ => hR'good _ (hcirc_norm θ)
      exact (Real.continuous_cos.mul (hcont.norm.log (fun θ => norm_ne_zero_iff.mpr (hnz θ)))).intervalIntegrable _ _
    · intro θ hcos
      have hre1 : 1 < (s + (R':ℂ) * Complex.exp (Complex.I * (θ:ℂ))).re := by
        rw [hcirc_re θ]; linarith only [hσ1, mul_nonneg hR'pos.le hcos]
      have hre2 : (s + (R':ℂ) * Complex.exp (Complex.I * (θ:ℂ))).re ≤ 2 := by
        rw [hcirc_re θ]
        have h1 : R' * Real.cos θ ≤ R' := mul_le_of_le_one_right hR'pos.le (Real.cos_le_one θ)
        have h2 : R' ≤ 1/(k:ℝ) := by linarith only [hR'le, hRdef]
        have h3 : (1:ℝ)/(8*(k:ℝ)) + 1/(k:ℝ) ≤ 1 := by
          rw [show (1:ℝ)/(8*(k:ℝ)) + 1/(k:ℝ) = 9/(8*(k:ℝ)) by field_simp; ring]
          rw [div_le_one (by positivity)]
          linarith only [hkR3]
        linarith only [hσle, hlogLdiv, h1, h2, h3]
      have hlow := LFunction_norm_ge_near_one_aux χ hre1 hre2
      have hmid : (1:ℝ) / (2 * L * Real.log L) ≤ ((s + (R':ℂ) * Complex.exp (Complex.I * (θ:ℂ))).re - 1) / 2 := by
        rw [hcirc_re θ]
        have h1 : σ - 1 ≤ σ + R' * Real.cos θ - 1 := by linarith only [mul_nonneg hR'pos.le hcos]
        have h2 : 1 / (2 * (L * Real.log L)) ≤ (σ - 1) / 2 := by
          rw [div_le_div_iff₀ (by positivity) (by norm_num)]
          have h4 : 1 ≤ (σ - 1) * (L * Real.log L) := by
            have h5 := hsig1
            rw [div_le_iff₀ hLlog_pos] at h5
            linarith only [h5]
          nlinarith only [h4, hLlog_pos]
        have h3 : (1:ℝ) / (2 * L * Real.log L) = 1 / (2 * (L * Real.log L)) := by ring
        rw [h3]
        linarith only [h1, h2]
      have hlog1 : Real.log (1 / (2 * L * Real.log L)) = -V := by
        rw [hVdef, one_div, Real.log_inv]
      calc -V = Real.log (1 / (2 * L * Real.log L)) := hlog1.symm
        _ ≤ Real.log (((s + (R':ℂ) * Complex.exp (Complex.I * (θ:ℂ))).re - 1) / 2) :=
            Real.log_le_log (by positivity) hmid
        _ ≤ Real.log ‖DirichletCharacter.LFunction χ (s + (R':ℂ) * Complex.exp (Complex.I * (θ:ℂ)))‖ :=
            Real.log_le_log (by positivity) hlow
    · intro θ hcos
      by_cases hreg : σ + R' * Real.cos θ ≤ 1 + cN
      · -- Region I: the Burgess bound applies
        have hσ1' : 1 - 1/(k:ℝ) ≤ σ + R' * Real.cos θ := by
          have h1 : -1 ≤ Real.cos θ := Real.neg_one_le_cos θ
          have h2 : -R' ≤ R' * Real.cos θ := by nlinarith only [h1, hR'pos.le]
          have h3 : R = 1/(k:ℝ) := hRdef
          linarith only [hR'le, h3, hσ1, h2]
        have hσ2' : σ + R' * Real.cos θ ≤ 1 + Real.log (Real.log (N:ℝ)) / Real.log (N:ℝ) := by
          rw [hcNdef] at hreg; exact hreg
        have hb := hCbb χ hχ hχ2 (σ + R' * Real.cos θ) (t + R' * Real.sin θ) hσ1' hσ2'
        rw [← hcirc_eq θ] at hb
        have h1t : 0 < 1 + |t + R' * Real.sin θ| := by positivity
        have hrpowzn : (N:ℝ) ^ (φ * (1 - (σ + R' * Real.cos θ)) * (1 + R) + ε') ≠ 0 := by
          positivity
        have he_nn : 0 ≤ φ * (1 - (σ + R' * Real.cos θ)) * (1 + R) + ε' := by
          rw [show φ * (1 - (σ + R' * Real.cos θ)) * (1 + R) + ε'
              = φ * (1 + R) * (1 - (σ + R' * Real.cos θ)) + ε' by ring]
          have h5 : -(Real.log L / L) ≤ 1 - (σ + R' * Real.cos θ) := by
            have h2 : 1 - (σ + R' * Real.cos θ) = (1 - σ) + -(R' * Real.cos θ) := by ring
            have h3 : 0 ≤ -(R' * Real.cos θ) := neg_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos hR'pos.le hcos)
            have h4 : -(Real.log L / L) ≤ 1 - σ := by linarith only [hσle]
            linarith only [h2, h3, h4]
          have h5b : φ * (1 + R) * (-(Real.log L / L))
              ≤ φ * (1 + R) * (1 - (σ + R' * Real.cos θ)) :=
            mul_le_mul_of_nonneg_left h5 (by positivity)
          have h6 : φ * (1 + R) * (Real.log L / L) ≤ ε' := by
            have h7 : 0 ≤ φ * (1 + R) := by positivity
            calc φ * (1 + R) * (Real.log L / L)
                ≤ φ * (1 + R) * (ε' / (φ * (1 + R))) :=
                  mul_le_mul_of_nonneg_left hlogLdivτ h7
              _ = ε' := by field_simp
          have h7 : φ * (1 + R) * (-(Real.log L / L))
              = -(φ * (1 + R) * (Real.log L / L)) := by ring
          linarith only [h5b, h6, h7]
        have hlogineq : Real.log ‖DirichletCharacter.LFunction χ (s + (R':ℂ) * Complex.exp (Complex.I * (θ:ℂ)))‖ ≤
            Real.log Cb + (φ * (1 - (σ + R' * Real.cos θ)) * (1 + R) + ε') * L + Real.log (10 * L + 2) := by
          have h := Real.log_le_log (norm_pos_iff.mpr (hR'good _ (hcirc_norm θ))) hb
          rw [Real.log_mul (by positivity : Cb * (N:ℝ) ^ (φ * (1 - (σ + R' * Real.cos θ)) * (1 + R) + ε') ≠ 0)
              (ne_of_gt h1t),
            Real.log_mul (ne_of_gt hCbpos) hrpowzn, Real.rpow_def_of_pos hNpos,
            Real.log_exp] at h
          have hMle : (φ * (1 - (σ + R' * Real.cos θ)) * (1 + R) + ε') * Real.log (N:ℝ)
              ≤ (φ * (1 - (σ + R' * Real.cos θ)) * (1 + R) + ε') * L :=
            mul_le_mul_of_nonneg_left hNL he_nn
          have hlogt' : Real.log (1 + |t + R' * Real.sin θ|) ≤ Real.log (10 * L + 2) := by
            apply Real.log_le_log (by positivity)
            have h1 : R' * Real.sin θ ≤ R' := mul_le_of_le_one_right hR'pos.le (Real.sin_le_one θ)
            have h2 : -R' ≤ R' * Real.sin θ := by
              nlinarith only [hR'pos.le, Real.neg_one_le_sin θ]
            have h3 : |t + R' * Real.sin θ| ≤ 10 * L + 1 := by
              have ht1 : t ≤ 10 * L := (abs_le.mp htabs).2
              have ht2 : -(10 * L) ≤ t := (abs_le.mp htabs).1
              have hR'1 : R' ≤ 1 := hR'le1
              rw [abs_le]
              constructor
              · linarith only [ht1, ht2, h1, h2, hR'1]
              · linarith only [ht1, ht2, h1, h2, hR'1]
            linarith only [h3]
          linarith only [h, hMle, hlogt']
        have hexpand : (φ * (1 - (σ + R' * Real.cos θ)) * (1 + R) + ε') * L
            = φ * (1 + R) * (1 - σ) * L + ε' * L - Qc * Real.cos θ := by
          rw [hQcdef]; ring
        rw [hexpand] at hlogineq
        have hPceq : Real.log Cb + (φ * (1 + R) * (1 - σ) * L + ε' * L - Qc * Real.cos θ)
              + Real.log (10 * L + 2) = Pc - Qc * Real.cos θ := by
          rw [hPcdef, hRdef]; ring
        have hPclt : Pc - Qc * Real.cos θ ≤ Pstar - Qc * Real.cos θ := by
          have h1 : Pc ≤ Pstar := by rw [hPstardef]; exact le_max_left _ _
          linarith only [h1]
        linarith only [hlogineq, hPceq, hPclt]
      · -- Region II: the Euler product / zeta upper bound
        push Not at hreg
        have hσ'1 : 1 < σ + R' * Real.cos θ := by linarith only [hreg, hcNpos]
        have hζ := Commons.NumberTheory.DirichletCharacter.LFunction_norm_le_inv_sub_one χ (σ := σ + R' * Real.cos θ)
          (T := t + R' * Real.sin θ) hσ'1
        have hceq : s + (R':ℂ) * Complex.exp (Complex.I * (θ:ℂ))
            = ((σ + R' * Real.cos θ : ℝ) : ℂ)
              + Complex.I * ((t + R' * Real.sin θ : ℝ) : ℂ) := by
          rw [hcirc_eq θ]; ring
        have hlogζ : Real.log ‖DirichletCharacter.LFunction χ (s + (R':ℂ) * Complex.exp (Complex.I * (θ:ℂ)))‖
            ≤ K₀ := by
          have h1 : Real.log ‖DirichletCharacter.LFunction χ (s + (R':ℂ) * Complex.exp (Complex.I * (θ:ℂ)))‖
              ≤ Real.log (1 + 1 / (σ + R' * Real.cos θ - 1)) := by
            have hpos : 0 < ‖DirichletCharacter.LFunction χ (s + (R':ℂ) * Complex.exp (Complex.I * (θ:ℂ)))‖ :=
              norm_pos_iff.mpr (hR'good _ (hcirc_norm θ))
            rw [hceq] at hpos ⊢
            exact Real.log_le_log hpos hζ
          have h2 : Real.log (1 + 1 / (σ + R' * Real.cos θ - 1)) ≤ Real.log (1 + 1 / cN) := by
            apply Real.log_le_log (by positivity)
            have h3 : 1 / (σ + R' * Real.cos θ - 1) ≤ 1 / cN :=
              one_div_le_one_div_of_le hcNpos (by linarith only [hreg])
            linarith only [h3]
          rw [hK₀def]; linarith only [h1, h2]
        have hPstarge : K₀ ≤ Pstar - Qc * Real.cos θ := by
          have h1 : K₀ ≤ Pstar := by rw [hPstardef]; exact le_max_right _ _
          have h2 : 0 ≤ -Qc * Real.cos θ := by
            have h3 : 0 ≤ Qc := by rw [hQcdef]; positivity
            nlinarith only [h3, hcos]
          linarith only [h1, h2]
        linarith only [hlogζ, hPstarge]

  -- ================= divisor sums =================
  rw [abs_of_pos hR'pos] at hJC
  set Intg : ℝ := ∫ θ in (0:ℝ)..(2*Real.pi), Real.cos θ * Real.log ‖DirichletCharacter.LFunction χ (s + (R':ℂ) * Complex.exp (Complex.I * (θ:ℂ)))‖ with hIntgdef
  have hdivfinL : (MeromorphicOn.divisor (DirichletCharacter.LFunction χ) (Metric.closedBall s R')).support.Finite :=
    MeromorphicOn.divisor_support_finite_of_subset
      (fun z _ => ((differentiable_LFunction hχ).analyticAt z).meromorphicAt)
      (isCompact_closedBall s R') subset_rfl
  have hdivfinA : (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) (Metric.closedBall 0 (|t| + 2))).support.Finite :=
    MeromorphicOn.divisor_support_finite_of_subset
      (fun z _ => ((differentiable_completedLFunction hχ).analyticAt z).meromorphicAt)
      (isCompact_closedBall 0 (|t| + 2)) subset_rfl
  set D : ℂ → ℝ := fun u => ((MeromorphicOn.divisor (DirichletCharacter.LFunction χ) (Metric.closedBall s R') u : ℤ) : ℝ) with hDdef
  set DA : ℂ → ℝ := fun u => ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) (Metric.closedBall 0 (|t| + 2)) u : ℤ) : ℝ) with hDAdef
  set ind : ℂ → ℝ := fun u => if ‖(1:ℂ) + (t:ℂ) * Complex.I - u‖ ≤ δ then 1 else 0 with hinddef
  have hDun : ∀ u : ℂ, D u = ((MeromorphicOn.divisor (DirichletCharacter.LFunction χ) (Metric.closedBall s R') u : ℤ) : ℝ) := by
    intro u; rw [hDdef]
  have hDAun : ∀ u : ℂ, DA u = ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) (Metric.closedBall 0 (|t| + 2)) u : ℤ) : ℝ) := by
    intro u; rw [hDAdef]
  have hindun : ∀ u : ℂ, ind u = (if ‖(1:ℂ) + (t:ℂ) * Complex.I - u‖ ≤ δ then 1 else 0) := by
    intro u; rw [hinddef]
  have hfinD : Function.HasFiniteSupport D := hdivfinL.subset (by
    intro u hu
    rw [Function.mem_support] at hu ⊢
    intro h0
    exact hu (by rw [hDun u, h0, Int.cast_zero]))
  have hfinDA : Function.HasFiniteSupport DA := hdivfinA.subset (by
    intro u hu
    rw [Function.mem_support] at hu ⊢
    intro h0
    exact hu (by rw [hDAun u, h0, Int.cast_zero]))
  have hfinDT : Function.HasFiniteSupport (fun u : ℂ => D u * ((u - s).re) * ((‖u - s‖ ^ 2)⁻¹ - (R')⁻¹ * (R')⁻¹)) :=
    hfinD.subset (by
      intro u hu
      rw [Function.mem_support] at hu ⊢
      intro h0
      exact hu (by rw [h0]; ring))
  have hfinIT : Function.HasFiniteSupport (fun u : ℂ => ind u * (D u * ((u - s).re) * ((‖u - s‖ ^ 2)⁻¹ - (R')⁻¹ * (R')⁻¹))) :=
    hfinDT.subset (by
      intro u hu
      rw [Function.mem_support] at hu ⊢
      intro h0
      exact hu (by rw [h0]; ring))
  have hfinSA : Function.HasFiniteSupport (fun u : ℂ => DA u * (if ‖(1:ℂ) + (t:ℂ) * Complex.I - u‖ ≤ δ then ((1/(s-u)).re) else 0)) :=
    hfinDA.subset (by
      intro u hu
      rw [Function.mem_support] at hu ⊢
      intro h0
      exact hu (by rw [h0]; ring))
  have hfinNear : Function.HasFiniteSupport (fun u : ℂ => ind u * D u * ((1/(s-u)).re)) :=
    hfinD.subset (by
      intro u hu
      rw [Function.mem_support] at hu ⊢
      intro h0
      exact hu (by rw [h0]; ring))
  have hfinCorr : Function.HasFiniteSupport (fun u : ℂ => ind u * D u * ((σ - u.re) * ((R')^2)⁻¹)) :=
    hfinD.subset (by
      intro u hu
      rw [Function.mem_support] at hu ⊢
      intro h0
      exact hu (by rw [h0]; ring))
  -- the Carleman identity, with the divisor sum written using `D`
  have hsumD : (∑ᶠ u : ℂ, ((MeromorphicOn.divisor (DirichletCharacter.LFunction χ) (Metric.closedBall s R')) u : ℤ) * ((u - s).re) * ((‖u - s‖ ^ 2)⁻¹ - (R')⁻¹ * (R')⁻¹))
      = ∑ᶠ u : ℂ, D u * ((u - s).re) * ((‖u - s‖ ^ 2)⁻¹ - (R')⁻¹ * (R')⁻¹) := by
    apply finsum_congr
    intro u
    rw [hDun u]
  have hJC' : (deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s).re
      = -(∑ᶠ u : ℂ, D u * ((u - s).re) * ((‖u - s‖ ^ 2)⁻¹ - (R')⁻¹ * (R')⁻¹))
        + (1/(Real.pi * R')) * Intg := by
    have h := hJC
    rw [hIntgdef, hsumD] at h
    exact h
  have hnegld : (-logDeriv (DirichletCharacter.LFunction χ) s).re
      = (∑ᶠ u : ℂ, D u * ((u - s).re) * ((‖u - s‖ ^ 2)⁻¹ - (R')⁻¹ * (R')⁻¹))
        - (1/(Real.pi * R')) * Intg := by
    have h := hJC'
    simp only [logDeriv, Pi.div_apply, Complex.neg_re] at h ⊢
    linarith only [h]
  -- pointwise facts about the divisor
  have hDnn : ∀ u : ℂ, 0 ≤ D u := by
    intro u
    have h := MeromorphicOn.AnalyticOnNhd.divisor_nonneg
      (f := DirichletCharacter.LFunction χ) (U := Metric.closedBall s R')
      (fun z _ => (differentiable_LFunction hχ).analyticAt z)
    have h2 : (0:ℤ) ≤ MeromorphicOn.divisor (DirichletCharacter.LFunction χ) (Metric.closedBall s R') u := h u
    rw [hDun u]
    exact_mod_cast h2
  have hDAnn : ∀ u : ℂ, 0 ≤ DA u := by
    intro u
    have h := MeromorphicOn.AnalyticOnNhd.divisor_nonneg
      (f := DirichletCharacter.completedLFunction χ) (U := Metric.closedBall 0 (|t| + 2))
      (fun z _ => (differentiable_completedLFunction hχ).analyticAt z)
    have h2 : (0:ℤ) ≤ MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) (Metric.closedBall 0 (|t| + 2)) u := h u
    rw [hDAun u]
    exact_mod_cast h2
  have hDmem : ∀ u : ℂ, D u ≠ 0 → u ∈ Metric.closedBall s R' := by
    intro u hu
    by_contra hc
    apply hu
    have h0 : ((MeromorphicOn.divisor (DirichletCharacter.LFunction χ) (Metric.closedBall s R') u : ℤ) : ℝ) = 0 := by
      rw [(MeromorphicOn.divisor (DirichletCharacter.LFunction χ) (Metric.closedBall s R')).apply_eq_zero_of_notMem hc]
      simp
    rw [hDun u]
    exact h0
  have hDzero : ∀ u : ℂ, D u ≠ 0 → DirichletCharacter.LFunction χ u = 0 := by
    intro u hu
    have hdiv : MeromorphicOn.divisor (DirichletCharacter.LFunction χ) (Metric.closedBall s R') u ≠ 0 := by
      intro h0
      exact hu (by rw [hDun u, h0, Int.cast_zero])
    exact divisor_ne_zero_imp_eq_zero
      (f := DirichletCharacter.LFunction χ)
      (fun z _ => (differentiable_LFunction hχ).analyticAt z) (hDmem u hu) hdiv
  have hDre : ∀ u : ℂ, D u ≠ 0 → u.re < 1 := by
    intro u hu
    by_contra hcon
    have hL0 := hDzero u hu
    exact (LFunction_ne_zero_of_one_le_re (s := u) χ (Or.inl hχ) (not_lt.mp hcon)) hL0
  -- the split identity for the Carleman summand
  have hTf_eq : ∀ u : ℂ, D u * ((u - s).re) * ((‖u - s‖ ^ 2)⁻¹ - (R')⁻¹ * (R')⁻¹)
      = -(D u * ((1/(s-u)).re)) + D u * ((σ - u.re) * ((R')^2)⁻¹) := by
    intro u
    by_cases hus : u = s
    · rw [hus]
      have h1 : (σ - s.re) = 0 := by rw [hσdef]; ring
      simp only [sub_self, Complex.zero_re, mul_zero, zero_mul, neg_zero, add_zero, one_div,
        inv_zero, h1]
    · have h1 : (u - s).re = -(σ - u.re) := by rw [Complex.sub_re, hσdef]; ring
      have h2 : ((1:ℂ)/(s-u)).re = (σ - u.re) * (‖s-u‖ ^ 2)⁻¹ := by
        rw [one_div, Complex.inv_re, Complex.normSq_eq_norm_sq, div_eq_mul_inv, Complex.sub_re,
          hσdef]
      have h3 : ‖u - s‖ ^ 2 = ‖s - u‖ ^ 2 := by rw [norm_sub_rev]
      have h4 : (R')⁻¹ * (R')⁻¹ = ((R')^2)⁻¹ := by rw [← mul_inv]; ring
      rw [h1, h2, h3, h4]
      ring
  -- nonpositivity of the summand
  have hTf_nonpos : ∀ u : ℂ, D u * ((u - s).re) * ((‖u - s‖ ^ 2)⁻¹ - (R')⁻¹ * (R')⁻¹) ≤ 0 := by
    intro u
    by_cases hDu : D u = 0
    · rw [hDu]; ring_nf; norm_num
    · have hmem := hDmem u hDu
      have hlt := hDre u hDu
      have hre : (u - s).re < 0 := by
        rw [Complex.sub_re]
        have : s.re = σ := hσdef.symm
        rw [this]
        linarith only [hlt, hσ1]
      have hne : u - s ≠ 0 := by
        intro h
        have h' : u.re = σ := by rw [sub_eq_zero.mp h, hσdef]
        linarith only [h', hlt, hσ1]
      have h1 : ‖u - s‖ ≤ R' := by
        rw [Metric.mem_closedBall, dist_eq_norm] at hmem
        exact hmem
      have h2 : 0 < ‖u - s‖ ^ 2 := by
        have := norm_pos_iff.mpr hne
        positivity
      have h3 : ‖u - s‖ ^ 2 ≤ (R')^2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
      have h4 : 0 < (R')^2 := by positivity
      have h5 : ((R')^2)⁻¹ ≤ (‖u - s‖ ^ 2)⁻¹ := (inv_le_inv₀ h4 h2).mpr h3
      have h6 : (R')⁻¹ * (R')⁻¹ = ((R')^2)⁻¹ := by rw [← mul_inv]; ring
      have hfac : 0 ≤ (‖u - s‖ ^ 2)⁻¹ - (R')⁻¹ * (R')⁻¹ := by rw [h6]; linarith only [h5]
      have hprod : D u * (u - s).re ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (hDnn u) hre.le
      exact mul_nonpos_of_nonpos_of_nonneg hprod hfac
  -- dropping the far zeros
  have hTf_le_ind : (∑ᶠ u : ℂ, D u * ((u - s).re) * ((‖u - s‖ ^ 2)⁻¹ - (R')⁻¹ * (R')⁻¹))
      ≤ ∑ᶠ u : ℂ, ind u * (D u * ((u - s).re) * ((‖u - s‖ ^ 2)⁻¹ - (R')⁻¹ * (R')⁻¹)) := by
    apply finsum_le_finsum' hfinDT hfinIT
    intro u
    show D u * ((u - s).re) * ((‖u - s‖ ^ 2)⁻¹ - (R')⁻¹ * (R')⁻¹)
      ≤ ind u * (D u * ((u - s).re) * ((‖u - s‖ ^ 2)⁻¹ - (R')⁻¹ * (R')⁻¹))
    by_cases hc : ‖(1:ℂ) + (t:ℂ) * Complex.I - u‖ ≤ δ
    · have h1 : ind u = 1 := by rw [hindun u]; simp [hc]
      rw [h1, one_mul]
    · have h1 : ind u = 0 := by rw [hindun u]; simp [hc]
      rw [h1, zero_mul]
      exact hTf_nonpos u

  -- ================= near-parameter facts =================
  have hnear_re : ∀ u : ℂ, ‖(1:ℂ) + (t:ℂ) * Complex.I - u‖ ≤ δ → 0 < u.re := by
    intro u hu
    have h1 : ((1:ℂ) + (t:ℂ) * Complex.I - u).re = 1 - u.re := by
      simp [Complex.sub_re, Complex.add_re, Complex.mul_re]
    have h2 : |1 - u.re| ≤ ‖(1:ℂ) + (t:ℂ) * Complex.I - u‖ := by
      rw [← h1]; exact Complex.abs_re_le_norm _
    rw [abs_le] at h2
    linarith only [h2.2, hu, hδ_lt1]
  have hnear_mem : ∀ u : ℂ, ‖(1:ℂ) + (t:ℂ) * Complex.I - u‖ ≤ δ → u ∈ Metric.closedBall s R' := by
    intro u hu
    have h1 : ‖s - u‖ ≤ ‖s - ((1:ℂ) + (t:ℂ) * Complex.I)‖ + ‖((1:ℂ) + (t:ℂ) * Complex.I) - u‖ := by
      have h := norm_add_le (s - ((1:ℂ) + (t:ℂ) * Complex.I)) (((1:ℂ) + (t:ℂ) * Complex.I) - u)
      have heq : (s - ((1:ℂ) + (t:ℂ) * Complex.I)) + (((1:ℂ) + (t:ℂ) * Complex.I) - u) = s - u := by
        ring
      rwa [heq] at h
    have h2 : ‖s - ((1:ℂ) + (t:ℂ) * Complex.I)‖ = σ - 1 := by
      have heq : s - ((1:ℂ) + (t:ℂ) * Complex.I) = ((σ - 1 : ℝ) : ℂ) := by
        apply Complex.ext <;>
          simp [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im, Complex.mul_re,
            Complex.mul_im, hσdef.symm, htdef.symm]
      rw [heq, show ‖((σ - 1 : ℝ) : ℂ)‖ = |σ - 1| from RCLike.norm_ofReal _,
        abs_of_nonneg (by linarith only [hσ1])]
    have h3 : σ - 1 + δ ≤ R' := by
      have h5 : δ ≤ R / 4 := hδ_R
      have h6 : Real.log L / L ≤ R / 4 := by
        have h6a : (1:ℝ)/(8*(k:ℝ)) ≤ R / 4 := by
          have hR4 : R / 4 = 1 / (4 * (k:ℝ)) := by rw [hRdef]; ring
          rw [hR4]
          exact one_div_le_one_div_of_le (by positivity) (by linarith only [hkRpos])
        linarith only [hlogLdiv, h6a]
      linarith only [hσle, h5, h6, hR'ge]
    rw [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev]
    rw [h2] at h1
    linarith only [h1, hu, h3]
  have hnear_big : ∀ u : ℂ, ‖(1:ℂ) + (t:ℂ) * Complex.I - u‖ ≤ δ →
      u ∈ Metric.closedBall 0 (|t| + 2) := by
    intro u hu
    have h1 : ‖u - ((1:ℂ) + (t:ℂ) * Complex.I)‖ ≤ δ := by
      rw [← norm_neg, neg_sub]; exact hu
    have h2 : ‖u‖ ≤ ‖u - ((1:ℂ) + (t:ℂ) * Complex.I)‖ + ‖(1:ℂ) + (t:ℂ) * Complex.I‖ := by
      have h := norm_add_le (u - ((1:ℂ) + (t:ℂ) * Complex.I)) ((1:ℂ) + (t:ℂ) * Complex.I)
      have heq : (u - ((1:ℂ) + (t:ℂ) * Complex.I)) + ((1:ℂ) + (t:ℂ) * Complex.I) = u := by ring
      rwa [heq] at h
    have h3 : ‖(1:ℂ) + (t:ℂ) * Complex.I‖ ≤ |t| + 1 := by
      have h4 : ((1:ℂ) + (t:ℂ) * Complex.I).re = 1 := by simp
      have h5 : ((1:ℂ) + (t:ℂ) * Complex.I).im = t := by simp
      have h6 : ‖(1:ℂ) + (t:ℂ) * Complex.I‖ = Real.sqrt (1 + t^2) := by
        rw [Complex.norm_def, Complex.normSq_apply, h4, h5]
        ring_nf
      rw [h6]
      have h7 : Real.sqrt (1 + t^2) ≤ Real.sqrt ((|t| + 1)^2) := by
        apply Real.sqrt_le_sqrt
        nlinarith only [sq_abs t, abs_nonneg t]
      rwa [Real.sqrt_sq (by positivity : (0:ℝ) ≤ |t| + 1)] at h7
    rw [Metric.mem_closedBall, dist_eq_norm]
    have h8 : ‖u - (0:ℂ)‖ = ‖u‖ := by rw [sub_zero]
    rw [h8]
    have h9 : ‖u‖ ≤ δ + (|t| + 1) := by linarith only [h1, h2, h3]
    linarith only [h9, hδ_lt1]
  -- ================= the corrective sum =================
  set SA : ℝ := ∑ᶠ u : ℂ, ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) (Metric.closedBall 0 (|t| + 2))) u : ℤ) *
      (if ‖(1:ℂ) + (t:ℂ) * Complex.I - u‖ ≤ δ then ((1/(s-u)).re) else 0) with hSAdef
  have hSA_eq : SA = ∑ᶠ u : ℂ, DA u * (ind u * ((1/(s-u)).re)) := by
    rw [hSAdef]
    apply finsum_congr
    intro u
    show ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) (Metric.closedBall 0 (|t| + 2))) u : ℤ) *
        (if ‖(1:ℂ) + (t:ℂ) * Complex.I - u‖ ≤ δ then ((1/(s-u)).re) else 0)
      = DA u * (ind u * ((1/(s-u)).re))
    rw [hDAun u, hindun u]
    by_cases hc : ‖(1:ℂ) + (t:ℂ) * Complex.I - u‖ ≤ δ <;> simp [hc]
  have hfinSA1 : Function.HasFiniteSupport (fun u : ℂ => DA u * (ind u * ((1/(s-u)).re))) :=
    hfinDA.subset (by
      intro u hu
      rw [Function.mem_support] at hu ⊢
      intro h0
      exact hu (by rw [h0]; ring))
  have hSA_le : SA ≤ ∑ᶠ u : ℂ, ind u * D u * ((1/(s-u)).re) := by
    rw [hSA_eq]
    apply finsum_le_finsum' hfinSA1 hfinNear
    intro u
    show DA u * (ind u * ((1/(s-u)).re)) ≤ ind u * D u * ((1/(s-u)).re)
    by_cases hc : ‖(1:ℂ) + (t:ℂ) * Complex.I - u‖ ≤ δ
    · have h1 : ind u = 1 := by rw [hindun u]; simp [hc]
      rw [h1]
      simp only [one_mul]
      have hmem : u ∈ Metric.closedBall s R' := hnear_mem u hc
      have hrepos : 0 < u.re := hnear_re u hc
      have hle := Commons.NumberTheory.DirichletCharacter.completedL_divisor_le_L χ hχ
        (Metric.closedBall s R') hmem hrepos
      have hDA' : DA u = ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) (Metric.closedBall s R') u : ℤ) : ℝ) := by
        rw [hDAun u]
        congr 1
        rw [divisor_eq_orderNat
            (fun z _ => ((differentiable_completedLFunction hχ).analyticAt z)) (hnear_big u hc),
          divisor_eq_orderNat
            (fun z _ => ((differentiable_completedLFunction hχ).analyticAt z)) hmem]
      have hD' : D u = ((MeromorphicOn.divisor (DirichletCharacter.LFunction χ) (Metric.closedBall s R') u : ℤ) : ℝ) := hDun u
      have hDAle : DA u ≤ D u := by
        rw [hDA', hD']
        exact_mod_cast hle
      by_cases hD0 : D u = 0
      · have h0 : DA u = 0 := le_antisymm (by rw [← hD0]; exact hDAle) (hDAnn u)
        rw [h0, hD0]
      · have hlt : u.re < 1 := hDre u hD0
        have hre_nn : 0 ≤ ((1/(s-u)).re) := by
          have h1 : ((1:ℂ)/(s-u)).re = (σ - u.re) / ‖s-u‖^2 := by
            rw [one_div, Complex.inv_re, Complex.normSq_eq_norm_sq, Complex.sub_re, hσdef]
          rw [h1]
          apply div_nonneg
          · linarith only [hσ1, hlt]
          · positivity
        exact mul_le_mul_of_nonneg_right hDAle hre_nn
    · have h1 : ind u = 0 := by rw [hindun u]; simp [hc]
      have h2 : DA u * (ind u * ((1/(s-u)).re)) = 0 := by rw [h1]; ring
      have h3 : ind u * D u * ((1/(s-u)).re) = 0 := by rw [h1]; ring
      rw [h2, h3]

  -- ================= the correction term =================
  have hcount : (∑ᶠ u : ℂ, D u) ≤ 4 * c0 * L := by
    have h1 := hc0 χ hχ hχprim s R' hR'pos (by linarith only [hR'le, hRle]) (by linarith only [hσ1])
      (by
        have h8 : 1/(8*(k:ℝ)) ≤ 1 := by
          rw [div_le_one (by positivity)]
          linarith only [hkR3]
        linarith only [hσle, hlogLdiv, h8])
    have h2 : (∑ᶠ u : ℂ, D u)
        = ∑ᶠ u : ℂ, ((MeromorphicOn.divisor (DirichletCharacter.LFunction χ) (Metric.closedBall s R') u : ℤ) : ℝ) := by
      apply finsum_congr
      intro u
      rw [hDun u]
    rw [h2]
    have h4 : ‖s‖ ≤ 10 * L + 2 := by
      have h5 : ‖s‖ ≤ |s.re| + |s.im| := Complex.norm_le_abs_re_add_abs_im s
      have h5a : |s.re| = σ := by rw [← hσdef]; exact abs_of_pos (by linarith only [hσ1])
      have h5b : |s.im| = |t| := by rw [← htdef]
      rw [h5a, h5b] at h5
      have h6 : σ ≤ 2 := by
        have h7 : Real.log L / L ≤ 1/(8*(k:ℝ)) := hlogLdiv
        have h8 : 1/(8*(k:ℝ)) ≤ 1 := by
          rw [div_le_one (by positivity)]
          linarith only [hkR3]
        linarith only [hσle, h7, h8]
      linarith only [h5, htabs, h6]
    have h3 : Real.log (‖s‖ + 3) ≤ 2 * L := by
      have h7 : ‖s‖ + 3 ≤ L ^ 2 := by nlinarith only [h4, hL11]
      have h8 : Real.log (‖s‖ + 3) ≤ Real.log (L ^ 2) := Real.log_le_log (by positivity) h7
      have h8b : Real.log (L ^ 2) = 2 * Real.log L := by rw [Real.log_pow]; norm_num
      rw [h8b] at h8
      have h19 : η * L ≤ L := mul_le_of_le_one_left hLpos.le hη_1
      linarith only [h8, hlogL, h19]
    have h12 : c0 * (Real.log (‖s‖ + 3) + Real.log (N:ℝ) + 2) ≤ 4 * c0 * L := by
      have h13 : Real.log (‖s‖ + 3) + Real.log (N:ℝ) + 2 ≤ 4 * L := by
        linarith only [h3, hNL, hL3]
      calc c0 * (Real.log (‖s‖ + 3) + Real.log (N:ℝ) + 2) ≤ c0 * (4 * L) :=
            mul_le_mul_of_nonneg_left h13 hc0pos.le
        _ = 4 * c0 * L := by ring
    linarith only [h1, h12]
  have hcorr : (∑ᶠ u : ℂ, ind u * D u * ((σ - u.re) * ((R')^2)⁻¹))
      ≤ (Real.log L / L + δ) * ((R')^2)⁻¹ * (4 * c0 * L) := by
    have h1 : 0 ≤ Real.log L / L + δ := by
      have h2 : 0 ≤ Real.log L / L := div_nonneg (Real.log_nonneg (by linarith only [hL1])) hLpos.le
      linarith only [h2, hδpos]
    have hfinG : Function.HasFiniteSupport
        (fun u : ℂ => ((Real.log L / L + δ) * ((R')^2)⁻¹) * D u) :=
      hfinD.subset (by
        intro u hu
        rw [Function.mem_support] at hu ⊢
        intro h0
        exact hu (by rw [h0]; ring))
    calc (∑ᶠ u : ℂ, ind u * D u * ((σ - u.re) * ((R')^2)⁻¹))
        ≤ ∑ᶠ u : ℂ, ((Real.log L / L + δ) * ((R')^2)⁻¹) * D u := by
          apply finsum_le_finsum' hfinCorr hfinG
          intro u
          show ind u * D u * ((σ - u.re) * ((R')^2)⁻¹)
            ≤ ((Real.log L / L + δ) * ((R')^2)⁻¹) * D u
          by_cases hc : ‖(1:ℂ) + (t:ℂ) * Complex.I - u‖ ≤ δ
          · have hind : ind u = 1 := by rw [hindun u]; simp [hc]
            rw [hind, one_mul]
            by_cases hDu : D u = 0
            · have h0 : D u * ((σ - u.re) * ((R')^2)⁻¹) = 0 := by rw [hDu]; ring
              have h0' : ((Real.log L / L + δ) * ((R')^2)⁻¹) * D u = 0 := by rw [hDu]; ring
              rw [h0, h0']
            · have h2 : σ - u.re ≤ Real.log L / L + δ := by
                have h3 : 1 - u.re ≤ δ := by
                  have h4 : ((1:ℂ) + (t:ℂ) * Complex.I - u).re = 1 - u.re := by
                    simp [Complex.sub_re, Complex.add_re, Complex.mul_re]
                  have h5 : |1 - u.re| ≤ ‖(1:ℂ) + (t:ℂ) * Complex.I - u‖ := by
                    rw [← h4]; exact Complex.abs_re_le_norm _
                  rw [abs_le] at h5
                  linarith only [h5.2, hc]
                linarith only [hσle, h3]
              have h6 : 0 < ((R')^2)⁻¹ := by positivity
              have h7 : 0 ≤ D u := hDnn u
              have h8 : D u * (σ - u.re) ≤ D u * (Real.log L / L + δ) :=
                mul_le_mul_of_nonneg_left h2 h7
              calc D u * ((σ - u.re) * ((R')^2)⁻¹)
                  = D u * (σ - u.re) * ((R')^2)⁻¹ := by ring
                _ ≤ D u * (Real.log L / L + δ) * ((R')^2)⁻¹ :=
                    mul_le_mul_of_nonneg_right h8 h6.le
                _ = ((Real.log L / L + δ) * ((R')^2)⁻¹) * D u := by ring
          · have hind : ind u = 0 := by rw [hindun u]; simp [hc]
            have h2 : 0 ≤ ((R')^2)⁻¹ := by positivity
            have h3 : 0 ≤ D u := hDnn u
            have h4 : 0 ≤ ((Real.log L / L + δ) * ((R')^2)⁻¹) := mul_nonneg h1 h2
            have h5 : (0:ℝ) * D u * ((σ - u.re) * ((R')^2)⁻¹) = 0 := by ring
            rw [hind, h5]
            exact mul_nonneg h4 h3
      _ = ((Real.log L / L + δ) * ((R')^2)⁻¹) * (∑ᶠ u : ℂ, D u) := by
          exact (map_finsum (AddMonoidHom.mulLeft ((Real.log L / L + δ) * ((R')^2)⁻¹)) hfinD).symm
      _ ≤ ((Real.log L / L + δ) * ((R')^2)⁻¹) * (4 * c0 * L) :=
          mul_le_mul_of_nonneg_left hcount (mul_nonneg h1 (by positivity))

  -- ================= final assembly =================
  have hL5 : 5 ≤ L := le_trans hK5 hK_le_L
  have hR'invk2 : 1 ≤ 2 * (k:ℝ) * R' := by
    have h1 : (2:ℝ) * (k:ℝ) * (R/2) ≤ 2 * (k:ℝ) * R' :=
      mul_le_mul_of_nonneg_left hR'ge (by positivity)
    have h2 : (2:ℝ) * (k:ℝ) * (R/2) = 1 := by rw [hRdef]; field_simp
    linarith only [h1, h2]
  have hPcb : Pc ≤ Real.log Cb + ε' * L + 2 * η * L := by
    rw [hPcdef]
    have h1 : φ * (1 + R) * (1 - σ) * L ≤ 0 := by
      have h2 : (1 - σ) ≤ 0 := by linarith only [hσ1]
      have h3 : 0 ≤ φ * (1 + R) * L := by positivity
      have h4 : φ * (1 + R) * (1 - σ) * L = (φ * (1 + R) * L) * (1 - σ) := by ring
      rw [h4]
      exact mul_nonpos_of_nonneg_of_nonpos h3 h2
    have h4 : Real.log (10 * L + 2) ≤ 2 * η * L := by
      have h5 : Real.log (10 * L + 2) ≤ Real.log (L ^ 2) :=
        Real.log_le_log (by positivity) (by nlinarith only [hL11])
      have h6 : Real.log (L ^ 2) = 2 * Real.log L := by rw [Real.log_pow]; norm_num
      rw [h6] at h5
      linarith only [h5, hlogL]
    linarith only [h1, h4]
  have hVnn : 0 ≤ V := by
    rw [hVdef]
    apply Real.log_nonneg
    have hlogL1 : (1:ℝ) ≤ Real.log L := by
      have h1 : Real.log 3 ≤ Real.log L := Real.log_le_log (by norm_num) hL3
      have h2 : (1:ℝ) < Real.log 3 := by
        rw [← Real.log_exp 1]
        exact Real.log_lt_log (Real.exp_pos 1) (by linarith only [Real.exp_one_lt_three])
      linarith only [h1, h2]
    nlinarith only [hL3, hlogL1]
  have hlogCbnn : 0 ≤ Real.log Cb := Real.log_nonneg hCb1
  have hlogLnn : 0 ≤ Real.log L / L := div_nonneg (Real.log_nonneg (by linarith only [hL1])) hLpos.le
  have hLL : Real.log (Real.log L) ≤ η * L := by
    have h1 : Real.log (Real.log L) ≤ Real.log (η * L) := Real.log_le_log hlog3 hlogL
    have h2 : Real.log (η * L) ≤ η * L := by
      have h3 := Real.log_le_sub_one_of_pos (show (0:ℝ) < η * L by positivity)
      linarith only [h3]
    linarith only [h1, h2]
  have hVb : V ≤ 3 * η * L := by
    have h1 : Real.log (2 * L * Real.log L) = Real.log 2 + Real.log L + Real.log (Real.log L) := by
      rw [Real.log_mul (by positivity) (by positivity),
        Real.log_mul (by norm_num) (ne_of_gt hLpos)]
    rw [hVdef, h1]
    linarith only [hlog2, hlogL, hLL]
  have hInvR' : 1/(Real.pi * R') ≤ 2 * (k:ℝ) / Real.pi := by
    rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul]
    have h2 : 2 * (k:ℝ) * (Real.pi * R') = Real.pi * (2*(k:ℝ)*R') := by ring
    rw [h2]
    simpa using mul_le_mul_of_nonneg_left hR'invk2 Real.pi_pos.le
  have hVterm : 2*V/(Real.pi * R') ≤ (4*(k:ℝ)/Real.pi)*V := by
    calc 2*V/(Real.pi * R') = (2*V) * (1/(Real.pi*R')) := by ring
      _ ≤ (2*V) * (2*(k:ℝ)/Real.pi) := by
          apply mul_le_mul_of_nonneg_left hInvR' (by positivity)
      _ = (4*(k:ℝ)/Real.pi)*V := by ring
  have hPterm : 2*Pc/(Real.pi * R') ≤ (4*(k:ℝ)/Real.pi)*(Real.log Cb + ε'*L + 2*η*L) := by
    have h1 : 2*Pc ≤ 2*(Real.log Cb + ε'*L + 2*η*L) := by linarith only [hPcb]
    calc 2*Pc/(Real.pi * R') = (2*Pc) * (1/(Real.pi*R')) := by ring
      _ ≤ (2*(Real.log Cb + ε'*L + 2*η*L)) * (2*(k:ℝ)/Real.pi) := by
          have hb2 : 0 ≤ ε'*L := by positivity
          have hb3 : 0 ≤ 2*η*L := by positivity
          apply mul_le_mul h1 hInvR' (by positivity) (by linarith only [hlogCbnn, hb2, hb3])
      _ = (4*(k:ℝ)/Real.pi)*(Real.log Cb + ε'*L + 2*η*L) := by ring
  have hQterm : (Real.pi/2)*Qc/(Real.pi*R') = Qc/(2*R') := by
    field_simp
  have hQterm2 : Qc/(2*R') = φ*(1+1/(k:ℝ))*L/2 := by
    rw [hQcdef]
    rw [div_eq_iff (by positivity : (2:ℝ) * R' ≠ 0)]
    ring
  have hVfinal : 2*V/(Real.pi * R') ≤ ε*L/8 := by
    have h1 : (4*(k:ℝ)/Real.pi)*V ≤ (4*(k:ℝ)/Real.pi)*(3*η*L) :=
      mul_le_mul_of_nonneg_left hVb (by positivity)
    have h2 : (4*(k:ℝ)/Real.pi)*(3*η*L) = (12*(k:ℝ)*η/Real.pi)*L := by ring
    rw [h2] at h1
    have h3 : 12*(k:ℝ)*η/Real.pi ≤ ε/8 := by
      have h4 : 12*(k:ℝ)*(Real.pi*ε/(4096*(k:ℝ)))/Real.pi = 12*ε/4096 := by
        field_simp
      calc 12*(k:ℝ)*η/Real.pi ≤ 12*(k:ℝ)*(Real.pi*ε/(4096*(k:ℝ)))/Real.pi := by
            apply div_le_div_of_nonneg_right _ Real.pi_pos.le
            exact mul_le_mul_of_nonneg_left hη_b (by positivity)
        _ = 12*ε/4096 := h4
        _ ≤ ε/8 := by linarith only [hε]
    have h5 : (12*(k:ℝ)*η/Real.pi)*L ≤ (ε/8)*L := mul_le_mul_of_nonneg_right h3 hLpos.le
    linarith only [hVterm, h1, h5]
  have hPfin_c : 2*Pc/(Real.pi * R') ≤ ε*L/16 + ε*L/8 + ε*L/8 := by
    have h3 : (4*(k:ℝ)/Real.pi)*(Real.log Cb + ε'*L + 2*η*L)
        = (4*(k:ℝ)/Real.pi)*Real.log Cb + (4*(k:ℝ)/Real.pi)*ε'*L + (8*(k:ℝ)/Real.pi)*η*L := by
      field_simp
      ring
    have h4 : (4*(k:ℝ)/Real.pi)*Real.log Cb ≤ (4*(k:ℝ)/Real.pi)*(η*L) :=
      mul_le_mul_of_nonneg_left hlogCb (by positivity)
    have h5 : (4*(k:ℝ)/Real.pi)*(η*L) = (4*(k:ℝ)*η/Real.pi)*L := by ring
    have h6 : 4*(k:ℝ)*η/Real.pi ≤ ε/16 := by
      have h7 : 4*(k:ℝ)*(Real.pi*ε/(4096*(k:ℝ)))/Real.pi = 4*ε/4096 := by field_simp
      calc 4*(k:ℝ)*η/Real.pi ≤ 4*(k:ℝ)*(Real.pi*ε/(4096*(k:ℝ)))/Real.pi := by
            apply div_le_div_of_nonneg_right _ Real.pi_pos.le
            exact mul_le_mul_of_nonneg_left hη_b (by positivity)
        _ = 4*ε/4096 := h7
        _ ≤ ε/16 := by linarith only [hε]
    have h8 : 8*(k:ℝ)*η/Real.pi ≤ ε/8 := by
      have h9 : 8*(k:ℝ)*(Real.pi*ε/(4096*(k:ℝ)))/Real.pi = 8*ε/4096 := by field_simp
      calc 8*(k:ℝ)*η/Real.pi ≤ 8*(k:ℝ)*(Real.pi*ε/(4096*(k:ℝ)))/Real.pi := by
            apply div_le_div_of_nonneg_right _ Real.pi_pos.le
            exact mul_le_mul_of_nonneg_left hη_b (by positivity)
        _ = 8*ε/4096 := h9
        _ ≤ ε/8 := by linarith only [hε]
    have h10 : (4*(k:ℝ)/Real.pi)*ε'*L = ε*L/(16*Real.pi) := by
      rw [hε'def]; field_simp; ring
    have h11 : ε*L/(16*Real.pi) ≤ ε*L/8 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have h11a : (8:ℝ) ≤ 16*Real.pi := by linarith only [Real.pi_gt_three]
      exact mul_le_mul_of_nonneg_left h11a (by positivity)
    calc 2*Pc/(Real.pi * R') ≤ (4*(k:ℝ)/Real.pi)*(Real.log Cb + ε'*L + 2*η*L) := hPterm
      _ = (4*(k:ℝ)/Real.pi)*Real.log Cb + (4*(k:ℝ)/Real.pi)*ε'*L + (8*(k:ℝ)/Real.pi)*η*L := h3
      _ ≤ (4*(k:ℝ)*η/Real.pi)*L + ε*L/(16*Real.pi) + (8*(k:ℝ)*η/Real.pi)*L := by
          have h12 : (4*(k:ℝ)/Real.pi)*(η*L) = (4*(k:ℝ)*η/Real.pi)*L := h5
          have h13 : (8*(k:ℝ)/Real.pi)*η*L = (8*(k:ℝ)*η/Real.pi)*L := by ring
          linarith only [h4, h12, h13, h10]
      _ ≤ ε*L/16 + ε*L/8 + ε*L/8 := by
          have h14 : (4*(k:ℝ)*η/Real.pi)*L ≤ (ε/16)*L := mul_le_mul_of_nonneg_right h6 hLpos.le
          have h15 : (8*(k:ℝ)*η/Real.pi)*L ≤ (ε/8)*L := mul_le_mul_of_nonneg_right h8 hLpos.le
          linarith only [h11, h14, h15]
  have hPfinal : 2*Pstar/(Real.pi * R') ≤ ε*L/16 + ε*L/8 + ε*L/8 + ε*L/32 := by
    have hA : 2 * Pstar / (Real.pi * R')
        = max (2 * Pc / (Real.pi * R')) (2 * K₀ / (Real.pi * R')) := by
      rw [hPstardef]
      rcases le_total Pc K₀ with h | h
      · have h1 : max Pc K₀ = K₀ := max_eq_right h
        have h2 : max (2 * Pc / (Real.pi * R')) (2 * K₀ / (Real.pi * R'))
            = 2 * K₀ / (Real.pi * R') :=
          max_eq_right (div_le_div_of_nonneg_right (by linarith only [h]) (by positivity))
        rw [h1, h2]
      · have h1 : max Pc K₀ = Pc := max_eq_left h
        have h2 : max (2 * Pc / (Real.pi * R')) (2 * K₀ / (Real.pi * R'))
            = 2 * Pc / (Real.pi * R') :=
          max_eq_left (div_le_div_of_nonneg_right (by linarith only [h]) (by positivity))
        rw [h1, h2]
    have hC : 2 * K₀ / (Real.pi * R') ≤ ε*L/32 := by
      have h1 : 2 * K₀ / (Real.pi * R') ≤ (4 * (k:ℝ) / Real.pi) * K₀ := by
        have h2 : 2 * K₀ / (Real.pi * R') = (2 * K₀) * (1 / (Real.pi * R')) := by ring
        rw [h2]
        have h3 : (2 * K₀) * (1/(Real.pi*R')) ≤ (2 * K₀) * (2*(k:ℝ)/Real.pi) :=
          mul_le_mul_of_nonneg_left hInvR' (by positivity)
        have h4 : (2 * K₀) * (2*(k:ℝ)/Real.pi) = (4*(k:ℝ)/Real.pi) * K₀ := by ring
        linarith only [h3, h4]
      have h5 : (4*(k:ℝ)/Real.pi) * K₀ ≤ (4*(k:ℝ)/Real.pi) * (2 * η * L) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        linarith only [hK₀bound, hC₀le, hlogL]
      have h6 : (4*(k:ℝ)/Real.pi) * (2 * η * L) = (8*(k:ℝ)*η/Real.pi) * L := by ring
      have h7 : 8*(k:ℝ)*η/Real.pi ≤ ε/32 := by
        have h8 : 8*(k:ℝ)*(Real.pi*ε/(4096*(k:ℝ)))/Real.pi = 8*ε/4096 := by field_simp
        calc 8*(k:ℝ)*η/Real.pi
            ≤ 8*(k:ℝ)*(Real.pi*ε/(4096*(k:ℝ)))/Real.pi := by
              apply div_le_div_of_nonneg_right _ Real.pi_pos.le
              exact mul_le_mul_of_nonneg_left hη_b (by positivity)
          _ = 8*ε/4096 := h8
          _ ≤ ε/32 := by linarith only [hε]
      have h9 : (8*(k:ℝ)*η/Real.pi) * L ≤ (ε/32)*L :=
        mul_le_mul_of_nonneg_right h7 hLpos.le
      linarith only [h1, h5, h6, h9]
    rw [hA]
    apply max_le
    · refine le_trans hPfin_c ?_
      have : (0:ℝ) ≤ ε*L/32 := by positivity
      linarith only [this]
    · refine le_trans hC ?_
      have : (0:ℝ) ≤ ε*L/16 + ε*L/8 + ε*L/8 := by positivity
      linarith only [this]
  have hQfinal : (Real.pi/2)*Qc/(Real.pi*R') ≤ φ*L/2 + ε*L/8 := by
    rw [hQterm, hQterm2]
    have h1 : φ*(1+1/(k:ℝ))*L/2 = φ*L/2 + φ*L/(2*(k:ℝ)) := by
      field_simp
    rw [h1]
    have h2 : φ/(2*(k:ℝ)) ≤ ε/8 := by
      rw [div_le_iff₀ (by positivity)]
      have h3 : 4*φ ≤ ε*(k:ℝ) := by
        have h4 := hk
        rw [div_le_iff₀ hε] at h4
        linarith only [h4]
      linarith only [h3]
    have h5 : φ*L/(2*(k:ℝ)) = (φ/(2*(k:ℝ)))*L := by ring
    rw [h5]
    have h6 : (φ/(2*(k:ℝ)))*L ≤ (ε/8)*L := mul_le_mul_of_nonneg_right h2 hLpos.le
    linarith only [h6]
  have hCfinal : (∑ᶠ u : ℂ, ind u * D u * ((σ - u.re) * ((R')^2)⁻¹)) ≤ ε*L/4 := by
    have hR'2k : (R'^2)⁻¹ ≤ 4*(k:ℝ)^2 := by
      have h2 : 1/(2*(k:ℝ)) ≤ R' := by
        have h3 : R/2 = 1/(2*(k:ℝ)) := by rw [hRdef]; ring
        rw [← h3]; exact hR'ge
      have h4 : (1/(2*(k:ℝ)))^2 ≤ R'^2 := pow_le_pow_left₀ (by positivity) h2 2
      calc (R'^2)⁻¹ ≤ ((1/(2*(k:ℝ)))^2)⁻¹ := (inv_le_inv₀ (by positivity) (by positivity)).mpr h4
        _ = 4*(k:ℝ)^2 := by field_simp; ring
    have h1 : (∑ᶠ u : ℂ, ind u * D u * ((σ - u.re) * ((R')^2)⁻¹))
        ≤ (Real.log L / L + δ) * (4*(k:ℝ)^2) * (4*c0*L) := by
      have h2 : 0 ≤ Real.log L / L + δ := by linarith only [hlogLnn, hδpos]
      have h3 : 0 ≤ 4*c0*L := by positivity
      calc (∑ᶠ u : ℂ, ind u * D u * ((σ - u.re) * ((R')^2)⁻¹))
          ≤ (Real.log L / L + δ) * (R'^2)⁻¹ * (4*c0*L) := hcorr
        _ ≤ (Real.log L / L + δ) * (4*(k:ℝ)^2) * (4*c0*L) := by
            exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hR'2k h2) h3
    have h4 : (Real.log L / L + δ) * (4*(k:ℝ)^2) * (4*c0*L)
        = 16*c0*(k:ℝ)^2*(Real.log L + δ*L) := by
      field_simp
      ring
    rw [h4] at h1
    have hA : 16*c0*(k:ℝ)^2*η ≤ ε/8 := by
      have h5 : 16*c0*(k:ℝ)^2*(ε/(1024*(c0+1)*((k:ℝ)+1)^2)) ≤ ε/8 := by
        rw [mul_div_assoc', div_le_iff₀ (by positivity : (0:ℝ) < 1024*(c0+1)*((k:ℝ)+1)^2)]
        have hkey : 16*c0*(k:ℝ)^2 ≤ 128*(c0+1)*((k:ℝ)+1)^2 := by
          linarith only [mul_nonneg hc0pos.le (sq_nonneg (k:ℝ)), mul_nonneg hc0pos.le hkRpos.le, hc0pos, hkRpos,
            sq_nonneg (k:ℝ)]
        calc 16*c0*(k:ℝ)^2*ε ≤ 128*(c0+1)*((k:ℝ)+1)^2*ε :=
              mul_le_mul_of_nonneg_right hkey hε.le
          _ = ε/8 * (1024*(c0+1)*((k:ℝ)+1)^2) := by ring
      calc 16*c0*(k:ℝ)^2*η ≤ 16*c0*(k:ℝ)^2*(ε/(1024*(c0+1)*((k:ℝ)+1)^2)) :=
            mul_le_mul_of_nonneg_left hη_a (by positivity)
        _ ≤ ε/8 := h5
    have hB : 16*c0*(k:ℝ)^2*δ ≤ ε/8 := by
      have h5 : 16*c0*(k:ℝ)^2*(ε/(256*c0*(k:ℝ)^2)) = ε/16 := by
        rw [mul_div_assoc']; field_simp; ring
      calc 16*c0*(k:ℝ)^2*δ ≤ 16*c0*(k:ℝ)^2*(ε/(256*c0*(k:ℝ)^2)) :=
            mul_le_mul_of_nonneg_left hδ_ε (by positivity)
        _ = ε/16 := h5
        _ ≤ ε/8 := by linarith only [hε]
    have h6 : 16*c0*(k:ℝ)^2*Real.log L ≤ ε*L/8 := by
      have h6a : 16*c0*(k:ℝ)^2*Real.log L ≤ 16*c0*(k:ℝ)^2*(η*L) :=
        mul_le_mul_of_nonneg_left hlogL (by positivity)
      have h6b : 16*c0*(k:ℝ)^2*(η*L) = (16*c0*(k:ℝ)^2*η)*L := by ring
      have h6c : (16*c0*(k:ℝ)^2*η)*L ≤ (ε/8)*L := mul_le_mul_of_nonneg_right hA hLpos.le
      linarith only [h6a, h6b, h6c]
    have h7 : 16*c0*(k:ℝ)^2*(δ*L) ≤ ε*L/8 := by
      have h7a : 16*c0*(k:ℝ)^2*(δ*L) = (16*c0*(k:ℝ)^2*δ)*L := by ring
      have h7c : (16*c0*(k:ℝ)^2*δ)*L ≤ (ε/8)*L := mul_le_mul_of_nonneg_right hB hLpos.le
      linarith only [h7a, h7c]
    linarith only [h1, h6, h7]
  have hsplit : (2*V + 2*Pstar + (Real.pi/2)*Qc)/(Real.pi*R')
      = 2*V/(Real.pi*R') + 2*Pstar/(Real.pi*R') + (Real.pi/2)*Qc/(Real.pi*R') := by
    field_simp
  have hmain : (-logDeriv (DirichletCharacter.LFunction χ) s).re + SA ≤ (φ/2 + ε) * L := by
    have hstep1 : (-logDeriv (DirichletCharacter.LFunction χ) s).re + SA
        ≤ (∑ᶠ u : ℂ, ind u * D u * ((σ - u.re) * ((R')^2)⁻¹)) - (1/(Real.pi * R')) * Intg := by
      have e3 : (∑ᶠ u : ℂ, ind u * (D u * ((u - s).re) * ((‖u - s‖ ^ 2)⁻¹ - (R')⁻¹ * (R')⁻¹)))
          = (∑ᶠ u : ℂ, ind u * D u * ((σ - u.re) * ((R')^2)⁻¹))
            - ∑ᶠ u : ℂ, ind u * D u * ((1/(s-u)).re) := by
        have h2a : (∑ᶠ u : ℂ, ind u * (D u * ((u - s).re) * ((‖u - s‖ ^ 2)⁻¹ - (R')⁻¹ * (R')⁻¹)))
            = ∑ᶠ u : ℂ, (ind u * D u * ((σ - u.re) * ((R')^2)⁻¹) - ind u * D u * ((1/(s-u)).re)) := by
          apply finsum_congr
          intro u
          show ind u * (D u * ((u - s).re) * ((‖u - s‖ ^ 2)⁻¹ - (R')⁻¹ * (R')⁻¹))
            = ind u * D u * ((σ - u.re) * ((R')^2)⁻¹) - ind u * D u * ((1/(s-u)).re)
          rw [hTf_eq u]; ring
        rw [h2a, finsum_sub_distrib hfinCorr hfinNear]
      linarith only [hnegld, hTf_le_ind, e3, hSA_le]
    have hstep2 : -(1/(Real.pi * R')) * Intg
        ≤ (2*V + 2*Pstar + (Real.pi/2)*Qc) / (Real.pi * R') := by
      have h := hInt
      have h2 : -(2*V) - 2*Pstar - (Real.pi/2)*Qc = -(2*V + 2*Pstar + (Real.pi/2)*Qc) := by ring
      rw [h2] at h
      have h3 : 0 < 1/(Real.pi * R') := by positivity
      calc -(1/(Real.pi * R')) * Intg = (1/(Real.pi * R')) * (-Intg) := by ring
        _ ≤ (1/(Real.pi * R')) * (2*V + 2*Pstar + (Real.pi/2)*Qc) := by
            apply mul_le_mul_of_nonneg_left _ h3.le
            linarith only [h]
        _ = (2*V + 2*Pstar + (Real.pi/2)*Qc) / (Real.pi * R') := by ring
    rw [hsplit] at hstep2
    linarith only [hstep1, hstep2, hVfinal, hPfinal, hQfinal, hCfinal, mul_pos hε hLpos]
  exact hmain

end Work.LinnikAreas.l31free
