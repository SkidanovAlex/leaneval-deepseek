import Mathlib
import Submission.Work.FIArea6Hecke.StripCoreDefs
import Submission.Work.FITop4.Bridge.area5_6_defs
import Submission.Commons.Analysis.Complex.logDeriv_zeroFree_ball_bound_analytic

/-!
# `Work.FIArea6Hecke.heckeStripGlue` — the formal reduction from the strip inputs to (16.23)

Given

* `StripCore ε` — the de la Vallée Poussin zero-free region together with the logarithmic-derivative
  bound `‖L'/L‖ ≤ K(log(4d(|m|+|t|+3)) + d^ε)` in it, and
* `StripNearOne ε` — the elementary lower bound `‖1/L(σ+it)‖ ≤ K/(σ-1)` for `1 < σ ≤ 2`,

the inverse bound (16.23)/(16.24) on the half-strip `re s ≤ 1` follows by integrating `L'/L` along
the horizontal segment from `s` up to the reference point `σ₀ + it`, `σ₀ = 1 + c/(d^ε log M)`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.FIArea6Hecke

open scoped BigOperators

noncomputable section

/-- The archimedean factor `heckeArch d m s = (4d/π)^s·Γ(s+|m|/2)` does not vanish when `re s > 0`. -/
private lemma heckeArch_ne_zero_of_re_pos_aux {d : ℕ} (hd : 1 ≤ d) (m : ℤ) {s : ℂ}
    (hs : 0 < s.re) : Work.FITop4.Bridge.heckeArch d m s ≠ 0 := by
  unfold Work.FITop4.Bridge.heckeArch
  apply mul_ne_zero
  · rw [Complex.cpow_def_of_ne_zero ?_]
    · exact Complex.exp_ne_zero _
    · have heq : (4 * (((d : ℝ)) : ℂ) / ((Real.pi : ℝ) : ℂ) : ℂ)
          = (((4 * (d : ℝ) / Real.pi : ℝ)) : ℂ) := by push_cast; ring
      rw [heq, Complex.ofReal_ne_zero]
      have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
      positivity
  · apply Complex.Gamma_ne_zero_of_re_pos
    simp only [Complex.add_re, Complex.ofReal_re]
    have h := abs_nonneg (m : ℝ)
    linarith

/-- `heckeArch d m` is holomorphic at every point with `re s > 0`. -/
private lemma heckeArch_differentiableAt_aux {d : ℕ} (hd : 1 ≤ d) (m : ℤ) {s : ℂ}
    (hs : 0 < s.re) : DifferentiableAt ℂ (Work.FITop4.Bridge.heckeArch d m) s := by
  have hbase : (4 * (((d : ℝ)) : ℂ) / ((Real.pi : ℝ) : ℂ) : ℂ) ≠ 0 := by
    have heq : (4 * (((d : ℝ)) : ℂ) / ((Real.pi : ℝ) : ℂ) : ℂ)
        = (((4 * (d : ℝ) / Real.pi : ℝ)) : ℂ) := by push_cast; ring
    rw [heq, Complex.ofReal_ne_zero]
    have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
    positivity
  have harg : ∀ k : ℕ, s + (((|((m : ℝ))| / 2 : ℝ)) : ℂ) ≠ -(k : ℂ) := by
    intro k hk
    have hre : (s + (((|((m : ℝ))| / 2 : ℝ)) : ℂ)).re = -(k : ℝ) := by rw [hk]; simp
    simp only [Complex.add_re, Complex.ofReal_re] at hre
    have h := abs_nonneg (m : ℝ)
    linarith
  unfold Work.FITop4.Bridge.heckeArch
  apply DifferentiableAt.mul
  · exact DifferentiableAt.const_cpow differentiableAt_id (Or.inl hbase)
  · exact (Complex.differentiableAt_Gamma _ harg).comp s
      (differentiableAt_id.add_const ((((|((m : ℝ))| / 2 : ℝ)) : ℂ)))

/-- **Mean-value bound for a holomorphic logarithm along a segment.**  If `F` is a primitive of
`f'/f` on the ball `B(c,R)` and `‖f'/f‖ ≤ K` on the segment `[x,y]`, then `‖F y - F x‖ ≤ K ‖y-x‖`. -/
private theorem norm_sub_le_of_segment {F f : ℂ → ℂ} {c x y : ℂ} {R K : ℝ}
    (hx : x ∈ Metric.ball c R) (hy : y ∈ Metric.ball c R)
    (hF : ∀ w ∈ Metric.ball c R, HasDerivAt F (deriv f w / f w) w)
    (hK : ∀ w ∈ segment ℝ x y, ‖deriv f w / f w‖ ≤ K) :
    ‖F y - F x‖ ≤ K * ‖y - x‖ := by
  have hsub : segment ℝ x y ⊆ Metric.ball c R :=
    (convex_ball c R).segment_subset hx hy
  exact Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (f := F) (s := segment ℝ x y) (C := K)
    (f' := fun w => ContinuousLinearMap.toSpanSingleton ℂ (deriv f w / f w))
    (x := x) (y := y)
    (fun w hw => ((hF w (hsub hw)).hasFDerivAt).hasFDerivWithinAt)
    (fun w hw => by
      rw [ContinuousLinearMap.norm_toSpanSingleton]
      exact hK w hw)
    (convex_segment x y) (left_mem_segment ℝ x y) (right_mem_segment ℝ x y)


theorem heckeStripGlue (ε : ℝ) (hε : 0 < ε) (hε4 : ε ≤ 1 / 4) :
    Work.FIArea6Hecke.StripCore ε → Work.FIArea6Hecke.StripNearOne ε →
      ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
        ∀ (d : ℕ) (chi : GaussianInt → ℂ) (m : ℤ) (Lam : ℂ → ℂ), 1 ≤ d →
          Work.FIArea5.S16Hecke.IsCharMod4dStrict d chi →
          AnalyticOn ℂ Lam Set.univ →
          (∀ s : ℂ, 1 + |(m : ℝ)| / 2 < s.re →
            Lam s = Work.FITop4.Bridge.heckeArch d m s *
              Work.FIArea5.S16Hecke.heckeLSeries chi m s) →
          ∀ s : ℂ,
            1 - c / ((d : ℝ) ^ ε * Real.log (|(m : ℝ)| + |s.im| + 3)) < s.re → s.re ≤ 1 →
            ‖(Lam s / Work.FITop4.Bridge.heckeArch d m s)⁻¹‖
              ≤ C * (d : ℝ) * (Real.log (|(m : ℝ)| + |s.im| + 3)) ^ (2 : ℕ) := by
  intro hcore hnear
  obtain ⟨c₀, Kc, hc₀pos, hKcpos, hcore'⟩ := hcore
  obtain ⟨Kn, hKnpos, hnear'⟩ := hnear
  -- the two output constants
  set G : ℝ := Real.log 4 + 1 / ε + 2 with hGdef
  have hGpos : 0 < G := by
    rw [hGdef]
    have h4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
    have h5 : 0 < 1 / ε := by positivity
    linarith
  set c : ℝ := min (c₀ / 2) (1 / 4) with hcdef
  have hcpos : 0 < c := lt_min (by positivity) (by norm_num)
  have hc_le₂ : c ≤ c₀ / 2 := min_le_left _ _
  have hc_le₄ : c ≤ 1 / 4 := min_le_right _ _
  have hc_le_c₀ : c ≤ c₀ := by linarith
  set C : ℝ := Kn / c * Real.exp (2 * Kc * c * G) + 1 with hCdef
  have hCpos : 0 < C := by rw [hCdef]; positivity
  refine ⟨c, C, hcpos, hCpos, ?_⟩
  intro d chi m Lam hd hchi hAn hagr s hreg hs1
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hd0 : (0 : ℝ) < (d : ℝ) := by linarith
  set t : ℝ := s.im with htdef
  set Mc : ℝ := |(m : ℝ)| + |t| + 3 with hMcdef
  have hMc3 : 3 ≤ Mc := by
    rw [hMcdef]; have h1 := abs_nonneg (m : ℝ); have h2 := abs_nonneg t; linarith
  have hMcpos : 0 < Mc := by linarith
  set L : ℝ := Real.log Mc with hLdef
  have hL1 : 1 < L := by
    have h3 : Real.log 3 ≤ L := by
      rw [hLdef]; exact Real.log_le_log (by norm_num) hMc3
    linarith [Real.log_three_gt_d9]
  have hLpos : 0 < L := by linarith
  set p : ℝ := (d : ℝ) ^ ε with hpdef
  have hp1 : 1 ≤ p := Real.one_le_rpow hd1 hε.le
  have hppos : 0 < p := lt_of_lt_of_le one_pos hp1
  have hp_le_d : p ≤ (d : ℝ) := by
    rw [hpdef]
    have hε1 : ε ≤ 1 := by linarith
    calc (d : ℝ) ^ ε ≤ (d : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hd1 hε1
      _ = (d : ℝ) := Real.rpow_one _
  have hpL1 : 1 ≤ p * L := by nlinarith [hp1, hL1]
  -- the main arithmetic estimate
  have hkey : (Real.log (4 * (d : ℝ) * Mc) + p) / (p * L) ≤ G := by
    have hlog4dMc : Real.log (4 * (d : ℝ) * Mc) = Real.log 4 + Real.log (d : ℝ) + L := by
      rw [show (4 : ℝ) * (d : ℝ) * Mc = (4 * (d : ℝ)) * Mc by ring,
          Real.log_mul (by positivity : (4 * (d : ℝ)) ≠ 0) hMcpos.ne',
          Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) hd0.ne',
          ← hLdef]
    rw [hlog4dMc, hGdef, div_le_iff₀ (by positivity : (0 : ℝ) < p * L)]
    have h4pos : (0 : ℝ) < Real.log 4 := Real.log_pos (by norm_num)
    have h4 : Real.log 4 ≤ Real.log 4 * (p * L) := by
      have := mul_le_mul_of_nonneg_left hpL1 h4pos.le
      simpa using this
    have hdd : Real.log (d : ℝ) ≤ (1 / ε) * (p * L) := by
      have h := Real.log_le_rpow_div hd0.le hε
      rw [← hpdef] at h
      have hpe : p / ε = (1 / ε) * p := by ring
      rw [hpe] at h
      refine le_trans h ?_
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      nlinarith [hL1, hppos]
    have hLp : L + p ≤ 2 * (p * L) := by
      have h1 : 0 ≤ p * (L - 1) := mul_nonneg (by linarith) (by linarith)
      have h2 : 0 ≤ L * (p - 1) := mul_nonneg hLpos.le (by linarith)
      nlinarith [h1, h2]
    nlinarith [h4, hdd, hLp]
  -- the reference height
  set δ : ℝ := c / (p * L) with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; positivity
  have hδ4 : δ ≤ 1 / 4 := by
    rw [hδdef, div_le_iff₀ (by positivity : (0 : ℝ) < p * L)]
    nlinarith [hc_le₄, hpL1]
  have hregδ : 1 - δ < s.re := by
    rw [hδdef]
    exact hreg
  set σ₀ : ℝ := 1 + δ with hσdef
  have hσ₀1 : 1 < σ₀ := by rw [hσdef]; linarith
  have hσ₀2 : σ₀ ≤ 2 := by rw [hσdef]; linarith
  have hσ₀_low : σ₀ - s.re < 2 * δ := by rw [hσdef]; linarith
  set R : ℝ := 2 * δ with hRdef
  have hRpos : 0 < R := by rw [hRdef]; linarith
  have hRhalf : R ≤ 1 / 2 := by rw [hRdef]; linarith
  have hσ₀R : σ₀ - R = 1 - δ := by rw [hσdef, hRdef]; ring
  have hσ₀Rup : σ₀ + R = 1 + 3 * δ := by rw [hσdef, hRdef]; ring
  have hσ₀Rup2 : σ₀ + R < 2 := by rw [hσ₀Rup]; linarith
  -- the log-derivative bound constant
  set A : ℝ := Kc * (Real.log (4 * (d : ℝ) * Mc) + p) with hAdef
  have hApos : 0 < A := by
    rw [hAdef]
    have h4 : 0 < Real.log (4 * (d : ℝ) * Mc) := Real.log_pos (by nlinarith [hd1, hMc3])
    have : 0 < Real.log (4 * (d : ℝ) * Mc) + p := by linarith
    exact mul_pos hKcpos this
  have hAδ : A * δ ≤ Kc * c * G := by
    rw [hAdef, hδdef,
      show Kc * (Real.log (4 * (d : ℝ) * Mc) + p) * (c / (p * L))
        = Kc * c * ((Real.log (4 * (d : ℝ) * Mc) + p) / (p * L)) by ring]
    exact mul_le_mul_of_nonneg_left hkey (by positivity)
  have hAσ : A * (σ₀ - s.re) ≤ 2 * Kc * c * G := by
    have h1 : A * (σ₀ - s.re) ≤ A * (2 * δ) := mul_le_mul_of_nonneg_left hσ₀_low.le hApos.le
    have h2 : A * (2 * δ) = 2 * (A * δ) := by ring
    linarith [h1, h2, hAδ]
  -- the geometry of the segment and the ball
  set cc : ℂ := (σ₀ : ℂ) + (t : ℂ) * Complex.I with hccdef
  set yy : ℂ := (s.re : ℂ) + (t : ℂ) * Complex.I with hyydef
  have hyyeq : yy = s := by rw [hyydef, htdef]; exact Complex.re_add_im s
  have hccre : cc.re = σ₀ := by rw [hccdef]; simp
  have hccim : cc.im = t := by rw [hccdef]; simp
  have hccyy : cc - yy = (((σ₀ - s.re : ℝ)) : ℂ) := by
    rw [hccdef, hyydef]; push_cast; ring
  have hyy_ball : yy ∈ Metric.ball cc R := by
    rw [Metric.mem_ball, dist_eq_norm]
    have h1 : yy - cc = (((s.re - σ₀ : ℝ)) : ℂ) := by
      rw [hyydef, hccdef]; push_cast; ring
    rw [h1, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonpos (by linarith [hσ₀1, hs1]), hRdef]
    linarith [hσ₀_low]
  have hcc_ball : cc ∈ Metric.ball cc R := Metric.mem_ball_self hRpos
  have hball_re_low : ∀ w ∈ Metric.ball cc R, 1 - δ < w.re := by
    intro w hw
    have h1 : ‖w - cc‖ < R := by simpa [Metric.mem_ball, dist_eq_norm] using hw
    have h2 : |w.re - σ₀| ≤ ‖w - cc‖ := by
      have h := Complex.abs_re_le_norm (w - cc)
      rwa [show (w - cc).re = w.re - σ₀ by simp [hccdef]] at h
    have h3 : σ₀ - R < w.re := by
      have := (abs_le.mp h2).1
      linarith
    rw [hσ₀R] at h3
    exact h3
  have hball_re_up : ∀ w ∈ Metric.ball cc R, w.re ≤ 2 := by
    intro w hw
    have h1 : ‖w - cc‖ < R := by simpa [Metric.mem_ball, dist_eq_norm] using hw
    have h2 : |w.re - σ₀| ≤ ‖w - cc‖ := by
      have h := Complex.abs_re_le_norm (w - cc)
      rwa [show (w - cc).re = w.re - σ₀ by simp [hccdef]] at h
    have h3 : w.re ≤ σ₀ + ‖w - cc‖ := by
      have := (abs_le.mp h2).2
      linarith
    have h4 : w.re < σ₀ + R := by linarith
    linarith [hσ₀Rup2]
  have hball_im : ∀ w ∈ Metric.ball cc R, |w.im - t| < R := by
    intro w hw
    have h1 : ‖w - cc‖ < R := by simpa [Metric.mem_ball, dist_eq_norm] using hw
    have h := Complex.abs_im_le_norm (w - cc)
    rw [show (w - cc).im = w.im - t by simp [hccdef]] at h
    linarith
  have hball_log : ∀ w ∈ Metric.ball cc R, Real.log (|(m : ℝ)| + |w.im| + 3) ≤ 2 * L := by
    intro w hw
    have him := hball_im w hw
    have h2 : |w.im| ≤ |t| + |w.im - t| := by
      calc |w.im| = |t + (w.im - t)| := by congr 1; ring
        _ ≤ |t| + |w.im - t| := abs_add_le _ _
    have h3 : |(m : ℝ)| + |w.im| + 3 < Mc + R := by rw [hMcdef]; linarith
    have h4 : 0 < |(m : ℝ)| + |w.im| + 3 := by
      have h1 := abs_nonneg (m : ℝ); have h2 := abs_nonneg w.im; linarith
    have h5 : Mc + R ≤ Mc * Mc := by nlinarith [hMc3, hRhalf, hMcpos, hRpos]
    calc Real.log (|(m : ℝ)| + |w.im| + 3) ≤ Real.log (Mc + R) :=
          Real.log_le_log h4 h3.le
      _ ≤ Real.log (Mc * Mc) := Real.log_le_log (by linarith [hMcpos, hRpos]) h5
      _ = 2 * L := by rw [Real.log_mul hMcpos.ne' hMcpos.ne', hLdef]; ring
  -- zero-freeness of the descent factor on the ball
  have hne_ball : ∀ w ∈ Metric.ball cc R, Lval d m Lam w ≠ 0 := by
    intro w hw
    have hregw : 1 - c₀ / ((d : ℝ) ^ ε * Real.log (|(m : ℝ)| + |w.im| + 3)) ≤ w.re := by
      rw [← hpdef]
      have hlogw := hball_log w hw
      have hlogwpos : 0 < Real.log (|(m : ℝ)| + |w.im| + 3) := by
        refine Real.log_pos ?_
        have h1 := abs_nonneg (m : ℝ); have h2 := abs_nonneg w.im; linarith
      have hpw : 0 < p * Real.log (|(m : ℝ)| + |w.im| + 3) := mul_pos hppos hlogwpos
      have hδle : δ ≤ c₀ / (p * Real.log (|(m : ℝ)| + |w.im| + 3)) := by
        rw [hδdef, div_le_div_iff₀ (by positivity : (0 : ℝ) < p * L) hpw]
        calc c * (p * Real.log (|(m : ℝ)| + |w.im| + 3))
            ≤ (c₀ / 2) * (p * Real.log (|(m : ℝ)| + |w.im| + 3)) :=
              mul_le_mul_of_nonneg_right hc_le₂ (le_of_lt (mul_pos hppos hlogwpos))
          _ ≤ (c₀ / 2) * (p * (2 * L)) :=
              mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left hlogw hppos.le) (by positivity)
          _ = c₀ * (p * L) := by ring
      have h1 := hball_re_low w hw
      linarith
    exact (hcore' d chi m Lam hd hchi hAn hagr w hregw (hball_re_up w hw)).1
  -- analyticity on the ball
  have hre_pos_ball : ∀ w ∈ Metric.ball cc R, 0 < w.re := by
    intro w hw
    have h1 := hball_re_low w hw
    linarith [hδ4]
  have hAnBall : AnalyticOnNhd ℂ (Lval d m Lam) (Metric.ball cc R) := by
    refine DifferentiableOn.analyticOnNhd ?_ Metric.isOpen_ball
    refine DifferentiableOn.div ?_ ?_ ?_
    · exact (hAn.differentiableOn).mono (Set.subset_univ _)
    · intro w hw
      exact (heckeArch_differentiableAt_aux hd m (hre_pos_ball w hw)).differentiableWithinAt
    · intro w hw
      exact heckeArch_ne_zero_of_re_pos_aux hd m (hre_pos_ball w hw)
  -- the log-derivative bound on the segment
  have hsegK : ∀ w ∈ segment ℝ yy cc, ‖deriv (Lval d m Lam) w / Lval d m Lam w‖ ≤ A := by
    intro w hw
    rw [segment_eq_image'] at hw
    obtain ⟨θ, hθ, hθw⟩ := hw
    have hweq : w = yy + θ • (cc - yy) := hθw.symm
    have hweq' : w = (((s.re + θ * (σ₀ - s.re)) : ℝ) : ℂ) + (t : ℂ) * Complex.I := by
      rw [hweq, hccyy, hyydef, Complex.real_smul]
      push_cast
      ring
    have hw_re : w.re = s.re + θ * (σ₀ - s.re) := by rw [hweq']; simp
    have hw_im : w.im = t := by rw [hweq']; simp
    have hw_ge : s.re ≤ w.re := by
      rw [hw_re]
      have h : 0 ≤ θ * (σ₀ - s.re) := mul_nonneg hθ.1 (by linarith [hσ₀1, hs1])
      linarith
    have hw_le : w.re ≤ σ₀ := by
      rw [hw_re]
      nlinarith [hθ.1, hθ.2, hσ₀_low, hs1, hδpos]
    have hlogw : Real.log (|(m : ℝ)| + |w.im| + 3) = L := by
      rw [hw_im, ← hMcdef, ← hLdef]
    have hregw : 1 - c₀ / ((d : ℝ) ^ ε * Real.log (|(m : ℝ)| + |w.im| + 3)) ≤ w.re := by
      rw [← hpdef, hlogw]
      have hδle : δ ≤ c₀ / (p * L) := by
        rw [hδdef, div_le_div_iff₀ (by positivity : (0 : ℝ) < p * L) (by positivity : (0 : ℝ) < p * L)]
        exact mul_le_mul_of_nonneg_right hc_le_c₀ (by positivity)
      linarith [hregδ, hw_ge]
    have hcore_w := hcore' d chi m Lam hd hchi hAn hagr w hregw (by linarith [hw_le, hσ₀2])
    have hlog4 : Real.log (4 * (d : ℝ) * (|(m : ℝ)| + |w.im| + 3)) = Real.log (4 * (d : ℝ) * Mc) := by
      rw [hw_im, ← hMcdef]
    have hb := hcore_w.2
    rw [hlog4, ← hpdef] at hb
    rw [hAdef]
    exact hb
  -- the holomorphic logarithm and the mean-value bound
  obtain ⟨F, _hFdiff, hFder, _hFc, hFre⟩ :=
    Commons.Analysis.Complex.logPrimitiveOnBall_analytic (g := Lval d m Lam) hAnBall hRpos hne_ball
  have hmv : ‖F cc - F yy‖ ≤ A * (σ₀ - s.re) := by
    have h1 : ‖cc - yy‖ = σ₀ - s.re := by
      rw [hccyy, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by linarith [hσ₀1, hs1])]
    have h2 := norm_sub_le_of_segment (F := F) (f := Lval d m Lam) (c := cc) (x := yy) (y := cc)
      (R := R) (K := A) hyy_ball hcc_ball hFder hsegK
    rwa [h1] at h2
  -- lower bound at the reference point
  have hlogcc : Real.log δ - Real.log Kn ≤ Real.log ‖Lval d m Lam cc‖ := by
    have hb := hnear' d chi m Lam hd hchi hAn hagr cc (by rw [hccre]; exact hσ₀1)
      (by rw [hccre]; exact hσ₀2)
    rw [hccre, show σ₀ - 1 = δ by rw [hσdef]; ring, norm_inv] at hb
    have hfpos : 0 < ‖Lval d m Lam cc‖ := norm_pos_iff.mpr (hne_ball cc hcc_ball)
    have h1 : δ ≤ ‖Lval d m Lam cc‖ * Kn := by
      have h := (le_div_iff₀ hδpos).mp hb
      have h4 : δ / ‖Lval d m Lam cc‖ ≤ Kn := by rw [div_eq_inv_mul]; exact h
      have h5 := (div_le_iff₀ hfpos).mp h4
      linarith
    have h2 : δ / Kn ≤ ‖Lval d m Lam cc‖ := (div_le_iff₀ hKnpos).mpr h1
    have h3 : Real.log (δ / Kn) ≤ Real.log ‖Lval d m Lam cc‖ :=
      Real.log_le_log (div_pos hδpos hKnpos) h2
    rwa [Real.log_div hδpos.ne' hKnpos.ne'] at h3
  -- lower bound at `s`
  have hlogmain : Real.log δ - Real.log Kn - 2 * Kc * c * G ≤ Real.log ‖Lval d m Lam yy‖ := by
    have h1 : Real.log ‖Lval d m Lam yy‖
        ≥ Real.log ‖Lval d m Lam cc‖ - A * (σ₀ - s.re) := by
      have h2 : (F cc - F yy).re ≤ ‖F cc - F yy‖ := Complex.re_le_norm _
      rw [Complex.sub_re, hFre cc hcc_ball, hFre yy hyy_ball] at h2
      linarith [h2, hmv]
    linarith [h1, hlogcc, hAσ]
  -- the final arithmetic
  have hCbig : (Kn / c) * Real.exp (2 * Kc * c * G) ≤ C := by
    rw [hCdef]; linarith
  have hKnδ : Kn / δ ≤ (Kn / c) * (d : ℝ) * L ^ 2 := by
    rw [hδdef, div_div_eq_mul_div, div_le_iff₀ hcpos]
    have hpL_le : p * L ≤ (d : ℝ) * L ^ 2 := by nlinarith [hp_le_d, hL1, hd0]
    calc Kn * (p * L) ≤ Kn * ((d : ℝ) * L ^ 2) := mul_le_mul_of_nonneg_left hpL_le hKnpos.le
      _ = (Kn / c * (d : ℝ) * L ^ 2) * c := by field_simp
  have hWle : Kn * Real.exp (2 * Kc * c * G) / δ ≤ C * (d : ℝ) * L ^ 2 := by
    have hE : Kn * Real.exp (2 * Kc * c * G) / δ = (Kn / δ) * Real.exp (2 * Kc * c * G) := by ring
    rw [hE]
    calc (Kn / δ) * Real.exp (2 * Kc * c * G)
        ≤ ((Kn / c) * (d : ℝ) * L ^ 2) * Real.exp (2 * Kc * c * G) :=
          mul_le_mul_of_nonneg_right hKnδ (Real.exp_pos _).le
      _ = ((Kn / c) * Real.exp (2 * Kc * c * G)) * ((d : ℝ) * L ^ 2) := by ring
      _ ≤ C * ((d : ℝ) * L ^ 2) := mul_le_mul_of_nonneg_right hCbig (by positivity)
      _ = C * (d : ℝ) * L ^ 2 := by ring
  have hlogfin : -Real.log (C * (d : ℝ) * L ^ 2) ≤ Real.log δ - Real.log Kn - 2 * Kc * c * G := by
    have hCLpos : 0 < C * (d : ℝ) * L ^ 2 := by positivity
    have hWpos : 0 < Kn * Real.exp (2 * Kc * c * G) / δ := by positivity
    have h1 : Real.log (Kn * Real.exp (2 * Kc * c * G) / δ) ≤ Real.log (C * (d : ℝ) * L ^ 2) :=
      Real.log_le_log hWpos hWle
    have h2 : Real.log (Kn * Real.exp (2 * Kc * c * G) / δ)
        = Real.log Kn + 2 * Kc * c * G - Real.log δ := by
      rw [Real.log_div (by positivity) hδpos.ne',
        Real.log_mul hKnpos.ne' (Real.exp_pos _).ne', Real.log_exp]
    linarith [h1, h2]
  have hZ : -Real.log (C * (d : ℝ) * L ^ 2) ≤ Real.log ‖Lval d m Lam yy‖ :=
    le_trans hlogfin hlogmain
  have hZpos : 0 < ‖Lval d m Lam yy‖ := norm_pos_iff.mpr (hne_ball yy hyy_ball)
  have hCLpos : 0 < C * (d : ℝ) * L ^ 2 := by positivity
  have hexp : (C * (d : ℝ) * L ^ 2)⁻¹ ≤ ‖Lval d m Lam yy‖ := by
    have h1 : Real.exp (-Real.log (C * (d : ℝ) * L ^ 2))
        ≤ Real.exp (Real.log ‖Lval d m Lam yy‖) := Real.exp_le_exp.mpr hZ
    rw [Real.exp_log hZpos] at h1
    rwa [Real.exp_neg, Real.exp_log hCLpos] at h1
  have hfin : ‖(Lval d m Lam yy)⁻¹‖ ≤ C * (d : ℝ) * L ^ 2 := by
    rw [norm_inv]
    have hexp' : 1 / (C * (d : ℝ) * L ^ 2) ≤ ‖Lval d m Lam yy‖ := by
      rw [one_div]; exact hexp
    have h1 : 1 ≤ (C * (d : ℝ) * L ^ 2) * ‖Lval d m Lam yy‖ := by
      have h := (div_le_iff₀ hCLpos).mp hexp'
      calc (1 : ℝ) ≤ ‖Lval d m Lam yy‖ * (C * (d : ℝ) * L ^ 2) := h
        _ = (C * (d : ℝ) * L ^ 2) * ‖Lval d m Lam yy‖ := by ring
    rw [← one_div]
    exact (div_le_iff₀ hZpos).mpr h1
  rw [hyyeq] at hfin
  simpa [Lval] using hfin


end

end Work.FIArea6Hecke
