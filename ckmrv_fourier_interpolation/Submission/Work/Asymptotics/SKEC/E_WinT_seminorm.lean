/-
# The `r`-seminorm bound for the window piece `E_WinT` of the cusp-`0` layer

Given the polynomial window `‖K(w,it)‖ ≤ C (scale w)^N (1+t)^M` on `[1, T w]`
(`Work.Asymptotics.E_window_mid`), the `r`-seminorms of

  `E_WinT ℓ d w r = sinSq r · ∫_1^{T w} Kaxis (Kfun ℓ d) w t · e^{-πr²t} dt`,  `T w = E_T w`,

grow at most like a power of `scale w`, uniformly on `E` and in `r`.
-/
import Mathlib
import Submission.Work.Asymptotics.SKEC.Defs
import Submission.Work.Asymptotics.exists_seminorm_bound_of_iteratedDeriv_bound
import Submission.Work.Asymptotics.Tile.tileIntervalDeriv
import Submission.Work.Asymptotics.layerTrunc_seminorm
import Submission.Work.Asymptotics.measurable_Kfun_snd_all
import Submission.Work.Asymptotics.sinSq_seminorm
import Submission.Work.Kernels.All

noncomputable section

open MeasureTheory Filter Topology UpperHalfPlane
open Work.Kernels
open scoped Topology ContDiff

namespace Work.Asymptotics

/-- The iterated derivatives of `x ↦ e^{a x}` are `a^m e^{a x}` (`a : ℂ`, `x : ℝ`). -/
lemma iteratedDeriv_exp_lin (a : ℂ) (m : ℕ) :
    iteratedDeriv m (fun x : ℝ => Complex.exp (a * (x : ℂ)))
      = fun x : ℝ => a ^ m * Complex.exp (a * (x : ℂ)) := by
  induction m with
  | zero => funext x; rw [iteratedDeriv_zero]; simp
  | succ m ih =>
    rw [iteratedDeriv_succ, ih]
    funext x
    have h2 : HasDerivAt (fun y : ℝ => a * (y : ℂ)) a x := by
      simpa using ((hasDerivAt_id x).ofReal_comp).const_mul a
    have h3 : HasDerivAt (fun y : ℝ => Complex.exp (a * (y : ℂ)))
        (Complex.exp (a * (x : ℂ)) * a) x :=
      (Complex.hasDerivAt_exp _).comp x h2
    have h4 := h3.const_mul (a ^ m)
    rw [h4.deriv]
    ring

/-- The Gaussian factor `sinSq s · e^{-π s² t}` in the `(2 - 2cos (πs²))·F(s²)` shape required by
`Work.Asymptotics.exists_seminorm_bound_of_iteratedDeriv_bound`, with `F x = e^{a x}`,
`a = -(πt)`. -/
lemma gaussFactor_eq_comp (t : ℝ) :
    (fun s : ℝ => sinSq s * Complex.exp (-(Real.pi * (s : ℂ) ^ 2 * (t : ℂ))))
      = fun s : ℝ => (2 - 2 * (Real.cos (Real.pi * s ^ 2) : ℂ))
          * (fun x : ℝ => Complex.exp (((-(Real.pi * t : ℝ)) : ℂ) * (x : ℂ))) (s ^ 2) := by
  funext s
  rw [sinSq_eq]
  congr 2
  push_cast
  ring

/-- **Weighted iterated-derivative bound for the Gaussian factor** `sinSq s · e^{-π s² t}`:
for `t ≥ 1`, `|r|^k ‖∂_r^l (sinSq · e^{-π·²t}) r‖ ≤ c (1+t)^l`. -/
lemma gaussFactor_weighted (k l : ℕ) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ (t r : ℝ), 1 ≤ t →
      |r| ^ k * ‖iteratedDeriv l (fun s : ℝ =>
        sinSq s * Complex.exp (-(Real.pi * (s : ℂ) ^ 2 * (t : ℂ)))) r‖
        ≤ c * (1 + t) ^ l := by
  obtain ⟨c0, hc00, hc0⟩ := exists_seminorm_bound_of_iteratedDeriv_bound k l
  refine ⟨c0 * Real.pi ^ l, by positivity, fun t r ht => ?_⟩
  set a : ℂ := -((Real.pi * t : ℝ) : ℂ) with ha
  have hdiff : ContDiffOn ℝ (l : ℕ∞) (fun x : ℝ => Complex.exp (a * (x : ℂ))) (Set.Ioi (-1)) :=
    ((Complex.contDiff_exp.comp (contDiff_const.mul Complex.ofRealCLM.contDiff)).contDiffOn)
  have hbd : ∀ m ≤ l, ∀ x : ℝ, 0 ≤ x →
      ‖iteratedDeriv m (fun x : ℝ => Complex.exp (a * (x : ℂ))) x‖
        ≤ (Real.pi * t) ^ l * Real.exp (-(Real.pi * x)) := by
    intro m hm x hx
    rw [iteratedDeriv_exp_lin a m, norm_mul, norm_pow]
    have ha_norm : ‖a‖ = Real.pi * t := by
      rw [ha, norm_neg, norm_ofReal_eq_abs, abs_of_nonneg (by positivity)]
    rw [ha_norm, Complex.norm_exp]
    have hre : (a * (x : ℂ)).re = -(Real.pi * t * x) := by
      simp only [ha, Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.ofReal_re,
        Complex.ofReal_im, mul_zero, sub_zero]
      ring
    rw [hre]
    have hπt : (1 : ℝ) ≤ Real.pi * t := by
      nlinarith [Real.pi_gt_three, ht]
    have h1 : (Real.pi * t) ^ m ≤ (Real.pi * t) ^ l := pow_le_pow_right₀ hπt hm
    have h2 : Real.exp (-(Real.pi * t * x)) ≤ Real.exp (-(Real.pi * x)) := by
      refine Real.exp_le_exp.mpr ?_
      have hpos : (0 : ℝ) ≤ Real.pi * x * (t - 1) := by positivity
      nlinarith [hpos]
    exact mul_le_mul h1 h2 (Real.exp_pos _).le (by positivity)
  have hJ := hc0 (fun x : ℝ => Complex.exp (a * (x : ℂ))) ((Real.pi * t) ^ l) (by positivity)
    hdiff hbd r
  rw [← gaussFactor_eq_comp t] at hJ
  refine le_trans hJ ?_
  have h1 : (Real.pi * t) ^ l ≤ Real.pi ^ l * (1 + t) ^ l := by
    rw [mul_pow]
    refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg Real.pi_pos.le l)
    exact pow_le_pow_left₀ (by linarith) (by linarith) l
  nlinarith [h1, hc00, Real.pi_pos, pow_pos Real.pi_pos l,
    pow_nonneg (by positivity : (0:ℝ) ≤ 1 + t) l]

/-- **Unweighted iterated-derivative bound for the Gaussian factor.** -/
lemma gaussFactor_plain (j : ℕ) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ (t r : ℝ), 1 ≤ t →
      ‖iteratedDeriv j (fun s : ℝ =>
        sinSq s * Complex.exp (-(Real.pi * (s : ℂ) ^ 2 * (t : ℂ)))) r‖ ≤ c * (1 + t) ^ j := by
  simpa using gaussFactor_weighted 0 j

theorem E_WinT_seminorm (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (C N M : ℝ) (hC : 0 < C) (hN : 0 ≤ N) (hM : 0 ≤ M)
    (hwin : ∀ (w : UpperHalfPlane) (t : ℝ), w ∈ Work.Asymptotics.KEpsilon → 1 ≤ t →
      t ≤ Work.Asymptotics.E_T w →
      ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) w t‖
        ≤ C * (Work.Kernels.scale w) ^ N * (1 + t) ^ M) :
    ∀ k l : ℕ, ∃ c N' : ℝ, 0 ≤ c ∧ 0 ≤ N' ∧
      ∀ (w : UpperHalfPlane), w ∈ Work.Asymptotics.KEpsilon → ∀ r : ℝ,
        (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ => Work.Asymptotics.E_WinT ℓ d w s) r‖
          ≤ c * (Work.Kernels.scale w) ^ N' := by
  intro k l
  obtain ⟨cW, hcW0, hcW⟩ := gaussFactor_weighted k l
  choose cs hcs0 hcs using fun j : ℕ => gaussFactor_plain j
  set CG : ℝ := ∑ j ∈ Finset.range (l + 1), cs j with hCGdef
  have hCG0 : 0 ≤ CG := by rw [hCGdef]; exact Finset.sum_nonneg fun j _ => hcs0 j
  have hCGj : ∀ j : ℕ, j ≤ l → cs j ≤ CG := by
    intro j hj
    rw [hCGdef]
    exact Finset.single_le_sum (fun i _ => hcs0 i) (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))
  refine ⟨(C * cW + CG * C) * 2 ^ (M + (l : ℝ)), N + M + l + 1, by positivity, by positivity, ?_⟩
  intro w hw r
  have hB1 : (1 : ℝ) ≤ E_T w := one_le_E_T hw
  have hBle : E_T w ≤ scale w := E_T_le_scale hw
  have hs1 : (1 : ℝ) ≤ scale w := one_le_scale w
  have hsp0 : (0 : ℝ) ≤ scale w := (scale_pos w).le
  set kfun : ℝ → ℝ → ℂ := fun s t => Kaxis (Kfun ℓ d) w t
    * (sinSq s * Complex.exp (-(Real.pi * (s : ℂ) ^ 2 * (t : ℂ)))) with hkfun
  have hlayer : ∀ s : ℝ, E_WinT ℓ d w s = ∫ t in (1 : ℝ)..(E_T w), kfun s t := by
    intro s
    rw [E_WinT, hkfun]
    rw [show (fun t : ℝ => Kaxis (Kfun ℓ d) w t
          * (sinSq s * Complex.exp (-(Real.pi * (s : ℂ) ^ 2 * (t : ℂ)))))
        = fun t : ℝ => (Kaxis (Kfun ℓ d) w t
          * Complex.exp (-(Real.pi * (s : ℂ) ^ 2 * (t : ℂ)))) * sinSq s from by
      funext t; ring]
    rw [intervalIntegral.integral_mul_const]
    ring
  have hmeasK : Measurable (fun t : ℝ => Kaxis (Kfun ℓ d) w t) :=
    measurable_Kaxis_of_measurable _ _ (measurable_Kfun_snd_all ℓ d hd w)
  have hsm : ∀ t : ℝ, ContDiff ℝ ∞ (fun s : ℝ =>
      sinSq s * Complex.exp (-(Real.pi * (s : ℂ) ^ 2 * (t : ℂ)))) := by
    intro t
    refine ContDiff.mul ?_ ?_
    · have h2 : ContDiff ℝ ∞ (fun s : ℝ => (2 - 2 * Real.cos (Real.pi * s ^ 2) : ℝ)) := by
        fun_prop
      have h3 : ContDiff ℝ ∞ (fun s : ℝ => ((2 - 2 * Real.cos (Real.pi * s ^ 2) : ℝ) : ℂ)) :=
        Complex.ofRealCLM.contDiff.comp h2
      have hfun : (fun s : ℝ => ((2 - 2 * Real.cos (Real.pi * s ^ 2) : ℝ) : ℂ))
          = fun s : ℝ => sinSq s := by
        funext s
        rw [sinSq_eq]
        push_cast
        ring
      rw [hfun] at h3
      exact h3
    · refine Complex.contDiff_exp.comp ?_
      exact (((contDiff_const.mul (Complex.ofRealCLM.contDiff.pow 2)).mul contDiff_const)).neg
  have hmeas : ∀ s : ℝ, Measurable (fun t : ℝ => kfun s t) := by
    intro s
    rw [hkfun]
    exact hmeasK.mul (by fun_prop)
  have hsmooth : ∀ t : ℝ, ContDiff ℝ ∞ (fun s : ℝ => kfun s t) := by
    intro t
    rw [hkfun]
    exact contDiff_const.mul (hsm t)
  have hbd : ∀ j : ℕ, j ≤ l → ∃ bd : ℝ → ℝ, IntegrableOn bd (Set.Ioc (1 : ℝ) (E_T w)) ∧
      ∀ᵐ u ∂(volume.restrict (Set.Ioc (1 : ℝ) (E_T w))), ∀ s : ℝ,
        ‖iteratedDeriv j (fun s' : ℝ => kfun s' u) s‖ ≤ bd u := by
    intro j hj
    refine ⟨fun _ => CG * (C * (scale w) ^ N * (1 + E_T w) ^ (M + l)),
      integrableOn_const (by simp), ?_⟩
    filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with u hu
    obtain ⟨hu1, huT⟩ := hu
    intro s
    have hu1' : (1 : ℝ) ≤ u := hu1.le
    have hfac : iteratedDeriv j (fun s' : ℝ => kfun s' u) s
        = Kaxis (Kfun ℓ d) w u * iteratedDeriv j
            (fun x : ℝ => sinSq x * Complex.exp (-(Real.pi * (x : ℂ) ^ 2 * (u : ℂ)))) s := by
      have h1 : (fun s' : ℝ => kfun s' u) = fun s' : ℝ =>
          Kaxis (Kfun ℓ d) w u * (sinSq s'
            * Complex.exp (-(Real.pi * (s' : ℂ) ^ 2 * (u : ℂ)))) := by
        funext s'; rw [hkfun]
      rw [h1]
      refine iteratedDeriv_const_mul _ ?_
      exact ((hsm u).contDiffAt).of_le (WithTop.coe_le_coe.mpr le_top)
    rw [hfac, norm_mul]
    have hstep1 : ‖Kaxis (Kfun ℓ d) w u‖ ≤ C * (scale w) ^ N * (1 + u) ^ M :=
      hwin w u hw hu1' (le_trans huT le_rfl)
    have hstep2 : ‖iteratedDeriv j (fun x : ℝ =>
          sinSq x * Complex.exp (-(Real.pi * (x : ℂ) ^ 2 * (u : ℂ)))) s‖
          ≤ CG * (1 + u) ^ l := by
      have hJ := hcs j u s hu1'
      have h1 : (1 + u) ^ j ≤ (1 + u) ^ l := by
        rw [← Real.rpow_natCast (1 + u) j, ← Real.rpow_natCast (1 + u) l]
        exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by exact_mod_cast hj)
      calc ‖iteratedDeriv j (fun x : ℝ =>
            sinSq x * Complex.exp (-(Real.pi * (x : ℂ) ^ 2 * (u : ℂ)))) s‖
          ≤ cs j * (1 + u) ^ j := hJ
        _ ≤ CG * (1 + u) ^ l := mul_le_mul (hCGj j hj) h1 (by positivity) hCG0
    refine le_trans (mul_le_mul hstep1 hstep2 (norm_nonneg _) (by positivity)) ?_
    have hpow : (1 + u) ^ M * (1 + u) ^ l = (1 + u) ^ (M + l) := by
      rw [← Real.rpow_natCast (1 + u) l,
        ← Real.rpow_add (by linarith : (0 : ℝ) < 1 + u)]
    have hle : (1 + u) ^ (M + l) ≤ (1 + E_T w) ^ (M + l) :=
      Real.rpow_le_rpow (by linarith) (by linarith) (by positivity)
    calc C * (scale w) ^ N * (1 + u) ^ M * (CG * (1 + u) ^ l)
        = CG * (C * (scale w) ^ N) * ((1 + u) ^ M * (1 + u) ^ l) := by ring
      _ = CG * (C * (scale w) ^ N) * (1 + u) ^ (M + l) := by rw [hpow]
      _ ≤ CG * (C * (scale w) ^ N) * (1 + E_T w) ^ (M + l) :=
          mul_le_mul_of_nonneg_left hle (by positivity)
      _ = CG * (C * (scale w) ^ N * (1 + E_T w) ^ (M + l)) := by ring
  have hderiv : iteratedDeriv l (fun s : ℝ => E_WinT ℓ d w s) r
      = ∫ t in (1 : ℝ)..(E_T w), iteratedDeriv l (fun s : ℝ => kfun s t) r := by
    have hfun : (fun s : ℝ => E_WinT ℓ d w s)
        = fun s : ℝ => ∫ t in (1 : ℝ)..(E_T w), kfun s t := funext hlayer
    rw [hfun,
      iteratedDeriv_intervalIntegral_of_meas_bound_interval kfun l hB1 hmeas hsmooth hbd l le_rfl]
  have hpoint : ∀ t ∈ Set.uIoc (1 : ℝ) (E_T w),
      ‖((((|r| ^ k : ℝ)) : ℂ)) • iteratedDeriv l (fun s : ℝ => kfun s t) r‖
        ≤ (C * cW + CG * C) * (scale w) ^ N * (1 + E_T w) ^ (M + l) := by
    intro t ht
    rw [Set.uIoc_of_le hB1] at ht
    obtain ⟨ht1, htT⟩ := ht
    have ht1' : (1 : ℝ) ≤ t := ht1.le
    have hfac : iteratedDeriv l (fun s : ℝ => kfun s t) r
        = Kaxis (Kfun ℓ d) w t * iteratedDeriv l
            (fun x : ℝ => sinSq x * Complex.exp (-(Real.pi * (x : ℂ) ^ 2 * (t : ℂ)))) r := by
      have h1 : (fun s : ℝ => kfun s t) = fun s : ℝ =>
          Kaxis (Kfun ℓ d) w t * (sinSq s
            * Complex.exp (-(Real.pi * (s : ℂ) ^ 2 * (t : ℂ)))) := by
        funext s; rw [hkfun]
      rw [h1]
      refine iteratedDeriv_const_mul _ ?_
      exact ((hsm t).contDiffAt).of_le (WithTop.coe_le_coe.mpr le_top)
    rw [hfac, norm_smul, norm_mul]
    have hnc : ‖((((|r| ^ k : ℝ)) : ℂ))‖ = |r| ^ k := by
      rw [norm_ofReal_eq_abs, abs_of_nonneg (by positivity)]
    rw [hnc]
    have hstep1 : ‖Kaxis (Kfun ℓ d) w t‖ ≤ C * (scale w) ^ N * (1 + t) ^ M :=
      hwin w t hw ht1' htT
    have hstep2 : |r| ^ k * ‖iteratedDeriv l (fun x : ℝ =>
          sinSq x * Complex.exp (-(Real.pi * (x : ℂ) ^ 2 * (t : ℂ)))) r‖ ≤ cW * (1 + t) ^ l :=
      hcW t r ht1'
    have hpow : (1 + t) ^ M * (1 + t) ^ l = (1 + t) ^ (M + l) := by
      rw [← Real.rpow_natCast (1 + t) l,
        ← Real.rpow_add (by linarith : (0 : ℝ) < 1 + t)]
    have hle : (1 + t) ^ (M + l) ≤ (1 + E_T w) ^ (M + l) :=
      Real.rpow_le_rpow (by linarith) (by linarith) (by positivity)
    calc |r| ^ k * (‖Kaxis (Kfun ℓ d) w t‖
          * ‖iteratedDeriv l (fun x : ℝ => sinSq x
            * Complex.exp (-(Real.pi * (x : ℂ) ^ 2 * (t : ℂ)))) r‖)
        = ‖Kaxis (Kfun ℓ d) w t‖ * (|r| ^ k * ‖iteratedDeriv l (fun x : ℝ =>
            sinSq x * Complex.exp (-(Real.pi * (x : ℂ) ^ 2 * (t : ℂ)))) r‖) := by ring
      _ ≤ (C * (scale w) ^ N * (1 + t) ^ M) * (cW * (1 + t) ^ l) :=
          mul_le_mul hstep1 hstep2 (by positivity) (by positivity)
      _ = C * cW * (scale w) ^ N * ((1 + t) ^ M * (1 + t) ^ l) := by ring
      _ = C * cW * (scale w) ^ N * (1 + t) ^ (M + l) := by rw [hpow]
      _ ≤ C * cW * (scale w) ^ N * (1 + E_T w) ^ (M + l) := by
          refine mul_le_mul_of_nonneg_left hle (by positivity)
      _ ≤ (C * cW + CG * C) * (scale w) ^ N * (1 + E_T w) ^ (M + l) := by
          have hCG : (0 : ℝ) ≤ CG * C := mul_nonneg hCG0 hC.le
          have h1 : C * cW ≤ C * cW + CG * C := by linarith
          calc C * cW * (scale w) ^ N * (1 + E_T w) ^ (M + l)
              = (C * cW) * ((scale w) ^ N * (1 + E_T w) ^ (M + l)) := by ring
            _ ≤ (C * cW + CG * C) * ((scale w) ^ N * (1 + E_T w) ^ (M + l)) :=
                mul_le_mul_of_nonneg_right h1 (by positivity)
            _ = (C * cW + CG * C) * (scale w) ^ N * (1 + E_T w) ^ (M + l) := by ring
  have hmain : |r| ^ k * ‖∫ t in (1 : ℝ)..(E_T w), iteratedDeriv l (fun s : ℝ => kfun s t) r‖
      ≤ (C * cW + CG * C) * (scale w) ^ N * ((1 + E_T w) ^ (M + l) * (E_T w - 1)) := by
    have hnorm_int : |r| ^ k * ‖∫ t in (1 : ℝ)..(E_T w), iteratedDeriv l (fun s : ℝ => kfun s t) r‖
        = ‖∫ t in (1 : ℝ)..(E_T w), ((((|r| ^ k : ℝ)) : ℂ))
            • iteratedDeriv l (fun s : ℝ => kfun s t) r‖ := by
      have hnc : ‖((((|r| ^ k : ℝ)) : ℂ))‖ = |r| ^ k := by
        rw [norm_ofReal_eq_abs, abs_of_nonneg (by positivity)]
      rw [intervalIntegral.integral_smul, norm_smul, hnc]
    rw [hnorm_int]
    have hlen : |E_T w - 1| = E_T w - 1 := abs_of_nonneg (by linarith)
    have hconst : (0 : ℝ) ≤ (C * cW + CG * C) * (scale w) ^ N * (1 + E_T w) ^ (M + l) := by
      positivity
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (1 : ℝ)) (b := E_T w) hpoint
    rw [hlen] at h
    refine le_trans h (le_of_eq ?_)
    ring
  calc |r| ^ k * ‖iteratedDeriv l (fun s : ℝ => E_WinT ℓ d w s) r‖
      = |r| ^ k * ‖∫ t in (1 : ℝ)..(E_T w), iteratedDeriv l (fun s : ℝ => kfun s t) r‖ := by
        rw [hderiv]
    _ ≤ (C * cW + CG * C) * (scale w) ^ N * ((1 + E_T w) ^ (M + l) * (E_T w - 1)) := hmain
    _ ≤ ((C * cW + CG * C) * 2 ^ (M + (l : ℝ))) * (scale w) ^ (N + M + l + 1) := by
        have h1 : (1 + E_T w) ^ (M + l) ≤ (2 * scale w) ^ (M + l) :=
          Real.rpow_le_rpow (by linarith) (by linarith) (by positivity)
        have h2 : E_T w - 1 ≤ scale w := by linarith
        have h4 : (0 : ℝ) ≤ (C * cW + CG * C) * (scale w) ^ N := by positivity
        have h5 : (2 * scale w) ^ (M + l) = 2 ^ (M + l) * (scale w) ^ (M + l) :=
          Real.mul_rpow (by norm_num) hsp0
        have h6 : (scale w) ^ (N + M + l + 1)
            = (scale w) ^ N * (scale w) ^ (M + l) * scale w := by
          rw [show N + M + l + 1 = N + ((M + (l : ℝ)) + 1) by ring,
            Real.rpow_add (scale_pos w) N ((M + (l : ℝ)) + 1),
            Real.rpow_add (scale_pos w) (M + (l : ℝ)) 1, Real.rpow_one]
          ring
        have h7 : (2 : ℝ) ^ (M + l) ≤ 2 ^ (M + (l : ℝ)) := le_refl _
        have h1' : (1 + E_T w) ^ (M + l) * (E_T w - 1)
            ≤ (2 ^ (M + l) * (scale w) ^ (M + l)) * scale w := by
          rw [← h5]
          exact mul_le_mul h1 h2 (by linarith) (by positivity)
        calc (C * cW + CG * C) * (scale w) ^ N * ((1 + E_T w) ^ (M + l) * (E_T w - 1))
            ≤ (C * cW + CG * C) * (scale w) ^ N
                * ((2 ^ (M + l) * (scale w) ^ (M + l)) * scale w) :=
              mul_le_mul_of_nonneg_left h1' h4
          _ = (C * cW + CG * C) * 2 ^ (M + l)
                * ((scale w) ^ N * (scale w) ^ (M + l) * scale w) := by ring
          _ = (C * cW + CG * C) * 2 ^ (M + l) * (scale w) ^ (N + M + l + 1) := by rw [h6]
          _ ≤ (C * cW + CG * C) * 2 ^ (M + (l : ℝ)) * (scale w) ^ (N + M + l + 1) := by
              refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hsp0 _)
              exact mul_le_mul_of_nonneg_left h7 (by positivity)
          _ = ((C * cW + CG * C) * 2 ^ (M + (l : ℝ))) * (scale w) ^ (N + M + l + 1) := by ring

end Work.Asymptotics
