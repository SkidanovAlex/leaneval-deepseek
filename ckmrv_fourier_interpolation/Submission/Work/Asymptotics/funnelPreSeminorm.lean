import Mathlib
import Submission.Work.Asymptotics.FunnelAsm.funnelDefs
import Submission.Work.Asymptotics.HalfFunnel.funnelPreDeclash
import Submission.Work.Asymptotics.exists_seminorm_bound_of_iteratedDeriv_bound
import Submission.Work.Asymptotics.layerLow_seminorm
import Submission.Work.Asymptotics.funnelSpikeSeminorm

namespace Work.Asymptotics

open MeasureTheory UpperHalfPlane Work.Kernels
open scoped Topology ContDiff

noncomputable section

/-- `S ^ a * S = S ^ (a + 1)` for a positive base. -/
lemma rpow_mul_one (S : ℝ) (hS : 0 < S) (a : ℝ) : S ^ a * S = S ^ (a + 1) := by
  rw [Real.rpow_add hS, Real.rpow_one]

/-- `S ^ a * (c * S ^ b) = c * S ^ (a + b)` for a positive base. -/
lemma rpow_fact (S : ℝ) (hS : 0 < S) (a b c : ℝ) :
    S ^ a * (c * S ^ b) = c * S ^ (a + b) := by
  rw [mul_comm (S ^ a) (c * S ^ b), mul_assoc, mul_comm (S ^ b) (S ^ a),
    ← Real.rpow_add hS]

/-!
# The `r`-seminorms of the `pre` piece of the funnel layer

`preT ℓ d τ x = ∫_{1}^{Im τ - 1} K(τ,it) e^{-π x t} dt` is the window piece of the CKMRV layer
on the funnel.  The pre-declash estimate `funnelPreDeclash` gives, on the window
`1 ≤ t ≤ Im τ - 1`,

  `‖K(τ,it)‖ ≤ C · (scale τ)^N · (1+t)^M · e^{a t}`,  `a = 0` (`d = 8`), `a = 2π` (`d = 24`),

so the derivatives of `preT` in the Fourier variable `x` are bounded by
`C · π^l · (scale τ)^N · (1+Im τ)^{M+l} · e^{a} · e^{-π x}` as soon as `π x ≥ a` (i.e. `x ≥ 0` in
eight dimensions and `x ≥ 2` in twenty-four, which is exactly the convergence condition
`d = 8 ∨ 2 ≤ x` of the paper).  The composition with `s ↦ sinSq s · F(s²)` — the chain rule with
the regularising factor `sinSq s = 2 - 2cos(π s²)` — then produces the seminorm bound.
-/

/-- **The derivatives of the window piece `preT` on the funnel.**  There are constants `c, N`,
independent of `τ` and `x`, such that `preT ℓ d τ` is `C^l` on `(-1,∞)` and all its derivatives
of order `≤ l` satisfy `‖∂^m (preT ℓ d τ) x‖ ≤ c (scale τ)^N e^{-π x}` in the region
`x ≥ 0` (`d = 8`) resp. `x ≥ 2` (`d = 24`). -/
lemma preT_deriv_bound (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) (l : ℕ) :
    ∃ c N : ℝ, 0 ≤ c ∧ 0 ≤ N ∧
      ∀ (τ : UpperHalfPlane), Funnel τ →
        ContDiffOn ℝ (l : ℕ∞ω) (fun y : ℝ => preT ℓ d τ y) (Set.Ioi (-1)) ∧
        ∀ (x : ℝ), (if d = 8 then (0 : ℝ) else 2) ≤ x →
          ∀ m : ℕ, m ≤ l →
            ‖iteratedDeriv m (preT ℓ d τ) x‖ ≤ c * (scale τ) ^ N * Real.exp (-(Real.pi * x)) := by
  obtain ⟨C, N₀, M, hC, hN₀, hM, hpre⟩ := (Work.Asymptotics.HalfFunnel.funnelPreDeclash ℓ d hd).1
  have hc0 : (0 : ℝ) ≤ C * Real.pi ^ l * Real.exp (if d = 8 then 0 else 2 * Real.pi)
      * 2 ^ (M + (l : ℝ)) := by
    refine mul_nonneg (mul_nonneg (mul_nonneg hC.le (by positivity))
      (Real.exp_pos _).le) ?_
    exact Real.rpow_nonneg (by norm_num) _
  have hN : (0 : ℝ) ≤ N₀ + (M + (l : ℝ)) + 1 := by linarith
  refine ⟨C * Real.pi ^ l * Real.exp (if d = 8 then 0 else 2 * Real.pi) * 2 ^ (M + (l : ℝ)),
    N₀ + (M + (l : ℝ)) + 1, hc0, hN, ?_⟩
  intro τ hτ
  set a : ℝ := (if d = 8 then 0 else 2 * Real.pi) with hadef
  have ha0 : 0 ≤ a := by
    rcases hd with h8 | h24
    · simp [a, h8]
    · have h : ¬ d = 8 := by omega
      simp only [a, if_neg h]; positivity
  have hY2 : 2 ≤ τ.im := hτ.2
  have hSpos : 0 < scale τ := scale_pos τ
  have hSN₀ : (0 : ℝ) ≤ (scale τ) ^ N₀ := Real.rpow_nonneg hSpos.le N₀
  have hYS : τ.im ≤ scale τ := le_trans (im_le_coe_norm τ) (coe_norm_le_scale τ)
  have h1Y : (1 : ℝ) ≤ τ.im - 1 := by linarith
  set f : ℝ → ℂ := fun t => Kaxis (Kfun ℓ d) τ t with hf
  have hfmeas : AEStronglyMeasurable f (volume.restrict (Set.Ioc (1 : ℝ) (τ.im - 1))) := by
    rw [hf]
    exact (measurable_Kaxis_of_measurable (Kfun ℓ d) τ
      (measurable_Kfun_snd_all ℓ d hd τ)).aestronglyMeasurable
  set B : ℝ := C * (scale τ) ^ N₀ * (1 + (τ.im - 1)) ^ M * Real.exp (a * (τ.im - 1))
    with hBdef
  have hB0 : 0 ≤ B := by
    rw [hBdef]
    exact mul_nonneg (mul_nonneg (mul_nonneg hC.le hSN₀)
      (Real.rpow_nonneg (by linarith) M)) (Real.exp_pos _).le
  have hbd : ∀ᵐ t ∂(volume.restrict (Set.Ioc (1 : ℝ) (τ.im - 1))), ‖f t‖ ≤ B := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with t ht
    have ht1 : (1 : ℝ) ≤ t := le_of_lt ht.1
    have ht2 : t ≤ τ.im - 1 := ht.2
    have hft := hpre τ t hτ.1 hY2 ht1 ht2
    have h1 : (1 + t) ^ M ≤ (1 + (τ.im - 1)) ^ M :=
      Real.rpow_le_rpow (by linarith) (by linarith) hM
    have h2 : Real.exp (a * t) ≤ Real.exp (a * (τ.im - 1)) :=
      Real.exp_le_exp.mpr (by nlinarith [ha0, ht2])
    have h3 : (1 + t) ^ M * Real.exp (a * t)
        ≤ (1 + (τ.im - 1)) ^ M * Real.exp (a * (τ.im - 1)) :=
      mul_le_mul h1 h2 (Real.exp_pos _).le (Real.rpow_nonneg (by linarith) M)
    have hK : (0 : ℝ) ≤ C * (scale τ) ^ N₀ := mul_nonneg hC.le hSN₀
    rw [hf]
    calc ‖Kaxis (Kfun ℓ d) τ t‖
        ≤ C * (scale τ) ^ N₀ * (1 + t) ^ M * Real.exp (a * t) := hft
      _ = (C * (scale τ) ^ N₀) * ((1 + t) ^ M * Real.exp (a * t)) := by ring
      _ ≤ (C * (scale τ) ^ N₀) * ((1 + (τ.im - 1)) ^ M * Real.exp (a * (τ.im - 1))) :=
          mul_le_mul_of_nonneg_left h3 hK
      _ = B := by rw [hBdef]; ring
  have hpre_eq : preT ℓ d τ
      = fun y : ℝ => ∫ t in (1 : ℝ)..(τ.im - 1),
          f t * ((Real.exp (-(Real.pi * y * t)) : ℝ) : ℂ) := by
    funext y
    rw [preT, hf]
    refine intervalIntegral.integral_congr (fun t _ => ?_)
    rw [wgt_apply, Complex.ofReal_exp, Complex.ofReal_neg]
  refine ⟨?_, ?_⟩
  · rw [hpre_eq]
    exact contDiffOn_intervalIntegral_exp_bound f 1 (τ.im - 1) h1Y hfmeas hB0 hbd l
  · intro x hx m hm
    have hx0 : (0 : ℝ) ≤ x := by
      have h1 : (0 : ℝ) ≤ (if d = 8 then (0 : ℝ) else 2) := by
        by_cases h8 : d = 8
        · rw [if_pos h8]
        · rw [if_neg h8]; norm_num
      linarith
    have hax : a ≤ Real.pi * x := by
      rw [hadef]
      have h1 : (if d = 8 then 0 else 2 * Real.pi)
          ≤ Real.pi * (if d = 8 then (0 : ℝ) else 2) := by
        by_cases h8 : d = 8
        · rw [if_pos h8, if_pos h8]; positivity
        · rw [if_neg h8, if_neg h8]; nlinarith [Real.pi_pos]
      have h2 : Real.pi * (if d = 8 then (0 : ℝ) else 2) ≤ Real.pi * x :=
        mul_le_mul_of_nonneg_left hx Real.pi_pos.le
      linarith
    -- pointwise bound for the differentiated integrand
    have hpt : ∀ t ∈ Set.uIoc (1 : ℝ) (τ.im - 1),
        ‖f t * (((-(Real.pi * t) : ℝ)) : ℂ) ^ m
            * ((Real.exp (-(Real.pi * x * t)) : ℝ) : ℂ)‖
          ≤ C * Real.pi ^ l * (scale τ) ^ N₀ * (1 + τ.im) ^ (M + (l : ℝ)) * Real.exp a
              * Real.exp (-(Real.pi * x)) := by
      intro t ht
      rw [Set.uIoc_of_le h1Y] at ht
      have ht1 : (1 : ℝ) ≤ t := le_of_lt ht.1
      have ht2 : t ≤ τ.im - 1 := ht.2
      have hft : ‖f t‖ ≤ C * (scale τ) ^ N₀ * (1 + t) ^ M * Real.exp (a * t) := by
        rw [hf]; exact hpre τ t hτ.1 hY2 ht1 ht2
      have ht0 : (0 : ℝ) < t := by linarith
      have hpit : (1 : ℝ) ≤ Real.pi * t := by nlinarith [Real.pi_gt_three, ht1]
      have hfac : ‖((( -(Real.pi * t)) : ℝ) : ℂ) ^ m‖ = (Real.pi * t) ^ m := by
        rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_mul,
          abs_of_pos Real.pi_pos, abs_of_pos ht0]
      have hexp : ‖((Real.exp (-(Real.pi * x * t)) : ℝ) : ℂ)‖
          = Real.exp (-(Real.pi * x * t)) := by
        rw [Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (Real.exp_pos (-(Real.pi * x * t)))]
      have hpow : (Real.pi * t) ^ m ≤ Real.pi ^ l * (1 + t) ^ (l : ℝ) := by
        have h1 : (Real.pi * t) ^ m ≤ (Real.pi * t) ^ l := pow_le_pow_right₀ hpit hm
        have h2 : (Real.pi * t) ^ l = Real.pi ^ l * t ^ l := mul_pow _ _ _
        have h3 : (t : ℝ) ^ l ≤ (1 + t) ^ (l : ℝ) := by
          rw [Real.rpow_natCast]
          exact pow_le_pow_left₀ (by linarith) (by linarith) l
        calc (Real.pi * t) ^ m ≤ (Real.pi * t) ^ l := h1
          _ = Real.pi ^ l * t ^ l := h2
          _ ≤ Real.pi ^ l * (1 + t) ^ (l : ℝ) := mul_le_mul_of_nonneg_left h3 (by positivity)
      have hexp2 : Real.exp (a * t - Real.pi * x * t) ≤ Real.exp a * Real.exp (-(Real.pi * x)) := by
        have h2 : (a - Real.pi * x) * (t - 1) ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
        rw [← Real.exp_add]
        exact Real.exp_le_exp.mpr (by linarith)
      have hpow2 : (1 + t) ^ M * (1 + t) ^ (l : ℝ) ≤ (1 + τ.im) ^ (M + (l : ℝ)) := by
        rw [← Real.rpow_add (by linarith : (0:ℝ) < 1 + t)]
        exact Real.rpow_le_rpow (by linarith) (by linarith) (by positivity)
      have hnorm : ‖f t * (((-(Real.pi * t) : ℝ)) : ℂ) ^ m
            * ((Real.exp (-(Real.pi * x * t)) : ℝ) : ℂ)‖
          = ‖f t‖ * (Real.pi * t) ^ m * Real.exp (-(Real.pi * x * t)) := by
        rw [norm_mul, norm_mul, hfac, hexp]
      rw [hnorm]
      have h2 : (0 : ℝ) ≤ C * (scale τ) ^ N₀ * (1 + t) ^ M * Real.exp (a * t) :=
        mul_nonneg (mul_nonneg (mul_nonneg hC.le hSN₀)
          (Real.rpow_nonneg (by linarith) M)) (Real.exp_pos _).le
      have h3 : (0 : ℝ) ≤ Real.exp (-(Real.pi * x * t)) := (Real.exp_pos _).le
      have hE : Real.exp (a * t) * Real.exp (-(Real.pi * x * t))
          = Real.exp (a * t - Real.pi * x * t) := by rw [← Real.exp_add]; ring_nf
      have hA0 : (0 : ℝ) ≤ C * Real.pi ^ l * (scale τ) ^ N₀ :=
        mul_nonneg (mul_nonneg hC.le (by positivity)) hSN₀
      calc ‖f t‖ * (Real.pi * t) ^ m * Real.exp (-(Real.pi * x * t))
          ≤ (C * (scale τ) ^ N₀ * (1 + t) ^ M * Real.exp (a * t)) * (Real.pi * t) ^ m
              * Real.exp (-(Real.pi * x * t)) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hft (by positivity)) h3
        _ ≤ (C * (scale τ) ^ N₀ * (1 + t) ^ M * Real.exp (a * t))
              * (Real.pi ^ l * (1 + t) ^ (l : ℝ)) * Real.exp (-(Real.pi * x * t)) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow h2) h3
        _ = C * Real.pi ^ l * (scale τ) ^ N₀ * ((1 + t) ^ M * (1 + t) ^ (l : ℝ))
              * Real.exp (a * t - Real.pi * x * t) := by
            rw [← hE]; ring
        _ ≤ C * Real.pi ^ l * (scale τ) ^ N₀ * (1 + τ.im) ^ (M + (l : ℝ))
              * (Real.exp a * Real.exp (-(Real.pi * x))) :=
            mul_le_mul (mul_le_mul_of_nonneg_left hpow2 hA0) hexp2 (Real.exp_pos _).le
              (mul_nonneg hA0 (Real.rpow_nonneg (by linarith) (M + (l : ℝ))))
        _ = C * Real.pi ^ l * (scale τ) ^ N₀ * (1 + τ.im) ^ (M + (l : ℝ)) * Real.exp a
              * Real.exp (-(Real.pi * x)) := by ring
    rw [hpre_eq, iteratedDeriv_intervalIntegral_exp_bound f 1 (τ.im - 1) h1Y hfmeas hB0 hbd m x]
    have hlen : |(τ.im - 1) - 1| = τ.im - 2 := by
      rw [abs_of_nonneg (by linarith)]; ring
    -- the final bookkeeping
    have hY1 : (1 : ℝ) ≤ τ.im := by linarith
    have hA0 : (0 : ℝ) ≤ τ.im - 2 := by linarith
    have hstep2 : τ.im - 2 ≤ scale τ := le_trans (by linarith) hYS
    have hstep1 : (1 + τ.im) ^ (M + (l : ℝ)) ≤ (2 * scale τ) ^ (M + (l : ℝ)) :=
      Real.rpow_le_rpow (by linarith) (by linarith) (by positivity)
    have hmult : (1 + τ.im) ^ (M + (l : ℝ)) * (τ.im - 2)
        ≤ 2 ^ (M + (l : ℝ)) * (scale τ) ^ (M + (l : ℝ) + 1) := by
      have h2S : (0 : ℝ) ≤ 2 * scale τ := by positivity
      have hA : (0 : ℝ) ≤ (2 * scale τ) ^ (M + (l : ℝ)) := Real.rpow_nonneg h2S _
      calc (1 + τ.im) ^ (M + (l : ℝ)) * (τ.im - 2)
          ≤ (2 * scale τ) ^ (M + (l : ℝ)) * scale τ :=
            mul_le_mul hstep1 hstep2 hA0 hA
        _ = 2 ^ (M + (l : ℝ)) * (scale τ) ^ (M + (l : ℝ)) * scale τ := by
            rw [Real.mul_rpow (by norm_num) hSpos.le]
        _ = 2 ^ (M + (l : ℝ)) * ((scale τ) ^ (M + (l : ℝ)) * scale τ) := by ring
        _ = 2 ^ (M + (l : ℝ)) * (scale τ) ^ (M + (l : ℝ) + 1) := by
            rw [rpow_mul_one (scale τ) hSpos (M + (l : ℝ))]
    have hmain2 : (C * Real.pi ^ l * (scale τ) ^ N₀ * (1 + τ.im) ^ (M + (l : ℝ))
            * Real.exp a * Real.exp (-(Real.pi * x))) * (τ.im - 2)
        ≤ (C * Real.pi ^ l * Real.exp a * 2 ^ (M + (l : ℝ)))
            * (scale τ) ^ (N₀ + (M + (l : ℝ)) + 1) * Real.exp (-(Real.pi * x)) := by
      calc (C * Real.pi ^ l * (scale τ) ^ N₀ * (1 + τ.im) ^ (M + (l : ℝ))
              * Real.exp a * Real.exp (-(Real.pi * x))) * (τ.im - 2)
          = C * Real.pi ^ l * Real.exp a * Real.exp (-(Real.pi * x))
              * ((scale τ) ^ N₀ * ((1 + τ.im) ^ (M + (l : ℝ)) * (τ.im - 2))) := by ring
        _ ≤ C * Real.pi ^ l * Real.exp a * Real.exp (-(Real.pi * x))
              * ((scale τ) ^ N₀
                  * (2 ^ (M + (l : ℝ)) * (scale τ) ^ (M + (l : ℝ) + 1))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hmult hSN₀)
              (mul_nonneg (mul_nonneg (mul_nonneg hC.le (by positivity))
                (Real.exp_pos _).le) (Real.exp_pos _).le)
        _ = (C * Real.pi ^ l * Real.exp a * 2 ^ (M + (l : ℝ)))
              * (scale τ) ^ (N₀ + (M + (l : ℝ)) + 1) * Real.exp (-(Real.pi * x)) := by
            rw [show N₀ + (M + (l : ℝ)) + 1 = N₀ + (M + (l : ℝ) + 1) by ring,
              rpow_fact (scale τ) hSpos N₀ (M + (l : ℝ) + 1) ((2 : ℝ) ^ (M + (l : ℝ)))]
            ring
    calc ‖∫ t in (1 : ℝ)..(τ.im - 1), f t * (((-(Real.pi * t) : ℝ)) : ℂ) ^ m
            * ((Real.exp (-(Real.pi * x * t)) : ℝ) : ℂ)‖
        ≤ (C * Real.pi ^ l * (scale τ) ^ N₀ * (1 + τ.im) ^ (M + (l : ℝ)) * Real.exp a
              * Real.exp (-(Real.pi * x))) * |(τ.im - 1) - 1| :=
          intervalIntegral.norm_integral_le_of_norm_le_const hpt
      _ = (C * Real.pi ^ l * (scale τ) ^ N₀ * (1 + τ.im) ^ (M + (l : ℝ)) * Real.exp a
              * Real.exp (-(Real.pi * x))) * (τ.im - 2) := by rw [hlen]
      _ ≤ (C * Real.pi ^ l * Real.exp a * 2 ^ (M + (l : ℝ)))
            * (scale τ) ^ (N₀ + (M + (l : ℝ)) + 1) * Real.exp (-(Real.pi * x)) := hmain2
      _ = C * Real.pi ^ l * Real.exp (if d = 8 then 0 else 2 * Real.pi) * 2 ^ (M + (l : ℝ))
            * (scale τ) ^ (N₀ + (M + (l : ℝ)) + 1) * Real.exp (-(Real.pi * x)) := by
          rw [hadef]

/-- **CKMRV, Proposition 4.6 (the window piece of the funnel layer):** the `r`-seminorms of
`sinSq r · ∫_1^{Im τ - 1} K(τ,it) e^{-π r² t} dt` are bounded by a polynomial in `scale τ` on the
funnel, in the region `d = 8 ∨ 2 ≤ r²` where the Gaussian weight dominates the exponential growth
of the kernel. -/
theorem funnelPreSeminorm (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (k l : ℕ) :
    ∃ c N : ℝ, 0 ≤ c ∧ 0 ≤ N ∧ ∀ (τ : UpperHalfPlane) (r : ℝ), Work.Asymptotics.Funnel τ →
      (d = 8 ∨ 2 ≤ r ^ 2) →
      (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ => Work.Asymptotics.sinSq s *
        Work.Asymptotics.preT ℓ d τ (s ^ 2)) r‖ ≤ c * (Work.Kernels.scale τ) ^ N := by
  obtain ⟨c₁, N₁, hc₁, hN₁, hpre⟩ := preT_deriv_bound ℓ d hd l
  obtain ⟨W, hW0, hW⟩ := exists_bound_abs_pow_mul_exp_neg_sq k l
  refine ⟨(l.factorial : ℝ) * (4 * (2 * Real.pi) ^ l) * c₁ * W, N₁, by positivity, hN₁, ?_⟩
  intro τ r hτ hreg
  have hr2 : (if d = 8 then (0 : ℝ) else 2) ≤ r ^ 2 := by
    by_cases h8 : d = 8
    · rw [if_pos h8]; positivity
    · rw [if_neg h8]
      rcases hreg with h | h
      · exact absurd h h8
      · exact h
  obtain ⟨hCD, hbd⟩ := hpre τ hτ
  have hSN₁ : (0 : ℝ) ≤ (scale τ) ^ N₁ := Real.rpow_nonneg (scale_pos τ).le N₁
  have hc1N : (0 : ℝ) ≤ c₁ * (scale τ) ^ N₁ * Real.exp (-(Real.pi * r ^ 2)) :=
    mul_nonneg (mul_nonneg hc₁ hSN₁) (Real.exp_pos _).le
  have hcont_cos : ContDiffOn ℝ (l : ℕ∞ω)
      (fun y : ℝ => (2 - 2 * Real.cos (Real.pi * y) : ℂ)) (Set.Ioi (-1)) := by
    have h1 : ContDiff ℝ (l : ℕ∞ω) (fun y : ℝ => (2 - 2 * Real.cos (Real.pi * y))) := by
      fun_prop
    have h2 := Complex.ofRealCLM.contDiff.comp h1
    refine h2.contDiffOn.congr (fun y _ => ?_)
    show (2 - 2 * (Real.cos (Real.pi * y) : ℂ)) = ((2 - 2 * Real.cos (Real.pi * y) : ℝ) : ℂ)
    push_cast
    ring
  have hfcont : ContDiffOn ℝ (l : ℕ∞ω) (fun s : ℝ => s ^ 2) Set.univ :=
    ((contDiff_id (𝕜 := ℝ)).pow 2).contDiffOn
  set C₀ : ℝ := (4 * (2 * Real.pi) ^ l) * (c₁ * (scale τ) ^ N₁ * Real.exp (-(Real.pi * r ^ 2)))
    with hC₀def
  have hbnd : ∀ i ≤ l, ‖iteratedDeriv i
      (fun y : ℝ => (2 - 2 * Real.cos (Real.pi * y) : ℂ) * preT ℓ d τ y) (r ^ 2)‖
      ≤ (4 * (2 * Real.pi) ^ l) * (c₁ * (scale τ) ^ N₁ * Real.exp (-(Real.pi * r ^ 2))) := by
    intro i hi
    have hr2mem : r ^ 2 ∈ Set.Ioi (-1) := by rw [Set.mem_Ioi]; nlinarith [sq_nonneg r]
    have hmul := norm_iteratedFDerivWithin_mul_le (𝕜 := ℝ) (s := Set.Ioi (-1))
      (f := fun y : ℝ => (2 - 2 * Real.cos (Real.pi * y) : ℂ))
      (g := fun y : ℝ => preT ℓ d τ y) (N := (l : ℕ∞ω)) hcont_cos hCD
      (uniqueDiffOn_Ioi (-1)) hr2mem
      (show (i : ℕ∞ω) ≤ (l : ℕ∞ω) from by exact_mod_cast hi)
    have hL : ‖iteratedFDerivWithin ℝ i
          (fun y : ℝ => (2 - 2 * Real.cos (Real.pi * y) : ℂ) * preT ℓ d τ y)
          (Set.Ioi (-1)) (r ^ 2)‖
        = ‖iteratedDeriv i
          (fun y : ℝ => (2 - 2 * Real.cos (Real.pi * y) : ℂ) * preT ℓ d τ y) (r ^ 2)‖ :=
      norm_iteratedFDerivWithin_eq_of_isOpen isOpen_Ioi hr2mem i _
    rw [hL] at hmul
    have hstep : ∀ j ∈ Finset.range (i + 1),
        (i.choose j : ℝ) *
          ‖iteratedFDerivWithin ℝ j
            (fun y : ℝ => (2 - 2 * Real.cos (Real.pi * y) : ℂ)) (Set.Ioi (-1)) (r ^ 2)‖ *
          ‖iteratedFDerivWithin ℝ (i - j) (fun y : ℝ => preT ℓ d τ y) (Set.Ioi (-1)) (r ^ 2)‖
        ≤ (i.choose j : ℝ) * (4 * Real.pi ^ j)
            * (c₁ * (scale τ) ^ N₁ * Real.exp (-(Real.pi * r ^ 2))) := by
      intro j hj
      have hc : ‖iteratedFDerivWithin ℝ j
            (fun y : ℝ => (2 - 2 * Real.cos (Real.pi * y) : ℂ)) (Set.Ioi (-1)) (r ^ 2)‖
          ≤ 4 * Real.pi ^ j := by
        rw [norm_iteratedFDerivWithin_eq_of_isOpen isOpen_Ioi hr2mem j]
        exact norm_iteratedDeriv_two_sub_two_cos j (r ^ 2)
      have ht : ‖iteratedFDerivWithin ℝ (i - j) (fun y : ℝ => preT ℓ d τ y)
            (Set.Ioi (-1)) (r ^ 2)‖
          ≤ c₁ * (scale τ) ^ N₁ * Real.exp (-(Real.pi * r ^ 2)) := by
        rw [norm_iteratedFDerivWithin_eq_of_isOpen isOpen_Ioi hr2mem (i - j)]
        exact hbd (r ^ 2) hr2 (i - j) (le_trans (Nat.sub_le i j) hi)
      exact mul_le_mul (mul_le_mul_of_nonneg_left hc (by positivity)) ht
        (by positivity) (by positivity)
    have hsum2 : (∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) * (4 * Real.pi ^ j))
        ≤ 4 * (2 * Real.pi) ^ l := by
      have hbin : (∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ)) = 2 ^ i := by
        have hh := add_pow (1 : ℝ) 1 i
        rw [one_add_one_eq_two] at hh
        rw [hh]
        apply Finset.sum_congr rfl
        intro j hj
        rw [one_pow, one_pow]
        ring
      calc (∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) * (4 * Real.pi ^ j))
          ≤ ∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) * (4 * Real.pi ^ l) := by
            refine Finset.sum_le_sum (fun j hj => ?_)
            have hjle : j ≤ l := le_trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)) hi
            have hpi : Real.pi ^ j ≤ Real.pi ^ l :=
              pow_le_pow_right₀ (by linarith [Real.pi_gt_three] : (1 : ℝ) ≤ Real.pi) hjle
            exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpi (by norm_num))
              (by positivity)
        _ = (∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ)) * (4 * Real.pi ^ l) := by
            rw [Finset.sum_mul]
        _ = 2 ^ i * (4 * Real.pi ^ l) := by rw [hbin]
        _ ≤ 4 * (2 * Real.pi) ^ l := by
            have h2 : (2 : ℝ) ^ i ≤ 2 ^ l := pow_le_pow_right₀ (by norm_num) hi
            have h3 : (2 : ℝ) ^ i * (4 * Real.pi ^ l) ≤ 2 ^ l * (4 * Real.pi ^ l) :=
              mul_le_mul_of_nonneg_right h2 (by positivity)
            refine h3.trans_eq ?_
            rw [mul_pow]
            ring
    calc ‖iteratedDeriv i
          (fun y : ℝ => (2 - 2 * Real.cos (Real.pi * y) : ℂ) * preT ℓ d τ y) (r ^ 2)‖
        ≤ ∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) *
            ‖iteratedFDerivWithin ℝ j
              (fun y : ℝ => (2 - 2 * Real.cos (Real.pi * y) : ℂ)) (Set.Ioi (-1)) (r ^ 2)‖ *
            ‖iteratedFDerivWithin ℝ (i - j) (fun y : ℝ => preT ℓ d τ y) (Set.Ioi (-1)) (r ^ 2)‖ :=
          hmul
      _ ≤ ∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) * (4 * Real.pi ^ j) *
            (c₁ * (scale τ) ^ N₁ * Real.exp (-(Real.pi * r ^ 2))) := Finset.sum_le_sum hstep
      _ = (c₁ * (scale τ) ^ N₁ * Real.exp (-(Real.pi * r ^ 2))) *
            (∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) * (4 * Real.pi ^ j)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j hj
          ring
      _ ≤ (c₁ * (scale τ) ^ N₁ * Real.exp (-(Real.pi * r ^ 2))) * (4 * (2 * Real.pi) ^ l) :=
          mul_le_mul_of_nonneg_left hsum2 hc1N
      _ = (4 * (2 * Real.pi) ^ l) * (c₁ * (scale τ) ^ N₁ * Real.exp (-(Real.pi * r ^ 2))) := by
          ring
  have hCbound : ∀ i ≤ l,
      ‖iteratedFDerivWithin ℝ i
        (fun y : ℝ => (2 - 2 * Real.cos (Real.pi * y) : ℂ) * preT ℓ d τ y)
        (Set.Ioi (-1)) (r ^ 2)‖ ≤ C₀ := by
    intro i hi
    have hr2mem : r ^ 2 ∈ Set.Ioi (-1) := by rw [Set.mem_Ioi]; nlinarith [sq_nonneg r]
    rw [norm_iteratedFDerivWithin_eq_of_isOpen isOpen_Ioi hr2mem i, hC₀def]
    exact hbnd i hi
  set D₀ : ℝ := 2 * |r| + 2 with hD₀def
  have hD₀0 : (0 : ℝ) ≤ D₀ := by rw [hD₀def]; positivity
  have hDbound : ∀ i, 1 ≤ i → i ≤ l →
      ‖iteratedFDerivWithin ℝ i (fun s : ℝ => s ^ 2) Set.univ r‖ ≤ D₀ ^ i := by
    intro i hi _
    rw [iteratedFDerivWithin_univ, norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    exact norm_iteratedDeriv_sq_le hi r
  have hcomp := norm_iteratedFDerivWithin_comp_le (𝕜 := ℝ)
    (g := fun y : ℝ => (2 - 2 * Real.cos (Real.pi * y) : ℂ) * preT ℓ d τ y)
    (f := fun s : ℝ => s ^ 2) (n := l) (s := Set.univ) (t := Set.Ioi (-1))
    (x := r) (N := (l : ℕ∞ω)) (hcont_cos.mul hCD) hfcont le_rfl
    (uniqueDiffOn_Ioi (-1)) uniqueDiffOn_univ
    (by intro x _; rw [Set.mem_Ioi]; nlinarith [sq_nonneg x]) (Set.mem_univ r) hCbound hDbound
  have hkey : ‖iteratedDeriv l (fun s : ℝ => sinSq s * preT ℓ d τ (s ^ 2)) r‖
      = ‖iteratedFDerivWithin ℝ l
          ((fun y : ℝ => (2 - 2 * Real.cos (Real.pi * y) : ℂ) * preT ℓ d τ y)
            ∘ (fun s : ℝ => s ^ 2)) Set.univ r‖ := by
    have heq : (fun s : ℝ => sinSq s * preT ℓ d τ (s ^ 2))
        = (fun y : ℝ => (2 - 2 * Real.cos (Real.pi * y) : ℂ) * preT ℓ d τ y)
          ∘ (fun s : ℝ => s ^ 2) := by
      funext s
      rw [Function.comp_apply, sinSq_eq]
    rw [heq, ← norm_iteratedFDeriv_eq_norm_iteratedDeriv, ← iteratedFDerivWithin_univ]
  have hcoef : (0 : ℝ) ≤ (l.factorial : ℝ) * (4 * (2 * Real.pi) ^ l) * c₁ * (scale τ) ^ N₁ :=
    mul_nonneg (mul_nonneg (mul_nonneg (by positivity) (by positivity)) hc₁) hSN₁
  calc (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ => sinSq s * preT ℓ d τ (s ^ 2)) r‖
      = (|r| ^ k) * ‖iteratedFDerivWithin ℝ l
          ((fun y : ℝ => (2 - 2 * Real.cos (Real.pi * y) : ℂ) * preT ℓ d τ y)
            ∘ (fun s : ℝ => s ^ 2)) Set.univ r‖ := by rw [hkey]
    _ ≤ (|r| ^ k) * ((l.factorial : ℝ) * C₀ * D₀ ^ l) :=
        mul_le_mul_of_nonneg_left hcomp (by positivity)
    _ = ((l.factorial : ℝ) * (4 * (2 * Real.pi) ^ l) * c₁ * (scale τ) ^ N₁)
          * (|r| ^ k * (2 * |r| + 2) ^ l * Real.exp (-(Real.pi * r ^ 2))) := by
        rw [hC₀def, hD₀def]; ring
    _ ≤ ((l.factorial : ℝ) * (4 * (2 * Real.pi) ^ l) * c₁ * (scale τ) ^ N₁) * W :=
        mul_le_mul_of_nonneg_left (hW r) hcoef
    _ = ((l.factorial : ℝ) * (4 * (2 * Real.pi) ^ l) * c₁ * W) * (scale τ) ^ N₁ := by ring

end

end Work.Asymptotics
