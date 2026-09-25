import Mathlib
import Submission.Commons.NumberTheory.Zeta.zeta_logDeriv_negStrip_bound
import Submission.Commons.NumberTheory.Zeta.zeta_logDeriv_left_far_strip_bound_negOne

/-!
# The far-left vertical edge bound for `a ∈ [-3/2, -1/4]`

The vertical-edge integral of the ζ₁-Perron kernel
`x^s/(s(s−1)) − (ζ₁'/ζ₁)(s)·x^s/s` along `Re s = a`, for `a ∈ [-3/2, -1/4]` and `Tp ≥ 5`,
is bounded, under the Riemann hypothesis, by `C·x^a·(log(Tp+3)+1)^4`.

Under RH the strip `−3/2 ≤ Re s ≤ −1/4` is zero-free for `ζ`: a zero there is neither `1`
nor a trivial zero `−2(n+1)` (whose real part is `≤ −2`), so RH forces real part `1/2`.  On
the compact part `|Im s| ≤ 3` this yields a plain bound; in the tail `|Im s| ≥ 2` the
functional-equation bounds `zeta_logDeriv_negStrip_bound` (for `σ ≤ −1/2`) and
`zeta_logDeriv_left_far_strip_bound_negOne` (for `σ ≥ −1/2`) give `O((log |Im s|)^3)`.
The whole integrand is therefore dominated by `K·x^a/(|y|+1)`, whose integral over
`[−Tp, Tp]` is `≤ 2K log((Tp+1)/2) + 2K`, i.e. `O(x^a (log Tp)^4)`.
-/

open Complex MeasureTheory intervalIntegral
open scoped Real Topology BigOperators

noncomputable section
set_option maxHeartbeats 1000000

namespace Commons.NumberTheory.Zeta

/-- The ζ₁-form of the Perron integrand. -/
private def kern (x : ℝ) (s : ℂ) : ℂ :=
  - (logDeriv riemannZeta₁ s) * ((x : ℂ) ^ s / s) + (x : ℂ) ^ s / (s * (s - 1))

/-- Norm bound for the Perron kernel in terms of `logDeriv ζ₁`, `‖s‖` and `‖s − 1‖`. -/
private lemma norm_kern_le {x : ℝ} (hx : 0 < x) (s : ℂ) :
    ‖kern x s‖ ≤
      (‖logDeriv riemannZeta₁ s‖ + 1 / ‖s - 1‖) * ((x : ℝ) ^ s.re / ‖s‖) := by
  have hnorm_cpow : ‖(x : ℂ) ^ s‖ = (x : ℝ) ^ s.re :=
    Complex.norm_cpow_eq_rpow_re_of_pos hx s
  have h1 : ‖-(logDeriv riemannZeta₁ s) * ((x : ℂ) ^ s / s)‖ =
      ‖logDeriv riemannZeta₁ s‖ * ((x : ℝ) ^ s.re / ‖s‖) := by
    rw [norm_mul, norm_neg, norm_div, hnorm_cpow]
  have h2 : ‖(x : ℂ) ^ s / (s * (s - 1))‖ = (x : ℝ) ^ s.re / (‖s‖ * ‖s - 1‖) := by
    rw [norm_div, norm_mul, hnorm_cpow]
  have hdecomp : kern x s =
      -(logDeriv riemannZeta₁ s) * ((x : ℂ) ^ s / s) + (x : ℂ) ^ s / (s * (s - 1)) := rfl
  have hsplit : ‖kern x s‖ ≤
      ‖logDeriv riemannZeta₁ s‖ * ((x : ℝ) ^ s.re / ‖s‖) +
        (x : ℝ) ^ s.re / (‖s‖ * ‖s - 1‖) := by
    rw [hdecomp]
    calc
      ‖-(logDeriv riemannZeta₁ s) * ((x : ℂ) ^ s / s) + (x : ℂ) ^ s / (s * (s - 1))‖
          ≤ ‖-(logDeriv riemannZeta₁ s) * ((x : ℂ) ^ s / s)‖ +
            ‖(x : ℂ) ^ s / (s * (s - 1))‖ := norm_add_le _ _
      _ = _ := by rw [h1, h2]
  have hstep2 : (x : ℝ) ^ s.re / (‖s‖ * ‖s - 1‖) =
      ((x : ℝ) ^ s.re / ‖s‖) * (1 / ‖s - 1‖) := by
    field_simp
  rw [hstep2] at hsplit
  calc
    ‖kern x s‖ ≤ ‖logDeriv riemannZeta₁ s‖ * ((x : ℝ) ^ s.re / ‖s‖) +
        ((x : ℝ) ^ s.re / ‖s‖) * (1 / ‖s - 1‖) := hsplit
    _ = (‖logDeriv riemannZeta₁ s‖ + 1 / ‖s - 1‖) * ((x : ℝ) ^ s.re / ‖s‖) := by ring

/-- Under RH `ζ₁` does not vanish on the wide far-left rectangle `−3/2 ≤ Re s ≤ −1/4`:
a zero of `ζ` there is neither `1` nor a trivial zero `−2(n+1)`, so RH forces real part `1/2`. -/
private lemma zeta1_ne_zero_farleft_wide (h : RiemannHypothesis) {s : ℂ}
    (hlo : -(3 / 2 : ℝ) ≤ s.re) (hhi : s.re ≤ -(1 / 4 : ℝ)) :
    riemannZeta₁ s ≠ 0 := by
  intro hz
  have hs1 : s ≠ 1 := by
    intro hh
    have hre : s.re = 1 := by rw [hh]; simp
    linarith
  have hzeta : riemannZeta s = 0 := by
    rw [riemannZeta_eq_inv_sub_mul hs1, hz, mul_zero]
  rcases Classical.em (∃ n : ℕ, s = -2 * (n + 1)) with htriv | htriv
  · rcases htriv with ⟨n, hn⟩
    have hre := congrArg Complex.re hn
    have hren : ((-2 : ℂ) * ((n : ℂ) + 1)).re = -2 * ((n : ℝ) + 1) := by norm_num
    rw [hren] at hre
    have hn0 : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
    linarith
  · have hhalf : s.re = 1 / 2 := h s hzeta htriv hs1
    linarith

/-- `logDeriv ζ₁` is bounded on the compact wide far-left rectangle, under RH. -/
private lemma zeta1_logDeriv_farleft_compact_wide (h : RiemannHypothesis) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, -(3 / 2 : ℝ) ≤ s.re → s.re ≤ -(1 / 4 : ℝ) → |s.im| ≤ 3 →
      ‖logDeriv riemannZeta₁ s‖ ≤ C := by
  let K : Set ℂ := {s : ℂ | -(3 / 2 : ℝ) ≤ s.re ∧ s.re ≤ -(1 / 4 : ℝ) ∧ |s.im| ≤ 3}
  have hKcompact : IsCompact K := by
    have himg : K = (fun p : ℝ × ℝ => ((p.1 : ℂ) + Complex.I * (p.2 : ℂ))) ''
        (Set.Icc (-(3 / 2 : ℝ)) (-(1 / 4 : ℝ)) ×ˢ Set.Icc (-3 : ℝ) 3) := by
      ext s
      constructor
      · rintro ⟨h1, h2, h3⟩
        rw [abs_le] at h3
        exact ⟨(s.re, s.im), ⟨⟨h1, h2⟩, h3⟩, by
          apply Complex.ext <;> simp⟩
      · rintro ⟨p, hp, rfl⟩
        obtain ⟨⟨hp1, hp2⟩, hp3, hp4⟩ := hp
        have hre : (((p.1 : ℂ) + Complex.I * (p.2 : ℂ))).re = p.1 := by simp
        have him : (((p.1 : ℂ) + Complex.I * (p.2 : ℂ))).im = p.2 := by simp
        refine ⟨?_, ?_, ?_⟩
        · rw [hre]; exact hp1
        · rw [hre]; exact hp2
        · rw [him, abs_le]; exact ⟨hp3, hp4⟩
    rw [himg]
    exact (isCompact_Icc.prod isCompact_Icc).image (by fun_prop)
  have hKne : K.Nonempty := ⟨((-(1 / 4 : ℝ)) : ℂ), by
    refine ⟨by norm_num, by norm_num, by norm_num⟩⟩
  have hne : ∀ s ∈ K, riemannZeta₁ s ≠ 0 := by
    intro s hs
    exact zeta1_ne_zero_farleft_wide h hs.1 hs.2.1
  have hcont : ContinuousOn (fun s : ℂ => ‖logDeriv riemannZeta₁ s‖) K := by
    have hderiv : Continuous (deriv riemannZeta₁) :=
      (differentiable_riemannZeta₁.contDiff (n := ⊤)).continuous_deriv le_top
    have hdiv : ContinuousOn (logDeriv riemannZeta₁) K :=
      hderiv.continuousOn.div differentiable_riemannZeta₁.continuous.continuousOn hne
    exact hdiv.norm
  rcases hKcompact.exists_isMaxOn hKne hcont with ⟨a, _haK, hmax⟩
  refine ⟨‖logDeriv riemannZeta₁ a‖ + 1, by positivity, ?_⟩
  intro s hs1 hs2 hs3
  have hsK : s ∈ K := ⟨hs1, hs2, hs3⟩
  have hle : ‖logDeriv riemannZeta₁ s‖ ≤ ‖logDeriv riemannZeta₁ a‖ := hmax hsK
  linarith

/-- Uniform far-strip bound for `logDeriv ζ₁` on `−3/2 ≤ σ ≤ −1/4`, `|t| ≥ 2`, under RH.
This combines `zeta_logDeriv_negStrip_bound` (for `σ ≤ −1/2`) with
`zeta_logDeriv_left_far_strip_bound_negOne` (for `σ ≥ −1/2`). -/
private lemma zeta_logDeriv_left_far_strip_bound_wide (h : RiemannHypothesis) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ t : ℝ, -(3 / 2 : ℝ) ≤ σ → σ ≤ -(1 / 4 : ℝ) → 2 ≤ |t| →
      ‖logDeriv riemannZeta₁ ((σ : ℂ) + Complex.I * (t : ℂ))‖ ≤
        C * (Real.log (|t| + 3) + 1) ^ 3 := by
  rcases zeta_logDeriv_negStrip_bound h with ⟨C₂, hC₂pos, hC₂b⟩
  rcases zeta_logDeriv_left_far_strip_bound_negOne h with ⟨C₃, hC₃pos, hC₃b⟩
  refine ⟨C₂ + C₃, by linarith, ?_⟩
  intro σ t hlo hhi ht
  have hL3nn : 0 ≤ (Real.log (|t| + 3) + 1) ^ 3 := by
    apply pow_nonneg
    have h1 : (0 : ℝ) ≤ Real.log (|t| + 3) := Real.log_nonneg (by linarith [abs_nonneg t])
    linarith
  by_cases hle : σ ≤ -(1 / 2 : ℝ)
  · have hb := hC₂b σ t hlo hle ht
    calc
      ‖logDeriv riemannZeta₁ ((σ : ℂ) + Complex.I * (t : ℂ))‖
          ≤ C₂ * (Real.log (|t| + 3) + 1) ^ 3 := hb
      _ ≤ (C₂ + C₃) * (Real.log (|t| + 3) + 1) ^ 3 :=
          mul_le_mul_of_nonneg_right (by linarith) hL3nn
  · have hb := hC₃b σ t (by linarith) (by linarith) ht
    calc
      ‖logDeriv riemannZeta₁ ((σ : ℂ) + Complex.I * (t : ℂ))‖
          ≤ C₃ * (Real.log (|t| + 3) + 1) ^ 3 := hb
      _ ≤ (C₂ + C₃) * (Real.log (|t| + 3) + 1) ^ 3 :=
          mul_le_mul_of_nonneg_right (by linarith) hL3nn

theorem edgeL_farleft_neg_three_halves_bound (h : RiemannHypothesis) :
    ∃ C : ℝ, 0 < C ∧ ∀ (x a Tp : ℝ), 1 ≤ x → -(3 / 2 : ℝ) ≤ a → a ≤ -(1 / 4 : ℝ) → 5 ≤ Tp →
      ‖(∫ (y : ℝ) in -Tp..Tp,
        (-(logDeriv riemannZeta₁ ((a : ℂ) + Complex.I * (y : ℂ))) *
            ((x : ℂ) ^ ((a : ℂ) + Complex.I * (y : ℂ)) /
              ((a : ℂ) + Complex.I * (y : ℂ))) +
          (x : ℂ) ^ ((a : ℂ) + Complex.I * (y : ℂ)) /
            (((a : ℂ) + Complex.I * (y : ℂ)) *
              (((a : ℂ) + Complex.I * (y : ℂ)) - 1))))‖ ≤
        C * (x : ℝ) ^ a * (Real.log (Tp + 3) + 1) ^ 4 := by
  rcases zeta1_logDeriv_farleft_compact_wide h with ⟨Cc, hCcpos, hCcb⟩
  rcases zeta_logDeriv_left_far_strip_bound_wide h with ⟨Cf, hCfpos, hCfb⟩
  refine ⟨4 * (12 * (Cc + 2) + 2 * Cf + 1), by linarith, ?_⟩
  intro x a Tp hx ha1 ha2 hTp
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le one_pos hx
  set LT : ℝ := Real.log (Tp + 3) + 1 with hLT
  set xr : ℝ := (x : ℝ) ^ a with hxr
  have hxr0 : 0 ≤ xr := by rw [hxr]; exact Real.rpow_nonneg (le_of_lt hx0) _
  have hxrpos : 0 < xr := by rw [hxr]; exact Real.rpow_pos_of_pos hx0 _
  have hLT1 : 1 ≤ LT := by
    rw [hLT]
    have h2 : (0 : ℝ) ≤ Real.log (Tp + 3) := Real.log_nonneg (by linarith)
    linarith
  have hLT0 : 0 ≤ LT := le_trans zero_le_one hLT1
  set K : ℝ := 12 * (Cc + 2) * xr + 2 * Cf * LT ^ 3 * xr with hK
  have hKpos : 0 < K := by
    rw [hK]
    have h1 : 0 < 12 * (Cc + 2) * xr := mul_pos (by linarith) hxrpos
    have h2 : 0 ≤ 2 * Cf * LT ^ 3 * xr := by positivity
    linarith
  let F : ℝ → ℂ := fun y => kern x ((a : ℂ) + Complex.I * (y : ℂ))
  change ‖(∫ (y : ℝ) in -Tp..Tp, F y)‖ ≤
      4 * (12 * (Cc + 2) + 2 * Cf + 1) * (x : ℝ) ^ a *
        (Real.log (Tp + 3) + 1) ^ 4
  -- pointwise domination of the integrand by `K/(|y|+1)`
  have hdom : ∀ y ∈ Set.Ioc (-Tp) Tp, ‖F y‖ ≤ K / (|y| + 1) := by
    intro y hy
    have hden : (0 : ℝ) < |y| + 1 := by positivity
    let s : ℂ := (a : ℂ) + Complex.I * (y : ℂ)
    have hFs : F y = kern x s := rfl
    have hsr : s.re = a := by simp [s]
    have hsi : s.im = y := by simp [s]
    have hkern := norm_kern_le hx0 s
    by_cases hy2 : |y| ≤ 2
    · -- compact part: `|Im s| ≤ 3`
      have h3 : |y| ≤ 3 := by linarith
      have hlog : ‖logDeriv riemannZeta₁ s‖ ≤ Cc := by
        refine hCcb s ?_ ?_ ?_
        · rw [hsr]; exact ha1
        · rw [hsr]; exact ha2
        · rw [hsi]; exact h3
      have hs_ge : (1 / 4 : ℝ) ≤ ‖s‖ := by
        have hh := Complex.abs_re_le_norm s
        rw [hsr] at hh
        have ha : (1 / 4 : ℝ) ≤ |a| := by
          rw [abs_of_nonpos (by linarith : a ≤ 0)]; linarith
        linarith
      have hs1_ge : (1 : ℝ) ≤ ‖s - 1‖ := by
        have hh := Complex.abs_re_le_norm (s - 1)
        have hr : (s - 1).re = a - 1 := by rw [Complex.sub_re, hsr]; simp
        rw [hr] at hh
        have ha : (1 : ℝ) ≤ |a - 1| := by
          rw [abs_of_nonpos (by linarith : a - 1 ≤ 0)]; linarith
        linarith
      have hxa : (x : ℝ) ^ s.re = xr := by rw [hsr, hxr]
      have hratio : (x : ℝ) ^ s.re / ‖s‖ ≤ xr * 4 := by
        rw [hxa, div_eq_mul_one_div]
        have h4 : 1 / ‖s‖ ≤ 4 := by
          rw [div_le_iff₀ (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 4) hs_ge)]
          linarith
        exact mul_le_mul_of_nonneg_left h4 hxr0
      have hinv1 : 1 / ‖s - 1‖ ≤ 1 := by
        have := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hs1_ge
        simpa using this
      have hFn : ‖F y‖ ≤ (Cc + 1) * (xr * 4) := by
        rw [hFs]
        calc
          ‖kern x s‖ ≤ (‖logDeriv riemannZeta₁ s‖ + 1 / ‖s - 1‖) *
              ((x : ℝ) ^ s.re / ‖s‖) := hkern
          _ ≤ (Cc + 1) * (xr * 4) :=
              mul_le_mul (by linarith) hratio (by positivity) (by linarith)
      have hKg : 12 * (Cc + 2) * xr ≤ K := by
        rw [hK]
        have h2 : 0 ≤ 2 * Cf * LT ^ 3 * xr := by positivity
        linarith
      have hgoal : (Cc + 1) * (xr * 4) ≤ K / (|y| + 1) := by
        rw [le_div_iff₀ hden]
        have hy3 : |y| + 1 ≤ 3 := by linarith
        have h1 : (Cc + 1) * (xr * 4) * (|y| + 1) ≤ (Cc + 1) * (xr * 4) * 3 :=
          mul_le_mul_of_nonneg_left hy3 (by positivity)
        have h2 : (Cc + 1) * (xr * 4) * 3 ≤ 12 * (Cc + 2) * xr := by
          nlinarith [hxr0, hCcpos]
        linarith [h1, h2, hKg]
      linarith [hFn, hgoal]
    · -- far part: `|Im s| ≥ 2`
      push_neg at hy2
      have hyT : |y| ≤ Tp := abs_le.mpr ⟨le_of_lt hy.1, hy.2⟩
      have hypos : (0 : ℝ) < |y| := by linarith
      have hlog : ‖logDeriv riemannZeta₁ s‖ ≤ Cf * LT ^ 3 := by
        have hb := hCfb a y ha1 ha2 (le_of_lt hy2)
        have hlogy : Real.log (|y| + 3) + 1 ≤ LT := by
          rw [hLT]
          have h1 : Real.log (|y| + 3) ≤ Real.log (Tp + 3) :=
            Real.log_le_log (by linarith) (by linarith)
          linarith
        have hlogy0 : (0 : ℝ) ≤ Real.log (|y| + 3) + 1 := by
          have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ |y| + 3)
          linarith
        have hp3 : (Real.log (|y| + 3) + 1) ^ 3 ≤ LT ^ 3 := pow_le_pow_left₀ hlogy0 hlogy 3
        calc
          ‖logDeriv riemannZeta₁ s‖ ≤ Cf * (Real.log (|y| + 3) + 1) ^ 3 := by
            simpa [s] using hb
          _ ≤ Cf * LT ^ 3 := mul_le_mul_of_nonneg_left hp3 (le_of_lt hCfpos)
      have hs_ge : |y| ≤ ‖s‖ := by
        have hh := Complex.abs_im_le_norm s
        rwa [hsi] at hh
      have hs1_ge : (1 : ℝ) ≤ ‖s - 1‖ := by
        have hh := Complex.abs_im_le_norm (s - 1)
        have hi : (s - 1).im = y := by rw [Complex.sub_im, hsi]; simp
        rw [hi] at hh
        linarith
      have hxa : (x : ℝ) ^ s.re = xr := by rw [hsr, hxr]
      have hratio : (x : ℝ) ^ s.re / ‖s‖ ≤ xr / |y| := by
        rw [hxa]
        exact div_le_div_of_nonneg_left hxr0 hypos hs_ge
      have hinv1 : 1 / ‖s - 1‖ ≤ 1 := by
        have := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hs1_ge
        simpa using this
      have hFn : ‖F y‖ ≤ (Cf * LT ^ 3 + 1) * (xr / |y|) := by
        rw [hFs]
        calc
          ‖kern x s‖ ≤ (‖logDeriv riemannZeta₁ s‖ + 1 / ‖s - 1‖) *
              ((x : ℝ) ^ s.re / ‖s‖) := hkern
          _ ≤ (Cf * LT ^ 3 + 1) * (xr / |y|) :=
              mul_le_mul (by linarith) hratio (by positivity) (by positivity)
      have hKg : 2 * Cf * LT ^ 3 * xr ≤ K := by
        rw [hK]
        have h2 : 0 ≤ 12 * (Cc + 2) * xr := by positivity
        linarith
      have hgoal : (Cf * LT ^ 3 + 1) * (xr / |y|) ≤ K / (|y| + 1) := by
        rw [le_div_iff₀ hden]
        have hstep : (Cf * LT ^ 3 + 1) * (xr / |y|) * (|y| + 1) ≤
            (Cf * LT ^ 3 + 1) * (xr / |y|) * (2 * |y|) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        have heq : (Cf * LT ^ 3 + 1) * (xr / |y|) * (2 * |y|) =
            2 * (Cf * LT ^ 3 + 1) * xr := by
          field_simp
        have hfin : 2 * (Cf * LT ^ 3 + 1) * xr ≤ K := by
          rw [hK]
          nlinarith [hxr0, hCcpos, hCfpos, hLT0]
        linarith [hstep, heq, hfin]
      linarith [hFn, hgoal]
  -- integral of the dominating function
  have hGcont : Continuous fun y : ℝ => K / (|y| + 1) := by
    have hden : Continuous fun y : ℝ => |y| + 1 := continuous_abs.add continuous_const
    exact continuous_const.div hden (fun y => by positivity)
  have hnorm : ‖(∫ y in (-Tp)..Tp, F y)‖ ≤ ∫ y in (-Tp)..Tp, K / (|y| + 1) := by
    refine intervalIntegral.norm_integral_le_of_norm_le (by linarith) ?_
      (hGcont.intervalIntegrable _ _)
    exact Filter.Eventually.of_forall (fun y hy => hdom y hy)
  have hmid : ∫ y in (-1)..1, K / (|y| + 1) ≤ 2 * K := by
    have h1 : ‖∫ y in (-1)..1, K / (|y| + 1)‖ ≤ K * |(1 : ℝ) - (-1)| :=
      intervalIntegral.norm_integral_le_of_norm_le_const (fun y hy => by
        rw [Set.uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hy
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact div_le_self (le_of_lt hKpos) (by linarith [abs_nonneg y]))
    have h2 : |(1 : ℝ) - (-1)| = 2 := by norm_num
    have hnn : (0 : ℝ) ≤ ∫ y in (-1)..1, K / (|y| + 1) :=
      intervalIntegral.integral_nonneg (by norm_num) (fun y _ => by positivity)
    rw [h2, Real.norm_eq_abs, abs_of_nonneg hnn] at h1
    linarith
  have hright : ∫ y in (1)..Tp, K / (|y| + 1) = K * Real.log ((Tp + 1) / 2) := by
    have heq : (∫ y in (1)..Tp, K / (|y| + 1)) =
        ∫ y in (1)..Tp, (fun u : ℝ => K / u) (y + 1) := by
      apply intervalIntegral.integral_congr
      intro y hy
      show K / (|y| + 1) = K / (y + 1)
      rw [Set.uIcc_of_le (by linarith : (1 : ℝ) ≤ Tp)] at hy
      rw [abs_of_nonneg (by linarith [hy.1] : (0 : ℝ) ≤ y)]
    rw [heq]
    have hcomp : (∫ y in (1)..Tp, (fun u : ℝ => K / u) (y + 1)) =
        ∫ u in (2)..(Tp + 1), K / u := by
      rw [intervalIntegral.integral_comp_add_right (f := fun u : ℝ => K / u)
        (a := (1 : ℝ)) (b := Tp) (d := 1)]
      norm_num
    rw [hcomp]
    have hstep : (∫ u in (2)..(Tp + 1), K / u) = K * ∫ u in (2)..(Tp + 1), u⁻¹ :=
      intervalIntegral.integral_const_mul K (fun u : ℝ => u⁻¹)
    rw [hstep, integral_inv_of_pos (by norm_num : (0 : ℝ) < 2) (by linarith : (0 : ℝ) < Tp + 1),
      Real.log_div (by linarith : (Tp + 1 : ℝ) ≠ 0) (by norm_num)]
  have hleft : ∫ y in (-Tp)..(-1), K / (|y| + 1) = K * Real.log ((Tp + 1) / 2) := by
    have hsym : (∫ y in (-Tp)..(-1), K / (|y| + 1)) = ∫ y in (1)..Tp, K / (|y| + 1) := by
      have hh := intervalIntegral.integral_comp_neg (f := fun u : ℝ => K / (|u| + 1))
        (a := (1 : ℝ)) (b := Tp)
      simpa using hh.symm
    rw [hsym, hright]
  have hsplit : ∫ y in (-Tp)..Tp, K / (|y| + 1) =
      (∫ y in (-Tp)..(-1), K / (|y| + 1)) + (∫ y in (-1)..1, K / (|y| + 1)) +
        (∫ y in (1)..Tp, K / (|y| + 1)) := by
    rw [(intervalIntegral.integral_add_adjacent_intervals
      (hGcont.intervalIntegrable (-Tp) (-1)) (hGcont.intervalIntegrable (-1) Tp)).symm]
    rw [(intervalIntegral.integral_add_adjacent_intervals
      (hGcont.intervalIntegrable (-1) 1) (hGcont.intervalIntegrable 1 Tp)).symm]
    ring
  -- final bookkeeping
  have hlog : Real.log ((Tp + 1) / 2) ≤ LT := by
    rw [hLT]
    have h1 : Real.log ((Tp + 1) / 2) ≤ Real.log (Tp + 3) :=
      Real.log_le_log (by linarith) (by linarith)
    linarith
  have hlog0 : 0 ≤ Real.log ((Tp + 1) / 2) := Real.log_nonneg (by linarith)
  have hLT3 : (1 : ℝ) ≤ LT ^ 3 := one_le_pow₀ hLT1
  have hKle : K ≤ (12 * (Cc + 2) + 2 * Cf) * xr * LT ^ 3 := by
    have h2 : 2 * Cf * LT ^ 3 * xr = 2 * Cf * xr * LT ^ 3 := by ring
    rw [hK, h2]
    have h1 : 12 * (Cc + 2) * xr ≤ 12 * (Cc + 2) * xr * LT ^ 3 :=
      le_mul_of_one_le_right (by positivity) hLT3
    have h3 : (12 * (Cc + 2) + 2 * Cf) * xr * LT ^ 3 =
        12 * (Cc + 2) * xr * LT ^ 3 + 2 * Cf * xr * LT ^ 3 := by ring
    rw [h3]
    linarith
  have hKL : K * Real.log ((Tp + 1) / 2) ≤ (12 * (Cc + 2) + 2 * Cf) * xr * LT ^ 4 := by
    have h1 : K * Real.log ((Tp + 1) / 2) ≤
        (12 * (Cc + 2) + 2 * Cf) * xr * LT ^ 3 * LT :=
      mul_le_mul hKle hlog hlog0 (by positivity)
    have h2 : (12 * (Cc + 2) + 2 * Cf) * xr * LT ^ 3 * LT =
        (12 * (Cc + 2) + 2 * Cf) * xr * LT ^ 4 := by ring
    linarith [h1, h2]
  have h2K : 2 * K ≤ 2 * ((12 * (Cc + 2) + 2 * Cf) * xr * LT ^ 4) := by
    have h1 : 2 * K ≤ 2 * ((12 * (Cc + 2) + 2 * Cf) * xr * LT ^ 3) :=
      mul_le_mul_of_nonneg_left hKle (by norm_num)
    have h34 : LT ^ 3 ≤ LT ^ 4 := by
      simpa using pow_le_pow_right₀ hLT1 (by norm_num : (3 : ℕ) ≤ 4)
    have h2 : (12 * (Cc + 2) + 2 * Cf) * xr * LT ^ 3 ≤
        (12 * (Cc + 2) + 2 * Cf) * xr * LT ^ 4 :=
      mul_le_mul_of_nonneg_left h34 (by positivity)
    linarith
  have hfin : K * Real.log ((Tp + 1) / 2) + 2 * K + K * Real.log ((Tp + 1) / 2) ≤
      4 * (12 * (Cc + 2) + 2 * Cf + 1) * xr * LT ^ 4 := by
    have hsum : K * Real.log ((Tp + 1) / 2) + 2 * K + K * Real.log ((Tp + 1) / 2) ≤
        4 * (12 * (Cc + 2) + 2 * Cf) * xr * LT ^ 4 := by linarith [hKL, h2K]
    have hxLT : (0 : ℝ) ≤ xr * LT ^ 4 := by positivity
    have hM : 4 * (12 * (Cc + 2) + 2 * Cf) ≤ 4 * (12 * (Cc + 2) + 2 * Cf + 1) := by linarith
    have := mul_le_mul_of_nonneg_right hM hxLT
    nlinarith [hsum, this]
  calc
    ‖(∫ y in (-Tp)..Tp, F y)‖ ≤ ∫ y in (-Tp)..Tp, K / (|y| + 1) := hnorm
    _ ≤ K * Real.log ((Tp + 1) / 2) + 2 * K + K * Real.log ((Tp + 1) / 2) := by
        rw [hsplit, hleft, hright]
        linarith [hmid]
    _ ≤ 4 * (12 * (Cc + 2) + 2 * Cf + 1) * xr * LT ^ 4 := hfin
    _ = 4 * (12 * (Cc + 2) + 2 * Cf + 1) * (x : ℝ) ^ a *
          (Real.log (Tp + 3) + 1) ^ 4 := by rw [hxr, hLT]

end Commons.NumberTheory.Zeta
