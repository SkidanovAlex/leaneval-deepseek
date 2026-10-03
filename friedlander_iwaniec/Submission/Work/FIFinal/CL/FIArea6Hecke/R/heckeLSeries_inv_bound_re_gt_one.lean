/-
# `Work.FIArea6Hecke.R.heckeLSeries_inv_bound_re_gt_one`

***FI* (16.23) in the half-plane of absolute convergence** (`1 < re s ≤ 2`) for the Hecke
`L`-series of `ℚ(i)`:

  `‖L(s,ψ)⁻¹‖ ≤ c·d·log²(|m|+|Im s|+3)`, uniformly in the strict character `χ` mod `4d` and in the
weight `m : ℤ`.

## The argument (this is exactly *FI* §16, the `σ > 1` half)

On `σ > 1` the `L`-series is the absolutely convergent Euler product, so everything can be read off
`heckeLSeries` itself; no analytic continuation is needed.

* **Anchor (elementary, proved here).**  `1/L(s) = ∏_𝔭 G_𝔭(s)` with `‖G_𝔭(s)‖ ≤ heckeB 𝔭 σ`,
  `∏_𝔭 heckeB 𝔭 σ ≪ 1/(σ-1)` (`heckeL_inv_halfPlane`).  Hence
  `‖L(σ+it)⁻¹‖ ≤ Cn/(σ-1)` on `1 < σ ≤ 2`, with `Cn` independent of `χ` and `m`.
* **The logarithmic derivative (delegated, the deep classical input).**  `Re(L'/L)(σ+it) ≪ d·log²`
  on `1 < σ ≤ 2`; `Submission/Work/FIArea6Hecke/R/heckeLSeries_logDeriv_bound_re_gt_one`.
  This is *FI* (16.20)/(16.21) fed into `L'/L` (the de la Vallée Poussin zero-free region off the
  real axis, Siegel's Lemma 16.1 on it).  Note that only the *real part* is bounded: the two-sided
  bound is false (the trivial character has a pole at `s = 1`, so `L'/L(σ) = -1/(σ-1) + O(1)`).
* **Assembly.**  Put `A := K·d·log²M + 1`, `δ := 1/(2A)`, `σ₀ := 1+δ`.  If `σ₀ ≤ σ` the anchor at
  `s` already gives `‖L(s)⁻¹‖ ≤ Cn/δ ≤ c·d·log²M`.  If `σ < σ₀`, integrate `log|L|` along the
  horizontal segment from `s` up to `σ₀ + it`:
  `log‖L(s)‖ ≥ log‖L(σ₀+it)‖ - A·(σ₀-σ) ≥ log(δ/Cn) - 1/2`, and the segment has length `< δ`, so
  the integration contributes only `O(1)`; exponentiating gives `‖L(s)⁻¹‖ ≤ 2A·Cn·√e`.

  The segment (and the ball used to build a holomorphic logarithm) stays in `σ > 1`, so no
  continuation of `L` is required — this is why the result is available on `σ > 1` alone.
-/
import Mathlib
import Submission.Work.FIFinal.CL.FIArea6Hecke.R.heckeLSeries_logDeriv_bound_re_gt_one
import Submission.Work.FIArea5.S16Hecke.ThetaDefs
import Submission.Work.FIArea5.S16Hecke.heckeL_inv_halfPlane
import Submission.Work.FIArea5.S16Hecke.heckeLStripAux
import Submission.Work.FIArea5.HeckeZFR.HeckeNonvanishing
import Submission.Commons.Analysis.Complex.logDeriv_zeroFree_ball_bound_analytic

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.FIArea6Hecke.R

open scoped BigOperators

noncomputable section

/-! ## 1.  The elementary anchor: `‖L(σ+it)⁻¹‖ ≤ Cn/(σ-1)` on `1 < σ ≤ 2` -/

/-- **Uniform Euler-product inverse bound.** The reciprocal Hecke `L`-series is `O(1/(σ-1))` on
`1 < σ ≤ 2`, with a constant independent of the character and of the weight.  This is
`heckeL_inv_halfPlane` with its constant pulled out of the character loop. -/
lemma heckeLSeries_inv_le_inv_sub_one :
    ∃ Cn : ℝ, 0 < Cn ∧ ∀ (chi : GaussianInt → ℂ) (m : ℤ), chi 1 = 1 →
      (∀ z w : GaussianInt, chi (z * w) = chi z * chi w) →
      (∀ z : GaussianInt, ‖chi z‖ ≤ 1) →
      ∀ s : ℂ, 1 < s.re → s.re ≤ 2 →
        ‖(Work.FIArea5.S16Hecke.heckeLSeries chi m s)⁻¹‖ ≤ Cn / (s.re - 1) := by
  obtain ⟨C0, hC0pos, hC0⟩ := Work.FIArea5.S16Hecke.heckeB_finset_prod_bound
  refine ⟨C0, hC0pos, fun chi m h1 hmul hb s hs1 hs2 => ?_⟩
  have hsigpos : 0 < s.re := by linarith
  have hGp_mult : Multipliable (fun p : Nat.Primes => Work.FIArea5.S16Hecke.heckeGp chi m p s) :=
    Work.FIArea5.S16Hecke.multipliable_heckeGp chi m s hmul hb hs1
  have hEq : (∏' p : Nat.Primes, Work.FIArea5.S16Hecke.heckeGp chi m p s)
      = (Work.FIArea5.S16Hecke.heckeLSeries chi m s)⁻¹ :=
    Work.FIArea5.S16Hecke.tprod_heckeGp_eq_inv chi m s hmul h1 hb hs1
  have hnorm : ‖(Work.FIArea5.S16Hecke.heckeLSeries chi m s)⁻¹‖
      = ∏' p : Nat.Primes, ‖Work.FIArea5.S16Hecke.heckeGp chi m p s‖ := by
    rw [← hEq, Multipliable.norm_tprod hGp_mult]
  rw [hnorm]
  refine Multipliable.tprod_le_of_prod_le hGp_mult.norm (fun t => ?_)
  have h1' : ∏ p ∈ t, ‖Work.FIArea5.S16Hecke.heckeGp chi m p s‖
      ≤ ∏ p ∈ t, Work.FIArea5.S16Hecke.heckeB p s.re :=
    Finset.prod_le_prod₀ (fun p _ => norm_nonneg _)
      (fun p _ => Work.FIArea5.S16Hecke.norm_heckeGp_le chi m p s hmul hb hsigpos)
  have h2' : ∏ p ∈ t, Work.FIArea5.S16Hecke.heckeB p s.re ≤ C0 / (s.re - 1) :=
    hC0 s.re hs1 hs2 t
  linarith

/-! ## 2.  The one-sided mean-value bound for `log ‖L‖` along a horizontal segment -/

/-- The chain rule along the parametrisation `θ ↦ x + θ•(y-x)` of a segment, for a primitive `F`
of `g'/g`: the derivative of `θ ↦ (F (x + θ•(y-x))).re` is `Re ((g'/g)(x+θ•(y-x)) * (y-x))`. -/
private lemma hasDerivAt_segment_re {F g : ℂ → ℂ} {c : ℂ} {R : ℝ} {x y : ℂ} {θ : ℝ}
    (hF : ∀ w ∈ Metric.ball c R, HasDerivAt F (deriv g w / g w) w)
    (hw : x + θ • (y - x) ∈ Metric.ball c R) :
    HasDerivAt (fun θ : ℝ => (F (x + θ • (y - x))).re)
      (((deriv g (x + θ • (y - x))) / g (x + θ • (y - x)) * (y - x)).re) θ := by
  have h1 : HasDerivAt (fun θ : ℝ => x + θ • (y - x)) (y - x) θ := by
    simpa using ((hasDerivAt_id θ).smul_const (y - x)).const_add x
  have h2 : HasDerivAt (fun θ : ℝ => F (x + θ • (y - x)))
      ((deriv g (x + θ • (y - x)) / g (x + θ • (y - x))) * (y - x)) θ :=
    HasDerivAt.comp θ (hF (x + θ • (y - x)) hw) h1
  have h3 : HasFDerivAt (fun θ : ℝ => (F (x + θ • (y - x))).re)
      (Complex.reCLM.comp
        (ContinuousLinearMap.toSpanSingleton ℝ
          ((deriv g (x + θ • (y - x)) / g (x + θ • (y - x))) * (y - x)))) θ := by
    exact (ContinuousLinearMap.hasFDerivAt (Complex.reCLM : ℂ →L[ℝ] ℝ)).comp θ
      h2.hasFDerivAt
  have h4 := h3.hasDerivAt
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply,
    one_smul, Complex.reCLM_apply] using h4

/-- **One-sided mean-value bound for the logarithm.**  If `F` is a primitive of `g'/g` on the ball
`B(c,R)`, `log‖g‖ = Re F` there, and `Re (g'/g) ≤ A` on the (horizontal) segment from `x` to `y`,
then `log‖g y‖ ≤ log‖g x‖ + A·(y.re - x.re)`. -/
private lemma log_norm_le_of_re_logDeriv_le {F g : ℂ → ℂ} {c x y : ℂ} {R A : ℝ}
    (hx : x ∈ Metric.ball c R) (hy : y ∈ Metric.ball c R)
    (hF : ∀ w ∈ Metric.ball c R, HasDerivAt F (deriv g w / g w) w)
    (hFre : ∀ w ∈ Metric.ball c R, (F w).re = Real.log ‖g w‖)
    (him : y.im = x.im) (hre : x.re ≤ y.re)
    (hA : ∀ w ∈ segment ℝ x y, (deriv g w / g w).re ≤ A) :
    Real.log ‖g y‖ ≤ Real.log ‖g x‖ + A * (y.re - x.re) := by
  have hsub : segment ℝ x y ⊆ Metric.ball c R :=
    (convex_ball c R).segment_subset hx hy
  have hmem : ∀ θ : ℝ, θ ∈ Set.Icc (0:ℝ) 1 → x + θ • (y - x) ∈ Metric.ball c R := by
    intro θ hθ
    refine hsub ?_
    rw [segment_eq_image']
    exact ⟨θ, hθ, rfl⟩
  set φ : ℝ → ℝ := fun θ => (F (x + θ • (y - x))).re with hφ
  have hderiv : ∀ θ ∈ Set.Icc (0:ℝ) 1,
      HasDerivAt φ (((deriv g (x + θ • (y - x))) / g (x + θ • (y - x)) * (y - x)).re) θ :=
    fun θ hθ => hasDerivAt_segment_re hF (hmem θ hθ)
  -- the slope bound on `(0,1)`
  have hslope : ∀ θ ∈ Set.Ioo (0:ℝ) 1,
      deriv φ θ ≤ A * (y.re - x.re) := by
    intro θ hθ
    have hθ' : θ ∈ Set.Icc (0:ℝ) 1 := Set.Ioo_subset_Icc_self hθ
    rw [(hderiv θ hθ').deriv]
    have hseg : x + θ • (y - x) ∈ segment ℝ x y := by
      rw [segment_eq_image']; exact ⟨θ, hθ', rfl⟩
    have hb := hA _ hseg
    -- `y - x` is the real number `y.re - x.re`
    have hsub_eq : y - x = (((y.re - x.re) : ℝ) : ℂ) := by
      apply Complex.ext
      · simp [Complex.sub_re]
      · simp [Complex.sub_im, him]
    have hre_mul : (((deriv g (x + θ • (y - x))) / g (x + θ • (y - x)) * (y - x)).re)
        = (y.re - x.re) * ((deriv g (x + θ • (y - x))) / g (x + θ • (y - x))).re := by
      rw [hsub_eq, Complex.mul_re]
      simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
      ring
    rw [hre_mul]
    have h0 : (0:ℝ) ≤ y.re - x.re := by linarith
    have h1 := mul_le_mul_of_nonneg_left hb h0
    linarith [h1]
  obtain ⟨ξ, hξ, hξder⟩ := exists_deriv_eq_slope φ (by norm_num : (0:ℝ) < 1)
    (fun θ hθ => (hderiv θ hθ).continuousAt.continuousWithinAt)
    (fun θ hθ => (hderiv θ (Set.Ioo_subset_Icc_self hθ)).differentiableAt.differentiableWithinAt)
  have hφ1 : φ 1 = Real.log ‖g y‖ := by
    have h1 : x + (1:ℝ) • (y - x) = y := by rw [one_smul]; abel
    simp only [hφ]
    rw [h1]
    exact hFre y hy
  have hφ0 : φ 0 = Real.log ‖g x‖ := by
    have h1 : x + (0:ℝ) • (y - x) = x := by rw [zero_smul, add_zero]
    simp only [hφ]
    rw [h1]
    exact hFre x hx
  have hslopeξ := hslope ξ hξ
  rw [hξder] at hslopeξ
  simp only [sub_zero, div_one] at hslopeξ
  rw [hφ1, hφ0] at hslopeξ
  linarith [hslopeξ]

/-! ## 3.  The assembly -/

/-- **The target from the delegated logarithmic-derivative bound.** -/
theorem heckeLSeries_inv_bound_re_gt_one_of
    (hdeep : ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 4 →
      ∃ K : ℝ, 0 < K ∧ ∀ (d : ℕ) (chi : GaussianInt → ℂ), 1 ≤ d →
        Work.FIArea5.S16Hecke.IsCharMod4dStrict d chi → ∀ (m : ℤ) (s : ℂ),
          1 < s.re → s.re ≤ 2 →
          (deriv (Work.FIArea5.S16Hecke.heckeLSeries chi m) s /
            Work.FIArea5.S16Hecke.heckeLSeries chi m s).re
            ≤ K * (d : ℝ) * (Real.log (|(m : ℝ)| + |s.im| + 3)) ^ (2 : ℕ)) :
    ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 4 →
    ∃ c : ℝ, 0 < c ∧ ∀ (d : ℕ) (chi : GaussianInt → ℂ), 1 ≤ d →
      Work.FIArea5.S16Hecke.IsCharMod4dStrict d chi → ∀ (m : ℤ) (s : ℂ),
        1 < s.re → s.re ≤ 2 →
        ‖(Work.FIArea5.S16Hecke.heckeLSeries chi m s)⁻¹‖
          ≤ c * (d : ℝ) * (Real.log (|(m : ℝ)| + |s.im| + 3)) ^ (2 : ℕ) := by
  obtain ⟨Cn, hCnpos, hnear⟩ := heckeLSeries_inv_le_inv_sub_one
  intro ε hε hε4
  obtain ⟨K, hKpos, hK⟩ := hdeep ε hε hε4
  refine ⟨2 * (K + 1) * (Cn + 1) * Real.exp 1, by positivity, ?_⟩
  intro d chi hd hchi m s hs1 hs2
  obtain ⟨h1, hmul, hb, -, -⟩ := hchi.1
  set t : ℝ := s.im with ht
  set M : ℝ := |(m : ℝ)| + |t| + 3 with hM
  have hM3 : 3 ≤ M := by
    rw [hM]; have h1 := abs_nonneg (m : ℝ); have h2 := abs_nonneg t; linarith
  have hMpos : 0 < M := by linarith
  set L : ℝ := Real.log M with hL
  have hL1 : 1 < L := by
    have h3 : Real.log 3 ≤ L := by rw [hL]; exact Real.log_le_log (by norm_num) hM3
    have h4 : (1 : ℝ) < Real.log 3 := by
      have h := Real.log_lt_log (Real.exp_pos 1) Real.exp_one_lt_three
      rwa [Real.log_exp] at h
    linarith
  have hLpos : 0 < L := by linarith
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hdpos : (0 : ℝ) < (d : ℝ) := by linarith
  have hL2 : (1 : ℝ) ≤ L ^ (2 : ℕ) := by nlinarith [hL1]
  have hdL : (1 : ℝ) ≤ (d : ℝ) * L ^ (2 : ℕ) := by nlinarith [hd1, hL2]
  -- the amplitude of the logarithmic derivative and the reference point
  set A : ℝ := K * (d : ℝ) * L ^ (2 : ℕ) + 1 with hA
  have hApos : 0 < A := by rw [hA]; positivity
  have hKL : 0 ≤ K * (d : ℝ) * L ^ (2 : ℕ) := by positivity
  have hAone : 1 ≤ A := by rw [hA]; linarith
  have hAle : A ≤ (K + 1) * (d : ℝ) * L ^ (2 : ℕ) := by
    rw [hA]; nlinarith [hdL, hKpos, hdpos]
  set δ : ℝ := 1 / (2 * A) with hδ
  have hδpos : 0 < δ := by rw [hδ]; positivity
  have hδhalf : δ ≤ 1 / 2 := by
    rw [hδ, div_le_iff₀ (by positivity)]; linarith
  have hAδ : A * δ = 1 / 2 := by rw [hδ]; field_simp
  set σ₀ : ℝ := 1 + δ with hσ₀
  have hσδ : σ₀ - 1 = δ := by rw [hσ₀]; ring
  have hσ₀1 : 1 < σ₀ := by rw [hσ₀]; linarith
  have hσ₀2 : σ₀ ≤ 2 := by rw [hσ₀]; linarith
  have hexp1 : (1 : ℝ) ≤ Real.exp 1 := by
    simpa using (Real.exp_le_exp.mpr (le_refl (1:ℝ)))
  have hgoal_of : ∀ x : ℝ, ‖(Work.FIArea5.S16Hecke.heckeLSeries chi m s)⁻¹‖
      ≤ x → x ≤ 2 * (K + 1) * (Cn + 1) * Real.exp 1 * (d : ℝ) * L ^ (2 : ℕ) →
      ‖(Work.FIArea5.S16Hecke.heckeLSeries chi m s)⁻¹‖
        ≤ 2 * (K + 1) * (Cn + 1) * Real.exp 1 * (d : ℝ)
            * (Real.log (|(m : ℝ)| + |s.im| + 3)) ^ (2 : ℕ) := by
    intro x hx h2
    have heq : 2 * (K + 1) * (Cn + 1) * Real.exp 1 * (d : ℝ) * L ^ (2 : ℕ)
        = 2 * (K + 1) * (Cn + 1) * Real.exp 1 * (d : ℝ)
            * (Real.log (|(m : ℝ)| + |s.im| + 3)) ^ (2 : ℕ) := by
      rw [hL, hM, ht]
    exact le_of_le_of_eq (le_trans hx h2) heq
  by_cases hcase : σ₀ ≤ s.re
  · -- the anchor at `s` itself
    have hb := hnear chi m h1 hmul hb s hs1 hs2
    have hδle : δ ≤ s.re - 1 := by linarith
    have h1' : Cn / (s.re - 1) ≤ Cn / δ :=
      div_le_div_of_nonneg_left hCnpos.le hδpos hδle
    have h2' : Cn / δ = Cn * (2 * A) := by rw [hδ]; field_simp
    have h3' : Cn * (2 * A) ≤ 2 * (K + 1) * (Cn + 1) * Real.exp 1 * (d : ℝ) * L ^ (2:ℕ) := by
      have hCn1 : Cn ≤ (Cn + 1) * Real.exp 1 := by nlinarith [hCnpos, hexp1]
      have hstep1 : Cn * (2 * A) ≤ Cn * (2 * ((K + 1) * (d : ℝ) * L ^ (2:ℕ))) :=
        mul_le_mul_of_nonneg_left (by linarith [hAle]) hCnpos.le
      have hstep2 : Cn * (2 * ((K + 1) * (d : ℝ) * L ^ (2:ℕ)))
          ≤ ((Cn + 1) * Real.exp 1) * (2 * ((K + 1) * (d : ℝ) * L ^ (2:ℕ))) :=
        mul_le_mul_of_nonneg_right hCn1 (by positivity)
      calc Cn * (2 * A)
          ≤ Cn * (2 * ((K + 1) * (d : ℝ) * L ^ (2:ℕ))) := hstep1
        _ ≤ ((Cn + 1) * Real.exp 1) * (2 * ((K + 1) * (d : ℝ) * L ^ (2:ℕ))) := hstep2
        _ = 2 * (K + 1) * (Cn + 1) * Real.exp 1 * (d : ℝ) * L ^ (2:ℕ) := by ring
    exact hgoal_of _ (le_trans hb (le_trans h1' (le_trans h2'.le h3'))) (le_refl _)
  · -- integrate `Re (L'/L)` along the segment from `s` to `σ₀ + it`
    push_neg at hcase
    have hsr : s.re < σ₀ := hcase
    set c₀ : ℂ := (((s.re + σ₀) / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I with hc₀
    set ρ : ℝ := (σ₀ - s.re) / 2 + (s.re - 1) / 4 with hρ
    have hρpos : 0 < ρ := by rw [hρ]; linarith
    set yy : ℂ := (s.re : ℂ) + (t : ℂ) * Complex.I with hyy
    set cc : ℂ := (σ₀ : ℂ) + (t : ℂ) * Complex.I with hcc
    have hyyeq : yy = s := by rw [hyy, ht]; exact Complex.re_add_im s
    have hyyim : yy.im = t := by rw [hyy]; simp
    have hccim : cc.im = t := by rw [hcc]; simp
    have hccre : cc.re = σ₀ := by rw [hcc]; simp
    have hyyre : yy.re = s.re := by rw [hyy]; simp
    have hcre : c₀.re = (s.re + σ₀) / 2 := by rw [hc₀]; simp
    have hyy_ball : yy ∈ Metric.ball c₀ ρ := by
      rw [Metric.mem_ball, dist_eq_norm]
      have h1 : yy - c₀ = (((s.re - (s.re + σ₀) / 2 : ℝ)) : ℂ) := by
        rw [hyy, hc₀]; push_cast; ring
      rw [h1, Complex.norm_real, Real.norm_eq_abs, hρ]
      have h2 : s.re - (s.re + σ₀) / 2 = -((σ₀ - s.re) / 2) := by ring
      rw [h2, abs_neg, abs_of_nonneg (by linarith)]
      linarith
    have hcc_ball : cc ∈ Metric.ball c₀ ρ := by
      rw [Metric.mem_ball, dist_eq_norm]
      have h1 : cc - c₀ = (((σ₀ - (s.re + σ₀) / 2 : ℝ)) : ℂ) := by
        rw [hcc, hc₀]; push_cast; ring
      rw [h1, Complex.norm_real, Real.norm_eq_abs, hρ]
      rw [abs_of_nonneg (by linarith)]
      linarith
    have hball_re_low : ∀ w ∈ Metric.ball c₀ ρ, 1 < w.re := by
      intro w hw
      have h1 : ‖w - c₀‖ < ρ := by simpa [Metric.mem_ball, dist_eq_norm] using hw
      have h2 : |w.re - c₀.re| ≤ ‖w - c₀‖ := by
        simpa using Complex.abs_re_le_norm (w - c₀)
      have h3 : c₀.re - ρ < w.re := by
        have := (abs_lt.mp (lt_of_le_of_lt h2 h1)).1
        linarith
      rw [hcre, hρ] at h3
      linarith
    have hnonzero : ∀ w ∈ Metric.ball c₀ ρ,
        Work.FIArea5.S16Hecke.heckeLSeries chi m w ≠ 0 :=
      fun w hw => Work.FIArea5.S16Hecke.heckeLSeries_ne_zero_of_one_lt_re chi m h1 hmul hb
        (hball_re_low w hw)
    have hAnal : AnalyticOnNhd ℂ (Work.FIArea5.S16Hecke.heckeLSeries chi m)
        (Metric.ball c₀ ρ) := by
      refine DifferentiableOn.analyticOnNhd ?_ Metric.isOpen_ball
      intro z hz
      refine (LSeries_differentiableOn (Work.FIArea5.S16Hecke.heckeLam chi m) z ?_).mono ?_
      · show LSeries.abscissaOfAbsConv (Work.FIArea5.S16Hecke.heckeLam chi m) < (z.re : EReal)
        exact lt_of_le_of_lt (Work.FIArea5.S16Hecke.heckeLSeries_absc_le_one chi m hb)
          (EReal.coe_lt_coe_iff.mpr (hball_re_low z hz))
      · intro w hw
        exact lt_of_le_of_lt (Work.FIArea5.S16Hecke.heckeLSeries_absc_le_one chi m hb)
          (EReal.coe_lt_coe_iff.mpr (hball_re_low w hw))
    obtain ⟨F, _hFdiff, hFder, _hFc, hFre⟩ :=
      Commons.Analysis.Complex.logPrimitiveOnBall_analytic
        (g := Work.FIArea5.S16Hecke.heckeLSeries chi m) hAnal hρpos hnonzero
    -- the logarithmic-derivative bound on the segment
    have hseg : ∀ w ∈ segment ℝ yy cc,
        (deriv (Work.FIArea5.S16Hecke.heckeLSeries chi m) w /
          Work.FIArea5.S16Hecke.heckeLSeries chi m w).re ≤ A := by
      intro w hw
      rw [segment_eq_image'] at hw
      obtain ⟨θ, hθ, hθw⟩ := hw
      have hweq : w = yy + θ • (cc - yy) := hθw.symm
      have hweq' : w = (((s.re + θ * (σ₀ - s.re)) : ℝ) : ℂ) + (t : ℂ) * Complex.I := by
        rw [hweq, hyy, hcc, Complex.real_smul]; push_cast; ring
      have hwre : w.re = s.re + θ * (σ₀ - s.re) := by rw [hweq']; simp
      have hwim : w.im = t := by rw [hweq']; simp
      have hge : s.re ≤ w.re := by
        rw [hwre]
        have : 0 ≤ θ * (σ₀ - s.re) := mul_nonneg hθ.1 (by linarith)
        linarith
      have hle : w.re ≤ σ₀ := by
        rw [hwre]; nlinarith [hθ.1, hθ.2, hsr]
      have hlog : Real.log (|(m : ℝ)| + |w.im| + 3) = L := by rw [hwim, ← hM, ← hL]
      have hb' := hK d chi hd hchi m w (by linarith) (by linarith [hle, hσ₀2])
      rw [hlog] at hb'
      calc (deriv (Work.FIArea5.S16Hecke.heckeLSeries chi m) w /
            Work.FIArea5.S16Hecke.heckeLSeries chi m w).re
          ≤ K * (d : ℝ) * L ^ (2 : ℕ) := hb'
        _ ≤ A := by rw [hA]; linarith
    -- the mean value bound
    have hmv := log_norm_le_of_re_logDeriv_le (F := F)
      (g := Work.FIArea5.S16Hecke.heckeLSeries chi m) (c := c₀) (x := yy) (y := cc)
      (R := ρ) (A := A) hyy_ball hcc_ball hFder hFre
      (by rw [hyyim, hccim]) (by rw [hyyre, hccre]; linarith) hseg
    rw [hccre, hyyre] at hmv
    -- the anchor at the reference point
    have hanchor := hnear chi m h1 hmul hb cc (by rw [hccre]; exact hσ₀1)
      (by rw [hccre]; exact hσ₀2)
    have hccne : Work.FIArea5.S16Hecke.heckeLSeries chi m cc ≠ 0 :=
      hnonzero cc hcc_ball
    have hgcc : 0 < ‖Work.FIArea5.S16Hecke.heckeLSeries chi m cc‖ :=
      norm_pos_iff.mpr hccne
    -- `δ/Cn ≤ ‖L cc‖`
    have h1cc : δ / Cn ≤ ‖Work.FIArea5.S16Hecke.heckeLSeries chi m cc‖ := by
      have hb : (‖Work.FIArea5.S16Hecke.heckeLSeries chi m cc‖)⁻¹ ≤ Cn / δ := by
        simpa only [hccre, hσδ, norm_inv] using hanchor
      have hdiv : Cn / δ = (δ / Cn)⁻¹ := by
        rw [div_eq_mul_inv, div_eq_mul_inv, mul_inv_rev, inv_inv]
      rw [hdiv] at hb
      exact (inv_le_inv₀ hgcc (div_pos hδpos hCnpos)).mp hb
    have hlogcc : Real.log δ - Real.log Cn
        ≤ Real.log ‖Work.FIArea5.S16Hecke.heckeLSeries chi m cc‖ := by
      have h := Real.log_le_log (div_pos hδpos hCnpos) h1cc
      rwa [Real.log_div hδpos.ne' hCnpos.ne'] at h
    -- the main lower bound at `s`
    have hlogyy : Real.log δ - Real.log Cn - 1 / 2
        ≤ Real.log ‖Work.FIArea5.S16Hecke.heckeLSeries chi m yy‖ := by
      have h2 : Real.log ‖Work.FIArea5.S16Hecke.heckeLSeries chi m cc‖ - A * (σ₀ - s.re)
          ≤ Real.log ‖Work.FIArea5.S16Hecke.heckeLSeries chi m yy‖ := by linarith [hmv]
      have h3 : A * (σ₀ - s.re) ≤ 1 / 2 := by
        have h4 : σ₀ - s.re < δ := by rw [hσ₀]; linarith
        nlinarith [h4, hApos, hAδ]
      linarith [hlogcc, h2, h3]
    have hgyy : 0 < ‖Work.FIArea5.S16Hecke.heckeLSeries chi m yy‖ :=
      norm_pos_iff.mpr (hnonzero yy hyy_ball)
    have hexp : 1 / ‖Work.FIArea5.S16Hecke.heckeLSeries chi m yy‖
        ≤ Real.exp (-(Real.log δ - Real.log Cn - 1 / 2)) := by
      have h := Real.exp_le_exp.mpr hlogyy
      rw [Real.exp_log hgyy] at h
      rw [Real.exp_neg]
      simpa only [one_div] using one_div_le_one_div_of_le (Real.exp_pos _) h
    have hexp2 : Real.exp (-(Real.log δ - Real.log Cn - 1 / 2))
        = 2 * A * Cn * Real.exp (1 / 2) := by
      have harg : -(Real.log δ - Real.log Cn - 1 / 2) = Real.log (Cn / δ) + 1 / 2 := by
        rw [Real.log_div hCnpos.ne' hδpos.ne']; ring
      rw [harg, Real.exp_add, Real.exp_log (div_pos hCnpos hδpos), hδ]
      field_simp
    have hlast : 2 * A * Cn * Real.exp (1 / 2)
        ≤ 2 * (K + 1) * (Cn + 1) * Real.exp 1 * (d : ℝ) * L ^ (2 : ℕ) := by
      have he : Real.exp (1 / 2) ≤ Real.exp 1 := Real.exp_le_exp.mpr (by norm_num)
      have hCn1 : Cn ≤ Cn + 1 := by linarith
      have hstep1 : 2 * A * Cn ≤ 2 * ((K + 1) * (d : ℝ) * L ^ (2:ℕ)) * Cn := by
        have h := mul_le_mul_of_nonneg_right hAle (by positivity : (0:ℝ) ≤ 2 * Cn)
        linarith [h]
      have hstep2 : Cn * Real.exp (1 / 2) ≤ (Cn + 1) * Real.exp 1 :=
        mul_le_mul hCn1 he (Real.exp_pos _).le (by positivity)
      have hstep3 : 2 * A * Cn * Real.exp (1 / 2)
          ≤ 2 * ((K + 1) * (d : ℝ) * L ^ (2:ℕ)) * ((Cn + 1) * Real.exp 1) := by
        calc 2 * A * Cn * Real.exp (1 / 2)
            = (2 * A * Cn) * Real.exp (1 / 2) := by ring
          _ ≤ (2 * ((K + 1) * (d : ℝ) * L ^ (2:ℕ)) * Cn) * Real.exp (1 / 2) :=
              mul_le_mul_of_nonneg_right hstep1 (Real.exp_pos _).le
          _ = 2 * ((K + 1) * (d : ℝ) * L ^ (2:ℕ)) * (Cn * Real.exp (1 / 2)) := by ring
          _ ≤ 2 * ((K + 1) * (d : ℝ) * L ^ (2:ℕ)) * ((Cn + 1) * Real.exp 1) :=
              mul_le_mul_of_nonneg_left hstep2 (by positivity)
      calc 2 * A * Cn * Real.exp (1 / 2)
          ≤ 2 * ((K + 1) * (d : ℝ) * L ^ (2:ℕ)) * ((Cn + 1) * Real.exp 1) := hstep3
        _ = 2 * (K + 1) * (Cn + 1) * Real.exp 1 * (d : ℝ) * L ^ (2:ℕ) := by ring
    have hfin : ‖(Work.FIArea5.S16Hecke.heckeLSeries chi m yy)⁻¹‖
        ≤ 2 * (K + 1) * (Cn + 1) * Real.exp 1 * (d : ℝ) * L ^ (2 : ℕ) := by
      rw [norm_inv]
      calc ‖Work.FIArea5.S16Hecke.heckeLSeries chi m yy‖⁻¹
          ≤ Real.exp (-(Real.log δ - Real.log Cn - 1 / 2)) := by
            simpa only [one_div] using hexp
        _ = 2 * A * Cn * Real.exp (1 / 2) := hexp2
        _ ≤ 2 * (K + 1) * (Cn + 1) * Real.exp 1 * (d : ℝ) * L ^ (2 : ℕ) := hlast
    rw [hyyeq] at hfin
    exact hgoal_of _ hfin (le_refl _)

/-- ***FI* (16.23) in the half-plane of absolute convergence** (`1 < re s ≤ 2`) for the Hecke
`L`-series of `ℚ(i)`: `‖L(s,ψ)⁻¹‖ ≤ c·d·log²(|m|+|Im s|+3)`, uniformly in the strict character
`χ` mod `4d`, in the weight `m` and in the point `s` of the half-plane `1 < re s ≤ 2`.

It is obtained from the elementary anchor `‖L(σ+it)⁻¹‖ ≤ Cn/(σ-1)` and the logarithmic-derivative
bound `Re (L'/L) ≤ K·d·log²` on the half-plane, which is the classical zero-free-region input
(*FI* §16, (16.20)-(16.24)); see
`Submission/Work/FIArea6Hecke/R/heckeLSeries_logDeriv_bound_re_gt_one`. -/
theorem heckeLSeries_inv_bound_re_gt_one : ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 4 →
    ∃ c : ℝ, 0 < c ∧ ∀ (d : ℕ) (chi : GaussianInt → ℂ), 1 ≤ d →
      Work.FIArea5.S16Hecke.IsCharMod4dStrict d chi → ∀ (m : ℤ) (s : ℂ),
        1 < s.re → s.re ≤ 2 →
        ‖(Work.FIArea5.S16Hecke.heckeLSeries chi m s)⁻¹‖
          ≤ c * (d : ℝ) * (Real.log (|(m : ℝ)| + |s.im| + 3)) ^ (2 : ℕ) := by
  exact heckeLSeries_inv_bound_re_gt_one_of heckeLSeries_logDeriv_bound_re_gt_one

end

end Work.FIArea6Hecke.R
