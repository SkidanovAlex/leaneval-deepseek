import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
import Submission.Commons.Analysis.Complex.laplace_vertical_endpoint_tendsto

namespace Commons.Analysis.Complex

open Complex MeasureTheory intervalIntegral Filter Set Topology
open scoped Real Topology BigOperators

private lemma ofReal_add_I_eq_inv (a b' : ℝ) (ha : 0 < a) :
    ((a/(a^2+b'^2) : ℝ):ℂ) + ((b'/(a^2+b'^2) : ℝ):ℂ) * Complex.I
      = (1:ℂ)/((a:ℂ) - (b':ℂ)*Complex.I) := by
  have hne : ((a:ℂ) - (b':ℂ)*Complex.I) ≠ 0 := by
    intro h
    have h2 := congrArg Complex.re h
    simp [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im] at h2
    nlinarith [ha]
  rw [eq_div_iff hne]
  apply Complex.ext <;>
    simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.sub_re,
      Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.one_re, Complex.one_im, mul_zero, sub_zero, mul_one, zero_add, add_zero,
      sub_self] <;>
    field_simp <;> ring

private lemma hasDerivAt_psi (a b : ℝ) (ha : 0 < a) (γ : ℝ) :
    HasDerivAt (fun y : ℝ => (Real.arctan ((y - b)/a) : ℂ)
        + ((1/2) * Real.log (a^2 + (y-b)^2) : ℂ) * Complex.I)
      ((1:ℂ)/((a:ℂ) - ((γ-b:ℝ):ℂ) * Complex.I)) γ := by
  have hden : a^2 + (γ-b)^2 ≠ 0 := by positivity
  have h1 : HasDerivAt (fun y : ℝ => (Real.arctan ((y - b)/a) : ℂ))
      (((a/(a^2+(γ-b)^2) : ℝ)) : ℂ) γ := by
    have hinner : HasDerivAt (fun y : ℝ => (y - b)/a) (1/a) γ :=
      ((hasDerivAt_id γ).sub_const b).div_const a
    have harc : HasDerivAt Real.arctan ((1 + ((γ-b)/a)^2)⁻¹) ((γ-b)/a) :=
      Real.hasDerivAt_arctan' ((γ-b)/a)
    have hcomp := (harc.comp γ hinner).ofReal_comp
    convert hcomp using 1
    · rfl
    · rw [Complex.ofReal_inj]
      field_simp
  have h2 : HasDerivAt (fun y : ℝ => ((1/2) * Real.log (a^2 + (y-b)^2) : ℂ))
      ((((γ-b)/(a^2+(γ-b)^2) : ℝ))) γ := by
    have hinner : HasDerivAt (fun y : ℝ => a^2 + (y-b)^2) (2*(γ-b)) γ := by
      have hca := (((hasDerivAt_id γ).sub_const b).pow 2).const_add (a^2)
      simpa using hca
    have hlog : HasDerivAt Real.log ((a^2+(γ-b)^2)⁻¹) (a^2+(γ-b)^2) := Real.hasDerivAt_log hden
    have hc := ((hlog.comp γ hinner).const_mul (1/2)).ofReal_comp
    have hder : (((1 / 2 * ((a^2+(γ-b)^2)⁻¹ * (2 * (γ-b))) : ℝ)) : ℂ)
        = ((((γ-b)/(a^2+(γ-b)^2) : ℝ)) : ℂ) := by
      rw [Complex.ofReal_inj]; field_simp
    have hfun : (fun y : ℝ => ((1 / 2 * (Real.log ∘ fun y => a^2 + (y-b)^2) y : ℝ) : ℂ))
        = fun y : ℝ => ((1/2) * Real.log (a^2 + (y-b)^2) : ℂ) := by
      funext y; simp only [Function.comp_apply]; push_cast; ring
    rw [hder, hfun] at hc
    exact hc
  have hsum := h1.add (h2.mul_const Complex.I)
  rw [ofReal_add_I_eq_inv a (γ-b) ha] at hsum
  exact hsum


private lemma arctan_shift_tendsto_atTop (a b : ℝ) (ha : 0 < a) :
    Tendsto (fun R : ℝ => Real.arctan ((R - b)/a)) atTop (nhds (Real.pi/2)) := by
  have htend : Tendsto (fun R : ℝ => (R - b)/a) atTop atTop := by
    have h1 : Tendsto (fun R : ℝ => R - b) atTop atTop := by
      have := tendsto_atTop_add_const_right atTop (-b) tendsto_id
      simpa [sub_eq_add_neg] using this
    have h2 : (fun R : ℝ => (R - b)/a) = fun R : ℝ => (1/a) * (R - b) := by funext R; ring
    rw [h2]; exact h1.const_mul_atTop (by positivity)
  exact (Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp htend

private lemma log_sub_log_tendsto_zero (a b : ℝ) (ha : 0 < a) :
    Tendsto (fun R : ℝ => Real.log (a^2+(R-b)^2) - Real.log (a^2+(R+b)^2)) atTop (nhds 0) := by
  have h2 : Tendsto (fun R : ℝ => Real.log (a^2+(R-b)^2) - Real.log (a^2+(R+b)^2)) atTop (nhds 0) := by
    have hR : Tendsto (fun R : ℝ => R) atTop atTop := tendsto_id
    have hbdiv : Tendsto (fun R : ℝ => b/R) atTop (nhds 0) :=
      Tendsto.div_atTop (tendsto_const_nhds : Tendsto (fun _ : ℝ => b) atTop (nhds b)) hR
    have haR : Tendsto (fun R : ℝ => a/R) atTop (nhds 0) :=
      Tendsto.div_atTop (tendsto_const_nhds : Tendsto (fun _ : ℝ => a) atTop (nhds a)) hR
    have haR2 : Tendsto (fun R : ℝ => a^2/R^2) atTop (nhds 0) := by
      have h := haR.mul haR
      have heq : (fun R : ℝ => a/R * (a/R)) = fun R : ℝ => a^2/R^2 := by funext R; ring
      rw [heq] at h; simpa using h
    have harg1 : Tendsto (fun R : ℝ => (1 - b/R)^2 + a^2/R^2) atTop (nhds 1) := by
      have h1 : Tendsto (fun R : ℝ => 1 - b/R) atTop (nhds 1) := by
        simpa using ((tendsto_const_nhds : Tendsto (fun _ : ℝ => (1:ℝ)) atTop (nhds 1)).sub hbdiv)
      have h2 : Tendsto (fun R : ℝ => (1 - b/R)^2) atTop (nhds (1^2)) := h1.pow 2
      have := h2.add haR2
      simpa using this
    have harg2 : Tendsto (fun R : ℝ => (1 + b/R)^2 + a^2/R^2) atTop (nhds 1) := by
      have h1 : Tendsto (fun R : ℝ => 1 + b/R) atTop (nhds 1) := by
        simpa using ((tendsto_const_nhds : Tendsto (fun _ : ℝ => (1:ℝ)) atTop (nhds 1)).add hbdiv)
      have h2 : Tendsto (fun R : ℝ => (1 + b/R)^2) atTop (nhds (1^2)) := h1.pow 2
      have := h2.add haR2
      simpa using this
    have hratio : Tendsto (fun R : ℝ => (a^2+(R-b)^2)/(a^2+(R+b)^2)) atTop (nhds 1) := by
      have hdiv := harg1.div harg2 (by norm_num : (1:ℝ) ≠ 0)
      simp only [div_one] at hdiv
      refine hdiv.congr' ?_
      filter_upwards [eventually_gt_atTop (0:ℝ)] with R hRpos
      have hRne : R ≠ 0 := ne_of_gt hRpos
      have hP : a^2+(R-b)^2 = R^2 * ((1 - b/R)^2 + a^2/R^2) := by field_simp; ring
      have hQ : a^2+(R+b)^2 = R^2 * ((1 + b/R)^2 + a^2/R^2) := by field_simp; ring
      rw [hP, hQ, mul_div_mul_left ((1 - b/R)^2 + a^2/R^2) ((1 + b/R)^2 + a^2/R^2) (pow_ne_zero 2 hRne)]
      rfl
    have hlogratio : Tendsto (fun R : ℝ => Real.log ((a^2+(R-b)^2)/(a^2+(R+b)^2))) atTop (nhds 0) := by
      have := hratio.log (by norm_num : (1:ℝ) ≠ 0)
      simpa using this
    refine hlogratio.congr' ?_
    filter_upwards [eventually_gt_atTop (0:ℝ)] with R hRpos
    rw [Real.log_div (by positivity) (by positivity)]
  exact h2

private lemma tendsto_pole_integral_aux {T : ℂ} (hT : 0 < T.re) {L : ℝ} (hL : 0 < L) (c : ℂ) :
    Tendsto (fun R : ℝ => ∫ γ in (-R)..R, c / ((T - (γ:ℂ)*Complex.I) * (L:ℂ)))
      atTop (nhds ((Real.pi : ℂ) * c / (L:ℂ))) := by
  set a : ℝ := T.re with ha
  set b : ℝ := T.im with hb
  have hapos : 0 < a := by rw [ha]; exact hT
  have hTdecomp : T = (a:ℂ) + (b:ℂ)*Complex.I := by
    rw [ha, hb]; exact (Complex.re_add_im T).symm
  have hstep1 : (fun R : ℝ => ∫ γ in (-R)..R, c / ((T - (γ:ℂ)*Complex.I) * (L:ℂ)))
      = fun R : ℝ => (c / (L:ℂ)) * ∫ γ in (-R)..R, (1:ℂ)/(T - (γ:ℂ)*Complex.I) := by
    funext R
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro γ _
    field_simp
  rw [hstep1]
  have hcore : Tendsto (fun R : ℝ => ∫ γ in (-R)..R, (1:ℂ)/(T - (γ:ℂ)*Complex.I))
      atTop (nhds (Real.pi:ℂ)) := by
    set Ψ : ℝ → ℂ := fun γ => (Real.arctan ((γ - b)/a) : ℂ)
        + ((1/2)*Real.log (a^2+(γ-b)^2) : ℂ)*Complex.I with hΨ
    have hderiv : ∀ γ : ℝ, HasDerivAt Ψ ((1:ℂ)/(T - (γ:ℂ)*Complex.I)) γ := by
      intro γ
      have hTγ : T - (γ:ℂ)*Complex.I = (a:ℂ) - ((γ-b:ℝ):ℂ)*Complex.I := by
        rw [hTdecomp]; push_cast; ring
      rw [hTγ]
      exact hasDerivAt_psi a b hapos γ
    have hne : ∀ γ : ℝ, T - (γ:ℂ)*Complex.I ≠ 0 := by
      intro γ
      have hre : (T - (γ:ℂ)*Complex.I).re = a := by
        rw [hTdecomp]; push_cast
        simp only [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
          Complex.I_re, Complex.I_im, mul_zero, sub_zero, add_zero, mul_one]
      intro h
      have := congrArg Complex.re h
      rw [hre] at this
      simp only [Complex.zero_re] at this
      exact absurd this (ne_of_gt hapos)
    have hcont : Continuous (fun γ : ℝ => (1:ℂ)/(T - (γ:ℂ)*Complex.I)) := by
      refine Continuous.div continuous_const (by fun_prop) ?_
      exact hne
    have hint : ∀ R : ℝ, (∫ γ in (-R)..R, (1:ℂ)/(T - (γ:ℂ)*Complex.I)) = Ψ R - Ψ (-R) := by
      intro R
      refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun γ _ => hderiv γ) ?_
      exact hcont.intervalIntegrable (-R) R
    have harctan1 := arctan_shift_tendsto_atTop a b hapos
    have harctan2 : Tendsto (fun R : ℝ => Real.arctan ((R+b)/a)) atTop (nhds (Real.pi/2)) := by
      have h := arctan_shift_tendsto_atTop a (-b) hapos
      simpa [sub_neg_eq_add] using h
    have ho1 : Tendsto (fun R : ℝ => ((Real.arctan ((R-b)/a):ℝ):ℂ)) atTop (nhds ((Real.pi/2:ℝ):ℂ)) :=
      (Complex.continuous_ofReal.tendsto (Real.pi/2)).comp harctan1
    have ho2 : Tendsto (fun R : ℝ => ((Real.arctan ((R+b)/a):ℝ):ℂ)) atTop (nhds ((Real.pi/2:ℝ):ℂ)) :=
      (Complex.continuous_ofReal.tendsto (Real.pi/2)).comp harctan2
    have hlogc : Tendsto (fun R : ℝ => ((1/2)*Real.log (a^2+(R-b)^2) : ℂ)
        - ((1/2)*Real.log (a^2+(R+b)^2) : ℂ)) atTop (nhds 0) := by
      have h1 := (Complex.continuous_ofReal.tendsto (0:ℝ)).comp (log_sub_log_tendsto_zero a b hapos)
      simp only [Function.comp_def, Complex.ofReal_zero] at h1
      have h2 := h1.const_mul ((1/2:ℂ))
      convert h2 using 1
      · ext R; push_cast; ring
      · ring
    have hcomb : Tendsto (fun R : ℝ => ((Real.arctan ((R-b)/a):ℝ):ℂ) + ((Real.arctan ((R+b)/a):ℝ):ℂ)
        + (((1/2)*Real.log (a^2+(R-b)^2) : ℂ) - ((1/2)*Real.log (a^2+(R+b)^2) : ℂ)) * Complex.I)
        atTop (nhds (Real.pi:ℂ)) := by
      have h3 := (ho1.add ho2).add (hlogc.mul_const Complex.I)
      convert h3 using 1
      push_cast
      ring
    have heq : (fun R : ℝ => Ψ R - Ψ (-R)) = fun R : ℝ =>
        ((Real.arctan ((R-b)/a):ℝ):ℂ) + ((Real.arctan ((R+b)/a):ℝ):ℂ)
        + (((1/2)*Real.log (a^2+(R-b)^2) : ℂ) - ((1/2)*Real.log (a^2+(R+b)^2) : ℂ)) * Complex.I := by
      funext R
      have hA : (Real.arctan (((-R) - b)/a) : ℂ) = -((Real.arctan ((R+b)/a)):ℂ) := by
        have h1 : ((-R) - b)/a = -((R+b)/a) := by ring
        rw [h1, Real.arctan_neg, Complex.ofReal_neg]
      have hB : ((1/2)*Real.log (a^2+((-R)-b)^2) : ℂ) = ((1/2)*Real.log (a^2+(R+b)^2) : ℂ) := by
        have : a^2+((-R)-b)^2 = a^2+(R+b)^2 := by ring
        rw [this]
      simp only [hΨ]
      simp only [hA, hB]
      push_cast
      ring
    rw [show (fun R : ℝ => ∫ γ in (-R)..R, (1:ℂ)/(T - (γ:ℂ)*Complex.I))
        = (fun R => Ψ R - Ψ (-R)) from funext hint]
    refine hcomb.congr' ?_
    exact Filter.Eventually.of_forall (fun R => congrFun heq.symm R)
  have hgoal := hcore.const_mul (c/(L:ℂ))
  convert hgoal using 1
  rw [mul_comm]
  ring


private lemma tendsto_pole_vertical_integral {L : ℝ} (hL : 0 < L) {s : ℂ}
    (hs : (0:ℝ) < s.re + 1/2) (c : ℂ) :
    Tendsto (fun R : ℝ => ∫ γ in (-R)..R,
        c / ((s - (((-1/2:ℝ):ℂ) + (γ : ℂ) * Complex.I)) * (L : ℂ)))
      atTop (nhds ((Real.pi : ℂ) * c / (L : ℂ))) := by
  have hT : (0:ℝ) < (s + 1/2).re := by simpa using hs
  refine (tendsto_pole_integral_aux (T := s + 1/2) hT hL c).congr' ?_
  refine Filter.Eventually.of_forall (fun R => ?_)
  apply intervalIntegral.integral_congr; intro γ _
  simp only []
  have hd : ((s + 1/2) - (γ:ℂ)*Complex.I) * (L:ℂ)
      = (s - (((-1/2:ℝ):ℂ) + (γ:ℂ)*Complex.I)) * (L:ℂ) := by
    push_cast; ring
  rw [hd]

private lemma tendsto_inner_vertical_integral {x₀ B : ℝ} (hx₀ : 0 < x₀) (hB : 0 ≤ B)
    {f : ℝ → ℂ} (hcont : ContinuousOn f (Set.Icc 0 x₀)) (hf2 : ContDiffOn ℝ 2 f (Set.Ioo 0 x₀))
    (hBnd : ∀ t ∈ Set.Ioo (0:ℝ) x₀, ‖iteratedDeriv 2 f t‖ ≤ B)
    (hvan : ∀ t : ℝ, x₀ ≤ t → f t = 0)
    {L : ℝ} (hL : 1 < L) {s : ℂ} (hs : (0:ℝ) < s.re + 1/2) :
    Tendsto (fun R : ℝ => ∫ γ in (-R)..R, ∫ t in (0:ℝ)..x₀,
          Complex.exp (-(((s - (((-1/2:ℝ):ℂ) + (γ : ℂ) * Complex.I)) * (L : ℂ)) * (t : ℂ))) * f t)
      atTop (nhds ((Real.pi : ℂ) * f 0 / (L : ℂ))) := by
  have hLpos : (0:ℝ) < L := by linarith
  set F : ℝ → ℝ → ℂ := fun γ t =>
      Complex.exp (-((((s + 1/2) - (γ : ℂ) * Complex.I) * (L:ℂ)) * (t:ℂ))) * f t with hFdef
  set G : ℝ → ℂ := fun u => Complex.exp (-((s + 1/2) * (u:ℂ))) * f (u/L) with hGdef
  have hEq : (fun R : ℝ => ∫ γ in (-R)..R, ∫ t in (0:ℝ)..x₀,
          Complex.exp (-(((s - (((-1/2:ℝ):ℂ) + (γ : ℂ) * Complex.I)) * (L : ℂ)) * (t : ℂ))) * f t)
      = fun R : ℝ => ∫ γ in (-R)..R, ∫ t in (0:ℝ)..x₀, F γ t := by
    funext R
    apply intervalIntegral.integral_congr; intro γ _
    apply intervalIntegral.integral_congr; intro t _
    rw [hFdef]; simp only []
    congr 1; push_cast; ring
  rw [hEq]
  obtain ⟨Mf0, hMf0⟩ := (isCompact_Icc (a := (0:ℝ)) (b := x₀)).exists_bound_of_continuousOn hcont
  obtain ⟨Mf1, hMf1⟩ := exists_norm_deriv_le hx₀ hf2 hBnd
  have hMf0' : 0 ≤ Mf0 := le_trans (norm_nonneg _) (hMf0 0 ⟨le_refl 0, hx₀.le⟩)
  have hMf1' : 0 ≤ Mf1 := le_trans (norm_nonneg _) (hMf1 (x₀/2) ⟨by linarith, by linarith⟩)
  -- Fubini
  have hFubini : ∀ R : ℝ, (∫ γ in (-R)..R, ∫ t in (0:ℝ)..x₀, F γ t)
      = ∫ t in (0:ℝ)..x₀, ∫ γ in (-R)..R, F γ t := by
    intro R
    refine intervalIntegral_intervalIntegral_swap ?_
    have hcontbox : ContinuousOn (Function.uncurry F)
        ((Set.uIcc (-R) R) ×ˢ (Set.uIcc (0:ℝ) x₀)) := by
      rw [hFdef]
      have hexp : Continuous (fun p : ℝ × ℝ =>
          Complex.exp (-((((s + 1/2) - (p.1:ℂ) * Complex.I) * (L:ℂ)) * (p.2:ℂ)))) := by fun_prop
      have hf' : ContinuousOn (fun p : ℝ × ℝ => f p.2)
          ((Set.uIcc (-R) R) ×ˢ (Set.uIcc (0:ℝ) x₀)) := by
        refine hcont.comp continuous_snd.continuousOn ?_
        intro p hp
        rw [Set.uIcc_of_le hx₀.le] at hp
        exact hp.2
      exact hexp.continuousOn.mul hf'
    have hInt : IntegrableOn (Function.uncurry F)
        ((Set.uIcc (-R) R) ×ˢ (Set.uIcc (0:ℝ) x₀)) volume :=
      hcontbox.integrableOn_compact (isCompact_uIcc.prod isCompact_uIcc)
    exact hInt.mono_set (Set.prod_mono Set.uIoc_subset_uIcc Set.uIoc_subset_uIcc)
  -- inner formula
  have hinner : ∀ R t : ℝ, (∫ γ in (-R)..R, F γ t)
      = Complex.exp (-((s+1/2) * (L:ℂ) * (t:ℂ))) * ((2*R*Real.sinc (R*(L*t)) : ℝ):ℂ) * f t := by
    intro R t
    have hfac : ∀ γ : ℝ, F γ t = Complex.exp (-((s+1/2) * (L:ℂ) * (t:ℂ)))
        * Complex.exp (Complex.I * ((L*t:ℝ):ℂ) * (γ:ℂ)) * f t := by
      intro γ
      rw [hFdef]; simp only []
      have hexp : -((((s + 1/2) - (γ:ℂ)*Complex.I) * (L:ℂ)) * (t:ℂ))
          = -((s+1/2) * (L:ℂ) * (t:ℂ)) + Complex.I * ((L*t:ℝ):ℂ) * (γ:ℂ) := by push_cast; ring
      rw [hexp, Complex.exp_add]
    simp_rw [hfac]
    rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_const_mul]
    have hB : (∫ γ in (-R)..R, Complex.exp (Complex.I * ((L*t:ℝ):ℂ) * (γ:ℂ)))
        = ((2*R*Real.sinc (R*(L*t)) : ℝ):ℂ) := by
      rw [show (fun γ : ℝ => Complex.exp (Complex.I * ((L*t:ℝ):ℂ) * (γ:ℂ)))
          = fun γ : ℝ => Complex.exp (-(Complex.I * ((-(L*t):ℝ):ℂ) * (γ:ℂ))) from by
        funext γ; congr 1; push_cast; ring]
      rw [integral_exp_neg_I_mul]
      rw [show R*(-(L*t)) = -(R*(L*t)) by ring, Real.sinc_neg]
    rw [hB]
  -- substitution
  have hsub : ∀ R : ℝ, (∫ t in (0:ℝ)..x₀,
        Complex.exp (-((s+1/2) * (L:ℂ) * (t:ℂ))) * ((2*R*Real.sinc (R*(L*t)) : ℝ):ℂ) * f t)
      = (L:ℂ)⁻¹ * ((2:ℂ)*(R:ℂ) * ∫ u in (0:ℝ)..(L*x₀), G u * (Real.sinc (R*u) : ℂ)) := by
    intro R
    set φ : ℝ → ℂ := fun u => Complex.exp (-((s+1/2) * (u:ℂ))) * ((2*R*Real.sinc (R*u) : ℝ):ℂ) * f (u/L) with hφdef
    have hpt : ∀ t : ℝ, Complex.exp (-((s+1/2) * (L:ℂ) * (t:ℂ))) * ((2*R*Real.sinc (R*(L*t)) : ℝ):ℂ) * f t = φ (L*t) := by
      intro t; rw [hφdef]; simp only []
      have hdiv : L*t/L = t := by field_simp
      rw [hdiv]
      push_cast; ring
    simp_rw [hpt]
    rw [intervalIntegral.integral_comp_mul_left φ (ne_of_gt hLpos)]
    simp only [mul_zero]
    rw [Complex.real_smul, Complex.ofReal_inv]
    congr 1
    rw [hφdef, hGdef]
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr; intro u _
    push_cast; ring
  -- the sinc limit
  have hGcont : ContinuousOn G (Set.Icc 0 (L*x₀)) := by
    rw [hGdef]
    refine ContinuousOn.mul ?_ ?_
    · exact (by fun_prop : Continuous (fun u : ℝ => Complex.exp (-((s+1/2) * (u:ℂ))))).continuousOn
    · exact hcont.comp (continuous_id.div_const L).continuousOn (fun u hu => by
        rw [Set.mem_Icc] at hu ⊢
        exact ⟨div_nonneg hu.1 hLpos.le, by rw [div_le_iff₀ hLpos]; linarith [hu.2]⟩)
  have hGx : G (L*x₀) = 0 := by
    rw [hGdef]; simp only []
    have hx : L*x₀/L = x₀ := by field_simp
    rw [hx, hvan x₀ le_rfl, mul_zero]
  have hsg : ∀ t ∈ Set.Ioo (0:ℝ) (L*x₀), HasDerivAt G (deriv G t) t := by
    intro t ht
    have htL : t/L ∈ Set.Ioo (0:ℝ) x₀ := by
      rw [Set.mem_Ioo] at ht ⊢
      exact ⟨div_pos ht.1 hLpos, by rw [div_lt_iff₀ hLpos]; linarith [ht.2]⟩
    have hfd : DifferentiableAt ℝ f (t/L) :=
      (hf2.differentiableOn (by norm_num)).differentiableAt (Ioo_mem_nhds htL.1 htL.2)
    have hexp : DifferentiableAt ℝ (fun u : ℝ => Complex.exp (-((s+1/2) * (u:ℂ)))) t := by fun_prop
    have hdiv : DifferentiableAt ℝ (fun u : ℝ => f (u/L)) t := hfd.comp t (by fun_prop)
    rw [hGdef]
    exact (hexp.mul hdiv).hasDerivAt
  have hbound : ∀ t ∈ Set.Ioo (0:ℝ) (L*x₀), ‖deriv G t‖ ≤ ‖s+1/2‖ * Mf0 + Mf1 := by
    intro t ht
    have htL : t/L ∈ Set.Ioo (0:ℝ) x₀ := by
      rw [Set.mem_Ioo] at ht ⊢
      exact ⟨div_pos ht.1 hLpos, by rw [div_lt_iff₀ hLpos]; linarith [ht.2]⟩
    have ht0 : 0 ≤ t := le_of_lt ht.1
    have hfd : DifferentiableAt ℝ f (t/L) :=
      (hf2.differentiableOn (by norm_num)).differentiableAt (Ioo_mem_nhds htL.1 htL.2)
    have h1 : HasDerivAt (fun u : ℝ => Complex.exp (-((s+1/2) * (u:ℂ))))
        (-(s+1/2) * Complex.exp (-((s+1/2) * (t:ℂ)))) t := by
      have hlin : HasDerivAt (fun u : ℝ => -((s+1/2) * (u:ℂ))) (-(s+1/2)) t := by
        have h0 : HasDerivAt (fun u : ℝ => (u:ℂ)) 1 t := (hasDerivAt_id t).ofReal_comp
        simpa only [neg_mul, mul_one] using h0.const_mul (-(s+1/2))
      have hc : HasDerivAt (fun u : ℝ => Complex.exp (-((s+1/2) * (u:ℂ))))
          ((-(s+1/2)) • Complex.exp (-((s+1/2) * (t:ℂ)))) t :=
        HasDerivAt.scomp t (Complex.hasDerivAt_exp (-((s+1/2) * (t:ℂ)))) hlin
      rwa [smul_eq_mul] at hc
    have h2 : HasDerivAt (fun u : ℝ => f (u/L)) ((1/L : ℝ) • deriv f (t/L)) t :=
      HasDerivAt.scomp t hfd.hasDerivAt ((hasDerivAt_id t).div_const L)
    have hg' : HasDerivAt G (-(s+1/2) * Complex.exp (-((s+1/2) * (t:ℂ))) * f (t/L)
        + Complex.exp (-((s+1/2) * (t:ℂ))) * ((1/L : ℝ) • deriv f (t/L))) t := by
      rw [hGdef]; exact h1.mul h2
    rw [hg'.deriv]
    have hexpnorm : ‖Complex.exp (-((s+1/2) * (t:ℂ)))‖ ≤ 1 := by
      rw [Complex.norm_exp]
      have hre : (-((s+1/2) * (t:ℂ))).re = -(s.re + 1/2) * t := by
        simp [Complex.mul_re, Complex.add_re, Complex.neg_re, Complex.ofReal_re, Complex.ofReal_im]
        ring
      rw [hre, Real.exp_le_one_iff]
      have : 0 ≤ (s.re + 1/2) * t := mul_nonneg (le_of_lt hs) ht0
      linarith
    have hfn : ‖f (t/L)‖ ≤ Mf0 := hMf0 (t/L) ⟨htL.1.le, htL.2.le⟩
    have hdn : ‖deriv f (t/L)‖ ≤ Mf1 := hMf1 (t/L) htL
    have hsl : ‖(1/L : ℝ)‖ ≤ 1 := by
      rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
      exact (div_le_one hLpos).mpr (le_of_lt hL)
    calc ‖-(s+1/2) * Complex.exp (-((s+1/2) * (t:ℂ))) * f (t/L)
            + Complex.exp (-((s+1/2) * (t:ℂ))) * ((1/L : ℝ) • deriv f (t/L))‖
        ≤ ‖-(s+1/2) * Complex.exp (-((s+1/2) * (t:ℂ))) * f (t/L)‖
            + ‖Complex.exp (-((s+1/2) * (t:ℂ))) * ((1/L : ℝ) • deriv f (t/L))‖ := norm_add_le _ _
      _ ≤ ‖s+1/2‖ * 1 * Mf0 + 1 * Mf1 := by
          refine add_le_add ?_ ?_
          · rw [norm_mul, norm_mul, norm_neg]
            exact mul_le_mul (mul_le_mul_of_nonneg_left hexpnorm (norm_nonneg _)) hfn
              (norm_nonneg _) (by positivity)
          · rw [norm_mul, norm_smul]
            exact (mul_le_mul hexpnorm (mul_le_mul hsl hdn (norm_nonneg _) (by norm_num))
              (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (by norm_num)).trans (le_of_eq (by ring))
      _ = ‖s+1/2‖ * Mf0 + Mf1 := by ring
  have hsinc : Tendsto (fun R : ℝ => (2:ℂ)*(R:ℂ) * ∫ u in (0:ℝ)..(L*x₀),
        G u * (Real.sinc (R*u) : ℂ)) atTop (nhds ((Real.pi:ℂ) * f 0)) := by
    have h := tendsto_two_mul_sinc_integral (g := G) (x₀ := L*x₀) (M := ‖s+1/2‖ * Mf0 + Mf1)
      (mul_pos hLpos hx₀) hGcont hsg hbound hGx
    have hG0 : G 0 = f 0 := by rw [hGdef]; simp
    rw [hG0] at h
    exact h
  have hkey : ∀ R : ℝ, (∫ γ in (-R)..R, ∫ t in (0:ℝ)..x₀, F γ t)
      = (L:ℂ)⁻¹ * ((2:ℂ)*(R:ℂ) * ∫ u in (0:ℝ)..(L*x₀), G u * (Real.sinc (R*u) : ℂ)) := by
    intro R
    rw [hFubini R]
    rw [show (∫ t in (0:ℝ)..x₀, ∫ γ in (-R)..R, F γ t)
        = ∫ t in (0:ℝ)..x₀, (Complex.exp (-((s+1/2) * (L:ℂ) * (t:ℂ)))
            * ((2*R*Real.sinc (R*(L*t)) : ℝ):ℂ) * f t) from by
      apply intervalIntegral.integral_congr; intro t _; exact hinner R t]
    exact hsub R
  have hfinal := hsinc.const_mul ((L:ℂ)⁻¹)
  rw [show (fun R : ℝ => ∫ γ in (-R)..R, ∫ t in (0:ℝ)..x₀, F γ t)
      = fun R : ℝ => (L:ℂ)⁻¹ * ((2:ℂ)*(R:ℂ) * ∫ u in (0:ℝ)..(L*x₀),
          G u * (Real.sinc (R*u) : ℂ)) from funext hkey]
  convert hfinal using 1
  rw [div_eq_mul_inv]
  ring

private lemma integral_eq_zero_of_intervalIntegral_tendsto_zero {g : ℝ → ℂ}
    (h : Filter.Tendsto (fun R : ℝ => ∫ x in (-R)..R, g x) Filter.atTop (nhds 0)) :
    ∫ x, g x = 0 := by
  by_cases hg : Integrable g
  · have h1 : Filter.Tendsto (fun R : ℝ => ∫ x in (-R)..R, g x) Filter.atTop (nhds (∫ x, g x)) :=
      intervalIntegral_tendsto_integral hg tendsto_neg_atTop_atBot tendsto_id
    exact tendsto_nhds_unique h1 h
  · exact integral_undef hg

theorem regularized_vertical_integral_eq_zero {x₀ B : ℝ} (hx₀ : 0 < x₀) (hB : 0 ≤ B)
    {f : ℝ → ℂ} (hcont : ContinuousOn f (Set.Icc 0 x₀)) (hf2 : ContDiffOn ℝ 2 f (Set.Ioo 0 x₀))
    (hBnd : ∀ t ∈ Set.Ioo (0:ℝ) x₀, ‖iteratedDeriv 2 f t‖ ≤ B)
    (hvan : ∀ t : ℝ, x₀ ≤ t → f t = 0)
    {L : ℝ} (hL : 1 < L) {s : ℂ} (hs : (0:ℝ) < s.re + 1/2) :
    (∫ τ : ℝ,
        ((∫ t in (0:ℝ)..x₀,
          Complex.exp (-(((s - (((-1/2:ℝ):ℂ) + (τ : ℂ) * Complex.I)) * (L : ℂ)) * (t : ℂ))) * f t)
          - f 0 / ((s - (((-1/2:ℝ):ℂ) + (τ : ℂ) * Complex.I)) * (L : ℂ))))
      = 0 := by
  set W : ℝ → ℂ := fun τ => ∫ t in (0:ℝ)..x₀,
      Complex.exp (-(((s - (((-1/2:ℝ):ℂ) + (τ : ℂ) * Complex.I)) * (L : ℂ)) * (t : ℂ))) * f t with hWdef
  set P : ℝ → ℂ := fun τ => f 0 / ((s - (((-1/2:ℝ):ℂ) + (τ : ℂ) * Complex.I)) * (L : ℂ)) with hPdef
  have hsσ : (0:ℝ) < (s + 1/2).re := by simpa using hs
  have hLpos : (0:ℝ) < L := by linarith
  -- continuity of W
  have hWcont : Continuous W := by
    rw [hWdef]
    refine continuous_of_dominated_interval (μ := volume) (E := ℂ) (X := ℝ)
      (F := fun τ t => Complex.exp (-(((s - (((-1/2:ℝ):ℂ) + (τ : ℂ) * Complex.I)) * (L : ℂ)) * (t : ℂ))) * f t)
      (bound := fun t => ‖f t‖) (a := (0:ℝ)) (b := x₀) ?_ ?_ ?_ ?_
    · intro τ
      have hfm : AEStronglyMeasurable f (volume.restrict (Set.uIoc (0:ℝ) x₀)) :=
        (hcont.mono (fun t ht => by
          have h := Set.uIoc_subset_uIcc ht
          rwa [Set.uIcc_of_le hx₀.le] at h)).aestronglyMeasurable measurableSet_uIoc
      have hexpm : AEStronglyMeasurable
          (fun t : ℝ => Complex.exp (-(((s - (((-1/2:ℝ):ℂ) + (τ : ℂ) * Complex.I)) * (L : ℂ)) * (t : ℂ))))
          (volume.restrict (Set.uIoc (0:ℝ) x₀)) :=
        (by fun_prop : Continuous (fun t : ℝ => Complex.exp (-(((s - (((-1/2:ℝ):ℂ) + (τ : ℂ) * Complex.I)) * (L : ℂ)) * (t : ℂ))))).aestronglyMeasurable
      exact hexpm.mul hfm
    · intro τ
      filter_upwards with t ht
      have ht0 : 0 ≤ t := by
        rw [Set.uIoc_of_le hx₀.le] at ht; exact ht.1.le
      have hsub_re : (s - (((-1/2:ℝ):ℂ) + (τ : ℂ) * Complex.I)).re = s.re + 1/2 := by
        simp [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.ofReal_re,
          Complex.I_im, Complex.ofReal_im]
        ring
      have hnorm : ‖Complex.exp (-(((s - (((-1/2:ℝ):ℂ) + (τ : ℂ) * Complex.I)) * (L : ℂ)) * (t : ℂ)))‖ ≤ 1 := by
        rw [Complex.norm_exp]
        have hre : (-(((s - (((-1/2:ℝ):ℂ) + (τ : ℂ) * Complex.I)) * (L : ℂ)) * (t : ℂ))).re
            = -((s.re + 1/2) * L * t) := by
          have h1 : ((s - (((-1/2:ℝ):ℂ) + (τ : ℂ) * Complex.I)) * (L : ℂ)).re = (s.re + 1/2) * L := by
            rw [Complex.mul_re, hsub_re]; simp
          rw [Complex.neg_re, Complex.mul_re, h1]
          simp
        rw [hre, Real.exp_le_one_iff]
        have hp : 0 ≤ (s.re + 1/2) * L * t :=
          mul_nonneg (mul_nonneg (le_of_lt hs) (le_of_lt hLpos)) ht0
        linarith
      rw [norm_mul]
      calc ‖Complex.exp (-(((s - (((-1/2:ℝ):ℂ) + (τ : ℂ) * Complex.I)) * (L : ℂ)) * (t : ℂ)))‖ * ‖f t‖
          ≤ 1 * ‖f t‖ := by gcongr
        _ = ‖f t‖ := one_mul _
    · exact (hcont.norm).intervalIntegrable_of_Icc hx₀.le
    · filter_upwards with t ht
      exact (by fun_prop : Continuous (fun τ : ℝ => Complex.exp (-(((s - (((-1/2:ℝ):ℂ) + (τ : ℂ) * Complex.I)) * (L : ℂ)) * (t : ℂ))) * f t))
  have hPcont : Continuous P := by
    rw [hPdef]
    refine Continuous.div continuous_const ?_ ?_
    · fun_prop
    · intro τ
      have h1 : ((s - (((-1/2:ℝ):ℂ) + (τ : ℂ) * Complex.I)) * (L : ℂ)).re = L * (s.re + 1/2) := by
        have hsub : (s - (((-1/2:ℝ):ℂ) + (τ : ℂ) * Complex.I)).re = s.re + 1/2 := by
          simp [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.I_re,
            Complex.I_im, Complex.ofReal_im]
          ring
        rw [Complex.mul_re, hsub]
        simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
        ring
      intro hzero
      have := congrArg Complex.re hzero
      rw [h1] at this
      simp only [Complex.zero_re] at this
      nlinarith [hs, hLpos]
  have hIntW : ∀ R : ℝ, IntervalIntegrable W volume (-R) R := fun R => hWcont.intervalIntegrable (-R) R
  have hIntP : ∀ R : ℝ, IntervalIntegrable P volume (-R) R := fun R => hPcont.intervalIntegrable (-R) R
  have hInner : Filter.Tendsto (fun R : ℝ => ∫ τ in (-R)..R, W τ) Filter.atTop (nhds ((Real.pi:ℂ)*f 0/(L:ℂ))) := by
    rw [hWdef]
    exact tendsto_inner_vertical_integral hx₀ hB hcont hf2 hBnd hvan hL hs
  have hPole : Filter.Tendsto (fun R : ℝ => ∫ τ in (-R)..R, P τ) Filter.atTop (nhds ((Real.pi:ℂ)*f 0/(L:ℂ))) := by
    rw [hPdef]
    exact tendsto_pole_vertical_integral hLpos hs (f 0)
  have hsub : Filter.Tendsto (fun R : ℝ => (∫ τ in (-R)..R, W τ) - (∫ τ in (-R)..R, P τ)) Filter.atTop (nhds 0) := by
    have h := hInner.sub hPole
    simpa using h
  have hEq : (fun R : ℝ => ∫ τ in (-R)..R, (W τ - P τ))
      = fun R : ℝ => (∫ τ in (-R)..R, W τ) - (∫ τ in (-R)..R, P τ) := by
    funext R
    rw [intervalIntegral.integral_sub (hIntW R) (hIntP R)]
  have hmain : Filter.Tendsto (fun R : ℝ => ∫ τ in (-R)..R, (W τ - P τ)) Filter.atTop (nhds 0) := by
    rw [hEq]; exact hsub
  exact integral_eq_zero_of_intervalIntegral_tendsto_zero hmain


end Commons.Analysis.Complex