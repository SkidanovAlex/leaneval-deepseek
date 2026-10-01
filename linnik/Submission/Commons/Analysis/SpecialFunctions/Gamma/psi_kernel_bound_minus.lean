import Mathlib
import Submission.Commons.Analysis.SpecialFunctions.Gamma.psi_kernel_bound

open MeasureTheory Set Complex Filter
open scoped Topology Interval BigOperators
noncomputable section

namespace PsiKernelMinus

open PsiKernelBound

/-- The "-" argument: `x - I·(b-u)/2`. -/
def wminus (x b u : ℝ) : ℂ := (x:ℂ) - (((b-u)/2:ℝ):ℂ)*Complex.I

lemma re_wminus (x b u : ℝ) : (wminus x b u).re = x := by
  simp [wminus, Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im]

lemma wminus_cont (x b : ℝ) : Continuous (fun u : ℝ => wminus x b u) := by
  unfold wminus
  fun_prop

lemma re_wminus_add_nat (x b u : ℝ) (n : ℕ) : (wminus x b u + (n:ℂ)).re = x + (n:ℝ) := by
  simp [wminus, Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im]

lemma re_add_I (P : ℂ) (u : ℝ) : (P + (u:ℂ)*Complex.I).re = P.re := by
  simp [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im]


lemma integrable_fubini_neg (a lam : ℝ) (ha : 0 < a) (P : ℂ) (hP : 0 < P.re) :
    Integrable (fun p : ℝ × ℝ => gK a lam p.1 * (Ioi (0:ℝ)).indicator (fun r : ℝ => Complex.exp (-((P + (p.1:ℂ)*Complex.I)*(r:ℂ)))) p.2)
      ((volume : Measure ℝ).prod (volume : Measure ℝ)) := by
  have hprod : Integrable (fun z : ℝ × ℝ => ‖gK a lam z.1‖ * (Ioi (0:ℝ)).indicator (fun r : ℝ => Real.exp (-P.re * r)) z.2)
      ((volume : Measure ℝ).prod (volume : Measure ℝ)) :=
    MeasureTheory.Integrable.mul_prod
      (f := fun u : ℝ => ‖gK a lam u‖)
      (g := fun r : ℝ => (Ioi (0:ℝ)).indicator (fun r : ℝ => Real.exp (-P.re * r)) r)
      (integrable_gK_norm a lam ha) ((integrable_indicator_iff measurableSet_Ioi).mpr (integrable_exp_restrict P hP))
  refine hprod.mono' ?_ ?_
  · apply Measurable.aestronglyMeasurable
    apply Measurable.mul
    · exact (continuous_gK a lam ha).measurable.comp measurable_fst
    · exact Measurable.ite (measurableSet_Ioi.preimage measurable_snd)
        (Complex.continuous_exp.measurable.comp (by fun_prop)) measurable_const
  · filter_upwards with p
    rw [norm_mul]
    have h2 : ‖(Ioi (0:ℝ)).indicator (fun r : ℝ => Complex.exp (-((P + (p.1:ℂ)*Complex.I)*(r:ℂ)))) p.2‖
        ≤ (Ioi (0:ℝ)).indicator (fun r : ℝ => Real.exp (-P.re * r)) p.2 := by
      by_cases hp : p.2 ∈ Ioi (0:ℝ)
      · rw [Set.indicator_of_mem hp, Set.indicator_of_mem hp, Complex.norm_exp]
        apply le_of_eq
        congr 1
        simp only [Complex.neg_re, Complex.mul_re, Complex.add_re, Complex.add_im, Complex.ofReal_re,
          Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_one, mul_zero, sub_zero, add_zero]
        ring
      · rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem hp, norm_zero]
    exact mul_le_mul_of_nonneg_left h2 (norm_nonneg _)

lemma J_fubini_neg (a lam : ℝ) (ha : 0 < a) (P : ℂ) (hP : 0 < P.re) :
    (∫ u : ℝ, gK a lam u / (P + (u:ℂ)*Complex.I))
      = ∫ r in Ioi (0:ℝ), Complex.exp (-(P*(r:ℂ))) * ghat a lam (-r) := by
  have hf := integrable_fubini_neg a lam ha P hP
  have hswap := integral_integral_swap (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
    (f := fun u r => gK a lam u * (Ioi (0:ℝ)).indicator (fun r : ℝ => Complex.exp (-((P + (u:ℂ)*Complex.I)*(r:ℂ)))) r) hf
  have hleft : (∫ u : ℝ, gK a lam u / (P + (u:ℂ)*Complex.I))
      = ∫ u : ℝ, ∫ r : ℝ, gK a lam u * (Ioi (0:ℝ)).indicator (fun r : ℝ => Complex.exp (-((P + (u:ℂ)*Complex.I)*(r:ℂ)))) r ∂volume ∂volume := by
    apply integral_congr_ae; filter_upwards with u
    have hP' : (-(P + (u:ℂ)*Complex.I)).re < 0 := by
      simp only [Complex.neg_re, Complex.add_re, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re,
        Complex.I_re, Complex.I_im, mul_one, mul_zero, sub_zero, add_zero]
      linarith [hP]
    have h := integral_exp_mul_complex_Ioi (a := -(P + (u:ℂ)*Complex.I)) hP' 0
    have hexp : (∫ r : ℝ in Ioi (0:ℝ), Complex.exp (-((P + (u:ℂ)*Complex.I)*(r:ℂ))))
        = (P + (u:ℂ)*Complex.I)⁻¹ := by
      rw [show (∫ r : ℝ in Ioi (0:ℝ), Complex.exp (-((P + (u:ℂ)*Complex.I)*(r:ℂ))))
          = ∫ r : ℝ in Ioi (0:ℝ), Complex.exp ((-(P + (u:ℂ)*Complex.I))*(r:ℂ)) from by
          apply integral_congr_ae; filter_upwards with r; congr 1; ring]
      rw [h, Complex.ofReal_zero, mul_zero, Complex.exp_zero]
      rw [show (-1 / -(P + (u:ℂ) * Complex.I)) = (P + (u:ℂ) * Complex.I)⁻¹ by field_simp]
    have hint : (∫ r : ℝ, (Ioi (0:ℝ)).indicator (fun r : ℝ => Complex.exp (-((P + (u:ℂ)*Complex.I)*(r:ℂ)))) r)
        = ∫ r : ℝ in Ioi (0:ℝ), Complex.exp (-((P + (u:ℂ)*Complex.I)*(r:ℂ))) := integral_indicator_Ioi _
    have hfac : (∫ r : ℝ, gK a lam u * (Ioi (0:ℝ)).indicator (fun r : ℝ => Complex.exp (-((P + (u:ℂ)*Complex.I)*(r:ℂ)))) r)
        = gK a lam u * (∫ r : ℝ, (Ioi (0:ℝ)).indicator (fun r : ℝ => Complex.exp (-((P + (u:ℂ)*Complex.I)*(r:ℂ)))) r) := by
      rw [← integral_const_mul]
    rw [hfac, hint, hexp, div_eq_mul_inv]
  have hright : (∫ r in Ioi (0:ℝ), Complex.exp (-(P*(r:ℂ))) * ghat a lam (-r))
      = ∫ r : ℝ, ∫ u : ℝ, gK a lam u * (Ioi (0:ℝ)).indicator (fun r : ℝ => Complex.exp (-((P + (u:ℂ)*Complex.I)*(r:ℂ)))) r ∂volume ∂volume := by
    rw [← integral_indicator_Ioi (fun r : ℝ => Complex.exp (-(P*(r:ℂ))) * ghat a lam (-r))]
    apply integral_congr_ae; filter_upwards with r
    by_cases hr : r ∈ Ioi (0:ℝ)
    · have hinner : (∫ u : ℝ, gK a lam u * (Ioi (0:ℝ)).indicator (fun r : ℝ => Complex.exp (-((P + (u:ℂ)*Complex.I)*(r:ℂ)))) r)
          = ∫ u : ℝ, gK a lam u * Complex.exp (-((P + (u:ℂ)*Complex.I)*(r:ℂ))) := by
        apply integral_congr_ae; filter_upwards with u; rw [Set.indicator_of_mem hr]
      have hswap2 : (∫ u : ℝ, gK a lam u * Complex.exp (-((P + (u:ℂ)*Complex.I)*(r:ℂ))))
          = Complex.exp (-(P*(r:ℂ))) * (∫ u : ℝ, gK a lam u * Complex.exp (((-r:ℝ):ℂ)*((u:ℂ)*Complex.I))) := by
        rw [← integral_const_mul]
        apply integral_congr_ae; filter_upwards with u
        rw [show Complex.exp (-((P + (u:ℂ)*Complex.I)*(r:ℂ))) = Complex.exp (-(P*(r:ℂ))) * Complex.exp (((-r:ℝ):ℂ)*((u:ℂ)*Complex.I)) from by
          rw [← Complex.exp_add]; congr 1; push_cast; ring]
        ring
      have hghat : (∫ u : ℝ, gK a lam u * Complex.exp (((-r:ℝ):ℂ)*((u:ℂ)*Complex.I))) = ghat a lam (-r) := rfl
      rw [Set.indicator_of_mem hr, hinner, hswap2, hghat]
    · have hzero : (∫ u : ℝ, gK a lam u * (Ioi (0:ℝ)).indicator (fun r : ℝ => Complex.exp (-((P + (u:ℂ)*Complex.I)*(r:ℂ)))) r) = 0 := by
        apply integral_eq_zero_of_ae; filter_upwards with u
        simp only [Set.indicator_of_notMem hr, mul_zero, Pi.zero_apply]
      rw [Set.indicator_of_notMem hr, hzero]
  rw [hleft, hright, hswap]

lemma integral_gK_div_add_I (a lam : ℝ) (ha : 0 < a) (hlam : 0 < lam) (P : ℂ) (hP : 0 < P.re) :
    ∫ u : ℝ, gK a lam u / (P + (u:ℂ)*Complex.I) = 0 := by
  rw [J_fubini_neg a lam ha P hP]
  have hzero : ∀ r ∈ Ioi (0:ℝ), Complex.exp (-(P*(r:ℂ))) * ghat a lam (-r) = 0 := by
    intro r hr
    rw [mem_Ioi] at hr
    rw [ghat_eq' a lam (-r) ha,
      K2_nonpos a ((-r)-lam) ha (by linarith), K2_nonpos a (-r) ha (by linarith)]
    ring
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hzero]
  simp

/-- The vanishing of `∫ gK / (wminus + n)`. -/
lemma integral_gK_div_wminus_add (a lam x b : ℝ) (ha : 0 < a) (hlam : 0 < lam)
    (n : ℕ) (hx : 0 < x + (n:ℝ)) :
    (∫ u : ℝ, gK a lam u / (wminus x b u + (n:ℂ))) = 0 := by
  set P : ℂ := ((2*(x+(n:ℝ)) : ℝ):ℂ) - (b:ℂ)*Complex.I with hPdef
  have hPre : P.re = 2*(x+(n:ℝ)) := by
    rw [hPdef]
    simp [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  have hP : 0 < P.re := by rw [hPre]; linarith
  have hcongr : (∫ u : ℝ, gK a lam u / (wminus x b u + (n:ℂ)))
      = ∫ u : ℝ, (2:ℂ) * (gK a lam u / (P + (u:ℂ)*Complex.I)) := by
    apply integral_congr_ae; filter_upwards with u
    have hz : wminus x b u + (n:ℂ) = (P + (u:ℂ)*Complex.I)/2 := by
      rw [hPdef]; simp only [wminus]; push_cast; ring
    have hne : P + (u:ℂ)*Complex.I ≠ 0 := by
      intro h
      have := congrArg Complex.re h
      rw [re_add_I P u, Complex.zero_re] at this
      linarith [hP]
    rw [hz]
    field_simp
  rw [hcongr, MeasureTheory.integral_const_mul, integral_gK_div_add_I a lam ha hlam P hP, mul_zero]

lemma continuous_dgTermC_wminus (x b : ℝ) (hx : (1:ℝ)/4 ≤ x) (n : ℕ) :
    Continuous (fun u : ℝ => Commons.Analysis.SpecialFunctions.Gamma.dgTermC (wminus x b u) n) := by
  have hne : ∀ u : ℝ, wminus x b u + (n:ℂ) ≠ 0 := by
    intro u h
    have h2 := congrArg Complex.re h
    rw [Complex.add_re, re_wminus] at h2
    simp at h2
    have hn : (0:ℝ) ≤ (n : ℝ) := by positivity
    linarith [hx]
  have h1 : Continuous (fun u : ℝ => (wminus x b u + (n:ℂ))⁻¹) := by
    apply Continuous.inv₀ _ hne
    exact (wminus_cont x b).add continuous_const
  have h2 : Continuous (fun _ : ℝ => (((n:ℂ)+1)⁻¹)) := continuous_const
  have hdef : Commons.Analysis.SpecialFunctions.Gamma.dgTermC = fun (s : ℂ) (n : ℕ) => ((n:ℂ)+1)⁻¹ - (s + (n:ℂ))⁻¹ := rfl
  rw [hdef]
  exact h2.sub h1

lemma integrable_inv_wminus_gK (a lam x b : ℝ) (ha : 0 < a) (n : ℕ) (hx : (1:ℝ)/4 ≤ x) :
    Integrable (fun u : ℝ => ((wminus x b u + (n:ℂ))⁻¹) * gK a lam u) (volume : Measure ℝ) := by
  have hval : (0:ℝ) < x + (n:ℝ) := by
    have hn : (0:ℝ) ≤ (n : ℝ) := by positivity
    linarith
  refine ((integrable_gK_norm a lam ha).const_mul ((x + (n:ℝ))⁻¹)).mono' ?_ ?_
  · have hc : Continuous (fun u : ℝ => (wminus x b u + (n:ℂ))⁻¹) := by
      apply Continuous.inv₀ ((wminus_cont x b).add continuous_const)
      intro u h
      have h2 : (wminus x b u + (n:ℂ)).re = 0 := by
        have hh := congrArg Complex.re h
        simpa only [Pi.add_apply, Complex.zero_re] using hh
      rw [re_wminus_add_nat] at h2
      linarith
    exact (hc.mul (continuous_gK a lam ha)).aestronglyMeasurable
  · filter_upwards with u
    rw [norm_mul]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    rw [norm_inv]
    apply inv_anti₀ hval
    have h := Complex.re_le_norm (wminus x b u + (n:ℂ))
    rw [Complex.add_re, re_wminus] at h
    simpa using h

lemma interchange_minus_small (a lam x' b : ℝ) (ha : 0 < a) (hlam : 0 < lam)
    (hx1 : (1:ℝ)/4 ≤ x') (hx2 : x' ≤ 8) :
    (∫ u : ℝ, Complex.digamma (wminus x' b u) * gK a lam u) = 0 := by
  have hcontN : ∀ N : ℕ, Continuous (fun u : ℝ => (-(Real.eulerMascheroniConstant:ℂ) +
      ∑ n ∈ Finset.range N, Commons.Analysis.SpecialFunctions.Gamma.dgTermC (wminus x' b u) n)) := by
    intro N
    apply Continuous.add continuous_const
    exact continuous_finsetSum _ (fun n _ => continuous_dgTermC_wminus x' b hx1 n)
  have hFmeas : ∀ N : ℕ, AEStronglyMeasurable
      (fun u : ℝ => (-(Real.eulerMascheroniConstant:ℂ) +
        ∑ n ∈ Finset.range N, Commons.Analysis.SpecialFunctions.Gamma.dgTermC (wminus x' b u) n) * gK a lam u) volume :=
    fun N => ((hcontN N).mul (continuous_gK a lam ha)).aestronglyMeasurable
  have hbnd : ∀ (N : ℕ) (u : ℝ), ‖(-(Real.eulerMascheroniConstant:ℂ) +
        ∑ n ∈ Finset.range N, Commons.Analysis.SpecialFunctions.Gamma.dgTermC (wminus x' b u) n) * gK a lam u‖
      ≤ (Real.log (2 + |b - u|/2) + 7 + ‖(Real.eulerMascheroniConstant : ℂ)‖) * ‖gK a lam u‖ := by
    intro N u
    rw [norm_mul]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    have hsum : Summable (fun n : ℕ => ‖Commons.Analysis.SpecialFunctions.Gamma.dgTermC (wminus x' b u) n‖) :=
      Commons.Analysis.SpecialFunctions.Gamma.summable_dgTerm_norm _ (by rw [re_wminus]; exact hx1)
    have hb1 : (∑' n : ℕ, ‖Commons.Analysis.SpecialFunctions.Gamma.dgTermC (wminus x' b u) n‖) ≤ Real.log (2 + |b-u|/2) + 7 := by
      have h := Commons.Analysis.SpecialFunctions.Gamma.digamma_series_norm_bound x' ((u-b)/2) hx1 hx2
      have harg : wminus x' b u = (x':ℂ) + (((u-b)/2:ℝ):ℂ)*Complex.I := by
        simp only [wminus]; push_cast; ring
      have hy : |((u-b)/2 : ℝ)| = |b-u|/2 := by rw [abs_div, abs_sub_comm]; norm_num
      simpa only [Commons.Analysis.SpecialFunctions.Gamma.dgTermC, harg, hy] using h
    have h2 : ‖∑ n ∈ Finset.range N, Commons.Analysis.SpecialFunctions.Gamma.dgTermC (wminus x' b u) n‖ ≤ Real.log (2 + |b-u|/2) + 7 :=
      le_trans (norm_sum_le _ _) (le_trans (hsum.sum_le_tsum _ (fun n _ => norm_nonneg _)) hb1)
    calc ‖(-(Real.eulerMascheroniConstant:ℂ)) + ∑ n ∈ Finset.range N, Commons.Analysis.SpecialFunctions.Gamma.dgTermC (wminus x' b u) n‖
        ≤ ‖(-(Real.eulerMascheroniConstant:ℂ))‖ + ‖∑ n ∈ Finset.range N, Commons.Analysis.SpecialFunctions.Gamma.dgTermC (wminus x' b u) n‖ := norm_add_le _ _
      _ ≤ ‖(Real.eulerMascheroniConstant:ℂ)‖ + (Real.log (2 + |b-u|/2) + 7) := by rw [norm_neg]; linarith
      _ = Real.log (2 + |b-u|/2) + 7 + ‖(Real.eulerMascheroniConstant : ℂ)‖ := by ring
  have hlim : ∀ᵐ u : ℝ ∂volume, Tendsto (fun N : ℕ => (-(Real.eulerMascheroniConstant:ℂ) +
        ∑ n ∈ Finset.range N, Commons.Analysis.SpecialFunctions.Gamma.dgTermC (wminus x' b u) n) * gK a lam u) atTop
      (nhds (Complex.digamma (wminus x' b u) * gK a lam u)) := by
    filter_upwards with u
    have hsum : Summable (fun n : ℕ => Commons.Analysis.SpecialFunctions.Gamma.dgTermC (wminus x' b u) n) := by
      refine Summable.of_norm ?_
      simpa using Commons.Analysis.SpecialFunctions.Gamma.summable_dgTerm_norm (wminus x' b u) (by rw [re_wminus]; exact hx1)
    have hs : HasSum (fun n : ℕ => Commons.Analysis.SpecialFunctions.Gamma.dgTermC (wminus x' b u) n)
        (Complex.digamma (wminus x' b u) + (Real.eulerMascheroniConstant:ℂ)) := by
      rw [hsum.hasSum_iff_tendsto_nat]
      have hthis := Commons.Analysis.SpecialFunctions.Gamma.digamma_eq_euler_sub_tsum (wminus x' b u) (by rw [re_wminus]; exact hx1)
      rw [hthis]
      rw [show (-(Real.eulerMascheroniConstant:ℂ) + ∑' n : ℕ, Commons.Analysis.SpecialFunctions.Gamma.dgTermC (wminus x' b u) n) + (Real.eulerMascheroniConstant:ℂ) = ∑' n : ℕ, Commons.Analysis.SpecialFunctions.Gamma.dgTermC (wminus x' b u) n by ring]
      exact hsum.hasSum.tendsto_sum_nat
    have ht' := hs.tendsto_sum_nat.const_add (-(Real.eulerMascheroniConstant:ℂ))
    have ht'' : Tendsto (fun N : ℕ => -(Real.eulerMascheroniConstant:ℂ) + ∑ n ∈ Finset.range N, Commons.Analysis.SpecialFunctions.Gamma.dgTermC (wminus x' b u) n) atTop (nhds (Complex.digamma (wminus x' b u))) := by
      rw [add_comm (Complex.digamma _)] at ht'
      simpa using ht'
    exact ht''.mul_const (gK a lam u)
  have hDCT := MeasureTheory.tendsto_integral_of_dominated_convergence
    (μ := (volume : Measure ℝ))
    (F := fun (N : ℕ) (u : ℝ) => (-(Real.eulerMascheroniConstant:ℂ) + ∑ n ∈ Finset.range N, Commons.Analysis.SpecialFunctions.Gamma.dgTermC (wminus x' b u) n) * gK a lam u)
    (f := fun u : ℝ => Complex.digamma (wminus x' b u) * gK a lam u)
    (fun u : ℝ => (Real.log (2 + |b - u|/2) + 7 + ‖(Real.eulerMascheroniConstant : ℂ)‖) * ‖gK a lam u‖)
    hFmeas (integrable_bound_gK a lam b ha) (fun N => Filter.Eventually.of_forall (fun u => hbnd N u)) hlim
  have hI1 : ∀ n : ℕ, Integrable (fun u : ℝ => (((n:ℂ)+1)⁻¹) * gK a lam u) (volume : Measure ℝ) :=
    fun n => (integrable_gK a lam ha).const_mul _
  have hI2 : ∀ n : ℕ, Integrable (fun u : ℝ => ((wminus x' b u + (n:ℂ))⁻¹) * gK a lam u) (volume : Measure ℝ) :=
    fun n => integrable_inv_wminus_gK a lam x' b ha n hx1
  have hpiece_integrable : ∀ n : ℕ, Integrable (fun u : ℝ => Commons.Analysis.SpecialFunctions.Gamma.dgTermC (wminus x' b u) n * gK a lam u) (volume : Measure ℝ) := by
    intro n
    refine ((integrable_gK_norm a lam ha).const_mul 5).mono' ?_ ?_
    · exact ((continuous_dgTermC_wminus x' b hx1 n).mul (continuous_gK a lam ha)).aestronglyMeasurable
    · filter_upwards with u
      rw [norm_mul]
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      rw [show Commons.Analysis.SpecialFunctions.Gamma.dgTermC (wminus x' b u) n = ((n:ℂ)+1)⁻¹ - (wminus x' b u + (n:ℂ))⁻¹ from rfl]
      calc ‖((n:ℂ)+1)⁻¹ - (wminus x' b u + (n:ℂ))⁻¹‖
          ≤ ‖((n:ℂ)+1)⁻¹‖ + ‖(wminus x' b u + (n:ℂ))⁻¹‖ := norm_sub_le _ _
        _ ≤ 1 + 4 := by
            apply add_le_add
            · rw [norm_inv, Commons.Analysis.SpecialFunctions.Gamma.norm_nat_add_one]
              have hn : (0:ℝ) < (n:ℝ)+1 := by positivity
              exact (inv_le_one₀ hn).mpr (by linarith)
            · rw [norm_inv]
              have h := Complex.re_le_norm (wminus x' b u + (n:ℂ))
              rw [re_wminus_add_nat] at h
              have hx'n : (0:ℝ) < x' + (n:ℝ) := by
                have hn : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
                linarith [hx1]
              have hne : wminus x' b u + (n:ℂ) ≠ 0 := by
                intro hh
                have h2 := congrArg Complex.re hh
                rw [re_wminus_add_nat, Complex.zero_re] at h2
                linarith
              have hnormpos : 0 < ‖wminus x' b u + (n:ℂ)‖ := norm_pos_iff.mpr hne
              calc (‖wminus x' b u + (n:ℂ)‖)⁻¹ ≤ (x' + (n:ℝ))⁻¹ := (inv_le_inv₀ hnormpos hx'n).mpr h
                _ ≤ 4 := by
                    rw [inv_le_comm₀ hx'n (by norm_num : (0:ℝ) < 4)]
                    have hn : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
                    linarith [hx1]
        _ ≤ 5 := by norm_num
  have hpieceval : ∀ n : ℕ, (∫ u : ℝ, Commons.Analysis.SpecialFunctions.Gamma.dgTermC (wminus x' b u) n * gK a lam u) = 0 := by
    intro n
    have hx'n : (0:ℝ) < x' + (n:ℝ) := by
      have hn : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
      linarith [hx1]
    have hcong : (∫ u : ℝ, Commons.Analysis.SpecialFunctions.Gamma.dgTermC (wminus x' b u) n * gK a lam u)
        = ∫ u : ℝ, ((((n:ℂ)+1)⁻¹) * gK a lam u - ((wminus x' b u + (n:ℂ))⁻¹) * gK a lam u) := by
      apply integral_congr_ae; filter_upwards with u
      rw [show Commons.Analysis.SpecialFunctions.Gamma.dgTermC (wminus x' b u) n = ((n:ℂ)+1)⁻¹ - (wminus x' b u + (n:ℂ))⁻¹ from rfl, sub_mul]
    rw [hcong, MeasureTheory.integral_sub (hI1 n) (hI2 n), integral_const_mul,
      integral_gK_zero a lam ha hlam, mul_zero, zero_sub]
    have hz : (∫ u : ℝ, ((wminus x' b u + (n:ℂ))⁻¹) * gK a lam u) = 0 := by
      rw [← integral_gK_div_wminus_add a lam x' b ha hlam n hx'n]
      apply integral_congr_ae; filter_upwards with u
      rw [div_eq_mul_inv, mul_comm]
    rw [hz, neg_zero]
  have hFint : ∀ N : ℕ, Integrable (fun u : ℝ => (-(Real.eulerMascheroniConstant:ℂ) +
      ∑ n ∈ Finset.range N, Commons.Analysis.SpecialFunctions.Gamma.dgTermC (wminus x' b u) n) * gK a lam u) (volume : Measure ℝ) :=
    fun N => (integrable_bound_gK a lam b ha).mono' (hFmeas N) (Filter.Eventually.of_forall (fun u => hbnd N u))
  have hFN : ∀ N : ℕ, (∫ u : ℝ, (-(Real.eulerMascheroniConstant:ℂ) +
      ∑ n ∈ Finset.range N, Commons.Analysis.SpecialFunctions.Gamma.dgTermC (wminus x' b u) n) * gK a lam u) = 0 := by
    intro N
    induction N with
    | zero =>
      simp only [Finset.sum_range_zero, add_zero]
      rw [show (∫ u : ℝ, (-(Real.eulerMascheroniConstant:ℂ)) * gK a lam u)
          = (-(Real.eulerMascheroniConstant:ℂ)) * (∫ u : ℝ, gK a lam u) from integral_const_mul _ _]
      rw [integral_gK_zero a lam ha hlam, mul_zero]
    | succ N ih =>
      simp only [Finset.sum_range_succ]
      rw [show (∫ u : ℝ, (-(Real.eulerMascheroniConstant:ℂ) + (∑ n ∈ Finset.range N, Commons.Analysis.SpecialFunctions.Gamma.dgTermC (wminus x' b u) n + Commons.Analysis.SpecialFunctions.Gamma.dgTermC (wminus x' b u) N)) * gK a lam u)
          = ∫ u : ℝ, ((-(Real.eulerMascheroniConstant:ℂ) + ∑ n ∈ Finset.range N, Commons.Analysis.SpecialFunctions.Gamma.dgTermC (wminus x' b u) n) * gK a lam u + Commons.Analysis.SpecialFunctions.Gamma.dgTermC (wminus x' b u) N * gK a lam u) from by
          apply integral_congr_ae; filter_upwards with u; ring]
      rw [MeasureTheory.integral_add (hFint N) (hpiece_integrable N), ih, hpieceval N]
      ring
  have hzero : Tendsto (fun N : ℕ => (∫ u : ℝ, (-(Real.eulerMascheroniConstant:ℂ) +
      ∑ n ∈ Finset.range N, Commons.Analysis.SpecialFunctions.Gamma.dgTermC (wminus x' b u) n) * gK a lam u)) atTop (nhds 0) := by
    have hfun : (fun N : ℕ => (∫ u : ℝ, (-(Real.eulerMascheroniConstant:ℂ) +
        ∑ n ∈ Finset.range N, Commons.Analysis.SpecialFunctions.Gamma.dgTermC (wminus x' b u) n) * gK a lam u)) = fun _ => (0:ℂ) :=
      funext hFN
    rw [hfun]
    exact tendsto_const_nhds
  exact tendsto_nhds_unique hDCT hzero

lemma psi_hFN_minus (a lam x' b : ℝ) (ha : 0 < a) (hlam : 0 < lam)
    (hx1 : (1:ℝ)/4 ≤ x') (hx2 : x' ≤ 8) (N : ℕ) :
    (∫ u : ℝ, (-(Real.eulerMascheroniConstant:ℂ) +
      ∑ n ∈ Finset.range N, Commons.Analysis.SpecialFunctions.Gamma.dgTermC (wminus x' b u) n) * gK a lam u) = 0 := by
  have hbnd : ∀ (M : ℕ) (u : ℝ), ‖(-(Real.eulerMascheroniConstant:ℂ) +
        ∑ n ∈ Finset.range M, Commons.Analysis.SpecialFunctions.Gamma.dgTermC (wminus x' b u) n) * gK a lam u‖
      ≤ (Real.log (2 + |b - u|/2) + 7 + ‖(Real.eulerMascheroniConstant : ℂ)‖) * ‖gK a lam u‖ := by
    intro M u
    rw [norm_mul]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    have hsum : Summable (fun n : ℕ => ‖Commons.Analysis.SpecialFunctions.Gamma.dgTermC (wminus x' b u) n‖) :=
      Commons.Analysis.SpecialFunctions.Gamma.summable_dgTerm_norm _ (by rw [re_wminus]; exact hx1)
    have hb1 : (∑' n : ℕ, ‖Commons.Analysis.SpecialFunctions.Gamma.dgTermC (wminus x' b u) n‖) ≤ Real.log (2 + |b-u|/2) + 7 := by
      have h := Commons.Analysis.SpecialFunctions.Gamma.digamma_series_norm_bound x' ((u-b)/2) hx1 hx2
      have harg : wminus x' b u = (x':ℂ) + (((u-b)/2:ℝ):ℂ)*Complex.I := by
        simp only [wminus]; push_cast; ring
      have hy : |((u-b)/2 : ℝ)| = |b-u|/2 := by rw [abs_div, abs_sub_comm]; norm_num
      simpa only [Commons.Analysis.SpecialFunctions.Gamma.dgTermC, harg, hy] using h
    have h2 : ‖∑ n ∈ Finset.range M, Commons.Analysis.SpecialFunctions.Gamma.dgTermC (wminus x' b u) n‖ ≤ Real.log (2 + |b-u|/2) + 7 :=
      le_trans (norm_sum_le _ _) (le_trans (hsum.sum_le_tsum _ (fun n _ => norm_nonneg _)) hb1)
    calc ‖(-(Real.eulerMascheroniConstant:ℂ)) + ∑ n ∈ Finset.range M, Commons.Analysis.SpecialFunctions.Gamma.dgTermC (wminus x' b u) n‖
        ≤ ‖(-(Real.eulerMascheroniConstant:ℂ))‖ + ‖∑ n ∈ Finset.range M, Commons.Analysis.SpecialFunctions.Gamma.dgTermC (wminus x' b u) n‖ := norm_add_le _ _
      _ ≤ ‖(Real.eulerMascheroniConstant:ℂ)‖ + (Real.log (2 + |b-u|/2) + 7) := by rw [norm_neg]; linarith
      _ = Real.log (2 + |b-u|/2) + 7 + ‖(Real.eulerMascheroniConstant : ℂ)‖ := by ring
  have hcontM : ∀ M : ℕ, Continuous (fun u : ℝ => (-(Real.eulerMascheroniConstant:ℂ) +
      ∑ n ∈ Finset.range M, Commons.Analysis.SpecialFunctions.Gamma.dgTermC (wminus x' b u) n)) := by
    intro M
    apply Continuous.add continuous_const
    exact continuous_finsetSum _ (fun n _ => continuous_dgTermC_wminus x' b hx1 n)
  have hFint : ∀ M : ℕ, Integrable (fun u : ℝ => (-(Real.eulerMascheroniConstant:ℂ) +
      ∑ n ∈ Finset.range M, Commons.Analysis.SpecialFunctions.Gamma.dgTermC (wminus x' b u) n) * gK a lam u) (volume : Measure ℝ) :=
    fun M => (integrable_bound_gK a lam b ha).mono'
      (((hcontM M)).mul (continuous_gK a lam ha)).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun u => hbnd M u))
  have hI1 : ∀ n : ℕ, Integrable (fun u : ℝ => (((n:ℂ)+1)⁻¹) * gK a lam u) (volume : Measure ℝ) :=
    fun n => (integrable_gK a lam ha).const_mul _
  have hI2 : ∀ n : ℕ, Integrable (fun u : ℝ => ((wminus x' b u + (n:ℂ))⁻¹) * gK a lam u) (volume : Measure ℝ) :=
    fun n => integrable_inv_wminus_gK a lam x' b ha n hx1
  have hpiece_integrable : ∀ n : ℕ, Integrable (fun u : ℝ => Commons.Analysis.SpecialFunctions.Gamma.dgTermC (wminus x' b u) n * gK a lam u) (volume : Measure ℝ) := by
    intro n
    refine ((integrable_gK_norm a lam ha).const_mul 5).mono' ?_ ?_
    · exact ((continuous_dgTermC_wminus x' b hx1 n).mul (continuous_gK a lam ha)).aestronglyMeasurable
    · filter_upwards with u
      rw [norm_mul]
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      rw [show Commons.Analysis.SpecialFunctions.Gamma.dgTermC (wminus x' b u) n = ((n:ℂ)+1)⁻¹ - (wminus x' b u + (n:ℂ))⁻¹ from rfl]
      calc ‖((n:ℂ)+1)⁻¹ - (wminus x' b u + (n:ℂ))⁻¹‖
          ≤ ‖((n:ℂ)+1)⁻¹‖ + ‖(wminus x' b u + (n:ℂ))⁻¹‖ := norm_sub_le _ _
        _ ≤ 1 + 4 := by
            apply add_le_add
            · rw [norm_inv, Commons.Analysis.SpecialFunctions.Gamma.norm_nat_add_one]
              have hn : (0:ℝ) < (n:ℝ)+1 := by positivity
              have hn0 : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
              exact (inv_le_one₀ hn).mpr (by linarith)
            · rw [norm_inv]
              have h := Complex.re_le_norm (wminus x' b u + (n:ℂ))
              rw [re_wminus_add_nat] at h
              have hx'n : (0:ℝ) < x' + (n:ℝ) := by
                have hn : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
                linarith [hx1]
              have hne : wminus x' b u + (n:ℂ) ≠ 0 := by
                intro hh
                have h2 := congrArg Complex.re hh
                rw [re_wminus_add_nat, Complex.zero_re] at h2
                linarith
              have hnormpos : 0 < ‖wminus x' b u + (n:ℂ)‖ := norm_pos_iff.mpr hne
              calc (‖wminus x' b u + (n:ℂ)‖)⁻¹ ≤ (x' + (n:ℝ))⁻¹ := (inv_le_inv₀ hnormpos hx'n).mpr h
                _ ≤ 4 := by
                    have hge : (1:ℝ)/4 ≤ x' + (n:ℝ) := by
                      have hn : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
                      linarith [hx1]
                    have hh := inv_anti₀ (by norm_num : (0:ℝ) < 1/4) hge
                    rw [show ((1:ℝ)/4)⁻¹ = 4 by norm_num] at hh
                    exact hh
        _ ≤ 5 := by norm_num
  have hpieceval : ∀ n : ℕ, (∫ u : ℝ, Commons.Analysis.SpecialFunctions.Gamma.dgTermC (wminus x' b u) n * gK a lam u) = 0 := by
    intro n
    have hx'n : (0:ℝ) < x' + (n:ℝ) := by
      have hn : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
      linarith [hx1]
    have hcong : (∫ u : ℝ, Commons.Analysis.SpecialFunctions.Gamma.dgTermC (wminus x' b u) n * gK a lam u)
        = ∫ u : ℝ, ((((n:ℂ)+1)⁻¹) * gK a lam u - ((wminus x' b u + (n:ℂ))⁻¹) * gK a lam u) := by
      apply integral_congr_ae; filter_upwards with u
      rw [show Commons.Analysis.SpecialFunctions.Gamma.dgTermC (wminus x' b u) n = ((n:ℂ)+1)⁻¹ - (wminus x' b u + (n:ℂ))⁻¹ from rfl, sub_mul]
    rw [hcong, MeasureTheory.integral_sub (hI1 n) (hI2 n), integral_const_mul,
      integral_gK_zero a lam ha hlam, mul_zero, zero_sub]
    have hz : (∫ u : ℝ, ((wminus x' b u + (n:ℂ))⁻¹) * gK a lam u) = 0 := by
      rw [← integral_gK_div_wminus_add a lam x' b ha hlam n hx'n]
      apply integral_congr_ae; filter_upwards with u
      rw [div_eq_mul_inv, mul_comm]
    rw [hz, neg_zero]
  induction N with
  | zero =>
    simp only [Finset.sum_range_zero, add_zero]
    rw [show (∫ u : ℝ, (-(Real.eulerMascheroniConstant:ℂ)) * gK a lam u)
        = (-(Real.eulerMascheroniConstant:ℂ)) * (∫ u : ℝ, gK a lam u) from integral_const_mul _ _]
    rw [integral_gK_zero a lam ha hlam, mul_zero]
  | succ N ih =>
    simp only [Finset.sum_range_succ]
    rw [show (∫ u : ℝ, (-(Real.eulerMascheroniConstant:ℂ) + (∑ n ∈ Finset.range N, Commons.Analysis.SpecialFunctions.Gamma.dgTermC (wminus x' b u) n + Commons.Analysis.SpecialFunctions.Gamma.dgTermC (wminus x' b u) N)) * gK a lam u)
        = ∫ u : ℝ, ((-(Real.eulerMascheroniConstant:ℂ) + ∑ n ∈ Finset.range N, Commons.Analysis.SpecialFunctions.Gamma.dgTermC (wminus x' b u) n) * gK a lam u + Commons.Analysis.SpecialFunctions.Gamma.dgTermC (wminus x' b u) N * gK a lam u) from by
        apply integral_congr_ae; filter_upwards with u; ring]
    rw [MeasureTheory.integral_add (hFint N) (hpiece_integrable N), ih, hpieceval N]
    ring

lemma norm_inv_wminus_add_le (x' b : ℝ) (hx1 : (1:ℝ)/4 ≤ x') (u : ℝ) (j : ℕ) :
    ‖((wminus x' b u) + (j:ℂ))⁻¹‖ ≤ 4 := by
  rw [norm_inv]
  have h := Complex.re_le_norm (wminus x' b u + (j:ℂ))
  rw [re_wminus_add_nat] at h
  have hpos : (0:ℝ) < x' + (j:ℝ) := by
    have hj0 : (0:ℝ) ≤ (j:ℝ) := Nat.cast_nonneg j
    linarith [hx1]
  have hne : wminus x' b u + (j:ℂ) ≠ 0 := by
    intro hh
    have h2 := congrArg Complex.re hh
    rw [re_wminus_add_nat, Complex.zero_re] at h2
    linarith
  have hnormpos : 0 < ‖wminus x' b u + (j:ℂ)‖ := norm_pos_iff.mpr hne
  calc (‖wminus x' b u + (j:ℂ)‖)⁻¹ ≤ (x' + (j:ℝ))⁻¹ := (inv_le_inv₀ hnormpos hpos).mpr h
    _ ≤ 4 := by
        have hge : (1:ℝ)/4 ≤ x' + (j:ℝ) := by
          have hj0 : (0:ℝ) ≤ (j:ℝ) := Nat.cast_nonneg j
          linarith [hx1]
        have hh := inv_anti₀ (by norm_num : (0:ℝ) < 1/4) hge
        rw [show ((1:ℝ)/4)⁻¹ = 4 by norm_num] at hh
        exact hh

lemma norm_sum_inv_wminus_le (x' b : ℝ) (hx1 : (1:ℝ)/4 ≤ x') (m : ℕ) (u : ℝ) :
    ‖∑ j ∈ Finset.range m, ((wminus x' b u) + (j:ℂ))⁻¹‖ ≤ 4*(m:ℝ) := by
  refine le_trans (norm_sum_le _ _) ?_
  have h1 : (∑ j ∈ Finset.range m, ‖((wminus x' b u) + (j:ℂ))⁻¹‖) ≤ ∑ _j ∈ Finset.range m, (4:ℝ) :=
    Finset.sum_le_sum (fun j _ => norm_inv_wminus_add_le x' b hx1 u j)
  have h2 : (∑ _j ∈ Finset.range m, (4:ℝ)) = 4*(m:ℝ) := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    ring
  linarith [h1, h2.le, h2.ge]

lemma norm_partial_sum_wminus_le (x' b : ℝ) (hx1 : (1:ℝ)/4 ≤ x') (hx2 : x' ≤ 8) (M : ℕ) (u : ℝ) :
    ‖(-(Real.eulerMascheroniConstant:ℂ) + ∑ n ∈ Finset.range M, Commons.Analysis.SpecialFunctions.Gamma.dgTermC (wminus x' b u) n)‖
      ≤ ‖(Real.eulerMascheroniConstant:ℂ)‖ + (Real.log (2 + |b-u|/2) + 7) := by
  have hsum : Summable (fun n : ℕ => ‖Commons.Analysis.SpecialFunctions.Gamma.dgTermC (wminus x' b u) n‖) :=
    Commons.Analysis.SpecialFunctions.Gamma.summable_dgTerm_norm _ (by rw [re_wminus]; exact hx1)
  have hb1 : (∑' n : ℕ, ‖Commons.Analysis.SpecialFunctions.Gamma.dgTermC (wminus x' b u) n‖) ≤ Real.log (2 + |b-u|/2) + 7 := by
    have h := Commons.Analysis.SpecialFunctions.Gamma.digamma_series_norm_bound x' ((u-b)/2) hx1 hx2
    have harg : wminus x' b u = (x':ℂ) + (((u-b)/2:ℝ):ℂ)*Complex.I := by
      simp only [wminus]; push_cast; ring
    have hy : |((u-b)/2 : ℝ)| = |b-u|/2 := by rw [abs_div, abs_sub_comm]; norm_num
    simpa only [Commons.Analysis.SpecialFunctions.Gamma.dgTermC, harg, hy] using h
  have h2 : ‖∑ n ∈ Finset.range M, Commons.Analysis.SpecialFunctions.Gamma.dgTermC (wminus x' b u) n‖ ≤ Real.log (2 + |b-u|/2) + 7 :=
    le_trans (norm_sum_le _ _) (le_trans (hsum.sum_le_tsum _ (fun n _ => norm_nonneg _)) hb1)
  calc ‖(-(Real.eulerMascheroniConstant:ℂ)) + ∑ n ∈ Finset.range M, Commons.Analysis.SpecialFunctions.Gamma.dgTermC (wminus x' b u) n‖
      ≤ ‖(-(Real.eulerMascheroniConstant:ℂ))‖ + ‖∑ n ∈ Finset.range M, Commons.Analysis.SpecialFunctions.Gamma.dgTermC (wminus x' b u) n‖ := norm_add_le _ _
    _ ≤ ‖(Real.eulerMascheroniConstant:ℂ)‖ + (Real.log (2 + |b-u|/2) + 7) := by rw [norm_neg]; linarith

lemma digamma_minus_integral_zero (a lam x b : ℝ) (ha : 0 < a) (hlam : 0 < lam)
    (hx : (1:ℝ)/4 ≤ x) :
    (∫ u : ℝ, Complex.digamma (wminus x b u) * gK a lam u) = 0 := by
  set m : ℕ := Nat.floor (x - (1:ℝ)/4) with hm
  set x' : ℝ := x - (m:ℝ) with hx'def
  have hxm : x = x' + (m:ℝ) := by rw [hx'def]; ring
  have hx'1 : (1:ℝ)/4 ≤ x' := by
    rw [hx'def]
    have hfl := Nat.floor_le (show (0:ℝ) ≤ x - (1:ℝ)/4 by linarith)
    linarith
  have hx'8 : x' ≤ 8 := by
    rw [hx'def]
    have hfl := Nat.lt_floor_add_one (x - (1:ℝ)/4)
    linarith
  have hpw : ∀ u : ℝ, Complex.digamma (wminus x b u) =
      Complex.digamma (wminus x' b u) + ∑ j ∈ Finset.range m, ((wminus x' b u) + (j:ℂ))⁻¹ := by
    intro u
    have hzw : wminus x b u = wminus x' b u + (m:ℂ) := by
      simp only [wminus]; rw [hxm]; push_cast; ring
    have hsh := psi_digamma_add_nat m (wminus x' b u) (by
      intro j hj n hflag
      exfalso
      have h3 : (wminus x' b u + (j:ℂ)).re = x' + (j:ℝ) := re_wminus_add_nat x' b u j
      have h5 := congrArg Complex.re hflag
      rw [h3] at h5
      have h5' : x' + (j:ℝ) = -(n:ℝ) := by rw [h5]; simp
      have hj0 : (0:ℝ) ≤ (j:ℝ) := Nat.cast_nonneg j
      have hn0 : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
      linarith [hx'1])
    rw [hzw, hsh]
  have hcontA : ∀ N : ℕ, Continuous (fun u : ℝ =>
      (-(Real.eulerMascheroniConstant:ℂ) + ∑ n ∈ Finset.range N, Commons.Analysis.SpecialFunctions.Gamma.dgTermC (wminus x' b u) n)
        + ∑ j ∈ Finset.range m, ((wminus x' b u) + (j:ℂ))⁻¹) := by
    intro N
    apply Continuous.add
    · apply Continuous.add continuous_const
      exact continuous_finsetSum _ (fun n _ => continuous_dgTermC_wminus x' b hx'1 n)
    · apply continuous_finsetSum
      intro j _
      apply Continuous.inv₀ ((wminus_cont x' b).add continuous_const)
      intro u hh
      have h2 : (wminus x' b u + (j:ℂ)).re = 0 := by
        have hh' := congrArg Complex.re hh
        simpa only [Pi.add_apply, Complex.zero_re] using hh'
      rw [re_wminus_add_nat] at h2
      have hj0 : (0:ℝ) ≤ (j:ℝ) := Nat.cast_nonneg j
      linarith [hx'1]
  have hmeasA : ∀ N : ℕ, AEStronglyMeasurable (fun u : ℝ =>
      ((-(Real.eulerMascheroniConstant:ℂ) + ∑ n ∈ Finset.range N, Commons.Analysis.SpecialFunctions.Gamma.dgTermC (wminus x' b u) n)
        + ∑ j ∈ Finset.range m, ((wminus x' b u) + (j:ℂ))⁻¹) * gK a lam u) volume :=
    fun N => ((hcontA N).mul (continuous_gK a lam ha)).aestronglyMeasurable
  have hdom : Integrable (fun u : ℝ =>
      (Real.log (2 + |b - u|/2) + 7 + ‖(Real.eulerMascheroniConstant:ℂ)‖ + 4*(m:ℝ)) * ‖gK a lam u‖) volume := by
    have hcong : (fun u : ℝ => (Real.log (2 + |b - u|/2) + 7 + ‖(Real.eulerMascheroniConstant:ℂ)‖ + 4*(m:ℝ)) * ‖gK a lam u‖)
        = fun u : ℝ => (Real.log (2 + |b - u|/2) + 7) * ‖gK a lam u‖ + (‖(Real.eulerMascheroniConstant:ℂ)‖ + 4*(m:ℝ)) * ‖gK a lam u‖ := by
      funext u; ring
    rw [hcong]
    exact (integrable_log_gK a lam b ha).add ((integrable_gK_norm a lam ha).const_mul _)
  have hleA : ∀ (N : ℕ) (u : ℝ),
      ‖((-(Real.eulerMascheroniConstant:ℂ) + ∑ n ∈ Finset.range N, Commons.Analysis.SpecialFunctions.Gamma.dgTermC (wminus x' b u) n)
        + ∑ j ∈ Finset.range m, ((wminus x' b u) + (j:ℂ))⁻¹) * gK a lam u‖
      ≤ (Real.log (2 + |b - u|/2) + 7 + ‖(Real.eulerMascheroniConstant:ℂ)‖ + 4*(m:ℝ)) * ‖gK a lam u‖ := by
    intro N u
    rw [norm_mul]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    have hfirst : ‖(-(Real.eulerMascheroniConstant:ℂ) + ∑ n ∈ Finset.range N, Commons.Analysis.SpecialFunctions.Gamma.dgTermC (wminus x' b u) n)‖
        ≤ ‖(Real.eulerMascheroniConstant:ℂ)‖ + (Real.log (2 + |b-u|/2) + 7) :=
      norm_partial_sum_wminus_le x' b hx'1 hx'8 N u
    have hsecond : ‖∑ j ∈ Finset.range m, ((wminus x' b u) + (j:ℂ))⁻¹‖ ≤ 4*(m:ℝ) :=
      norm_sum_inv_wminus_le x' b hx'1 m u
    calc ‖(-(Real.eulerMascheroniConstant:ℂ) + ∑ n ∈ Finset.range N, Commons.Analysis.SpecialFunctions.Gamma.dgTermC (wminus x' b u) n)
          + ∑ j ∈ Finset.range m, ((wminus x' b u) + (j:ℂ))⁻¹‖
        ≤ ‖(-(Real.eulerMascheroniConstant:ℂ) + ∑ n ∈ Finset.range N, Commons.Analysis.SpecialFunctions.Gamma.dgTermC (wminus x' b u) n)‖
          + ‖∑ j ∈ Finset.range m, ((wminus x' b u) + (j:ℂ))⁻¹‖ := norm_add_le _ _
      _ ≤ (‖(Real.eulerMascheroniConstant:ℂ)‖ + (Real.log (2 + |b-u|/2) + 7)) + 4*(m:ℝ) := add_le_add hfirst hsecond
      _ = Real.log (2 + |b-u|/2) + 7 + ‖(Real.eulerMascheroniConstant:ℂ)‖ + 4*(m:ℝ) := by ring
  have hlim : ∀ᵐ u : ℝ ∂volume, Tendsto (fun N : ℕ =>
      ((-(Real.eulerMascheroniConstant:ℂ) + ∑ n ∈ Finset.range N, Commons.Analysis.SpecialFunctions.Gamma.dgTermC (wminus x' b u) n)
        + ∑ j ∈ Finset.range m, ((wminus x' b u) + (j:ℂ))⁻¹) * gK a lam u) atTop
      (nhds (Complex.digamma (wminus x b u) * gK a lam u)) := by
    filter_upwards with u
    have hsum : Summable (fun n : ℕ => Commons.Analysis.SpecialFunctions.Gamma.dgTermC (wminus x' b u) n) := by
      refine Summable.of_norm ?_
      simpa using Commons.Analysis.SpecialFunctions.Gamma.summable_dgTerm_norm (wminus x' b u) (by rw [re_wminus]; exact hx'1)
    have hs : HasSum (fun n : ℕ => Commons.Analysis.SpecialFunctions.Gamma.dgTermC (wminus x' b u) n)
        (Complex.digamma (wminus x' b u) + (Real.eulerMascheroniConstant:ℂ)) := by
      rw [hsum.hasSum_iff_tendsto_nat]
      have hthis := Commons.Analysis.SpecialFunctions.Gamma.digamma_eq_euler_sub_tsum (wminus x' b u) (by rw [re_wminus]; exact hx'1)
      rw [hthis]
      rw [show (-(Real.eulerMascheroniConstant:ℂ) + ∑' n : ℕ, Commons.Analysis.SpecialFunctions.Gamma.dgTermC (wminus x' b u) n) + (Real.eulerMascheroniConstant:ℂ) = ∑' n : ℕ, Commons.Analysis.SpecialFunctions.Gamma.dgTermC (wminus x' b u) n by ring]
      exact hsum.hasSum.tendsto_sum_nat
    have ht' := hs.tendsto_sum_nat.const_add (-(Real.eulerMascheroniConstant:ℂ))
    have ht'' : Tendsto (fun N : ℕ => -(Real.eulerMascheroniConstant:ℂ) + ∑ n ∈ Finset.range N, Commons.Analysis.SpecialFunctions.Gamma.dgTermC (wminus x' b u) n) atTop (nhds (Complex.digamma (wminus x' b u))) := by
      rw [add_comm (Complex.digamma _)] at ht'
      simpa using ht'
    have ht2 := (ht''.add_const (∑ j ∈ Finset.range m, ((wminus x' b u) + (j:ℂ))⁻¹)).mul_const (gK a lam u)
    have hlim2 : Complex.digamma (wminus x' b u) + ∑ j ∈ Finset.range m, ((wminus x' b u) + (j:ℂ))⁻¹ = Complex.digamma (wminus x b u) := (hpw u).symm
    rwa [hlim2] at ht2
  have hDCT := MeasureTheory.tendsto_integral_of_dominated_convergence
    (μ := (volume : Measure ℝ))
    (F := fun (N : ℕ) (u : ℝ) => ((-(Real.eulerMascheroniConstant:ℂ) + ∑ n ∈ Finset.range N, Commons.Analysis.SpecialFunctions.Gamma.dgTermC (wminus x' b u) n)
        + ∑ j ∈ Finset.range m, ((wminus x' b u) + (j:ℂ))⁻¹) * gK a lam u)
    (f := fun u : ℝ => Complex.digamma (wminus x b u) * gK a lam u)
    (fun u : ℝ => (Real.log (2 + |b - u|/2) + 7 + ‖(Real.eulerMascheroniConstant:ℂ)‖ + 4*(m:ℝ)) * ‖gK a lam u‖)
    hmeasA hdom (fun N => Filter.Eventually.of_forall (fun u => hleA N u)) hlim
  have hFirst_int : ∀ N : ℕ, Integrable (fun u : ℝ => (-(Real.eulerMascheroniConstant:ℂ) +
      ∑ n ∈ Finset.range N, Commons.Analysis.SpecialFunctions.Gamma.dgTermC (wminus x' b u) n) * gK a lam u) volume := by
    intro N
    refine (integrable_bound_gK a lam b ha).mono' ?_ ?_
    · have hc : Continuous (fun u : ℝ => -(Real.eulerMascheroniConstant:ℂ) +
          ∑ n ∈ Finset.range N, Commons.Analysis.SpecialFunctions.Gamma.dgTermC (wminus x' b u) n) := by
        apply Continuous.add continuous_const
        exact continuous_finsetSum _ (fun n _ => continuous_dgTermC_wminus x' b hx'1 n)
      exact (hc.mul (continuous_gK a lam ha)).aestronglyMeasurable
    · filter_upwards with u
      rw [norm_mul]
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      have h := norm_partial_sum_wminus_le x' b hx'1 hx'8 N u
      linarith
  have hSecond_int : Integrable (fun u : ℝ => (∑ j ∈ Finset.range m, ((wminus x' b u) + (j:ℂ))⁻¹) * gK a lam u) volume := by
    refine ((integrable_gK_norm a lam ha).const_mul (4*(m:ℝ))).mono' ?_ ?_
    · have hc : Continuous (fun u : ℝ => ∑ j ∈ Finset.range m, ((wminus x' b u) + (j:ℂ))⁻¹) := by
        apply continuous_finsetSum
        intro j _
        apply Continuous.inv₀ ((wminus_cont x' b).add continuous_const)
        intro u hh
        have h2 : (wminus x' b u + (j:ℂ)).re = 0 := by
          have hh' := congrArg Complex.re hh
          simpa only [Pi.add_apply, Complex.zero_re] using hh'
        rw [re_wminus_add_nat] at h2
        have hj0 : (0:ℝ) ≤ (j:ℝ) := Nat.cast_nonneg j
        linarith [hx'1]
      exact (hc.mul (continuous_gK a lam ha)).aestronglyMeasurable
    · filter_upwards with u
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (norm_sum_inv_wminus_le x' b hx'1 m u) (norm_nonneg _)
  have hSecondVal : (∫ u : ℝ, (∑ j ∈ Finset.range m, ((wminus x' b u) + (j:ℂ))⁻¹) * gK a lam u) = 0 := by
    have hcong : (∫ u : ℝ, (∑ j ∈ Finset.range m, ((wminus x' b u) + (j:ℂ))⁻¹) * gK a lam u)
        = ∫ u : ℝ, ∑ j ∈ Finset.range m, (((wminus x' b u) + (j:ℂ))⁻¹ * gK a lam u) := by
      apply integral_congr_ae; filter_upwards with u; rw [Finset.sum_mul]
    rw [hcong]
    rw [MeasureTheory.integral_finsetSum]
    · apply Finset.sum_eq_zero
      intro j hj
      have hx'j : (0:ℝ) < x' + (j:ℝ) := by
        have hj0 : (0:ℝ) ≤ (j:ℝ) := Nat.cast_nonneg j
        linarith [hx'1]
      rw [← integral_gK_div_wminus_add a lam x' b ha hlam j hx'j]
      apply integral_congr_ae; filter_upwards with u
      rw [div_eq_mul_inv, mul_comm]
    · intro j hj
      exact integrable_inv_wminus_gK a lam x' b ha j hx'1
  have hSplit : ∀ N : ℕ, (∫ u : ℝ, ((-(Real.eulerMascheroniConstant:ℂ) +
        ∑ n ∈ Finset.range N, Commons.Analysis.SpecialFunctions.Gamma.dgTermC (wminus x' b u) n)
        + ∑ j ∈ Finset.range m, ((wminus x' b u) + (j:ℂ))⁻¹) * gK a lam u)
      = (∫ u : ℝ, (-(Real.eulerMascheroniConstant:ℂ) +
        ∑ n ∈ Finset.range N, Commons.Analysis.SpecialFunctions.Gamma.dgTermC (wminus x' b u) n) * gK a lam u)
        + (∫ u : ℝ, (∑ j ∈ Finset.range m, ((wminus x' b u) + (j:ℂ))⁻¹) * gK a lam u) := by
    intro N
    rw [show (∫ u : ℝ, ((-(Real.eulerMascheroniConstant:ℂ) +
          ∑ n ∈ Finset.range N, Commons.Analysis.SpecialFunctions.Gamma.dgTermC (wminus x' b u) n)
          + ∑ j ∈ Finset.range m, ((wminus x' b u) + (j:ℂ))⁻¹) * gK a lam u)
        = ∫ u : ℝ, ((-(Real.eulerMascheroniConstant:ℂ) +
          ∑ n ∈ Finset.range N, Commons.Analysis.SpecialFunctions.Gamma.dgTermC (wminus x' b u) n) * gK a lam u
          + (∑ j ∈ Finset.range m, ((wminus x' b u) + (j:ℂ))⁻¹) * gK a lam u) from by
        apply integral_congr_ae; filter_upwards with u; ring]
    exact MeasureTheory.integral_add (hFirst_int N) hSecond_int
  have hzero : Tendsto (fun N : ℕ => (∫ u : ℝ, ((-(Real.eulerMascheroniConstant:ℂ) +
        ∑ n ∈ Finset.range N, Commons.Analysis.SpecialFunctions.Gamma.dgTermC (wminus x' b u) n)
        + ∑ j ∈ Finset.range m, ((wminus x' b u) + (j:ℂ))⁻¹) * gK a lam u)) atTop (nhds 0) := by
    have hfun : (fun N : ℕ => (∫ u : ℝ, ((-(Real.eulerMascheroniConstant:ℂ) +
          ∑ n ∈ Finset.range N, Commons.Analysis.SpecialFunctions.Gamma.dgTermC (wminus x' b u) n)
          + ∑ j ∈ Finset.range m, ((wminus x' b u) + (j:ℂ))⁻¹) * gK a lam u)) = fun _ => (0:ℂ) := by
      funext N
      rw [hSplit N, psi_hFN_minus a lam x' b ha hlam hx'1 hx'8 N, hSecondVal, add_zero]
    rw [hfun]
    exact tendsto_const_nhds
  exact tendsto_nhds_unique hDCT hzero

end PsiKernelMinus

namespace Commons.Analysis.SpecialFunctions.Gamma

open MeasureTheory Set Complex Filter
open scoped Topology Interval BigOperators
open PsiKernelMinus PsiKernelBound

theorem psi_kernel_bound_minus (a lam x b : ℝ) (ha : 0 < a) (hlam : 0 < lam) (hx : (1:ℝ)/4 ≤ x) :
    ‖∫ u : ℝ, Complex.digamma ((x : ℂ) - (((b - u)/2 : ℝ) : ℂ) * Complex.I) *
      ((Complex.exp (-(((a : ℂ) + (u : ℂ) * Complex.I) * (lam : ℂ))) - 1) /
        (((a : ℂ) + (u : ℂ) * Complex.I)^2))‖ ≤ 200 := by
  have hz : (∫ u : ℝ, Complex.digamma ((x : ℂ) - (((b - u)/2 : ℝ) : ℂ) * Complex.I) *
      ((Complex.exp (-(((a : ℂ) + (u : ℂ) * Complex.I) * (lam : ℂ))) - 1) /
        (((a : ℂ) + (u : ℂ) * Complex.I)^2)))
      = ∫ u : ℝ, Complex.digamma (wminus x b u) * gK a lam u := by
    apply integral_congr_ae
    filter_upwards with u
    simp only [wminus, gK, div_eq_mul_inv]
  rw [hz, digamma_minus_integral_zero a lam x b ha hlam hx]
  norm_num

end Commons.Analysis.SpecialFunctions.Gamma

