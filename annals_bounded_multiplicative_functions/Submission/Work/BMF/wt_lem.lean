import Mathlib
import Submission.Work.BMF.wt_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF
open Polynomial Finset Real Complex MeasureTheory Filter
open scoped FourierTransform RealInnerProductSpace

section Phi
lemma phi_nonneg (x : ℝ) : 0 ≤ phi x := cbump.nonneg_normed x
lemma phi_contDiff : ContDiff ℝ 2 phi := cbump.contDiff_normed
lemma phi_continuous : Continuous phi := cbump.continuous_normed
lemma phi_integral : ∫ x, phi x = 1 := cbump.integral_normed
lemma phi_hasCompactSupport : HasCompactSupport phi := cbump.hasCompactSupport_normed
lemma phi_even (x : ℝ) : phi (-x) = phi x := by
  change cbump.normed volume (-x) = cbump.normed volume x
  exact cbump.normed_neg x
lemma phi_support {x : ℝ} (h : 1 / 2 ≤ |x|) : phi x = 0 := by
  change cbump.normed volume x = 0
  rw [← Function.notMem_support, cbump.support_normed_eq, Metric.mem_ball, dist_zero_right, not_lt]
  exact h
end Phi

section PhiB
lemma phiB_nonneg (B : ℝ) (hB : 0 < B) (x : ℝ) : 0 ≤ phiB B x := by
  unfold phiB; exact mul_nonneg (by positivity) (phi_nonneg _)
lemma phiB_contDiff (B : ℝ) : ContDiff ℝ 2 (phiB B) := by
  unfold phiB
  exact contDiff_const.mul (phi_contDiff.comp (contDiff_id.div_const B))
lemma phiB_continuous (B : ℝ) : Continuous (phiB B) := (phiB_contDiff B).continuous
lemma phiB_integral (B : ℝ) (hB : 0 < B) : ∫ x, phiB B x = 1 := by
  unfold phiB
  rw [MeasureTheory.integral_const_mul, Measure.integral_comp_div, abs_of_pos hB, phi_integral,
    smul_eq_mul, mul_one]
  field_simp
lemma phiB_support (B : ℝ) (hB : 0 < B) {x : ℝ} (h : B / 2 ≤ |x|) : phiB B x = 0 := by
  have hx : 1 / 2 ≤ |x / B| := by
    rw [abs_div, abs_of_pos hB, le_div_iff₀ hB]; linarith
  unfold phiB; rw [phi_support hx, mul_zero]
lemma phiB_integrable (B : ℝ) (hB : 0 < B) : Integrable (phiB B) := by
  unfold phiB
  exact (cbump.integrable_normed.comp_div hB.ne').const_mul (1 / B)
end PhiB

section gH_Wf
lemma gH_hasDerivAt (B x : ℝ) : HasDerivAt (gH B) (phiB B x) x := by
  unfold gH
  exact intervalIntegral.integral_hasDerivAt_right ((phiB_continuous B).intervalIntegrable 0 x)
    ((phiB_continuous B).stronglyMeasurableAtFilter volume (nhds x))
    ((phiB_continuous B).continuousAt)

lemma differentiable_gH (B : ℝ) : Differentiable ℝ (gH B) :=
  fun x => (gH_hasDerivAt B x).differentiableAt

lemma Wf_eq_integral (B a c t : ℝ) : Wf B a c t = ∫ s in (t - c)..(t - a), phiB B s := by
  unfold Wf gH
  exact intervalIntegral.integral_interval_sub_left
    ((phiB_continuous B).intervalIntegrable 0 (t - a))
    ((phiB_continuous B).intervalIntegrable 0 (t - c))

lemma Wf_hasDerivAt (B a c t : ℝ) :
    HasDerivAt (Wf B a c) (phiB B (t - a) - phiB B (t - c)) t := by
  unfold Wf
  have h1 : HasDerivAt (fun t => gH B (t - a)) (phiB B (t - a)) t := by
    have h := (gH_hasDerivAt B (t - a)).comp t ((hasDerivAt_id t).sub_const a)
    simpa [Function.comp_def, id_eq, mul_one] using h
  have h2 : HasDerivAt (fun t => gH B (t - c)) (phiB B (t - c)) t := by
    have h := (gH_hasDerivAt B (t - c)).comp t ((hasDerivAt_id t).sub_const c)
    simpa [Function.comp_def, id_eq, mul_one] using h
  exact h1.sub h2

lemma deriv_Wf (B a c : ℝ) : deriv (Wf B a c) = fun t => phiB B (t - a) - phiB B (t - c) :=
  funext fun t => (Wf_hasDerivAt B a c t).deriv

lemma Wf_nonneg (B a c t : ℝ) (hB : 0 < B) (hac : a ≤ c) : 0 ≤ Wf B a c t := by
  rw [Wf_eq_integral]
  exact intervalIntegral.integral_nonneg_of_forall (by linarith)
    (fun u => phiB_nonneg B hB u)

lemma Wf_le_one (B a c t : ℝ) (hB : 0 < B) (hac : a ≤ c) : Wf B a c t ≤ 1 := by
  rw [Wf_eq_integral, intervalIntegral.integral_of_le (by linarith), ← phiB_integral B hB]
  exact MeasureTheory.setIntegral_le_integral (phiB_integrable B hB)
    (Eventually.of_forall (fun x => phiB_nonneg B hB x))

lemma Wf_abs_le_one (B a c t : ℝ) (hB : 0 < B) (hac : a ≤ c) : |Wf B a c t| ≤ 1 :=
  abs_le.2 ⟨by linarith [Wf_nonneg B a c t hB hac], Wf_le_one B a c t hB hac⟩

lemma Wf_zero_left (B a c t : ℝ) (hB : 0 < B) (hac : a ≤ c) (h : t ≤ a - B / 2) :
    Wf B a c t = 0 := by
  rw [Wf_eq_integral, ← intervalIntegral.integral_zero]
  refine intervalIntegral.integral_congr_ae (Eventually.of_forall fun u hu => ?_)
  rw [Set.uIoc_of_le (by linarith)] at hu
  exact phiB_support B hB (by rw [abs_of_nonpos (by linarith [hu.2])]; linarith [hu.2])

lemma Wf_zero_right (B a c t : ℝ) (hB : 0 < B) (hac : a ≤ c) (h : c + B / 2 ≤ t) :
    Wf B a c t = 0 := by
  rw [Wf_eq_integral, ← intervalIntegral.integral_zero]
  refine intervalIntegral.integral_congr_ae (Eventually.of_forall fun u hu => ?_)
  rw [Set.uIoc_of_le (by linarith)] at hu
  exact phiB_support B hB (by rw [abs_of_nonneg (by linarith [hu.1])]; linarith [hu.1])

lemma Wf_one (B a c t : ℝ) (hB : 0 < B) (hac : a ≤ c) (h1 : a + B / 2 ≤ t)
    (h2 : t ≤ c - B / 2) : Wf B a c t = 1 := by
  rw [Wf_eq_integral,
    intervalIntegral.integral_eq_integral_of_support_subset
      (f := phiB B) (a := t - c) (b := t - a) (h := ?_), phiB_integral B hB]
  intro x hx
  simp only [Function.mem_support] at hx
  have hx' : |x| < B / 2 := by
    by_contra hc
    exact hx (phiB_support B hB (le_of_not_gt hc))
  rw [abs_lt] at hx'
  exact ⟨by linarith [hx'.1], by linarith [hx'.2]⟩

end gH_Wf

section Deriv
lemma differentiable_phi : Differentiable ℝ phi :=
  phi_contDiff.differentiable (by norm_num)
lemma differentiable_phiB (B : ℝ) : Differentiable ℝ (phiB B) :=
  (phiB_contDiff B).differentiable (by norm_num)

lemma deriv_phiB (B : ℝ) (hB : 0 < B) (x : ℝ) :
    deriv (phiB B) x = (1 / B ^ 2) * deriv phi (x / B) := by
  have h1 : HasDerivAt (fun y : ℝ => phi (y / B)) (deriv phi (x / B) * (1 / B)) x :=
    (differentiable_phi (x / B)).hasDerivAt.comp x ((hasDerivAt_id x).div_const B)
  have h2 : HasDerivAt (fun y : ℝ => (1 / B) * phi (y / B))
      ((1 / B) * (deriv phi (x / B) * (1 / B))) x := h1.const_mul (1 / B)
  unfold phiB
  rw [h2.deriv]
  ring

lemma deriv_phiB_fun (B : ℝ) (hB : 0 < B) :
    deriv (phiB B) = fun x => (1 / B ^ 2) * deriv phi (x / B) :=
  funext fun x => deriv_phiB B hB x

lemma deriv_comp_sub_const (f : ℝ → ℝ) (hf : Differentiable ℝ f) (a : ℝ) :
    deriv (fun t => f (t - a)) = fun t => deriv f (t - a) := by
  funext t
  have h := (hf (t - a)).hasDerivAt.comp t ((hasDerivAt_id t).sub_const a)
  simpa [Function.comp_def, id_eq, mul_one] using h.deriv

lemma Wf_second_deriv (B a c : ℝ) (hB : 0 < B) :
    iteratedDeriv 2 (Wf B a c) = fun t => deriv (phiB B) (t - a) - deriv (phiB B) (t - c) := by
  have h2 : deriv (deriv (Wf B a c))
      = fun t => deriv (phiB B) (t - a) - deriv (phiB B) (t - c) := by
    rw [deriv_Wf]
    funext t
    have ha : HasDerivAt (fun s => phiB B (s - a)) (deriv (phiB B) (t - a)) t := by
      have h := (differentiable_phiB B (t - a)).hasDerivAt.comp t ((hasDerivAt_id t).sub_const a)
      simpa [Function.comp_def, id_eq, mul_one] using h
    have hb : HasDerivAt (fun s => phiB B (s - c)) (deriv (phiB B) (t - c)) t := by
      have h := (differentiable_phiB B (t - c)).hasDerivAt.comp t ((hasDerivAt_id t).sub_const c)
      simpa [Function.comp_def, id_eq, mul_one] using h
    exact (ha.sub hb).deriv
  rw [show iteratedDeriv 2 (Wf B a c) = deriv (deriv (Wf B a c)) from ?_, h2]
  rw [show (2:ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]

lemma integrable_deriv_phi : Integrable (deriv phi) :=
  ((phi_contDiff.continuous_deriv (by norm_num)).integrable_of_hasCompactSupport
    phi_hasCompactSupport.deriv)

lemma integrable_deriv_phiB (B : ℝ) (hB : 0 < B) : Integrable (deriv (phiB B)) := by
  rw [deriv_phiB_fun B hB]
  exact ((integrable_deriv_phi.comp_div hB.ne').const_mul (1 / B ^ 2))

end Deriv

section Complex
lemma differentiable_ofReal_comp (f : ℝ → ℝ) (hf : Differentiable ℝ f) :
    Differentiable ℝ (fun t => (f t : ℂ)) :=
  fun t => (hf t).hasDerivAt.ofReal_comp.differentiableAt

lemma deriv_ofReal_fun (f : ℝ → ℝ) (hf : Differentiable ℝ f) :
    deriv (fun s => (f s : ℂ)) = fun s => ((deriv f s : ℝ) : ℂ) :=
  funext fun s => (hf s).hasDerivAt.ofReal_comp.deriv

lemma iteratedDeriv_two_ofReal (f : ℝ → ℝ) (hf : Differentiable ℝ f)
    (hf' : Differentiable ℝ (deriv f)) :
    iteratedDeriv 2 (fun s => (f s : ℂ)) = fun s => ((iteratedDeriv 2 f s : ℝ) : ℂ) := by
  have htwo : ∀ g : ℝ → ℂ, iteratedDeriv 2 g = deriv (deriv g) := fun g => by
    rw [show (2:ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
  have htwo' : iteratedDeriv 2 f = deriv (deriv f) := by
    rw [show (2:ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
  rw [htwo, htwo', deriv_ofReal_fun f hf, deriv_ofReal_fun (deriv f) hf']

lemma differentiable_Wf (B a c : ℝ) : Differentiable ℝ (Wf B a c) :=
  fun t => (Wf_hasDerivAt B a c t).differentiableAt

lemma differentiable_deriv_Wf (B a c : ℝ) : Differentiable ℝ (deriv (Wf B a c)) := by
  rw [deriv_Wf]
  exact ((differentiable_phiB B).comp (by fun_prop)).sub
    ((differentiable_phiB B).comp (by fun_prop))

lemma iteratedDeriv_two_Wt (B a c : ℝ) :
    iteratedDeriv 2 (Wt B a c) = fun t => ((iteratedDeriv 2 (Wf B a c) t : ℝ) : ℂ) := by
  unfold Wt
  exact iteratedDeriv_two_ofReal (Wf B a c) (differentiable_Wf B a c)
    (differentiable_deriv_Wf B a c)

lemma deriv_Wt (B a c : ℝ) :
    deriv (Wt B a c) = fun t => ((deriv (Wf B a c) t : ℝ) : ℂ) := by
  unfold Wt
  exact deriv_ofReal_fun (Wf B a c) (differentiable_Wf B a c)

lemma deriv_deriv_Wt (B a c : ℝ) :
    deriv (deriv (Wt B a c)) = fun t => ((deriv (deriv (Wf B a c)) t : ℝ) : ℂ) := by
  rw [deriv_Wt]
  exact deriv_ofReal_fun (deriv (Wf B a c)) (differentiable_deriv_Wf B a c)

lemma deriv_deriv_Wf (B a c : ℝ) (hB : 0 < B) :
    deriv (deriv (Wf B a c)) = fun t => deriv (phiB B) (t - a) - deriv (phiB B) (t - c) := by
  rw [deriv_Wf]
  funext t
  have ha : HasDerivAt (fun s => phiB B (s - a)) (deriv (phiB B) (t - a)) t := by
    have h := (differentiable_phiB B (t - a)).hasDerivAt.comp t ((hasDerivAt_id t).sub_const a)
    simpa [Function.comp_def, id_eq, mul_one] using h
  have hb : HasDerivAt (fun s => phiB B (s - c)) (deriv (phiB B) (t - c)) t := by
    have h := (differentiable_phiB B (t - c)).hasDerivAt.comp t ((hasDerivAt_id t).sub_const c)
    simpa [Function.comp_def, id_eq, mul_one] using h
  exact (ha.sub hb).deriv

lemma integrable_deriv_Wf (B a c : ℝ) (hB : 0 < B) : Integrable (deriv (Wf B a c)) := by
  rw [deriv_Wf]
  exact ((phiB_integrable B hB).comp_sub_right a).sub
    ((phiB_integrable B hB).comp_sub_right c)

lemma integrable_deriv_Wt (B a c : ℝ) (hB : 0 < B) : Integrable (deriv (Wt B a c)) := by
  rw [deriv_Wt]
  exact (integrable_deriv_Wf B a c hB).ofReal

lemma integrable_deriv_deriv_Wf (B a c : ℝ) (hB : 0 < B) :
    Integrable (deriv (deriv (Wf B a c))) := by
  rw [deriv_deriv_Wf B a c hB]
  exact ((integrable_deriv_phiB B hB).comp_sub_right a).sub
    ((integrable_deriv_phiB B hB).comp_sub_right c)

lemma integrable_deriv_deriv_Wt (B a c : ℝ) (hB : 0 < B) :
    Integrable (deriv (deriv (Wt B a c))) := by
  rw [deriv_deriv_Wt]
  exact (integrable_deriv_deriv_Wf B a c hB).ofReal

lemma differentiable_deriv_Wt (B a c : ℝ) : Differentiable ℝ (deriv (Wt B a c)) := by
  rw [deriv_Wt]
  exact differentiable_ofReal_comp (deriv (Wf B a c)) (differentiable_deriv_Wf B a c)
end Complex

section Integrals
lemma continuous_gH (B : ℝ) : Continuous (gH B) := (differentiable_gH B).continuous

lemma Wf_continuous (B a c : ℝ) : Continuous (Wf B a c) := by
  unfold Wf
  exact ((continuous_gH B).comp (continuous_id.sub continuous_const)).sub
    ((continuous_gH B).comp (continuous_id.sub continuous_const))

lemma Wf_hasCompactSupport (B a c : ℝ) (hB : 0 < B) (hac : a ≤ c) :
    HasCompactSupport (Wf B a c) := by
  refine HasCompactSupport.intro (K := Set.Icc (a - B / 2) (c + B / 2)) isCompact_Icc (fun t ht => ?_)
  rw [Set.mem_Icc, not_and_or, not_le, not_le] at ht
  rcases ht with h | h
  · exact Wf_zero_left B a c t hB hac (le_of_lt h)
  · exact Wf_zero_right B a c t hB hac (le_of_lt h)

lemma integrable_Wf (B a c : ℝ) (hB : 0 < B) (hac : a ≤ c) : Integrable (Wf B a c) :=
  (Wf_continuous B a c).integrable_of_hasCompactSupport (Wf_hasCompactSupport B a c hB hac)

lemma integrable_Wt (B a c : ℝ) (hB : 0 < B) (hac : a ≤ c) : Integrable (Wt B a c) := by
  unfold Wt
  exact (integrable_Wf B a c hB hac).ofReal

lemma differentiable_Wt (B a c : ℝ) : Differentiable ℝ (Wt B a c) :=
  fun t => ((Wf_hasDerivAt B a c t).ofReal_comp).differentiableAt

lemma integral_abs_deriv_phiB (B : ℝ) (hB : 0 < B) : ∫ x, |deriv (phiB B) x| = Kphi / B := by
  have hkey : ∫ x, |deriv phi (x / B)| = B * ∫ y, |deriv phi y| := by
    rw [Measure.integral_comp_div (fun y : ℝ => |deriv phi y|) B, abs_of_pos hB, smul_eq_mul]
  rw [deriv_phiB_fun B hB]
  simp only [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 1 / B ^ 2)]
  rw [MeasureTheory.integral_const_mul, hkey]
  unfold Kphi
  field_simp

lemma abs_sub_le_abs_add (x y : ℝ) : |x - y| ≤ |x| + |y| :=
  abs_sub_le_iff.2 ⟨by linarith [le_abs_self x, neg_le_abs y],
    by linarith [le_abs_self y, neg_le_abs x]⟩

lemma integral_abs_deriv_phiB_translate (B a : ℝ) (hB : 0 < B) :
    ∫ t, |deriv (phiB B) (t - a)| = Kphi / B := by
  have hshift := MeasureTheory.integral_add_right_eq_self (μ := volume)
    (fun x : ℝ => |deriv (phiB B) x|) (-a)
  rw [← integral_abs_deriv_phiB B hB, ← hshift]
  simp only [sub_eq_add_neg]

lemma integral_iteratedDerivTwo_Wt_le (B a c : ℝ) (hB : 0 < B) :
    ∫ t, ‖iteratedDeriv 2 (Wt B a c) t‖ ≤ 2 * Kphi / B := by
  have hsecond : iteratedDeriv 2 (Wt B a c)
      = fun t => ((deriv (deriv (Wf B a c)) t : ℝ) : ℂ) := by
    rw [iteratedDeriv_two_Wt B a c]
    congr 1
    rw [show (2:ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
  rw [hsecond]
  simp only [Complex.norm_real]
  rw [show deriv (deriv (Wf B a c))
        = fun t => deriv (phiB B) (t - a) - deriv (phiB B) (t - c) from
        deriv_deriv_Wf B a c hB]
  have hg1 : Integrable (fun t : ℝ => deriv (phiB B) (t - a)) :=
    (integrable_deriv_phiB B hB).comp_sub_right a
  have hg2 : Integrable (fun t : ℝ => deriv (phiB B) (t - c)) :=
    (integrable_deriv_phiB B hB).comp_sub_right c
  have hIntabs : Integrable
      (fun t : ℝ => |deriv (phiB B) (t - a) - deriv (phiB B) (t - c)|) := (hg1.sub hg2).abs
  calc ∫ t, |deriv (phiB B) (t - a) - deriv (phiB B) (t - c)|
      ≤ ∫ t, (|deriv (phiB B) (t - a)| + |deriv (phiB B) (t - c)|) :=
        integral_mono_ae hIntabs (hg1.abs.add hg2.abs)
          (Eventually.of_forall fun t => abs_sub_le_abs_add _ _)
      _ = (∫ t, |deriv (phiB B) (t - a)|) + (∫ t, |deriv (phiB B) (t - c)|) :=
        MeasureTheory.integral_add (μ := volume) hg1.abs hg2.abs
      _ = Kphi / B + Kphi / B := by
        rw [integral_abs_deriv_phiB_translate B a hB, integral_abs_deriv_phiB_translate B c hB]
      _ = 2 * Kphi / B := by ring
end Integrals

section FT
lemma norm_Wt (B a c t : ℝ) : ‖Wt B a c t‖ = |Wf B a c t| := by
  unfold Wt; rw [Complex.norm_real, Real.norm_eq_abs]

lemma integral_Wt_le (B a c : ℝ) (hB : 0 < B) (hac : a ≤ c) :
    ∫ t, ‖Wt B a c t‖ ≤ (c - a) + B + 1 := by
  have hsupp : ∀ t : ℝ, t ∉ Set.Icc (a - B / 2) (c + B / 2) → ‖Wt B a c t‖ = 0 := by
    intro t ht
    rw [Set.mem_Icc, not_and_or, not_le, not_le] at ht
    rcases ht with h | h
    · unfold Wt; rw [Wf_zero_left B a c t hB hac (le_of_lt h)]; simp
    · unfold Wt; rw [Wf_zero_right B a c t hB hac (le_of_lt h)]; simp
  rw [← MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hsupp]
  have h1 : ∫ t in Set.Icc (a - B / 2) (c + B / 2), ‖Wt B a c t‖
      ≤ ∫ t in Set.Icc (a - B / 2) (c + B / 2), (1 : ℝ) := by
    refine MeasureTheory.setIntegral_mono_on ?_ ?_ measurableSet_Icc (fun t _ => ?_)
    · exact (integrable_Wt B a c hB hac).norm.integrableOn
    · exact MeasureTheory.integrableOn_const (by simp) (by simp)
    · rw [norm_Wt]; exact Wf_abs_le_one B a c t hB hac
  calc ∫ t in Set.Icc (a - B / 2) (c + B / 2), ‖Wt B a c t‖
      ≤ ∫ t in Set.Icc (a - B / 2) (c + B / 2), (1 : ℝ) := h1
    _ = volume.real (Set.Icc (a - B / 2) (c + B / 2)) := by
        rw [MeasureTheory.setIntegral_const, smul_eq_mul, mul_one]
    _ = (c - a) + B := by
        rw [MeasureTheory.Measure.real_def, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]
        ring
    _ ≤ (c - a) + B + 1 := by linarith

lemma norm_FT_le (f : ℝ → ℂ) (ξ : ℝ) : ‖FT f ξ‖ ≤ ∫ t, ‖f t‖ := by
  rw [FT, Real.fourier_eq]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp only [Circle.smul_def, smul_eq_mul, norm_mul, Circle.norm_coe, one_mul]

lemma FT_second_Wt (B a c : ℝ) (hB : 0 < B) (hac : a ≤ c) :
    FT (deriv (deriv (Wt B a c)))
      = fun ξ : ℝ => (2 * (π : ℂ) * I * (ξ : ℂ)) ^ 2 • FT (Wt B a c) ξ := by
  have h1 : FT (deriv (Wt B a c))
      = fun ξ : ℝ => (2 * (π : ℂ) * I * (ξ : ℂ)) • FT (Wt B a c) ξ :=
    fourier_deriv (integrable_Wt B a c hB hac) (differentiable_Wt B a c)
      (integrable_deriv_Wt B a c hB)
  have h2 : FT (deriv (deriv (Wt B a c)))
      = fun ξ : ℝ => (2 * (π : ℂ) * I * (ξ : ℂ)) • FT (deriv (Wt B a c)) ξ :=
    fourier_deriv (integrable_deriv_Wt B a c hB) (differentiable_deriv_Wt B a c)
      (integrable_deriv_deriv_Wt B a c hB)
  rw [h2, h1]
  funext ξ
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [pow_two]
  ring

lemma norm_two_pi_I_mul (ξ : ℝ) : ‖(2 * (π : ℂ) * I * (ξ : ℂ)) ^ 2‖ = 4 * π ^ 2 * ξ ^ 2 := by
  rw [norm_pow]
  have h : ‖(2 * (π : ℂ) * I * (ξ : ℂ))‖ = 2 * π * |ξ| := by
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_ofNat, mul_one]
    rw [Complex.norm_real, Real.norm_eq_abs, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg Real.pi_pos.le]
  rw [h, mul_pow, mul_pow, sq_abs, show (2:ℝ)^2 = 4 from by norm_num]

lemma FT_decay (B a c : ℝ) (hB : 0 < B) (hac : a ≤ c) {ξ : ℝ} (hξ : ξ ≠ 0) :
    ‖FT (Wt B a c) ξ‖ ≤ (2 * Kphi / B) / (4 * π ^ 2 * ξ ^ 2) := by
  have h2 := FT_second_Wt B a c hB hac
  have hid : (∫ t, ‖deriv (deriv (Wt B a c)) t‖)
      = ∫ t, ‖iteratedDeriv 2 (Wt B a c) t‖ := by
    congr 1
    ext t
    congr 1
    rw [show (2:ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
  have hnorm : ‖FT (deriv (deriv (Wt B a c))) ξ‖ ≤ 2 * Kphi / B := by
    refine le_trans (norm_FT_le _ ξ) ?_
    rw [hid]
    exact integral_iteratedDerivTwo_Wt_le B a c hB
  have key : ‖(2 * (π : ℂ) * I * (ξ : ℂ)) ^ 2‖ * ‖FT (Wt B a c) ξ‖ ≤ 2 * Kphi / B := by
    have h3 : (2 * (π : ℂ) * I * (ξ : ℂ)) ^ 2 * FT (Wt B a c) ξ
        = FT (deriv (deriv (Wt B a c))) ξ := by
      rw [h2]; simp [Pi.smul_apply, smul_eq_mul]
    calc ‖(2 * (π : ℂ) * I * (ξ : ℂ)) ^ 2‖ * ‖FT (Wt B a c) ξ‖
        = ‖(2 * (π : ℂ) * I * (ξ : ℂ)) ^ 2 * FT (Wt B a c) ξ‖ := (norm_mul _ _).symm
      _ = ‖FT (deriv (deriv (Wt B a c))) ξ‖ := by rw [h3]
      _ ≤ 2 * Kphi / B := hnorm
  rw [norm_two_pi_I_mul] at key
  rw [le_div_iff₀ (by positivity)]
  calc ‖FT (Wt B a c) ξ‖ * (4 * π ^ 2 * ξ ^ 2)
      = (4 * π ^ 2 * ξ ^ 2) * ‖FT (Wt B a c) ξ‖ := by ring
    _ ≤ 2 * Kphi / B := key
end FT
end Work.BMF

namespace Work.BMF
open Polynomial Finset Real Complex MeasureTheory Filter
open scoped FourierTransform RealInnerProductSpace

section MinInt
lemma one_div_sq_eq_rpow (t : ℝ) (ht : 0 < t) : (1:ℝ)/t^2 = t^(-2:ℝ) := by
  rw [one_div, ← Real.rpow_natCast t 2, ← Real.rpow_neg ht.le]
  rw [show (-(↑(2:ℕ)) : ℝ) = -2 from by norm_num]

lemma integral_Ioi_inv_sq (c : ℝ) (hc : 0 < c) :
    ∫ t in Set.Ioi c, (1 : ℝ) / t ^ 2 = 1 / c := by
  have h1 : ∫ t in Set.Ioi c, (1:ℝ)/t^2 = ∫ t in Set.Ioi c, t^(-2:ℝ) := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    exact one_div_sq_eq_rpow t (lt_trans hc ht)
  rw [h1, integral_Ioi_rpow_of_lt (by norm_num : (-2:ℝ) < -1) hc]
  rw [show (-2:ℝ) + 1 = -1 from by norm_num, Real.rpow_neg_one]
  ring

lemma integral_Iio_neg_inv_sq (c D : ℝ) (hc : 0 < c) :
    ∫ t in Set.Iio (-c), D / t ^ 2 = D / c := by
  have hneg := MeasureTheory.integral_neg_eq_self
    (fun t : ℝ => (Set.Iio (-c)).indicator (fun t => D / t^2) t) volume
  rw [← MeasureTheory.integral_indicator (s := Set.Iio (-c)) measurableSet_Iio, ← hneg]
  rw [show (fun t : ℝ => (Set.Iio (-c)).indicator (fun t : ℝ => D / t^2) (-t))
        = (Set.Ioi c).indicator (fun t => D / t^2) from by
    funext t
    simp only [Set.indicator_apply, Set.mem_Iio, Set.mem_Ioi]
    by_cases h : c < t
    · rw [if_pos (by linarith), if_pos h]; ring
    · rw [if_neg (by linarith), if_neg h]]
  rw [MeasureTheory.integral_indicator measurableSet_Ioi]
  rw [show (∫ t in Set.Ioi c, D/t^2) = D * ∫ t in Set.Ioi c, (1:ℝ)/t^2 from by
        rw [← MeasureTheory.integral_const_mul]; congr 1; ext t; ring]
  rw [integral_Ioi_inv_sq c hc]
  field_simp
end MinInt
end Work.BMF
namespace Work.BMF
open Polynomial Finset Real Complex MeasureTheory Filter
open scoped FourierTransform RealInnerProductSpace

section FT2
lemma integrable_min {A D : ℝ} (hA : 0 ≤ A) (hD : 0 ≤ D) :
    Integrable (fun ξ : ℝ => min A (D / ξ ^ 2)) := by
  have hInd : Integrable ((Set.Icc (-1) 1).indicator (fun _ : ℝ => A)) := by
    rw [integrable_indicator_iff measurableSet_Icc]
    exact MeasureTheory.integrableOn_const (by simp) (by simp)
  have hIntg : Integrable (fun ξ : ℝ => A * (Set.Icc (-1) 1).indicator (fun _ => (1:ℝ)) ξ
      + 2 * D / (1 + ξ ^ 2)) := by
    refine Integrable.add ?_ ?_
    · exact hInd.congr (Filter.Eventually.of_forall (fun ξ => by
        simp only [Set.indicator_apply, Pi.mul_apply]; split_ifs <;> ring))
    · exact (integrable_inv_one_add_sq.const_mul (2 * D)).congr
        (Filter.Eventually.of_forall (fun ξ => by
          simp only [Pi.smul_apply, smul_eq_mul]; rw [div_eq_mul_inv, inv_eq_one_div, mul_comm]))
  refine hIntg.mono' (Measurable.aestronglyMeasurable
    (measurable_const.min (measurable_const.div (measurable_id.pow_const 2))))
    (Filter.Eventually.of_forall fun ξ => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (le_min hA (by positivity))]
  by_cases hξ : |ξ| ≤ 1
  · have hmem : ξ ∈ Set.Icc (-1) 1 := by rw [Set.mem_Icc]; exact abs_le.1 hξ
    rw [Set.indicator_of_mem hmem, mul_one]
    exact le_add_of_le_of_nonneg (min_le_left _ _) (by positivity)
  · have hξ' : (1:ℝ) < |ξ| := lt_of_not_ge hξ
    have hξ2 : (1:ℝ) < ξ^2 := by nlinarith [abs_nonneg ξ, sq_abs ξ, hξ']
    have h1 : min A (D/ξ^2) ≤ D/ξ^2 := min_le_right _ _
    have h2 : D/ξ^2 ≤ 2 * D/(1 + ξ^2) := by
      rw [div_le_div_iff₀ (by linarith) (by linarith)]
      nlinarith [hξ2, hD]
    have hind : 0 ≤ (Set.Icc (-1) 1).indicator (fun _ : ℝ => (1:ℝ)) ξ := by
      rw [Set.indicator_apply]; split_ifs <;> norm_num
    have h3 : 2 * D/(1 + ξ^2) ≤ A * (Set.Icc (-1) 1).indicator (fun _ => (1:ℝ)) ξ
        + 2 * D/(1 + ξ^2) := by nlinarith [mul_nonneg hA hind]
    linarith

lemma integral_const_indicator (A : ℝ) :
    ∫ ξ : ℝ, A * (Set.Icc (-1) 1).indicator (fun _ => (1:ℝ)) ξ = 2 * A := by
  rw [show (fun ξ : ℝ => A * (Set.Icc (-1) 1).indicator (fun _ => (1:ℝ)) ξ)
      = (Set.Icc (-1) 1).indicator (fun _ => A) from by
        funext ξ; simp only [Set.indicator_apply]; split_ifs <;> ring]
  rw [MeasureTheory.integral_indicator measurableSet_Icc, MeasureTheory.setIntegral_const,
    MeasureTheory.Measure.real_def, Real.volume_Icc, ENNReal.toReal_ofReal (by norm_num),
    smul_eq_mul]
  ring

lemma integral_two_inv_one_add_sq (D : ℝ) :
    ∫ ξ : ℝ, 2 * D / (1 + ξ ^ 2) = 2 * D * π := by
  rw [show (fun ξ : ℝ => 2 * D / (1 + ξ^2)) = fun ξ => (2 * D) * ((1:ℝ)/(1 + ξ^2)) from by
        funext ξ; rw [div_eq_mul_inv, inv_eq_one_div]]
  rw [MeasureTheory.integral_const_mul,
    show (∫ a : ℝ, (1:ℝ)/(1 + a^2)) = ∫ a : ℝ, (1 + a^2)⁻¹ from by
      simp only [one_div]]
  rw [integral_univ_inv_one_add_sq]

lemma integral_min_le {A D : ℝ} (hA : 0 ≤ A) (hD : 0 ≤ D) :
    ∫ ξ : ℝ, min A (D / ξ ^ 2) ≤ 2 * A + 2 * π * D := by
  have hInd : Integrable ((Set.Icc (-1) 1).indicator (fun _ : ℝ => A)) := by
    rw [integrable_indicator_iff measurableSet_Icc]
    exact MeasureTheory.integrableOn_const (by simp) (by simp)
  have hIntg : Integrable (fun ξ : ℝ => A * (Set.Icc (-1) 1).indicator (fun _ => (1:ℝ)) ξ
      + 2 * D / (1 + ξ ^ 2)) := by
    refine Integrable.add ?_ ?_
    · exact hInd.congr (Filter.Eventually.of_forall (fun ξ => by
        simp only [Set.indicator_apply, Pi.mul_apply]; split_ifs <;> ring))
    · exact (integrable_inv_one_add_sq.const_mul (2 * D)).congr
        (Filter.Eventually.of_forall (fun ξ => by
          simp only [Pi.smul_apply, smul_eq_mul]; rw [div_eq_mul_inv, inv_eq_one_div, mul_comm]))
  have hpoint : ∀ ξ : ℝ, min A (D / ξ^2) ≤ A * (Set.Icc (-1) 1).indicator (fun _ => (1:ℝ)) ξ
      + 2 * D / (1 + ξ ^ 2) := by
    intro ξ
    by_cases hξ : |ξ| ≤ 1
    · have hmem : ξ ∈ Set.Icc (-1) 1 := by rw [Set.mem_Icc]; exact abs_le.1 hξ
      rw [Set.indicator_of_mem hmem, mul_one]
      exact le_add_of_le_of_nonneg (min_le_left _ _) (by positivity)
    · have hξ' : (1:ℝ) < |ξ| := lt_of_not_ge hξ
      have hξ2 : (1:ℝ) < ξ^2 := by nlinarith [abs_nonneg ξ, sq_abs ξ, hξ']
      have h1 : min A (D/ξ^2) ≤ D/ξ^2 := min_le_right _ _
      have h2 : D/ξ^2 ≤ 2 * D/(1 + ξ^2) := by
        rw [div_le_div_iff₀ (by linarith) (by linarith)]
        nlinarith [hξ2, hD]
      have hind : 0 ≤ (Set.Icc (-1) 1).indicator (fun _ : ℝ => (1:ℝ)) ξ := by
        rw [Set.indicator_apply]; split_ifs <;> norm_num
      have h3 : 2 * D/(1 + ξ^2) ≤ A * (Set.Icc (-1) 1).indicator (fun _ => (1:ℝ)) ξ
          + 2 * D/(1 + ξ^2) := by nlinarith [mul_nonneg hA hind]
      linarith
  calc ∫ ξ : ℝ, min A (D/ξ^2) ≤ ∫ ξ : ℝ, (A * (Set.Icc (-1) 1).indicator (fun _ => (1:ℝ)) ξ
        + 2 * D/(1 + ξ^2)) :=
        integral_mono_ae (integrable_min hA hD) hIntg (Filter.Eventually.of_forall hpoint)
    _ = (∫ ξ : ℝ, A * (Set.Icc (-1) 1).indicator (fun _ => (1:ℝ)) ξ) + ∫ ξ : ℝ, 2 * D/(1 + ξ^2) := by
        rw [MeasureTheory.integral_add]
        · exact hInd.congr (Filter.Eventually.of_forall (fun ξ => by
            simp only [Set.indicator_apply, Pi.mul_apply]; split_ifs <;> ring))
        · exact (integrable_inv_one_add_sq.const_mul (2 * D)).congr
            (Filter.Eventually.of_forall (fun ξ => by
              simp only [Pi.smul_apply, smul_eq_mul]; rw [div_eq_mul_inv, inv_eq_one_div, mul_comm]))
    _ = 2 * A + 2 * π * D := by
        rw [integral_const_indicator A, integral_two_inv_one_add_sq D]
        ring_nf

lemma integral_norm_FT_le (B a c : ℝ) (hB : 0 < B) (hac : a ≤ c) :
    ∫ ξ, ‖FT (Wt B a c) ξ‖ ≤ 2 * (∫ t, ‖Wt B a c t‖) + 2 * π * ((2*Kphi/B)/(4*π^2)) := by
  set A : ℝ := ∫ t, ‖Wt B a c t‖ with hAdef
  set Dl : ℝ := (2*Kphi/B)/(4*π^2) with hDdef
  have hA : 0 ≤ A := integral_nonneg (fun t => norm_nonneg _)
  have hKphi : 0 ≤ Kphi := integral_nonneg (fun t => abs_nonneg _)
  have hD : 0 ≤ Dl := by rw [hDdef]; positivity
  have hpoint : ∀ᵐ ξ : ℝ ∂(volume : MeasureTheory.Measure ℝ),
      ‖FT (Wt B a c) ξ‖ ≤ min A (Dl / ξ^2) := by
    filter_upwards [MeasureTheory.ae_iff.mpr
      (show volume {ξ : ℝ | ¬ (‖FT (Wt B a c) ξ‖ ≤ min A (Dl / ξ^2))} = 0 from by
        refine measure_mono_null (fun ξ hξ => ?_) (by simp : volume ({0} : Set ℝ) = 0)
        simp only [Set.mem_setOf_eq, not_le] at hξ
        by_contra hne
        have h1 : ‖FT (Wt B a c) ξ‖ ≤ Dl / ξ^2 := by
          rw [hDdef, div_div]
          exact FT_decay B a c hB hac hne
        exact absurd (le_min (norm_FT_le _ ξ) h1) (not_le.mpr hξ))] with ξ hξ
    exact hξ
  calc ∫ ξ : ℝ, ‖FT (Wt B a c) ξ‖ ≤ ∫ ξ : ℝ, min A (Dl/ξ^2) :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun ξ => norm_nonneg _)
          (integrable_min hA hD) hpoint
    _ ≤ 2 * A + 2 * π * Dl := integral_min_le hA hD
    _ = 2 * (∫ t, ‖Wt B a c t‖) + 2 * π * ((2*Kphi/B)/(4*π^2)) := by rw [hAdef, hDdef]

end FT2
end Work.BMF
namespace Work.BMF
open Polynomial Finset Real Complex MeasureTheory Filter
open scoped FourierTransform RealInnerProductSpace

section CFT
lemma continuous_Wt (B a c : ℝ) : Continuous (Wt B a c) :=
  Complex.continuous_ofReal.comp (Wf_continuous B a c)

lemma stronglyMeasurable_FT (f : ℝ → ℂ) (hf : StronglyMeasurable f) : StronglyMeasurable (FT f) := by
  rw [FT, show (𝓕 f) = fun ξ => ∫ v, 𝐞 (-⟪v, ξ⟫) • f v from funext fun ξ => Real.fourier_eq f ξ]
  refine StronglyMeasurable.integral_prod_right (f := fun ξ v => 𝐞 (-⟪v, ξ⟫) • f v) ?_
  have h1 : StronglyMeasurable (fun p : ℝ × ℝ => (𝐞 (-⟪p.2, p.1⟫) : ℂ)) := by
    apply Continuous.stronglyMeasurable
    simp only [continuous_iff_continuousAt]
    fun_prop
  have h2 : StronglyMeasurable (fun p : ℝ × ℝ => f p.2) := hf.comp_measurable measurable_snd
  exact h1.mul h2

lemma integrable_FT_Wt (B a c : ℝ) (hB : 0 < B) (hac : a ≤ c) : Integrable (FT (Wt B a c)) := by
  have hA : 0 ≤ ∫ t, ‖Wt B a c t‖ := integral_nonneg (fun t => norm_nonneg _)
  have hKphi : 0 ≤ Kphi := integral_nonneg (fun t => abs_nonneg _)
  have hD : 0 ≤ (2*Kphi/B)/(4*π^2) := by positivity
  refine (integrable_min hA hD).mono'
    ((stronglyMeasurable_FT _ (continuous_Wt B a c).stronglyMeasurable).aestronglyMeasurable)
    (by
      have hae : ∀ᵐ ξ : ℝ ∂volume, ξ ≠ 0 := by
        rw [MeasureTheory.ae_iff]
        simpa using MeasureTheory.measure_singleton (0 : ℝ)
      filter_upwards [hae] with ξ hξ
      refine le_min (norm_FT_le _ ξ) ?_
      rw [div_div]
      exact FT_decay B a c hB hac hξ)
end CFT

section Identity
lemma fourierChar_coe_eq_eC (x : ℝ) : ((𝐞 x : Circle) : ℂ) = eC x := by
  rw [Real.fourierChar_apply]
  unfold eC
  congr 1
  push_cast
  ring

lemma Wt_inversion (B a c t : ℝ) (hB : 0 < B) (hac : a ≤ c) :
    Wt B a c t = ∫ ξ, FT (Wt B a c) ξ * eC (t * ξ) := by
  have hinv : 𝓕⁻ (𝓕 (Wt B a c)) = Wt B a c :=
    Continuous.fourierInv_fourier_eq (continuous_Wt B a c) (integrable_Wt B a c hB hac)
      (integrable_FT_Wt B a c hB hac)
  rw [← congr_fun hinv t, fourierInv_eq]
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  simp only [Circle.smul_def, smul_eq_mul]
  have hinner : (⟪v, t⟫ : ℝ) = t * v := by simp [mul_comm]
  rw [fourierChar_coe_eq_eC, hinner, mul_comm]
  rfl

lemma Wt_identity (b : ℕ → ℂ) (A0 B0 : ℕ) (B a c : ℝ) (hB : 0 < B) (hac : a ≤ c) :
    ∑ n ∈ Finset.Icc A0 B0, b n * Wt B a c n
      = ∫ ξ, FT (Wt B a c) ξ * (∑ n ∈ Finset.Icc A0 B0, b n * eC (n * ξ)) := by
  have hv : ∀ t : ℝ, Wt B a c t = ∫ ξ, FT (Wt B a c) ξ * eC (t * ξ) :=
    fun t => Wt_inversion B a c t hB hac
  calc ∑ n ∈ Finset.Icc A0 B0, b n * Wt B a c n
      = ∑ n ∈ Finset.Icc A0 B0, b n * (∫ ξ, FT (Wt B a c) ξ * eC (n * ξ)) := by
        refine Finset.sum_congr rfl (fun n _ => ?_); rw [hv n]
    _ = ∑ n ∈ Finset.Icc A0 B0, ∫ ξ, b n * (FT (Wt B a c) ξ * eC (n * ξ)) := by
        refine Finset.sum_congr rfl (fun n _ => ?_)
        rw [← MeasureTheory.integral_const_mul]
    _ = ∫ ξ, ∑ n ∈ Finset.Icc A0 B0, b n * (FT (Wt B a c) ξ * eC (n * ξ)) := by
        rw [MeasureTheory.integral_finset_sum]
        intro n _
        have h1 : Integrable (fun ξ : ℝ => FT (Wt B a c) ξ * eC (n * ξ)) := by
          refine ((integrable_FT_Wt B a c hB hac).norm).mono'
            ((integrable_FT_Wt B a c hB hac).1.mul
              (Continuous.aestronglyMeasurable (by unfold eC; fun_prop)))
            (Filter.Eventually.of_forall fun ξ => ?_)
          rw [norm_mul]
          have h2 : ‖eC ((n:ℝ) * ξ)‖ = 1 := by
            unfold eC; rw [Complex.norm_exp]; simp
          rw [h2, mul_one]
        exact h1.const_mul (b n)
    _ = ∫ ξ, FT (Wt B a c) ξ * (∑ n ∈ Finset.Icc A0 B0, b n * eC (n * ξ)) := by
        congr 1; ext ξ
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun n _ => ?_); ring
lemma phiB_neg (B x : ℝ) : phiB B (-x) = phiB B x := by
  unfold phiB; rw [neg_div, phi_even]

lemma interval_phiB_symm (B : ℝ) (hB : 0 < B) :
    ∫ s in (-(B/2))..(0:ℝ), phiB B s = ∫ s in (0:ℝ)..(B/2), phiB B s := by
  rw [show (∫ s in (-(B/2))..(0:ℝ), phiB B s)
      = ∫ s in (-(B/2))..(0:ℝ), phiB B (-s) from by
        refine intervalIntegral.integral_congr (fun s _ => ?_); rw [phiB_neg]]
  rw [intervalIntegral.integral_comp_neg]
  norm_num

lemma gH_half (B : ℝ) (hB : 0 < B) : gH B (B/2) = 1/2 := by
  have hsupp : Function.support (phiB B) ⊆ Set.Ioc (-(B/2)) (B/2) := by
    intro x hx
    simp only [Function.mem_support] at hx
    have h1 : |x| < B/2 := by
      by_contra h; exact hx (phiB_support B hB (le_of_not_gt h))
    obtain ⟨h2, h3⟩ := abs_lt.1 h1
    exact ⟨h2, le_of_lt h3⟩
  have htot : ∫ s in (-(B/2))..(B/2), phiB B s = 1 := by
    rw [intervalIntegral.integral_eq_integral_of_support_subset (μ := volume) hsupp,
      phiB_integral B hB]
  have hadd : (∫ s in (-(B/2))..(0:ℝ), phiB B s) + ∫ s in (0:ℝ)..(B/2), phiB B s = 1 := by
    have h1 := intervalIntegral.integral_add_adjacent_intervals (μ := volume) (f := phiB B)
      (a := -(B/2)) (b := (0:ℝ)) (c := B/2)
      ((phiB_continuous B).intervalIntegrable _ _) ((phiB_continuous B).intervalIntegrable _ _)
    rw [h1]
    exact htot
  rw [interval_phiB_symm B hB] at hadd
  have h : ∫ s in (0:ℝ)..(B/2), phiB B s = 1/2 := by linarith
  unfold gH
  rw [h]

lemma gH_neg_half (B : ℝ) (hB : 0 < B) : gH B (-(B/2)) = -(1/2) := by
  unfold gH
  rw [intervalIntegral.integral_symm]
  have h : (∫ s in (-(B/2))..(0:ℝ), phiB B s) = 1/2 := by
    rw [interval_phiB_symm B hB]
    have hh := gH_half B hB
    unfold gH at hh
    exact hh
  rw [h]

lemma gH_eq_half (B : ℝ) (hB : 0 < B) {x : ℝ} (h : B/2 ≤ x) : gH B x = 1/2 := by
  rw [show gH B x = gH B (B/2) + ∫ s in (B/2)..x, phiB B s from by
      unfold gH; rw [intervalIntegral.integral_add_adjacent_intervals
        ((phiB_continuous B).intervalIntegrable _ _) ((phiB_continuous B).intervalIntegrable _ _)]]
  rw [gH_half B hB]
  rw [show (∫ s in (B/2)..x, phiB B s) = 0 from by
      rw [← intervalIntegral.integral_zero]
      refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall fun s hs => ?_)
      rw [Set.uIoc_of_le h] at hs
      exact phiB_support B hB (by rw [abs_of_nonneg (by linarith [hs.1])]; linarith [hs.1])]
  ring

lemma gH_eq_neg_half (B : ℝ) (hB : 0 < B) {x : ℝ} (h : x ≤ -(B/2)) : gH B x = -(1/2) := by
  rw [show gH B x = gH B (-(B/2)) - ∫ s in x..(-(B/2)), phiB B s from by
      unfold gH
      rw [← intervalIntegral.integral_add_adjacent_intervals (μ := volume) (f := phiB B) (a := (0:ℝ))
        (b := x) (c := -(B/2))
        ((phiB_continuous B).intervalIntegrable _ _) ((phiB_continuous B).intervalIntegrable _ _)]
      ring]
  rw [gH_neg_half B hB]
  rw [show (∫ s in x..(-(B/2)), phiB B s) = 0 from by
      rw [← intervalIntegral.integral_zero]
      refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall fun s hs => ?_)
      rw [Set.uIoc_of_le h] at hs
      exact phiB_support B hB (by rw [abs_of_nonpos (by linarith [hs.2])]; linarith [hs.2])]
  ring

end Identity
end Work.BMF
namespace Work.BMF
open Polynomial Finset Real Complex MeasureTheory Filter
open scoped FourierTransform RealInnerProductSpace

section Sharp
lemma integrableOn_inv_sq_Ioi (x0 : ℝ) (hx0 : 0 < x0) :
    IntegrableOn (fun t : ℝ => (1:ℝ)/t^2) (Set.Ioi x0) :=
  (integrableOn_Ioi_rpow_of_lt (a := (-2:ℝ)) (by norm_num) hx0).congr_fun
    (fun t ht => (one_div_sq_eq_rpow t (lt_trans hx0 ht)).symm) measurableSet_Ioi

lemma integral_tail_inv_sq (x0 : ℝ) (hx0 : 0 < x0) :
    ∫ ξ : ℝ, (1:ℝ)/ξ^2 * (Set.Ioi x0).indicator (fun _ => (1:ℝ)) |ξ| = 2 / x0 := by
  rw [show (fun ξ : ℝ => (1:ℝ)/ξ^2 * (Set.Ioi x0).indicator (fun _ => (1:ℝ)) |ξ|)
      = fun ξ => (1:ℝ)/|ξ|^2 * (Set.Ioi x0).indicator (fun _ => (1:ℝ)) |ξ| from by
      funext ξ; rw [sq_abs]]
  rw [integral_comp_abs
    (f := fun t : ℝ => (1:ℝ)/t^2 * (Set.Ioi x0).indicator (fun _ => (1:ℝ)) t)]
  rw [show (∫ x in Set.Ioi (0:ℝ), (1:ℝ)/x^2 * (Set.Ioi x0).indicator (fun _ => (1:ℝ)) x)
      = ∫ x in Set.Ioi (0:ℝ), (Set.Ioi x0).indicator (fun x => (1:ℝ)/x^2) x from by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun x _ => ?_)
    rw [Set.indicator_apply]; by_cases h : x ∈ Set.Ioi x0 <;> simp [h]]
  rw [MeasureTheory.setIntegral_indicator measurableSet_Ioi,
    show Set.Ioi (0:ℝ) ∩ Set.Ioi x0 = Set.Ioi x0 from by
      rw [Set.inter_eq_right]; intro x hx; exact lt_trans hx0 hx]
  rw [integral_Ioi_inv_sq x0 hx0]
  ring
/-- Integrability of `A · 1_[−x0,x0]`. -/
lemma integrable_Icc_ind (A x0 : ℝ) :
    Integrable (fun ξ : ℝ => A * (Set.Icc (-x0) x0).indicator (fun _ => (1:ℝ)) ξ) := by
  rw [show (fun ξ : ℝ => A * (Set.Icc (-x0) x0).indicator (fun _ => (1:ℝ)) ξ)
      = (Set.Icc (-x0) x0).indicator (fun _ => A) from by
        funext ξ; simp only [Set.indicator_apply]; split_ifs <;> ring]
  rw [integrable_indicator_iff measurableSet_Icc]
  exact MeasureTheory.integrableOn_const (by simp) (by simp)

/-- Integrability of the tail piece `D · ξ⁻² · 1_{|ξ| > x0}`. -/
lemma integrable_tail_inv_sq (D x0 : ℝ) (hD : 0 ≤ D) (hx0 : 0 < x0) :
    Integrable (fun ξ : ℝ => D * ((1:ℝ)/ξ^2 * (Set.Ioi x0).indicator (fun _ => (1:ℝ)) |ξ|)) := by
  set M := max 1 x0 with hMdef
  have h1M : (1:ℝ) ≤ M := le_max_left _ _
  have hx02 : 0 < x0^2 := pow_pos hx0 2
  have hdom_int : Integrable (fun ξ : ℝ => (D/x0^2) * (Set.Icc (-M) M).indicator (fun _ => (1:ℝ)) ξ
      + 2*D / (1 + ξ^2)) := by
    refine Integrable.add ?_ ?_
    · have : Integrable ((Set.Icc (-M) M).indicator (fun _ : ℝ => D/x0^2)) := by
        rw [integrable_indicator_iff measurableSet_Icc]
        exact MeasureTheory.integrableOn_const (by simp) (by simp)
      exact this.congr (Filter.Eventually.of_forall (fun ξ => by
        simp only [Set.indicator_apply, Pi.mul_apply]; split_ifs <;> ring))
    · exact (integrable_inv_one_add_sq.const_mul (2*D)).congr
        (Filter.Eventually.of_forall (fun ξ => by
          simp only [Pi.smul_apply, smul_eq_mul]; rw [div_eq_mul_inv, inv_eq_one_div, mul_comm]))
  refine hdom_int.mono' (by measurability) (Filter.Eventually.of_forall fun ξ => ?_)
  have hLHS0 : 0 ≤ D * ((1:ℝ)/ξ^2 * (Set.Ioi x0).indicator (fun _ => (1:ℝ)) |ξ|) :=
    mul_nonneg hD (mul_nonneg (by positivity)
      (Set.indicator_nonneg (fun _ _ => by norm_num) |ξ|))
  rw [Real.norm_eq_abs, abs_of_nonneg hLHS0]
  have htail_le : (1:ℝ)/ξ^2 * (Set.Ioi x0).indicator (fun _ => (1:ℝ)) |ξ| ≤ 1/x0^2 := by
    rw [Set.indicator_apply]
    split_ifs with h
    · rw [mul_one]
      have hlt : x0 < |ξ| := h
      have hp : 0 < (|ξ| - x0) * (|ξ| + x0) := mul_pos (by linarith) (by linarith)
      have hξ2 : x0^2 < ξ^2 := by nlinarith [hp, sq_abs ξ]
      rw [div_le_div_iff₀ (by linarith [hξ2, sq_nonneg x0]) hx02]
      linarith [hξ2]
    · rw [mul_zero]; positivity
  by_cases hM : ξ ∈ Set.Icc (-M) M
  · rw [Set.indicator_of_mem hM, mul_one]
    have h2 : D * ((1:ℝ)/ξ^2 * (Set.Ioi x0).indicator (fun _ => (1:ℝ)) |ξ|) ≤ D * (1/x0^2) :=
      mul_le_mul_of_nonneg_left htail_le hD
    have h3 : D * (1/x0^2) = D/x0^2 := by ring
    have h4 : 0 ≤ 2*D/(1+ξ^2) := div_nonneg (by linarith) (by positivity)
    linarith
  · rw [Set.indicator_of_notMem hM, mul_zero, zero_add]
    have hM' : M < |ξ| := by
      by_contra hc
      exact hM (by rw [Set.mem_Icc]; exact abs_le.1 (le_of_not_gt hc))
    have hξ1 : (1:ℝ) < |ξ| := lt_of_le_of_lt h1M hM'
    have hξ2 : (1:ℝ) < ξ^2 := by nlinarith [abs_nonneg ξ, sq_abs ξ, hξ1]
    have hind : (Set.Ioi x0).indicator (fun _ => (1:ℝ)) |ξ| ≤ 1 := by
      rw [Set.indicator_apply]; split_ifs <;> norm_num
    have hnn : 0 ≤ (1:ℝ)/ξ^2 := by positivity
    have hstep : (1:ℝ)/ξ^2 * (Set.Ioi x0).indicator (fun _ => (1:ℝ)) |ξ| ≤ 1/ξ^2 := by
      calc _ ≤ (1:ℝ)/ξ^2 * 1 := mul_le_mul_of_nonneg_left hind hnn
        _ = 1/ξ^2 := by ring
    have hstep2 : (1:ℝ)/ξ^2 ≤ 2/(1+ξ^2) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
    calc D * ((1:ℝ)/ξ^2 * (Set.Ioi x0).indicator (fun _ => (1:ℝ)) |ξ|)
        ≤ D * (1/ξ^2) := mul_le_mul_of_nonneg_left hstep hD
      _ ≤ D * (2/(1+ξ^2)) := mul_le_mul_of_nonneg_left hstep2 hD
      _ = 2*D/(1+ξ^2) := by ring

/-- The sharp bound `∫ min A (D/x²) dx ≤ 4√(AD)`. -/
lemma integral_min_le_sqrt {A D : ℝ} (hA : 0 ≤ A) (hD : 0 ≤ D) :
    ∫ ξ : ℝ, min A (D / ξ ^ 2) ≤ 4 * Real.sqrt (A * D) := by
  rcases eq_or_lt_of_le hA with hA0 | hApos
  · have hz : (fun ξ : ℝ => min A (D/ξ^2)) = fun _ => (0:ℝ) := by
      funext ξ; rw [← hA0]; exact min_eq_left (div_nonneg hD (sq_nonneg ξ))
    rw [hz, integral_zero, ← hA0, zero_mul, Real.sqrt_zero]; norm_num
  · rcases eq_or_lt_of_le hD with hD0 | hDpos
    · have hz : (fun ξ : ℝ => min A (D/ξ^2)) = fun _ => (0:ℝ) := by
        funext ξ; rw [← hD0, zero_div]; exact min_eq_right hA
      rw [hz, integral_zero, ← hD0, mul_zero, Real.sqrt_zero]; norm_num
    · set x0 := Real.sqrt (D / A) with hx0def
      have hx0pos : 0 < x0 := Real.sqrt_pos.2 (div_pos hDpos hApos)
      have hx0sq : x0^2 = D/A := by rw [hx0def, Real.sq_sqrt (by positivity)]
      have hAx0sq : (A * x0)^2 = A * D := by rw [mul_pow, hx0sq]; field_simp
      have hAx0 : A * x0 = Real.sqrt (A * D) := by
        rw [← Real.sqrt_sq (by positivity : (0:ℝ) ≤ A * x0), hAx0sq]
      have hDx0sq : (D / x0)^2 = A * D := by rw [div_pow, hx0sq]; field_simp
      have hDx0 : D / x0 = Real.sqrt (A * D) := by
        rw [← Real.sqrt_sq (by positivity : (0:ℝ) ≤ D / x0), hDx0sq]
      have hInt1 := integrable_Icc_ind A x0
      have hInt2 := integrable_tail_inv_sq D x0 hDpos.le hx0pos
      have hpoint : ∀ ξ : ℝ, min A (D/ξ^2)
          ≤ A * (Set.Icc (-x0) x0).indicator (fun _ => (1:ℝ)) ξ
            + D * ((1:ℝ)/ξ^2 * (Set.Ioi x0).indicator (fun _ => (1:ℝ)) |ξ|) := by
        intro ξ
        by_cases hξ : |ξ| ≤ x0
        · have hmem : ξ ∈ Set.Icc (-x0) x0 := by rw [Set.mem_Icc]; exact abs_le.1 hξ
          rw [Set.indicator_of_mem hmem, mul_one]
          have h1 : min A (D/ξ^2) ≤ A := min_le_left _ _
          have h2 : 0 ≤ D * ((1:ℝ)/ξ^2 * (Set.Ioi x0).indicator (fun _ => (1:ℝ)) |ξ|) :=
            mul_nonneg hDpos.le (mul_nonneg (by positivity)
              (Set.indicator_nonneg (fun _ _ => by norm_num) |ξ|))
          linarith
        · have hξ' : x0 < |ξ| := lt_of_not_ge hξ
          have hξ2 : x0^2 < ξ^2 := by
            have hp : 0 < (|ξ| - x0) * (|ξ| + x0) := mul_pos (by linarith) (by linarith)
            nlinarith [hp, sq_abs ξ]
          have hDle : D/ξ^2 ≤ A := by
            rw [div_le_iff₀ (by nlinarith [hξ2])]
            have h3 : A * x0^2 = D := by rw [hx0sq]; field_simp
            nlinarith [h3, hξ2, hApos]
          have hmin : min A (D/ξ^2) = D/ξ^2 := le_antisymm (min_le_right _ _) (le_min hDle le_rfl)
          have hmem : ξ ∉ Set.Icc (-x0) x0 := by
            intro hmem
            rw [Set.mem_Icc] at hmem
            linarith [abs_le.2 hmem]
          have hmem2 : |ξ| ∈ Set.Ioi x0 := hξ'
          have hgoal : D/ξ^2 = A * (Set.Icc (-x0) x0).indicator (fun _ => (1:ℝ)) ξ
              + D * ((1:ℝ)/ξ^2 * (Set.Ioi x0).indicator (fun _ => (1:ℝ)) |ξ|) := by
            rw [Set.indicator_of_notMem hmem, mul_zero, zero_add,
              Set.indicator_of_mem hmem2, mul_one, div_eq_mul_inv]
            ring
          calc min A (D/ξ^2) = D/ξ^2 := hmin
            _ ≤ A * (Set.Icc (-x0) x0).indicator (fun _ => (1:ℝ)) ξ
                + D * ((1:ℝ)/ξ^2 * (Set.Ioi x0).indicator (fun _ => (1:ℝ)) |ξ|) := le_of_eq hgoal
      have hAeq : (∫ ξ : ℝ, A * (Set.Icc (-x0) x0).indicator (fun _ => (1:ℝ)) ξ)
          = A * (2 * x0) := by
        rw [show (fun ξ : ℝ => A * (Set.Icc (-x0) x0).indicator (fun _ => (1:ℝ)) ξ)
            = (Set.Icc (-x0) x0).indicator (fun _ => A) from by
              funext ξ; simp only [Set.indicator_apply]; split_ifs <;> ring]
        rw [MeasureTheory.integral_indicator measurableSet_Icc, MeasureTheory.setIntegral_const,
          MeasureTheory.Measure.real_def, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]
        rw [smul_eq_mul]; ring
      have hDeq : (∫ ξ : ℝ, D * ((1:ℝ)/ξ^2 * (Set.Ioi x0).indicator (fun _ => (1:ℝ)) |ξ|))
          = D * (2 / x0) := by
        rw [MeasureTheory.integral_const_mul, integral_tail_inv_sq x0 hx0pos]
      calc ∫ ξ : ℝ, min A (D/ξ^2)
          ≤ ∫ ξ : ℝ, (A * (Set.Icc (-x0) x0).indicator (fun _ => (1:ℝ)) ξ
              + D * ((1:ℝ)/ξ^2 * (Set.Ioi x0).indicator (fun _ => (1:ℝ)) |ξ|)) :=
            integral_mono_of_nonneg (Filter.Eventually.of_forall fun ξ =>
              le_min hA (div_nonneg hD (sq_nonneg ξ)))
              (hInt1.add hInt2) (Filter.Eventually.of_forall hpoint)
        _ = (∫ ξ : ℝ, A * (Set.Icc (-x0) x0).indicator (fun _ => (1:ℝ)) ξ)
              + (∫ ξ : ℝ, D * ((1:ℝ)/ξ^2 * (Set.Ioi x0).indicator (fun _ => (1:ℝ)) |ξ|)) := by
            rw [MeasureTheory.integral_add hInt1 hInt2]
        _ = A * (2 * x0) + D * (2 / x0) := by rw [hAeq, hDeq]
        _ = 4 * Real.sqrt (A * D) := by
          have e1 : A * (2 * x0) = 2 * (A * x0) := by ring
          have e2 : D * (2 / x0) = 2 * (D / x0) := by ring
          rw [e1, e2, hAx0, hDx0]; ring

end Sharp
