import Mathlib
import Submission.Work.RHContract.Corpus
import Submission.Work.RHContract.Identity.TailInt.integrableOn_psi_sub_id_mul_kW

/-!
# `Work.RHContract.B.mellin_psiTail`

The Mellin transform of the tail `J = psiTail`: for `0 < Re s`,

`∫_2^∞ J(x) x^{-s-1} dx = (2^{-s} J(2) − Φ(s))/s`,

where `Φ(s) = ∫_2^∞ (ψ t − t) k(t) t^{-s} dt` (`Work.RHContract.Landau.Phi`).

This is the Fubini/partial-integration identity underlying the Landau step of the route:
writing `f(t) = (ψ t − t) k(t)`, `J(x) = ∫_x^∞ f`, and swapping the order of integration over
the region `{(x,t) : 2 < x < t}` gives

`∫_2^∞ J(x) x^{-s-1} dx = ∫_2^∞ f(t) (∫_2^t x^{-s-1} dx) dt
                        = ∫_2^∞ f(t) ((2^{-s} − t^{-s})/s) dt
                        = (2^{-s} J(2) − Φ(s))/s`.

The swap is justified by the integrability of `f` on `(2,∞)`
(`Work.RHContract.Identity.TailInt.integrableOn_psi_sub_id_mul_kW`) and the bound
`∫_2^t x^{-Re s - 1} dx ≤ 2^{-Re s}/Re s`.
-/

namespace Work.RHContract.B

open MeasureTheory

noncomputable section

/-- The integrand `t ↦ (ψ t − t) k(t)` of `psiTail` and `Phi`. -/
private def psiKer (t : ℝ) : ℝ := (Chebyshev.psi t - t) * Work.RHContract.kW t

private lemma measurable_psiKer : Measurable psiKer := by
  have hψ : Measurable Chebyshev.psi := Chebyshev.psi_mono.measurable
  have hk : Measurable Work.RHContract.kW := by
    unfold Work.RHContract.kW
    fun_prop
  exact (hψ.sub measurable_id).mul hk

private lemma integrableOn_psiKer : IntegrableOn psiKer (Set.Ioi 2) :=
  Work.RHContract.Identity.TailInt.integrableOn_psi_sub_id_mul_kW le_rfl

/-- `x ↦ (x : ℂ) ^ c` is measurable (for the Borel σ-algebras). -/
private lemma measurable_cpow_ofReal (c : ℂ) : Measurable (fun x : ℝ => (x : ℂ) ^ c) := by
  have h : Measurable (fun z : ℂ => z ^ c) := by
    simp only [Complex.cpow_def]
    refine Measurable.ite (measurableSet_singleton 0) ?_ ?_
    · exact measurable_const
    · exact Complex.measurable_exp.comp (Complex.measurable_log.mul_const c)
  exact h.comp Complex.measurable_ofReal

/-- The joint integrand `(x,t) ↦ 1_{x<t} f(t) x^{-s-1}` restricted to `(2,∞)²`. -/
private def cpj (s : ℂ) (x t : ℝ) : ℂ :=
  if x < t then (psiKer t : ℂ) * (x : ℂ) ^ (-s - 1) else 0

private lemma measurable_cpj' (s : ℂ) : Measurable (fun p : ℝ × ℝ => cpj s p.1 p.2) := by
  have h1 : Measurable (fun p : ℝ × ℝ => ((psiKer p.2 : ℝ) : ℂ)) :=
    Complex.measurable_ofReal.comp (measurable_psiKer.comp measurable_snd)
  have h2 : Measurable (fun p : ℝ × ℝ => (p.1 : ℂ) ^ (-s - 1)) :=
    (measurable_cpow_ofReal (-s - 1)).comp measurable_fst
  have hset : MeasurableSet {p : ℝ × ℝ | p.1 < p.2} :=
    measurableSet_lt measurable_fst measurable_snd
  have h3 : Measurable (fun p : ℝ × ℝ =>
      if p.1 < p.2 then (psiKer p.2 : ℂ) * (p.1 : ℂ) ^ (-s - 1) else 0) :=
    Measurable.ite hset (h1.mul h2) measurable_const
  simpa only [cpj] using h3

/-- `∫_a^b x^{-s-1} dx = (a^{-s} − b^{-s})/s` for `0 < a ≤ b` and `s ≠ 0`. -/
private lemma integral_Ioo_cpow (s : ℂ) (hs : s ≠ 0) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∫ x in Set.Ioo a b, (x : ℂ) ^ (-s - 1) = ((a : ℂ) ^ (-s) - (b : ℂ) ^ (-s)) / s := by
  rw [MeasureTheory.setIntegral_congr_set (MeasureTheory.Ioo_ae_eq_Ioc (a := a) (b := b))]
  rw [← intervalIntegral.integral_of_le hab]
  have hderiv : ∀ x ∈ Set.uIcc a b,
      HasDerivAt (fun y : ℝ => -((y : ℂ) ^ (-s)) / s) ((x : ℂ) ^ (-s - 1)) x := by
    intro x hx
    have hax : a ≤ x := by
      rw [Set.uIcc_of_le hab] at hx
      exact hx.1
    have hx0 : x ≠ 0 := by linarith
    have h1 : HasDerivAt (fun y : ℝ => (y : ℂ) ^ (-s)) ((-s) * (x : ℂ) ^ (-s - 1)) x :=
      hasDerivAt_ofReal_cpow_const hx0 (neg_ne_zero.mpr hs)
    have h2 : HasDerivAt (fun y : ℝ => -((y : ℂ) ^ (-s)) / s)
        (-((-s) * (x : ℂ) ^ (-s - 1)) / s) x := h1.neg.div_const s
    refine h2.congr_deriv ?_
    rw [show -((-s) * (x : ℂ) ^ (-s - 1)) = s * (x : ℂ) ^ (-s - 1) by ring,
      mul_div_cancel_left₀ _ hs]
  have hint : IntervalIntegrable (fun x : ℝ => (x : ℂ) ^ (-s - 1)) volume a b := by
    refine ContinuousOn.intervalIntegrable ?_
    refine ContinuousOn.cpow_const Complex.continuous_ofReal.continuousOn ?_
    intro x hx
    rw [Complex.ofReal_mem_slitPlane]
    have hax : a ≤ x := by
      rw [Set.uIcc_of_le hab] at hx
      exact hx.1
    linarith
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  ring

/-- `∫_2^∞ 1_{x<t} c x^{-s-1} dx = c (2^{-s} − t^{-s})/s` for `t > 2`, `s ≠ 0`. -/
private lemma integral_Ioi_indicator_cpow (s : ℂ) (hs : s ≠ 0) (c : ℂ) {t : ℝ} (ht : 2 < t) :
    ∫ x in Set.Ioi 2, (if x < t then c * (x : ℂ) ^ (-s - 1) else 0)
      = c * (((2 : ℂ) ^ (-s) - (t : ℂ) ^ (-s)) / s) := by
  have h1 : ∫ x in Set.Ioi 2, (if x < t then c * (x : ℂ) ^ (-s - 1) else 0)
      = ∫ x in Set.Ioi 2, (Set.Iio t).indicator (fun x => c * (x : ℂ) ^ (-s - 1)) x := by
    refine MeasureTheory.setIntegral_congr_ae measurableSet_Ioi
      (Filter.Eventually.of_forall (fun x _ => ?_))
    simp only [Set.indicator_apply, Set.mem_Iio]
  rw [h1, MeasureTheory.setIntegral_indicator measurableSet_Iio]
  rw [show Set.Ioi 2 ∩ Set.Iio t = Set.Ioo 2 t from by
    ext x; simp [Set.mem_Ioo, Set.mem_Ioi, Set.mem_Iio]]
  rw [MeasureTheory.integral_const_mul]
  rw [integral_Ioo_cpow s hs (by norm_num) ht.le]
  norm_num

/-- Joint integrability of the kernel on `(2,∞)²` (the hypothesis of Fubini). -/
private lemma integrable_uncurry_cpj (s : ℂ) (hs : 0 < s.re) :
    Integrable (fun p : ℝ × ℝ => cpj s p.1 p.2)
      ((volume.restrict (Set.Ioi 2)).prod (volume.restrict (Set.Ioi 2))) := by
  have hA : Integrable (fun x : ℝ => ‖(x : ℂ) ^ (-s - 1)‖) (volume.restrict (Set.Ioi 2)) := by
    have h1 : IntegrableOn (fun x : ℝ => x ^ (-s.re - 1)) (Set.Ioi 2) :=
      integrableOn_Ioi_rpow_of_lt (by linarith) (by norm_num)
    refine h1.congr_fun (fun x hx => ?_) measurableSet_Ioi
    have hx0 : (0:ℝ) < x := lt_trans (by norm_num) hx
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hx0, Complex.sub_re, Complex.neg_re, Complex.one_re]
  have hB : Integrable (fun t : ℝ => ‖psiKer t‖) (volume.restrict (Set.Ioi 2)) :=
    integrableOn_psiKer.norm
  have hD : Integrable (fun p : ℝ × ℝ => ‖(p.1 : ℂ) ^ (-s - 1)‖ * ‖psiKer p.2‖)
      ((volume.restrict (Set.Ioi 2)).prod (volume.restrict (Set.Ioi 2))) := hA.mul_prod hB
  refine hD.mono' (measurable_cpj' s).aestronglyMeasurable ?_
  filter_upwards with p
  by_cases hp : p.1 < p.2
  · simp only [cpj, if_pos hp, norm_mul]
    have hcast : ‖((psiKer p.2 : ℝ) : ℂ)‖ = ‖psiKer p.2‖ := by simp
    rw [hcast, mul_comm]
  · simp only [cpj, if_neg hp, norm_zero]
    positivity

private lemma integrableOn_psiKer_ofReal :
    IntegrableOn (fun t : ℝ => (psiKer t : ℂ)) (Set.Ioi 2) :=
  MeasureTheory.Integrable.ofReal (𝕜 := ℂ) (μ := volume.restrict (Set.Ioi 2)) integrableOn_psiKer

/-- Integrability of the `Phi` integrand on `(2,∞)`, for `0 < Re s`. -/
private lemma integrableOn_psiKer_mul_cpow (s : ℂ) (hs : 0 < s.re) :
    IntegrableOn (fun t : ℝ => (psiKer t : ℂ) * (t : ℂ) ^ (-s)) (Set.Ioi 2) := by
  have hdom : Integrable (fun t : ℝ => (2:ℝ) ^ (-s.re) * ‖psiKer t‖)
      (volume.restrict (Set.Ioi 2)) := integrableOn_psiKer.norm.const_mul _
  refine hdom.mono'
    ((Complex.measurable_ofReal.comp measurable_psiKer).mul
      (measurable_cpow_ofReal (-s))).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht0 : (0:ℝ) < t := lt_trans (by norm_num) ht
  have hcast : ‖((psiKer t : ℝ) : ℂ)‖ = ‖psiKer t‖ := by simp
  rw [norm_mul, hcast, Complex.norm_cpow_eq_rpow_re_of_pos ht0, Complex.neg_re]
  have hle : t ^ (-s.re) ≤ (2:ℝ) ^ (-s.re) :=
    Real.rpow_le_rpow_of_nonpos (by norm_num) ht.le (by linarith)
  calc ‖psiKer t‖ * t ^ (-s.re) ≤ ‖psiKer t‖ * 2 ^ (-s.re) :=
        mul_le_mul_of_nonneg_left hle (norm_nonneg _)
    _ = 2 ^ (-s.re) * ‖psiKer t‖ := mul_comm _ _

/-- `Phi` in terms of the integrand `psiKer`. -/
private lemma Phi_eq (s : ℂ) : Work.RHContract.Landau.Phi s
    = ∫ t in Set.Ioi 2, (psiKer t : ℂ) * (t : ℂ) ^ (-s) := by
  rw [show Work.RHContract.Landau.Phi s
      = ∫ t in Set.Ioi 2, ((Chebyshev.psi t - t) * Work.RHContract.kW t : ℂ) * (t:ℂ)^(-s)
      from rfl]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun t => ?_))
  simp only [psiKer]
  norm_num [Complex.ofReal_mul, Complex.ofReal_sub]

/-- **Mellin transform of the `psiTail`**: `∫_2^∞ J(x) x^{-s-1} dx
= (2^{-s} J(2) − Φ(s))/s` for `0 < Re s`. -/
theorem mellin_psiTail (s : ℂ) (hs : 0 < s.re) :
    ∫ x in Set.Ioi 2, (Work.RHContract.psiTail x : ℂ) * (x : ℂ) ^ (-s - 1)
      = ((2 : ℂ) ^ (-s) * (Work.RHContract.psiTail 2 : ℂ) - Work.RHContract.Landau.Phi s) / s := by
  have hs0 : s ≠ 0 := by intro h; rw [h] at hs; simp at hs
  -- Step 1: expand `psiTail x` as the inner integral and restrict to `Ioi 2`.
  have step1 : ∫ x in Set.Ioi 2, (Work.RHContract.psiTail x : ℂ) * (x : ℂ) ^ (-s - 1)
      = ∫ x in Set.Ioi 2, ∫ t in Set.Ioi 2, cpj s x t := by
    refine MeasureTheory.setIntegral_congr_ae measurableSet_Ioi
      (Filter.Eventually.of_forall (fun x hx => ?_))
    have hx2 : (2:ℝ) < x := hx
    have hpsi : Work.RHContract.psiTail x = ∫ t in Set.Ioi x, psiKer t := rfl
    have hcast : ((∫ t in Set.Ioi x, psiKer t : ℝ) : ℂ) = ∫ t in Set.Ioi x, (psiKer t : ℂ) :=
      (integral_ofReal (𝕜 := ℂ) (μ := volume.restrict (Set.Ioi x)) (f := psiKer)).symm
    have hmul : (∫ t in Set.Ioi x, (psiKer t : ℂ)) * (x : ℂ) ^ (-s - 1)
        = ∫ t in Set.Ioi x, (psiKer t : ℂ) * (x : ℂ) ^ (-s - 1) :=
      (MeasureTheory.integral_mul_const ((x : ℂ) ^ (-s - 1))
        (fun t : ℝ => (psiKer t : ℂ))).symm
    have hkey : ∫ t in Set.Ioi 2, cpj s x t
        = ∫ t in Set.Ioi 2,
            (Set.Ioi x).indicator (fun t => (psiKer t : ℂ) * (x : ℂ) ^ (-s - 1)) t := by
      refine MeasureTheory.setIntegral_congr_ae measurableSet_Ioi
        (Filter.Eventually.of_forall (fun t _ => ?_))
      simp only [cpj, Set.indicator_apply, Set.mem_Ioi]
    calc (Work.RHContract.psiTail x : ℂ) * (x : ℂ) ^ (-s - 1)
        = ((∫ t in Set.Ioi x, psiKer t : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1) := by rw [hpsi]
      _ = (∫ t in Set.Ioi x, (psiKer t : ℂ)) * (x : ℂ) ^ (-s - 1) := by rw [hcast]
      _ = (∫ t in Set.Ioi x, (psiKer t : ℂ) * (x : ℂ) ^ (-s - 1)) := hmul
      _ = ∫ t in Set.Ioi 2, cpj s x t := by
            rw [hkey, MeasureTheory.setIntegral_indicator measurableSet_Ioi, Set.Ioi_inter_Ioi,
              max_eq_right hx2.le]
  -- Step 2: Fubini.
  have step2 : ∫ x in Set.Ioi 2, ∫ t in Set.Ioi 2, cpj s x t
      = ∫ t in Set.Ioi 2, ∫ x in Set.Ioi 2, cpj s x t :=
    MeasureTheory.integral_integral_swap (f := cpj s) (integrable_uncurry_cpj s hs)
  -- Step 3: evaluate the inner integral `∫_2^∞ 1_{x<t} x^{-s-1} dx`.
  have step3 : ∫ t in Set.Ioi 2, (∫ x in Set.Ioi 2, cpj s x t)
      = ∫ t in Set.Ioi 2, (psiKer t : ℂ) * (((2:ℂ) ^ (-s) - (t:ℂ) ^ (-s)) / s) := by
    refine MeasureTheory.setIntegral_congr_ae measurableSet_Ioi
      (Filter.Eventually.of_forall (fun t ht => ?_))
    simpa only [cpj] using integral_Ioi_indicator_cpow s hs0 (psiKer t) ht
  have hInt1 : IntegrableOn (fun t : ℝ => (psiKer t : ℂ) * ((2:ℂ) ^ (-s)) / s) (Set.Ioi 2) :=
    ((integrableOn_psiKer_ofReal).mul_const _).div_const _
  have hInt2 : IntegrableOn (fun t : ℝ => (psiKer t : ℂ) * ((t:ℂ) ^ (-s)) / s) (Set.Ioi 2) :=
    (integrableOn_psiKer_mul_cpow s hs).div_const s
  -- Step 4: split into the two defining integrals `J(2)` and `Phi s`.
  have step4 : ∫ t in Set.Ioi 2, (psiKer t : ℂ) * (((2:ℂ) ^ (-s) - (t:ℂ) ^ (-s)) / s)
      = ((2:ℂ) ^ (-s) * (Work.RHContract.psiTail 2 : ℂ) - Work.RHContract.Landau.Phi s) / s := by
    have hsplit : ∫ t in Set.Ioi 2, (psiKer t : ℂ) * (((2:ℂ) ^ (-s) - (t:ℂ) ^ (-s)) / s)
        = ∫ t in Set.Ioi 2,
            ((psiKer t : ℂ) * ((2:ℂ) ^ (-s)) / s - (psiKer t : ℂ) * ((t:ℂ) ^ (-s)) / s) := by
      refine MeasureTheory.setIntegral_congr_ae measurableSet_Ioi
        (Filter.Eventually.of_forall (fun t _ => ?_))
      ring
    rw [hsplit, MeasureTheory.integral_sub hInt1 hInt2]
    have h1 : ∫ t in Set.Ioi 2, (psiKer t : ℂ) * ((2:ℂ) ^ (-s)) / s
        = (Work.RHContract.psiTail 2 : ℂ) * ((2:ℂ) ^ (-s) / s) := by
      rw [show (fun t : ℝ => (psiKer t : ℂ) * ((2:ℂ) ^ (-s)) / s)
            = (fun t : ℝ => (psiKer t : ℂ) * (((2:ℂ) ^ (-s)) / s)) from by funext t; ring]
      rw [MeasureTheory.integral_mul_const]
      congr 1
      rw [show Work.RHContract.psiTail 2 = ∫ t in Set.Ioi 2, psiKer t from rfl]
      exact integral_ofReal
    have h2 : ∫ t in Set.Ioi 2, (psiKer t : ℂ) * ((t:ℂ) ^ (-s)) / s
        = Work.RHContract.Landau.Phi s / s := by
      rw [show (fun t : ℝ => (psiKer t : ℂ) * ((t:ℂ) ^ (-s)) / s)
            = (fun t : ℝ => ((psiKer t : ℂ) * ((t:ℂ) ^ (-s))) / s) from rfl]
      rw [MeasureTheory.integral_div]
      congr 1
      rw [Phi_eq s]
    rw [h1, h2]
    ring
  calc ∫ x in Set.Ioi 2, (Work.RHContract.psiTail x : ℂ) * (x : ℂ) ^ (-s - 1)
      = ∫ x in Set.Ioi 2, ∫ t in Set.Ioi 2, cpj s x t := step1
    _ = ∫ t in Set.Ioi 2, ∫ x in Set.Ioi 2, cpj s x t := step2
    _ = ∫ t in Set.Ioi 2, (psiKer t : ℂ) * (((2:ℂ) ^ (-s) - (t:ℂ) ^ (-s)) / s) := step3
    _ = ((2:ℂ) ^ (-s) * (Work.RHContract.psiTail 2 : ℂ)
          - Work.RHContract.Landau.Phi s) / s := step4

end

end Work.RHContract.B
