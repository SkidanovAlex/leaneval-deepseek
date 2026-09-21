import Mathlib
import Submission.Work.OddVolterra.Defs
import Submission.Work.OddVolterra.Estimates
import Submission.Work.OddVolterra.Kernel.Diag
import Submission.Work.OddVolterra.KernelExt.Defs
import Submission.Work.OddVolterra.KernelExt.JM_diag
import Submission.Work.OddVolterra.KernelExt.Rnu_contDiff
import Submission.Work.OddVolterra.KernelExt.Rnu_spec
import Submission.Work.OddVolterra.KernelExt.fderiv_fst_eq_deriv
import Submission.Work.OddVolterra.Existence.krad_pos_state_region
import Submission.Work.OddVolterra.Existence.continuousOn_deriv_G2_apply
import Submission.Work.OddVolterra.Existence.JetBound
import Submission.Work.OddVolterra.Existence.hquot_contDiff
import Submission.Work.Analysis.Calculus.contDiff_dslope
import Submission.Commons.Geometry.Ulam.even_profile_moment_solution
import Submission.Commons.Geometry.Ulam.even_profile_perturbation_from_smooth_bump_aux_independent_core
import Submission.Work.Anchor.ThetaM_contDiffOn
import Submission.Work.OddExistence.Manifest.aw_toolkit
import Submission.Work.OddExistence.Manifest.hasDerivAt_G2M_apply

namespace Work.Anchor

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval
open Work.OddVolterra Work.OddVolterra.KernelExt

noncomputable section

lemma z_coords {σ : ℝ} (hσ : σ ∈ Set.Icc (1/2 : ℝ) 1) {z : Work.OddVolterra.St}
    (hz : z ∈ Metric.closedBall (Work.OddVolterra.baseState σ) (1/2)) :
    (1/5 : ℝ) ≤ z 0 ∧ (1/5 : ℝ) ≤ z 1 ∧ (∀ i : Fin 4, |z i| ≤ 3/2) := by
  have hcoord : ∀ i : Fin 4, |z i - Work.OddVolterra.baseState σ i| ≤ 1/2 := by
    intro i
    have h := dist_le_pi_dist z (Work.OddVolterra.baseState σ) i
    rw [Real.dist_eq] at h
    linarith [Metric.mem_closedBall.mp hz]
  have hbase : ∀ i : Fin 4, |Work.OddVolterra.baseState σ i| ≤ 1 := by
    intro i
    fin_cases i
    · show |Work.OddVolterra.baseState σ 0| ≤ 1
      rw [show Work.OddVolterra.baseState σ 0 = Commons.Geometry.Ulam.profileX σ from rfl]
      exact abs_le.mpr (Commons.Geometry.Ulam.profileX_mem_Icc σ)
    · show |Work.OddVolterra.baseState σ 1| ≤ 1
      rw [show Work.OddVolterra.baseState σ 1 = Commons.Geometry.Ulam.profileX σ from rfl]
      exact abs_le.mpr (Commons.Geometry.Ulam.profileX_mem_Icc σ)
    · show |Work.OddVolterra.baseState σ 2| ≤ 1
      rw [show Work.OddVolterra.baseState σ 2 = deriv Commons.Geometry.Ulam.profileX σ from rfl]
      linarith [Commons.Geometry.Ulam.abs_deriv_profileX_le σ]
    · show |Work.OddVolterra.baseState σ 3| ≤ 1
      rw [show Work.OddVolterra.baseState σ 3 = deriv Commons.Geometry.Ulam.profileX σ from rfl]
      linarith [Commons.Geometry.Ulam.abs_deriv_profileX_le σ]
  have hprof : (1 : ℝ) / 5 ≤ Commons.Geometry.Ulam.profileX σ - 1 / 2 := by
    have h0 : 0 ≤ σ := le_trans (by norm_num) hσ.1
    have h1 : Commons.Geometry.Ulam.profileX 1 ≤ Commons.Geometry.Ulam.profileX σ :=
      Commons.Geometry.Ulam.profileX_le_profileX' h0 hσ.2
    have h2 : Commons.Geometry.Ulam.profileX 1 = 1 / Real.sqrt 2 := by
      simp only [Commons.Geometry.Ulam.profileX]; norm_num
    have h3 : Real.sqrt 2 < 10 / 7 := by
      rw [Real.sqrt_lt' (by norm_num)]; norm_num
    have h4 : (7 : ℝ) / 10 < 1 / Real.sqrt 2 := by
      rw [lt_div_iff₀ (Real.sqrt_pos.mpr (by norm_num))]
      nlinarith [h3]
    rw [h2] at h1
    linarith
  refine ⟨?_, ?_, ?_⟩
  · have h := hcoord 0
    rw [show Work.OddVolterra.baseState σ 0 = Commons.Geometry.Ulam.profileX σ from rfl] at h
    linarith [abs_le.mp h]
  · have h := hcoord 1
    rw [show Work.OddVolterra.baseState σ 1 = Commons.Geometry.Ulam.profileX σ from rfl] at h
    linarith [abs_le.mp h]
  · intro i
    have h := abs_le.mp (hcoord i)
    have hb := abs_le.mp (hbase i)
    rw [abs_le]
    constructor <;> linarith

lemma krad_region {h : ℝ → ℝ} {a σ t : ℝ}
    (h0 : ∀ x : ℝ, |h x| ≤ 1/100) (h1 : ∀ x : ℝ, |deriv h x| ≤ 1/100)
    (ha : (1/4 : ℝ) ≤ a) (ha2 : a ≤ 3/2) (hσ : (1/2 : ℝ) ≤ σ) (hσ1 : σ ≤ 1)
    (ht : (1/5 : ℝ) ≤ |t|) (ht2 : |t| ≤ 3/2) :
    (1/100 : ℝ) ≤ Work.OddVolterra.krad h σ t a ∧ Work.OddVolterra.krad h σ t a ≤ 8 := by
  have hq : |Work.OddVolterra.hquot h a σ| ≤ 1/100 :=
    Work.OddVolterra.abs_hquot_le h1 (by norm_num)
  have hqb := abs_le.mp hq
  have hS : (0 : ℝ) < σ + a := by linarith
  have hhl : |h σ + h a| ≤ 1/50 := by
    have h1' := abs_le.mp (h0 σ)
    have h2' := abs_le.mp (h0 a)
    rw [abs_le]
    constructor <;> linarith [h1'.1, h1'.2, h2'.1, h2'.2]
  have hlt : |h σ + h a| < (σ + a) * (1/5) := by
    have h : (3/4 : ℝ) * (1/5) ≤ (σ + a) * (1/5) :=
      mul_le_mul_of_nonneg_right (by linarith) (by norm_num)
    have : (1/50 : ℝ) < 3/20 := by norm_num
    linarith [abs_le.mp hhl]
  have hline : Work.OddVolterra.line h σ t + Work.OddVolterra.line h a t
      = (σ + a) * t + (h σ + h a) := by
    unfold Work.OddVolterra.line; ring
  have htabs : |t| ≤ 3/2 := ht2
  have hfacs : (19/100 : ℝ) ≤ |t + Work.OddVolterra.hquot h a σ| ∧
      (13/100 : ℝ) ≤ |(σ + a) * t + (h σ + h a)| := by
    have h1a : (19/100 : ℝ) ≤ |t + Work.OddVolterra.hquot h a σ| := by
      have h' : |t| ≤ |t + Work.OddVolterra.hquot h a σ| + |Work.OddVolterra.hquot h a σ| := by
        have habs := abs_add_le (t + Work.OddVolterra.hquot h a σ) (-(Work.OddVolterra.hquot h a σ))
        rw [show t + Work.OddVolterra.hquot h a σ + -(Work.OddVolterra.hquot h a σ) = t by ring] at habs
        simpa only [abs_neg] using habs
      linarith [ht, hq]
    have h2a : (13/100 : ℝ) ≤ |(σ + a) * t + (h σ + h a)| := by
      have hAb : |(σ + a) * t| = (σ + a) * |t| := by rw [abs_mul, abs_of_pos hS]
      have h3 : (3/20 : ℝ) ≤ |(σ + a) * t| := by
        rw [hAb]
        calc (3/20 : ℝ) = (3/4) * (1/5) := by norm_num
          _ ≤ (σ + a) * |t| := by
              have h1 : (3/4 : ℝ) ≤ σ + a := by linarith
              have hSa : (0:ℝ) ≤ σ + a := by linarith
              exact le_trans (mul_le_mul_of_nonneg_right h1 (by norm_num : (0:ℝ) ≤ 1/5))
                (mul_le_mul_of_nonneg_left ht hSa)
      have h' : |(σ + a) * t| ≤ |(σ + a) * t + (h σ + h a)| + |h σ + h a| := by
        have habs := abs_add_le ((σ + a) * t + (h σ + h a)) (-(h σ + h a))
        rw [show (σ + a) * t + (h σ + h a) + -(h σ + h a) = (σ + a) * t by ring] at habs
        simpa only [abs_neg] using habs
      linarith [h3, abs_le.mp hhl]
    exact ⟨h1a, h2a⟩
  have hsunb : |(σ + a) * t| ≤ 5/2 * (3/2) := by
    rw [abs_mul, abs_of_pos hS]
    exact mul_le_mul (by linarith : σ + a ≤ 5/2) htabs (abs_nonneg t) (by norm_num)
  have hsumub : |(σ + a) * t + (h σ + h a)| ≤ 4 := by
    have h1' : |(σ + a) * t| + |h σ + h a| ≤ 4 := by linarith [hsunb, abs_le.mp hhl]
    linarith [abs_add_le ((σ + a) * t) (h σ + h a), h1']
  have hqabs2 : |t + Work.OddVolterra.hquot h a σ| ≤ 2 := by
    have h1 := abs_le.mp hq
    have h2 := abs_le.mp htabs
    rw [abs_le]; constructor <;> linarith
  have hpos : 0 < Work.OddVolterra.krad h σ t a := by
    rw [Work.OddVolterra.krad_apply, hline]
    rcases lt_trichotomy t 0 with htn | htz | htp
    · have htle : t ≤ -(1/5) := by
        have h := ht; rw [abs_of_neg htn] at h; linarith
      have h1' : t + Work.OddVolterra.hquot h a σ < 0 := by linarith [hqb.2]
      have hlt' : h σ + h a < (σ + a) * (1/5) := lt_of_le_of_lt (le_abs_self _) hlt
      have hmul : (σ + a) * t ≤ -((σ + a) * (1/5)) := by
        have h := mul_le_mul_of_nonneg_left htle (le_of_lt hS)
        rwa [show (σ + a) * (-(1/5)) = -((σ + a) * (1/5)) by ring] at h
      have h2' : (σ + a) * t + (h σ + h a) < 0 := by linarith
      exact mul_pos_of_neg_of_neg h1' h2'
    · rw [htz] at ht; norm_num at ht
    · have htge : (1/5 : ℝ) ≤ t := by
        have h := ht; rwa [abs_of_pos htp] at h
      have h1' : 0 < t + Work.OddVolterra.hquot h a σ := by linarith [hqb.1]
      have hnegabs : -((σ + a) * (1/5)) < -|h σ + h a| := by linarith
      have hgt' : -((σ + a) * (1/5)) < h σ + h a := lt_of_lt_of_le hnegabs (neg_abs_le _)
      have hmul : (σ + a) * (1/5) ≤ (σ + a) * t := mul_le_mul_of_nonneg_left htge (le_of_lt hS)
      have h2' : 0 < (σ + a) * t + (h σ + h a) := by linarith
      exact mul_pos h1' h2'
  have hup : Work.OddVolterra.krad h σ t a ≤ 8 := by
    rw [Work.OddVolterra.krad_apply, hline]
    calc (t + Work.OddVolterra.hquot h a σ) * ((σ + a) * t + (h σ + h a))
        ≤ |(t + Work.OddVolterra.hquot h a σ) * ((σ + a) * t + (h σ + h a))| := le_abs_self _
      _ = |t + Work.OddVolterra.hquot h a σ| * |(σ + a) * t + (h σ + h a)| := abs_mul _ _
      _ ≤ 2 * 4 := mul_le_mul hqabs2 hsumub (abs_nonneg _) (by norm_num)
      _ = 8 := by norm_num
  have hlow : (1/100 : ℝ) ≤ Work.OddVolterra.krad h σ t a := by
    have hkle : Work.OddVolterra.krad h σ t a
        = (t + Work.OddVolterra.hquot h a σ) * ((σ + a) * t + (h σ + h a)) := by
      rw [Work.OddVolterra.krad_apply, hline]
    rw [hkle]
    calc (1/100 : ℝ) ≤ (19/100) * (13/100) := by norm_num
      _ ≤ |t + Work.OddVolterra.hquot h a σ| * |(σ + a) * t + (h σ + h a)| :=
          mul_le_mul hfacs.1 hfacs.2 (by norm_num) (abs_nonneg _)
      _ = |(t + Work.OddVolterra.hquot h a σ) * ((σ + a) * t + (h σ + h a))| := (abs_mul _ _).symm
      _ = (t + Work.OddVolterra.hquot h a σ) * ((σ + a) * t + (h σ + h a)) := by
          rw [← hkle]; exact abs_of_pos hpos
  exact ⟨hlow, hup⟩

/-- The `a`-derivative of `hquot h · σ` is bounded by `sup |h''|`. -/
lemma hquot_deriv_bound {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hδ : ∀ x : ℝ, |iteratedDeriv 2 h x| ≤ δ) (σ a : ℝ) :
    |deriv (fun a' : ℝ => Work.OddVolterra.hquot h a' σ) a| ≤ δ := by
  have hd1 : ContDiff ℝ (⊤ : ℕ∞) (deriv h) := by
    simpa only [Function.iterate_one] using hh.iterate_deriv 1
  have hd2 : ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ => iteratedDeriv 2 h x) := by
    rw [show (2:ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ', iteratedDeriv_one]
    simpa only [Function.iterate_one] using hd1.iterate_deriv 1
  have hderiv_all : ∀ y τ : ℝ, HasDerivAt (fun y' : ℝ => deriv h (y' + τ * (σ - y')))
      (iteratedDeriv 2 h (y + τ * (σ - y)) * (1 - τ)) y := by
    intro y τ
    have hinner : HasDerivAt (fun y' : ℝ => y' + τ * (σ - y')) (1 - τ) y := by
      have h1 : (fun y' : ℝ => y' + τ * (σ - y')) = fun y' => (1 - τ) * y' + (τ * σ) := by
        funext y'; ring
      rw [h1]
      simpa using ((hasDerivAt_id y).const_mul (1 - τ)).add_const (τ * σ)
    have h2eq : iteratedDeriv 2 h = deriv (deriv h) := by
      simpa using (iteratedDeriv_succ' (n := 1) (f := h))
    have houter : HasDerivAt (deriv h) (iteratedDeriv 2 h (y + τ * (σ - y))) (y + τ * (σ - y)) := by
      rw [h2eq]
      exact ((hd1.differentiable (by simp)) (y + τ * (σ - y))).hasDerivAt
    exact houter.comp y hinner
  have hmain : HasDerivAt (fun y : ℝ => ∫ τ in (0:ℝ)..1, deriv h (y + τ * (σ - y)))
      (∫ τ in (0:ℝ)..1, iteratedDeriv 2 h (a + τ * (σ - a)) * (1 - τ)) a := by
    refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := volume) (a := (0:ℝ)) (b := 1)
      (F := fun (y : ℝ) (τ : ℝ) => deriv h (y + τ * (σ - y)))
      (F' := fun (y : ℝ) (τ : ℝ) => iteratedDeriv 2 h (y + τ * (σ - y)) * (1 - τ))
      (x₀ := a) (s := Set.univ) (bound := fun _ : ℝ => δ)
      Filter.univ_mem ?_ ?_ ?_ ?_ ?_ ?_).2
    · filter_upwards with y
      have hcont : Continuous (fun τ : ℝ => y + τ * (σ - y)) := by fun_prop
      exact (hd1.continuous.comp hcont).aestronglyMeasurable
    · have hcont : Continuous (fun τ : ℝ => a + τ * (σ - a)) := by fun_prop
      exact (hd1.continuous.comp hcont).intervalIntegrable _ _
    · have hcont : Continuous (fun τ : ℝ => a + τ * (σ - a)) := by fun_prop
      have hcont2 : Continuous (fun τ : ℝ => (1 : ℝ) - τ) := by fun_prop
      exact ((hd2.continuous.comp hcont).mul hcont2).aestronglyMeasurable
    · filter_upwards with τ hτ y _
      rw [Real.norm_eq_abs, abs_mul]
      have h2 : |1 - τ| ≤ 1 := by
        rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hτ
        rw [abs_le]; constructor <;> linarith [hτ.1, hτ.2]
      calc |iteratedDeriv 2 h (y + τ * (σ - y))| * |1 - τ| ≤ δ * 1 :=
            mul_le_mul (hδ _) h2 (abs_nonneg _) hδ0
        _ = δ := by ring
    · exact intervalIntegrable_const
    · filter_upwards with τ hτ y _
      exact hderiv_all y τ
  have hquot_eq : (fun y : ℝ => Work.OddVolterra.hquot h y σ)
      = fun y : ℝ => ∫ τ in (0:ℝ)..1, deriv h (y + τ * (σ - y)) := rfl
  rw [hquot_eq, hmain.deriv]
  have hb : ∀ τ ∈ Set.uIoc (0:ℝ) 1, ‖iteratedDeriv 2 h (a + τ * (σ - a)) * (1 - τ)‖ ≤ δ := by
    intro τ hτ
    rw [Real.norm_eq_abs, abs_mul]
    have h2 : |1 - τ| ≤ 1 := by
      rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hτ
      rw [abs_le]; constructor <;> linarith [hτ.1, hτ.2]
    calc |iteratedDeriv 2 h (a + τ * (σ - a))| * |1 - τ| ≤ δ * 1 :=
          mul_le_mul (hδ _) h2 (abs_nonneg _) hδ0
      _ = δ := by ring
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0:ℝ)) (b := 1) hb
  rwa [Real.norm_eq_abs, sub_zero, abs_one, mul_one] at this





/-- `(k : ℕ∞ω) ≤ ⊤`. -/
lemma coe_nat_le_top (k : ℕ) : (k : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω) := by
  exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤)

/-- Leibniz bound for the `j`-th derivative of a product. -/
lemma product_bound {f g : ℝ → ℝ} {x : ℝ} {j : ℕ} {Bf Bg : ℝ}
    (hf : ∀ k ≤ j, |iteratedDeriv k f x| ≤ Bf) (hg : ∀ k ≤ j, |iteratedDeriv k g x| ≤ Bg)
    (hfd : ContDiffAt ℝ (j : ℕ∞) f x) (hgd : ContDiffAt ℝ (j : ℕ∞) g x)
    (hBf : 0 ≤ Bf) (hBg : 0 ≤ Bg) :
    |iteratedDeriv j (fun y => f y * g y) x| ≤ Bf * Bg * 2 ^ j := by
  have key : iteratedDeriv j (fun y => f y * g y) x
      = ∑ i ∈ Finset.range (j + 1), ↑(j.choose i) * iteratedDeriv i f x * iteratedDeriv (j - i) g x :=
    iteratedDeriv_mul (n := j) (x := x) hfd hgd
  rw [key]
  calc |∑ i ∈ Finset.range (j + 1), ↑(j.choose i) * iteratedDeriv i f x * iteratedDeriv (j - i) g x|
      ≤ ∑ i ∈ Finset.range (j + 1), |↑(j.choose i) * iteratedDeriv i f x * iteratedDeriv (j - i) g x| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * (Bf * Bg) := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hi' : i ≤ j := by simpa [Finset.mem_range] using hi
        have h1 : |iteratedDeriv i f x| ≤ Bf := hf i hi'
        have h2 : |iteratedDeriv (j - i) g x| ≤ Bg := hg (j - i) (by omega)
        have h3 : (0:ℝ) ≤ (j.choose i : ℝ) := by positivity
        rw [abs_mul, abs_mul, abs_of_nonneg h3]
        calc (j.choose i : ℝ) * |iteratedDeriv i f x| * |iteratedDeriv (j - i) g x|
            ≤ (j.choose i : ℝ) * Bf * Bg := by
              refine mul_le_mul (mul_le_mul_of_nonneg_left h1 h3) h2 (abs_nonneg _) (by positivity)
          _ = (j.choose i : ℝ) * (Bf * Bg) := by ring
    _ = Bf * Bg * 2 ^ j := by
        have hsum : (∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ)) = (2:ℝ) ^ j := by
          rw [← Nat.cast_sum, Nat.sum_range_choose]
          norm_num
        rw [← Finset.sum_mul, hsum]
        ring

/-- Leibniz bound for the `j`-th derivative of a difference of products. -/
lemma product_sub_bound {f₁ f₂ g₁ g₂ : ℝ → ℝ} {x : ℝ} {j : ℕ} {Bf Bg Df Dg : ℝ}
    (hf : ∀ k ≤ j, |iteratedDeriv k f₁ x| ≤ Bf) (hg : ∀ k ≤ j, |iteratedDeriv k g₂ x| ≤ Bg)
    (hDf : ∀ k ≤ j, |iteratedDeriv k (fun y => f₁ y - f₂ y) x| ≤ Df)
    (hDg : ∀ k ≤ j, |iteratedDeriv k (fun y => g₁ y - g₂ y) x| ≤ Dg)
    (hf₁ : ContDiffAt ℝ (j : ℕ∞) f₁ x) (hf₂ : ContDiffAt ℝ (j : ℕ∞) f₂ x)
    (hg₁ : ContDiffAt ℝ (j : ℕ∞) g₁ x) (hg₂ : ContDiffAt ℝ (j : ℕ∞) g₂ x)
    (hBf : 0 ≤ Bf) (hBg : 0 ≤ Bg) (hDf0 : 0 ≤ Df) (hDg0 : 0 ≤ Dg) :
    |iteratedDeriv j (fun y => f₁ y * g₁ y) x - iteratedDeriv j (fun y => f₂ y * g₂ y) x| ≤
      (Bf * Dg + Df * Bg) * 2 ^ j := by
  have hEq : (fun y => f₁ y * g₁ y) - (fun y => f₂ y * g₂ y)
      = (fun y => f₁ y * (g₁ y - g₂ y)) + (fun y => (f₁ y - f₂ y) * g₂ y) := by
    funext y
    simp only [Pi.sub_apply, Pi.add_apply]
    ring
  have hsub := iteratedDeriv_sub (n := j) (x := x) (hf₁.mul hg₁) (hf₂.mul hg₂)
  have hadd := iteratedDeriv_add (n := j) (x := x) (hf₁.mul (hg₁.sub hg₂)) ((hf₁.sub hf₂).mul hg₂)
  rw [← hsub, hEq, hadd]
  refine le_trans (abs_add_le _ _) ?_
  have h1 : |iteratedDeriv j (fun y => f₁ y * (g₁ y - g₂ y)) x| ≤ Bf * Dg * 2 ^ j :=
    product_bound (fun k hk => hf k hk) (fun k hk => hDg k hk) hf₁ (hg₁.sub hg₂) hBf hDg0
  have h2 : |iteratedDeriv j (fun y => (f₁ y - f₂ y) * g₂ y) x| ≤ Df * Bg * 2 ^ j :=
    product_bound (fun k hk => hDf k hk) (fun k hk => hg k hk) (hf₁.sub hf₂) hg₂ hDf0 hBg
  linarith

/-! ## The two building blocks `P` and `Q` -/

lemma iteratedDeriv_P_zero (h : ℝ → ℝ) (t a : ℝ) :
    iteratedDeriv 0 (fun u : ℝ => u * t + h u) a = a * t + h a := by simp

lemma iteratedDeriv_P_one {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) (t a : ℝ) :
    iteratedDeriv 1 (fun u : ℝ => u * t + h u) a = t + deriv h a := by
  rw [iteratedDeriv_one]
  have h1 : HasDerivAt (fun u : ℝ => u * t + h u) (t + deriv h a) a := by
    have h2 : HasDerivAt (fun u : ℝ => u * t) t a := by
      simpa [mul_comm] using (hasDerivAt_id a).mul_const t
    have h3 : HasDerivAt (fun u : ℝ => h u) (deriv h a) a :=
      ((hh.differentiable (by simp)) a).hasDerivAt
    exact h2.add h3
  exact h1.deriv

lemma iteratedDeriv_P_ge2 {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) (t a : ℝ) {i : ℕ}
    (hi : 2 ≤ i) :
    iteratedDeriv i (fun u : ℝ => u * t + h u) a = iteratedDeriv i h a := by
  have h1 : iteratedDeriv i (fun u : ℝ => u * t + h u) a
      = iteratedDeriv i (fun u : ℝ => u * t) a + iteratedDeriv i h a := by
    have e : (fun u : ℝ => u * t + h u) = (fun u : ℝ => u * t) + h := rfl
    rw [e, iteratedDeriv_add]
    · exact (contDiffAt_id.mul contDiffAt_const).of_le (coe_nat_le_top i)
    · exact (hh.contDiffAt).of_le (coe_nat_le_top i)
  have h2 : iteratedDeriv i (fun u : ℝ => u * t) a = 0 := by
    have e : (fun u : ℝ => u * t) = fun u : ℝ => t * id u := by funext u; simp [mul_comm]
    rw [e, iteratedDeriv_const_mul (n := i) (x := a) (f := id) t contDiffAt_id, iteratedDeriv_id]
    simp [show i ≠ 0 by omega, show i ≠ 1 by omega]
  rw [h1, h2, zero_add]

lemma iteratedDeriv_Q_zero {h : ℝ → ℝ} (t a : ℝ) :
    iteratedDeriv 0 (fun u : ℝ => t + deriv h u) a = t + deriv h a := by simp

lemma iteratedDeriv_Q_pos {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) (t a : ℝ) {i : ℕ} (hi : 1 ≤ i) :
    iteratedDeriv i (fun u : ℝ => t + deriv h u) a = iteratedDeriv (i + 1) h a := by
  have hd1 : ContDiff ℝ (⊤ : ℕ∞) (deriv h) := by
    simpa only [Function.iterate_one] using hh.iterate_deriv 1
  have h1 : iteratedDeriv i (fun u : ℝ => t + deriv h u) a
      = iteratedDeriv i (fun _ : ℝ => t) a + iteratedDeriv i (deriv h) a := by
    have e : (fun u : ℝ => t + deriv h u) = (fun _ : ℝ => t) + deriv h := rfl
    rw [e, iteratedDeriv_add]
    · exact contDiffAt_const
    · exact (hd1.contDiffAt).of_le (coe_nat_le_top i)
  rw [h1, iteratedDeriv_const, if_neg (by omega : ¬ i = 0), zero_add]
  rw [← iteratedDeriv_succ' (n := i) (f := h)]





/-- `Zrad` in terms of `P u = u*t + h u`. -/
lemma Zrad_sec (h : ℝ → ℝ) (σ t a : ℝ) :
    Zrad h (a, σ, t) = (line h σ t) ^ 2 - (a * t + h a) ^ 2 := by
  unfold Zrad line; ring

/-- `ZradS` in terms of `P u = u*t + h u` and `Q u = t + h' u`. -/
lemma ZradS_sec {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) (σ t a : ℝ) :
    ZradS h (a, σ, t) = -2 * ((a * t + h a) * (t + deriv h a)) := by
  have hZ : DifferentiableAt ℝ (Zrad h) (a, σ, t) :=
    (Zrad_contDiff h hh).differentiable (by simp) _
  rw [ZradS, fderiv_fst_eq_deriv _ a σ t hZ]
  have hfun : (fun u : ℝ => Zrad h (u, σ, t))
      = fun u : ℝ => (line h σ t) ^ 2 - (u * t + h u) ^ 2 := by
    funext u; exact Zrad_sec h σ t u
  rw [hfun]
  have h1 : HasDerivAt (fun u : ℝ => u * t + h u) (t + deriv h a) a := by
    have h2 : HasDerivAt (fun u : ℝ => u * t) t a := by
      simpa [mul_comm] using (hasDerivAt_id a).mul_const t
    have h3 : HasDerivAt (fun u : ℝ => h u) (deriv h a) a :=
      ((hh.differentiable (by simp)) a).hasDerivAt
    exact h2.add h3
  have h4 : HasDerivAt (fun u : ℝ => (u * t + h u) ^ 2)
      (2 * (a * t + h a) ^ (2 - 1) * (t + deriv h a)) a := h1.pow 2
  have h5 : HasDerivAt (fun u : ℝ => (line h σ t) ^ 2 - (u * t + h u) ^ 2)
      (0 - 2 * (a * t + h a) ^ (2 - 1) * (t + deriv h a)) a :=
    (hasDerivAt_const a ((line h σ t) ^ 2)).sub h4
  rw [h5.deriv]
  ring

/-- The jet bounds for `P u = u*t + h u`, its reference `P₀ u = u*t`, and their difference. -/
lemma P_bounds {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1/100)
    {K : ℕ} (hjet : ∀ j ≤ K, ∀ x : ℝ, |iteratedDeriv j h x| ≤ δ) {t a : ℝ}
    (ha : |a| ≤ 1) (ht : |t| ≤ 3/2) {k : ℕ} (hk : k ≤ K) :
    |iteratedDeriv k (fun u : ℝ => u * t + h u) a| ≤ 151/100 ∧
    |iteratedDeriv k (fun u : ℝ => u * t) a| ≤ 3/2 ∧
    |iteratedDeriv k (fun u : ℝ => (u * t + h u) - (u * t)) a| ≤ δ := by
  have hP0 : ∀ j ≤ K, |iteratedDeriv j (fun u : ℝ => u * t) a| ≤ 3/2 := by
    intro j hj
    have e : (fun u : ℝ => u * t) = fun u : ℝ => t * id u := by funext u; simp [mul_comm]
    rw [e]
    rcases Nat.lt_or_ge j 2 with hj2 | hj2
    · interval_cases j
      · simp [iteratedDeriv_zero, abs_mul, abs_of_nonneg (abs_nonneg _)]
        nlinarith [abs_nonneg a, abs_nonneg t, abs_mul a t]
      · rw [iteratedDeriv_const_mul (n := 1) (x := a) (f := id) t contDiffAt_id, iteratedDeriv_id]
        simpa using ht
    · rw [iteratedDeriv_const_mul (n := j) (x := a) (f := id) t contDiffAt_id, iteratedDeriv_id]
      simp only [show j ≠ 0 by omega, show j ≠ 1 by omega, ↓reduceIte, mul_zero, abs_zero]
      norm_num
  have hPD : ∀ j ≤ K, |iteratedDeriv j (fun u : ℝ => (u * t + h u) - (u * t)) a| ≤ δ := by
    intro j hj
    have e : (fun u : ℝ => (u * t + h u) - (u * t)) = h := by funext u; ring
    rw [e]; exact hjet j hj a
  have hP : ∀ j ≤ K, |iteratedDeriv j (fun u : ℝ => u * t + h u) a| ≤ 151/100 := by
    intro j hj
    have hsplit : (fun u : ℝ => u * t + h u) = (fun u : ℝ => u * t) + fun u : ℝ => h u := rfl
    have hadd : iteratedDeriv j (fun u : ℝ => u * t + h u) a
        = iteratedDeriv j (fun u : ℝ => u * t) a + iteratedDeriv j (fun u : ℝ => h u) a := by
      rw [hsplit, iteratedDeriv_add]
      · exact (contDiffAt_id.mul contDiffAt_const).of_le (coe_nat_le_top j)
      · exact (hh.contDiffAt).of_le (coe_nat_le_top j)
    rw [hadd]
    have h2 : |iteratedDeriv j (fun u : ℝ => h u) a| ≤ δ := by
      have e : (fun u : ℝ => h u) = h := rfl
      rw [e]; exact hjet j hj a
    linarith [hP0 j hj, h2, abs_add_le (iteratedDeriv j (fun u : ℝ => u * t) a)
      (iteratedDeriv j (fun u : ℝ => h u) a), hδ1]
  exact ⟨hP k hk, hP0 k hk, hPD k hk⟩

/-- The jet bounds for `Q u = t + h' u`, its reference `Q₀ u = t`, and their difference. -/
lemma Q_bounds {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1/100)
    {K : ℕ} (hK : 1 ≤ K) (hjet : ∀ j ≤ K, ∀ x : ℝ, |iteratedDeriv j h x| ≤ δ) {t a : ℝ}
    (ha : |a| ≤ 1) (ht : |t| ≤ 3/2) {k : ℕ} (hk : k ≤ K - 1) :
    |iteratedDeriv k (fun u : ℝ => t + deriv h u) a| ≤ 151/100 ∧
    |iteratedDeriv k (fun u : ℝ => t) a| ≤ 3/2 ∧
    |iteratedDeriv k (fun u : ℝ => (t + deriv h u) - t) a| ≤ δ := by
  have hd1 : ContDiff ℝ (⊤ : ℕ∞) (deriv h) := by
    simpa only [Function.iterate_one] using hh.iterate_deriv 1
  have hQD : ∀ j ≤ K - 1, |iteratedDeriv j (fun u : ℝ => (t + deriv h u) - t) a| ≤ δ := by
    intro j hj
    have e : (fun u : ℝ => (t + deriv h u) - t) = deriv h := by funext u; ring
    rw [e]
    rcases Nat.eq_zero_or_pos j with hj0 | hjpos
    · subst hj0
      rw [iteratedDeriv_zero]
      simpa [iteratedDeriv_one] using hjet 1 hK a
    · rw [← iteratedDeriv_succ' (n := j) (f := h)]
      exact hjet (j + 1) (by omega) a
  have hQ0 : ∀ j ≤ K - 1, |iteratedDeriv j (fun u : ℝ => t) a| ≤ 3/2 := by
    intro j hj
    rw [iteratedDeriv_const]
    rcases Nat.eq_zero_or_pos j with hj0 | hjpos
    · rw [hj0]; simp only [↓reduceIte]; exact ht
    · simp only [if_neg (by omega : ¬ j = 0), abs_zero]; norm_num
  have hQ : ∀ j ≤ K - 1, |iteratedDeriv j (fun u : ℝ => t + deriv h u) a| ≤ 151/100 := by
    intro j hj
    have hadd : iteratedDeriv j (fun u : ℝ => t + deriv h u) a
        = iteratedDeriv j (fun _ : ℝ => t) a + iteratedDeriv j (deriv h) a := by
      have e : (fun u : ℝ => t + deriv h u) = (fun _ : ℝ => t) + deriv h := rfl
      rw [e, iteratedDeriv_add]
      · exact contDiffAt_const
      · exact (hd1.contDiffAt).of_le (coe_nat_le_top j)
    rw [hadd]
    have h2 : |iteratedDeriv j (deriv h) a| ≤ δ := by
      rcases Nat.eq_zero_or_pos j with hj0 | hjpos
      · subst hj0
        rw [iteratedDeriv_zero]
        simpa [iteratedDeriv_one] using hjet 1 hK a
      · rw [← iteratedDeriv_succ' (n := j) (f := h)]
        exact hjet (j + 1) (by omega) a
    linarith [hQ0 j hj, h2, abs_add_le (iteratedDeriv j (fun _ : ℝ => t) a)
      (iteratedDeriv j (deriv h) a), hδ1]
  exact ⟨hQ k hk, hQ0 k hk, hQD k hk⟩





lemma contDiff_P_top {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) (t : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun u : ℝ => u * t + h u) := by
  have h2 : ContDiff ℝ (⊤ : ℕ∞) (fun u : ℝ => u * t) := by fun_prop
  exact h2.add hh

lemma contDiff_P0_top (t : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (fun u : ℝ => u * t) := by fun_prop

lemma contDiff_P2_top {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) (t : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) ((fun u : ℝ => u * t + h u) ^ 2) :=
  (contDiff_P_top hh t).pow 2

lemma contDiff_Q_top {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) (t : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun u : ℝ => t + deriv h u) := by
  have hd1 : ContDiff ℝ (⊤ : ℕ∞) (deriv h) := by
    simpa only [Function.iterate_one] using hh.iterate_deriv 1
  exact contDiff_const.add hd1

lemma pow_two_apply' (f : ℝ → ℝ) : f ^ 2 = fun y => f y * f y := by
  funext y; rw [Pi.pow_apply, pow_two]

lemma abs_sub_le_abs_add (x y : ℝ) : |x - y| ≤ |x| + |y| := by
  rw [abs_sub_le_iff]
  constructor <;> linarith [le_abs_self x, le_abs_self y, neg_abs_le x, neg_abs_le y]

/-- Bound for the `k`-th `a`-derivative of `Zrad h (·,σ,t)`. -/
lemma Zrad_deriv_bound {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) {δ : ℝ}
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1/100)
    {K : ℕ} (hjet : ∀ j ≤ K, ∀ x : ℝ, |iteratedDeriv j h x| ≤ δ) {a σ t : ℝ}
    (ha : |a| ≤ 1) (hσ : |σ| ≤ 1) (ht : |t| ≤ 3/2) {k : ℕ} (hk : k ≤ K) :
    |iteratedDeriv k (fun a' : ℝ => Zrad h (a', σ, t)) a| ≤ (151/100)^2 * (2 + 2^k) := by
  have hL : |line h σ t| ≤ 151/100 := by
    have h1 : |σ * t| ≤ 3/2 := by
      rw [abs_mul]; nlinarith [abs_nonneg t, abs_nonneg σ, hσ, ht]
    have h2 : |h σ| ≤ 1/100 := le_trans (hjet 0 (Nat.zero_le K) σ) hδ1
    have h3 : line h σ t = σ * t + h σ := rfl
    rw [h3]
    linarith [abs_add_le (σ * t) (h σ), h1, h2]
  have hPall : ∀ k' ≤ k, |iteratedDeriv k' (fun u : ℝ => u * t + h u) a| ≤ 151/100 :=
    fun k' hk' => (P_bounds hh hδ0 hδ1 hjet (a := a) (t := t) ha ht (k := k')
      (le_trans hk' hk)).1
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · subst hk0
    rw [iteratedDeriv_zero, Zrad_sec]
    have hL2 : |a * t + h a| ≤ 151/100 := hPall 0 (le_refl 0)
    have h5 : |(line h σ t)^2 - (a * t + h a)^2| ≤ 2 * (151/100)^2 := by
      rw [abs_le]
      have h1 := abs_le.mp hL
      have h2 := abs_le.mp hL2
      constructor <;> nlinarith [h1.1, h1.2, h2.1, h2.2]
    calc |(line h σ t)^2 - (a * t + h a)^2| ≤ 2 * (151/100)^2 := h5
      _ ≤ (151/100)^2 * (2 + 2^0) := by norm_num
  · have hsubst : (fun a' : ℝ => Zrad h (a', σ, t))
        = fun a' : ℝ => (line h σ t) ^ 2 - (a' * t + h a') ^ 2 := by
      funext u; exact Zrad_sec h σ t u
    have hfun : (fun a' : ℝ => (line h σ t) ^ 2 - (a' * t + h a') ^ 2)
        = (fun _ : ℝ => (line h σ t) ^ 2) - (fun u : ℝ => u * t + h u) ^ 2 := rfl
    rw [hsubst, hfun, iteratedDeriv_sub (n := k) (x := a) contDiffAt_const
        ((contDiff_P2_top hh t).contDiffAt.of_le (Work.OddVolterra.Existence.coe_nat_le_infty k)),
      iteratedDeriv_const, if_neg (by omega : ¬ k = 0), zero_sub, abs_neg,
      pow_two_apply' (fun u : ℝ => u * t + h u)]
    have h2 := product_bound (f := fun u : ℝ => u * t + h u) (g := fun u : ℝ => u * t + h u)
      (x := a) (j := k) hPall hPall
      ((contDiff_P_top hh t).contDiffAt.of_le (Work.OddVolterra.Existence.coe_nat_le_infty k))
      ((contDiff_P_top hh t).contDiffAt.of_le (Work.OddVolterra.Existence.coe_nat_le_infty k))
      (by norm_num) (by norm_num)
    refine le_trans h2 ?_
    have hpow : (0:ℝ) ≤ 2 ^ k := by positivity
    nlinarith [hpow]

/-- Difference bound for the `k`-th `a`-derivative of `Zrad`. -/
lemma Zrad_deriv_diff_bound {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) {δ : ℝ}
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1/100)
    {K : ℕ} (hjet : ∀ j ≤ K, ∀ x : ℝ, |iteratedDeriv j h x| ≤ δ) {a σ t : ℝ}
    (ha : |a| ≤ 1) (hσ : |σ| ≤ 1) (ht : |t| ≤ 3/2) {k : ℕ} (hk : k ≤ K) :
    |iteratedDeriv k (fun a' : ℝ => Zrad h (a', σ, t)) a -
      iteratedDeriv k (fun a' : ℝ => Zrad (0 : ℝ → ℝ) (a', σ, t)) a|
      ≤ (4 + 2 * (151/100 + 3/2) * 2^k) * δ := by
  have hh0 : ContDiff ℝ (⊤ : ℕ∞) (0 : ℝ → ℝ) :=
    (contDiff_const : ContDiff ℝ (⊤ : ℕ∞) fun _ : ℝ => (0:ℝ))
  have hjet0 : ∀ j ≤ K, ∀ x : ℝ, |iteratedDeriv j (0 : ℝ → ℝ) x| ≤ δ := by
    intro j hj x; simp [hδ0]
  have hPall : ∀ k' ≤ k, |iteratedDeriv k' (fun u : ℝ => u * t + h u) a| ≤ 151/100 :=
    fun k' hk' => (P_bounds hh hδ0 hδ1 hjet (a := a) (t := t) ha ht (k := k')
      (le_trans hk' hk)).1
  have hP0all : ∀ k' ≤ k, |iteratedDeriv k' (fun u : ℝ => u * t) a| ≤ 3/2 :=
    fun k' hk' => (P_bounds (h := (0:ℝ→ℝ)) hh0 hδ0 hδ1 hjet0 (a := a) (t := t) ha ht (k := k')
      (le_trans hk' hk)).2.1
  have hDall : ∀ k' ≤ k, |iteratedDeriv k' (fun u : ℝ => (u * t + h u) - u * t) a| ≤ δ :=
    fun k' hk' => (P_bounds hh hδ0 hδ1 hjet (a := a) (t := t) ha ht (k := k')
      (le_trans hk' hk)).2.2
  have hL : |line h σ t| ≤ 151/100 := by
    have h1 : |σ * t| ≤ 3/2 := by
      rw [abs_mul]; nlinarith [abs_nonneg t, abs_nonneg σ, hσ, ht]
    have h2 : |h σ| ≤ 1/100 := le_trans (hjet 0 (Nat.zero_le K) σ) hδ1
    have h3 : line h σ t = σ * t + h σ := rfl
    rw [h3]
    linarith [abs_add_le (σ * t) (h σ), h1, h2]
  have hL0 : |line (0:ℝ→ℝ) σ t| ≤ 3/2 := by
    have e : line (0:ℝ→ℝ) σ t = σ * t := by simp [line]
    rw [e, abs_mul]
    calc |σ| * |t| ≤ 1 * (3/2) := mul_le_mul hσ ht (abs_nonneg t) (by norm_num)
      _ = 3/2 := by ring
  have hLD : |line h σ t - line (0:ℝ→ℝ) σ t| ≤ δ := by
    have e : line h σ t - line (0:ℝ→ℝ) σ t = h σ := by simp [line]
    rw [e]; exact hjet 0 (Nat.zero_le K) σ
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · subst hk0
    rw [iteratedDeriv_zero, iteratedDeriv_zero, Zrad_sec, Zrad_sec]
    simp only [Pi.zero_apply, add_zero]
    have h1 : |(line h σ t)^2 - (line (0:ℝ→ℝ) σ t)^2| ≤ (151/100 + 3/2) * δ := by
      have hsum : |line h σ t + line (0:ℝ→ℝ) σ t| ≤ 151/100 + 3/2 :=
        le_trans (abs_add_le _ _) (add_le_add hL hL0)
      calc |(line h σ t)^2 - (line (0:ℝ→ℝ) σ t)^2|
          = |(line h σ t - line (0:ℝ→ℝ) σ t) * (line h σ t + line (0:ℝ→ℝ) σ t)| := by ring_nf
        _ = |line h σ t - line (0:ℝ→ℝ) σ t| * |line h σ t + line (0:ℝ→ℝ) σ t| := abs_mul _ _
        _ ≤ δ * (151/100 + 3/2) := mul_le_mul hLD hsum (abs_nonneg _) hδ0
        _ = (151/100 + 3/2) * δ := by ring
    have h2 : |(a * t + h a)^2 - (a * t)^2| ≤ (151/100 + 3/2) * δ := by
      have hsum : |a * t + h a + a * t| ≤ 151/100 + 3/2 :=
        le_trans (abs_add_le _ _) (add_le_add (hPall 0 (le_refl 0)) (hP0all 0 (le_refl 0)))
      calc |(a * t + h a)^2 - (a * t)^2|
          = |(a * t + h a - a * t) * (a * t + h a + a * t)| := by ring_nf
        _ = |a * t + h a - a * t| * |a * t + h a + a * t| := abs_mul _ _
        _ ≤ δ * (151/100 + 3/2) := mul_le_mul (hDall 0 (le_refl 0)) hsum (abs_nonneg _) hδ0
        _ = (151/100 + 3/2) * δ := by ring
    have h3 : |(line h σ t)^2 - (a*t + h a)^2 - ((line (0:ℝ→ℝ) σ t)^2 - (a*t)^2)|
        ≤ 2 * (151/100 + 3/2) * δ := by
      have hsplit : (line h σ t)^2 - (a*t + h a)^2 - ((line (0:ℝ→ℝ) σ t)^2 - (a*t)^2)
          = ((line h σ t)^2 - (line (0:ℝ→ℝ) σ t)^2) - ((a*t + h a)^2 - (a*t)^2) := by ring
      rw [hsplit]
      refine le_trans (abs_sub_le_abs_add _ _) ?_
      linarith [h1, h2]
    calc |(line h σ t)^2 - (a * t + h a)^2 - ((line (0:ℝ→ℝ) σ t)^2 - (a * t)^2)|
        ≤ 2 * (151/100 + 3/2) * δ := h3
      _ ≤ (4 + 2 * (151/100 + 3/2) * 2^0) * δ := by
            rw [show (2:ℝ)^0 = 1 by norm_num]; nlinarith [hδ0]
  · have hsubst1 : (fun a' : ℝ => Zrad h (a', σ, t))
        = fun a' : ℝ => (line h σ t) ^ 2 - (a' * t + h a') ^ 2 := by
      funext u; exact Zrad_sec h σ t u
    have hsubst2 : (fun a' : ℝ => Zrad (0:ℝ→ℝ) (a', σ, t))
        = fun a' : ℝ => (line (0:ℝ→ℝ) σ t) ^ 2 - (a' * t + (0:ℝ→ℝ) a') ^ 2 := by
      funext u; exact Zrad_sec (0:ℝ→ℝ) σ t u
    have hfun1 : (fun a' : ℝ => (line h σ t) ^ 2 - (a' * t + h a') ^ 2)
        = (fun _ : ℝ => (line h σ t) ^ 2) - (fun u : ℝ => u * t + h u) ^ 2 := rfl
    have hfun2 : (fun a' : ℝ => (line (0:ℝ→ℝ) σ t) ^ 2 - (a' * t + (0:ℝ→ℝ) a') ^ 2)
        = (fun _ : ℝ => (line (0:ℝ→ℝ) σ t) ^ 2) - (fun u : ℝ => u * t + (0:ℝ→ℝ) u) ^ 2 := rfl
    rw [hsubst1, hsubst2, hfun1, hfun2,
      iteratedDeriv_sub (n := k) (x := a) contDiffAt_const
        ((contDiff_P2_top hh t).contDiffAt.of_le (Work.OddVolterra.Existence.coe_nat_le_infty k)),
      iteratedDeriv_sub (n := k) (x := a) contDiffAt_const
        ((contDiff_P2_top (h := (0:ℝ→ℝ)) hh0 t).contDiffAt.of_le (Work.OddVolterra.Existence.coe_nat_le_infty k)),
      iteratedDeriv_const, iteratedDeriv_const, if_neg (by omega : ¬ k = 0), if_neg (by omega : ¬ k = 0)]
    have hA : iteratedDeriv k ((fun u : ℝ => u * t + h u) ^ 2) a
        = iteratedDeriv k (fun y : ℝ => (y * t + h y) * (y * t + h y)) a := by
      congr 1
      rw [pow_two_apply']
    have hB : iteratedDeriv k ((fun u : ℝ => u * t + (0:ℝ→ℝ) u) ^ 2) a
        = iteratedDeriv k (fun y : ℝ => (y * t) * (y * t)) a := by
      congr 1
      rw [pow_two_apply']
      congr 1
      funext y
      simp
    rw [hA, hB]
    have hgoal : (0 - iteratedDeriv k (fun y : ℝ => (y * t + h y) * (y * t + h y)) a)
        - (0 - iteratedDeriv k (fun y : ℝ => (y * t) * (y * t)) a)
        = -(iteratedDeriv k (fun y : ℝ => (y * t + h y) * (y * t + h y)) a
            - iteratedDeriv k (fun y : ℝ => (y * t) * (y * t)) a) := by ring
    rw [hgoal, abs_neg]
    have hprod := product_sub_bound (f₁ := fun u : ℝ => u * t + h u) (f₂ := fun u : ℝ => u * t)
      (g₁ := fun u : ℝ => u * t + h u) (g₂ := fun u : ℝ => u * t) (x := a) (j := k)
      hPall hP0all hDall hDall
      ((contDiff_P_top hh t).contDiffAt.of_le (Work.OddVolterra.Existence.coe_nat_le_infty k))
      ((contDiff_P0_top t).contDiffAt.of_le (Work.OddVolterra.Existence.coe_nat_le_infty k))
      ((contDiff_P_top hh t).contDiffAt.of_le (Work.OddVolterra.Existence.coe_nat_le_infty k))
      ((contDiff_P0_top t).contDiffAt.of_le (Work.OddVolterra.Existence.coe_nat_le_infty k))
      (by norm_num) (by norm_num) hδ0 hδ0
    refine le_trans hprod ?_
    have hpow : (0:ℝ) ≤ 2 ^ k := by positivity
    nlinarith [hpow, hδ0]





lemma mul_apply' (f g : ℝ → ℝ) : f * g = fun y => f y * g y := rfl

/-- Bound for the `k`-th `a`-derivative of `ZradS h (·,σ,t)`. -/
lemma ZradS_deriv_bound {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) {δ : ℝ}
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1/100) {K : ℕ} (hK : 1 ≤ K)
    (hjet : ∀ j ≤ K, ∀ x : ℝ, |iteratedDeriv j h x| ≤ δ) {a σ t : ℝ}
    (ha : |a| ≤ 1) (hσ : |σ| ≤ 1) (ht : |t| ≤ 3/2) {k : ℕ} (hk : k ≤ K - 1) :
    |iteratedDeriv k (fun a' : ℝ => ZradS h (a', σ, t)) a| ≤ 2 * (151/100)^2 * 2^k := by
  have hPall : ∀ k' ≤ k, |iteratedDeriv k' (fun u : ℝ => u * t + h u) a| ≤ 151/100 :=
    fun k' hk' => (P_bounds hh hδ0 hδ1 hjet (a := a) (t := t) ha ht (k := k')
      (le_trans hk' (by omega : k ≤ K))).1
  have hQall : ∀ k' ≤ k, |iteratedDeriv k' (fun u : ℝ => t + deriv h u) a| ≤ 151/100 :=
    fun k' hk' => (Q_bounds hh hδ0 hδ1 hK hjet (a := a) (t := t) ha ht (k := k')
      (le_trans hk' hk)).1
  have hsubst : (fun a' : ℝ => ZradS h (a', σ, t))
      = fun a' : ℝ => -2 * ((a' * t + h a') * (t + deriv h a')) := by
    funext u; exact ZradS_sec hh σ t u
  have hfun : (fun a' : ℝ => -2 * ((a' * t + h a') * (t + deriv h a')))
      = fun a' : ℝ => (-2 : ℝ) * (((fun u : ℝ => u * t + h u) * (fun u : ℝ => t + deriv h u)) a') := by
    funext u; rw [mul_apply']
  rw [hsubst, hfun, iteratedDeriv_const_mul (n := k) (x := a) (c := (-2:ℝ))
      (f := (fun u : ℝ => u * t + h u) * (fun u : ℝ => t + deriv h u))
      (((contDiff_P_top hh t).mul (contDiff_Q_top hh t)).contDiffAt.of_le
        (Work.OddVolterra.Existence.coe_nat_le_infty k))]
  rw [abs_mul, show |(-2:ℝ)| = 2 by norm_num]
  have h2 := product_bound (f := fun u : ℝ => u * t + h u) (g := fun u : ℝ => t + deriv h u)
    (x := a) (j := k) hPall hQall
    ((contDiff_P_top hh t).contDiffAt.of_le (Work.OddVolterra.Existence.coe_nat_le_infty k))
    ((contDiff_Q_top hh t).contDiffAt.of_le (Work.OddVolterra.Existence.coe_nat_le_infty k))
    (by norm_num) (by norm_num)
  refine le_trans (mul_le_mul_of_nonneg_left h2 (by norm_num)) ?_
  have hpow : (0:ℝ) ≤ 2 ^ k := by positivity
  nlinarith [hpow]

/-- Difference bound for the `k`-th `a`-derivative of `ZradS`. -/
lemma ZradS_deriv_diff_bound {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) {δ : ℝ}
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1/100) {K : ℕ} (hK : 1 ≤ K)
    (hjet : ∀ j ≤ K, ∀ x : ℝ, |iteratedDeriv j h x| ≤ δ) {a σ t : ℝ}
    (ha : |a| ≤ 1) (hσ : |σ| ≤ 1) (ht : |t| ≤ 3/2) {k : ℕ} (hk : k ≤ K - 1) :
    |iteratedDeriv k (fun a' : ℝ => ZradS h (a', σ, t)) a -
      iteratedDeriv k (fun a' : ℝ => ZradS (0 : ℝ → ℝ) (a', σ, t)) a|
      ≤ 2 * (151/100 + 3/2) * 2^k * δ := by
  have hh0 : ContDiff ℝ (⊤ : ℕ∞) (0 : ℝ → ℝ) :=
    (contDiff_const : ContDiff ℝ (⊤ : ℕ∞) fun _ : ℝ => (0:ℝ))
  have hjet0 : ∀ j ≤ K, ∀ x : ℝ, |iteratedDeriv j (0 : ℝ → ℝ) x| ≤ δ := by
    intro j hj x; simp [hδ0]
  have hPall : ∀ k' ≤ k, |iteratedDeriv k' (fun u : ℝ => u * t + h u) a| ≤ 151/100 :=
    fun k' hk' => (P_bounds hh hδ0 hδ1 hjet (a := a) (t := t) ha ht (k := k')
      (le_trans hk' (by omega : k ≤ K))).1
  have hP0all : ∀ k' ≤ k, |iteratedDeriv k' (fun u : ℝ => u * t) a| ≤ 3/2 :=
    fun k' hk' => (P_bounds (h := (0:ℝ→ℝ)) hh0 hδ0 hδ1 hjet0 (a := a) (t := t) ha ht (k := k')
      (le_trans hk' (by omega : k ≤ K))).2.1
  have hQall : ∀ k' ≤ k, |iteratedDeriv k' (fun u : ℝ => t + deriv h u) a| ≤ 151/100 :=
    fun k' hk' => (Q_bounds hh hδ0 hδ1 hK hjet (a := a) (t := t) ha ht (k := k')
      (le_trans hk' hk)).1
  have hQ0all : ∀ k' ≤ k, |iteratedDeriv k' (fun u : ℝ => t) a| ≤ 3/2 :=
    fun k' hk' => (Q_bounds hh hδ0 hδ1 hK hjet (a := a) (t := t) ha ht (k := k')
      (le_trans hk' hk)).2.1
  have hPDall : ∀ k' ≤ k, |iteratedDeriv k' (fun u : ℝ => (u * t + h u) - u * t) a| ≤ δ :=
    fun k' hk' => (P_bounds hh hδ0 hδ1 hjet (a := a) (t := t) ha ht (k := k')
      (le_trans hk' (by omega : k ≤ K))).2.2
  have hQDall : ∀ k' ≤ k, |iteratedDeriv k' (fun u : ℝ => (t + deriv h u) - t) a| ≤ δ :=
    fun k' hk' => (Q_bounds hh hδ0 hδ1 hK hjet (a := a) (t := t) ha ht (k := k')
      (le_trans hk' hk)).2.2
  have hP0eq : (fun u : ℝ => u * t + (0:ℝ→ℝ) u) = fun u : ℝ => u * t := by funext u; simp
  have hQ0eq : (fun u : ℝ => t + deriv (0:ℝ→ℝ) u) = fun u : ℝ => t := by
    funext u; simp
  have hsubst1 : (fun a' : ℝ => ZradS h (a', σ, t))
      = fun a' : ℝ => -2 * ((a' * t + h a') * (t + deriv h a')) := by
    funext u; exact ZradS_sec hh σ t u
  have hsubst2 : (fun a' : ℝ => ZradS (0:ℝ→ℝ) (a', σ, t))
      = fun a' : ℝ => -2 * ((a' * t + (0:ℝ→ℝ) a') * (t + deriv (0:ℝ→ℝ) a')) := by
    funext u; exact ZradS_sec hh0 σ t u
  have hfun1 : (fun a' : ℝ => -2 * ((a' * t + h a') * (t + deriv h a')))
      = fun a' : ℝ => (-2 : ℝ) * (((fun u : ℝ => u * t + h u) * (fun u : ℝ => t + deriv h u)) a') := by
    funext u; rw [mul_apply']
  have hfun2 : (fun a' : ℝ => -2 * ((a' * t + (0:ℝ→ℝ) a') * (t + deriv (0:ℝ→ℝ) a')))
      = fun a' : ℝ => (-2 : ℝ) *
        (((fun u : ℝ => u * t + (0:ℝ→ℝ) u) * (fun u : ℝ => t + deriv (0:ℝ→ℝ) u)) a') := by
    funext u; rw [mul_apply']
  rw [hsubst1, hsubst2, hfun1, hfun2, hP0eq, hQ0eq,
    iteratedDeriv_const_mul (n := k) (x := a) (c := (-2:ℝ))
      (f := (fun u : ℝ => u * t + h u) * (fun u : ℝ => t + deriv h u))
      (((contDiff_P_top hh t).mul (contDiff_Q_top hh t)).contDiffAt.of_le
        (Work.OddVolterra.Existence.coe_nat_le_infty k)),
    iteratedDeriv_const_mul (n := k) (x := a) (c := (-2:ℝ))
      (f := (fun u : ℝ => u * t) * (fun u : ℝ => t))
      (((contDiff_P0_top t).mul contDiff_const).contDiffAt.of_le
        (Work.OddVolterra.Existence.coe_nat_le_infty k))]
  have hgoal : (-2 : ℝ) * iteratedDeriv k ((fun u : ℝ => u * t + h u) * (fun u : ℝ => t + deriv h u)) a
      - (-2 : ℝ) * iteratedDeriv k ((fun u : ℝ => u * t) * (fun u : ℝ => t)) a
      = (-2 : ℝ) * (iteratedDeriv k ((fun u : ℝ => u * t + h u) * (fun u : ℝ => t + deriv h u)) a
          - iteratedDeriv k ((fun u : ℝ => u * t) * (fun u : ℝ => t)) a) := by ring
  rw [hgoal, abs_mul, show |(-2:ℝ)| = 2 by norm_num]
  have hprod := product_sub_bound (f₁ := fun u : ℝ => u * t + h u) (f₂ := fun u : ℝ => u * t)
    (g₁ := fun u : ℝ => t + deriv h u) (g₂ := fun u : ℝ => t) (x := a) (j := k)
    hPall hQ0all hPDall hQDall
    ((contDiff_P_top hh t).contDiffAt.of_le (Work.OddVolterra.Existence.coe_nat_le_infty k))
    ((contDiff_P0_top t).contDiffAt.of_le (Work.OddVolterra.Existence.coe_nat_le_infty k))
    ((contDiff_Q_top hh t).contDiffAt.of_le (Work.OddVolterra.Existence.coe_nat_le_infty k))
    ((contDiff_const : ContDiff ℝ (⊤:ℕ∞) (fun _ : ℝ => t)).contDiffAt.of_le
      (Work.OddVolterra.Existence.coe_nat_le_infty k))
    (by norm_num) (by norm_num) hδ0 hδ0
  refine le_trans (mul_le_mul_of_nonneg_left hprod (by norm_num)) ?_
  have hpow : (0:ℝ) ≤ 2 ^ k := by positivity
  nlinarith [hpow, hδ0]





theorem zrad_bounds (Nj : ℕ) (hNj : 1 ≤ Nj) :
    ∃ Zb Zd Zb' Zd' : ℕ → ℝ,
      (∀ i, 0 ≤ Zb i) ∧ (∀ i, 0 ≤ Zd i) ∧ (∀ i, 0 ≤ Zb' i) ∧ (∀ i, 0 ≤ Zd' i) ∧
      ∀ h : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) h →
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 100 →
      (∀ k ≤ Nj, ∀ x : ℝ, |iteratedDeriv k h x| ≤ δ) →
      ∀ a ∈ Set.Icc (1/2 : ℝ) 1, ∀ σ ∈ Set.Icc (1/2 : ℝ) 1,
      ∀ t ∈ Set.Icc (-(3/2) : ℝ) (3/2), ∀ i ≤ Nj - 1,
        |iteratedDeriv i (fun a' : ℝ => Zrad h (a', σ, t)) a| ≤ Zb i ∧
        |iteratedDeriv i (fun a' : ℝ => Zrad h (a', σ, t)) a -
          iteratedDeriv i (fun a' : ℝ => Zrad (0 : ℝ → ℝ) (a', σ, t)) a| ≤ Zd i * δ ∧
        |iteratedDeriv i (fun a' : ℝ => ZradS h (a', σ, t)) a| ≤ Zb' i ∧
        |iteratedDeriv i (fun a' : ℝ => ZradS h (a', σ, t)) a -
          iteratedDeriv i (fun a' : ℝ => ZradS (0 : ℝ → ℝ) (a', σ, t)) a| ≤ Zd' i * δ := by
  refine ⟨fun i => (151/100)^2 * (2 + 2^i), fun i => 4 + 2 * (151/100 + 3/2) * 2^i,
    fun i => 2 * (151/100)^2 * 2^i, fun i => 2 * (151/100 + 3/2) * 2^i, ?_⟩
  refine ⟨fun i => by positivity, fun i => by positivity, fun i => by positivity,
    fun i => by positivity, ?_⟩
  intro h hh δ hδ hδ1 hjet a ha σ hσ t ht i hi
  have ha' : |a| ≤ 1 := by rw [abs_le]; exact ⟨by linarith [ha.1], ha.2⟩
  have hσ' : |σ| ≤ 1 := by rw [abs_le]; exact ⟨by linarith [hσ.1], hσ.2⟩
  have ht' : |t| ≤ 3/2 := by rw [abs_le]; exact ht
  have hiK : i ≤ Nj := by omega
  exact ⟨Zrad_deriv_bound hh hδ.le hδ1 hjet ha' hσ' ht' hiK,
    Zrad_deriv_diff_bound hh hδ.le hδ1 hjet ha' hσ' ht' hiK,
    ZradS_deriv_bound hh hδ.le hδ1 hNj hjet ha' hσ' ht' hi,
    ZradS_deriv_diff_bound hh hδ.le hδ1 hNj hjet ha' hσ' ht' hi⟩





/-- Uniform (order-independent) version of `zrad_bounds`. -/
theorem zrad_bounds_uniform (Nj : ℕ) (hNj : 1 ≤ Nj) :
    ∃ Zb Zd Zb' Zd' : ℝ, 0 ≤ Zb ∧ 0 ≤ Zd ∧ 0 ≤ Zb' ∧ 0 ≤ Zd' ∧
      ∀ h : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) h →
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 100 →
      (∀ k ≤ Nj, ∀ x : ℝ, |iteratedDeriv k h x| ≤ δ) →
      ∀ a ∈ Set.Icc (1/2 : ℝ) 1, ∀ σ ∈ Set.Icc (1/2 : ℝ) 1,
      ∀ t ∈ Set.Icc (-(3/2) : ℝ) (3/2), ∀ i ≤ Nj - 1,
        |iteratedDeriv i (fun a' : ℝ => Zrad h (a', σ, t)) a| ≤ Zb ∧
        |iteratedDeriv i (fun a' : ℝ => Zrad h (a', σ, t)) a -
          iteratedDeriv i (fun a' : ℝ => Zrad (0 : ℝ → ℝ) (a', σ, t)) a| ≤ Zd * δ ∧
        |iteratedDeriv i (fun a' : ℝ => ZradS h (a', σ, t)) a| ≤ Zb' ∧
        |iteratedDeriv i (fun a' : ℝ => ZradS h (a', σ, t)) a -
          iteratedDeriv i (fun a' : ℝ => ZradS (0 : ℝ → ℝ) (a', σ, t)) a| ≤ Zd' * δ := by
  refine ⟨(151/100)^2 * (2 + 2^(Nj-1)), 4 + 2 * (151/100 + 3/2) * 2^(Nj-1),
    2 * (151/100)^2 * 2^(Nj-1), 2 * (151/100 + 3/2) * 2^(Nj-1),
    by positivity, by positivity, by positivity, by positivity, ?_⟩
  intro h hh δ hδ hδ1 hjet a ha σ hσ t ht i hi
  have ha' : |a| ≤ 1 := by rw [abs_le]; exact ⟨by linarith [ha.1], ha.2⟩
  have hσ' : |σ| ≤ 1 := by rw [abs_le]; exact ⟨by linarith [hσ.1], hσ.2⟩
  have ht' : |t| ≤ 3/2 := by rw [abs_le]; exact ht
  have hiK : i ≤ Nj := by omega
  have hpow : (2:ℝ)^i ≤ 2^(Nj-1) := by
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  have h1 := Zrad_deriv_bound hh hδ.le hδ1 hjet ha' hσ' ht' hiK
  have h2 := Zrad_deriv_diff_bound hh hδ.le hδ1 hjet ha' hσ' ht' hiK
  have h3 := ZradS_deriv_bound hh hδ.le hδ1 hNj hjet ha' hσ' ht' hi
  have h4 := ZradS_deriv_diff_bound hh hδ.le hδ1 hNj hjet ha' hσ' ht' hi
  refine ⟨le_trans h1 ?_, le_trans h2 ?_, le_trans h3 ?_, le_trans h4 ?_⟩
  · have : (0:ℝ) ≤ 2 ^ i := by positivity
    nlinarith [hpow]
  · have : (0:ℝ) ≤ 2 ^ i := by positivity
    nlinarith [hpow, hδ.le]
  · have : (0:ℝ) ≤ 2 ^ i := by positivity
    nlinarith [hpow]
  · have : (0:ℝ) ≤ 2 ^ i := by positivity
    nlinarith [hpow, hδ.le]





lemma product_bound_sm {f g : ℝ → ℝ} (hfs : ContDiff ℝ (⊤ : ℕ∞) f) (hgs : ContDiff ℝ (⊤ : ℕ∞) g)
    {x : ℝ} {j : ℕ} {Bf Bg : ℝ}
    (hf : ∀ k ≤ j, |iteratedDeriv k f x| ≤ Bf) (hg : ∀ k ≤ j, |iteratedDeriv k g x| ≤ Bg)
    (hBf : 0 ≤ Bf) (hBg : 0 ≤ Bg) :
    |iteratedDeriv j (fun y => f y * g y) x| ≤ Bf * Bg * 2 ^ j := by
  have hfd : ContDiffAt ℝ (j : ℕ∞ω) f x :=
    (hfs.contDiffAt).of_le (Work.OddVolterra.Existence.coe_nat_le_infty j)
  have hgd : ContDiffAt ℝ (j : ℕ∞ω) g x :=
    (hgs.contDiffAt).of_le (Work.OddVolterra.Existence.coe_nat_le_infty j)
  have key : iteratedDeriv j (fun y => f y * g y) x
      = ∑ i ∈ Finset.range (j + 1), ↑(j.choose i) * iteratedDeriv i f x * iteratedDeriv (j - i) g x :=
    iteratedDeriv_mul (n := j) (x := x) hfd hgd
  rw [key]
  calc |∑ i ∈ Finset.range (j + 1), ↑(j.choose i) * iteratedDeriv i f x * iteratedDeriv (j - i) g x|
      ≤ ∑ i ∈ Finset.range (j + 1), |↑(j.choose i) * iteratedDeriv i f x * iteratedDeriv (j - i) g x| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * (Bf * Bg) := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hi' : i ≤ j := by simpa [Finset.mem_range] using hi
        have h1 : |iteratedDeriv i f x| ≤ Bf := hf i hi'
        have h2 : |iteratedDeriv (j - i) g x| ≤ Bg := hg (j - i) (by omega)
        have h3 : (0:ℝ) ≤ (j.choose i : ℝ) := by positivity
        rw [abs_mul, abs_mul, abs_of_nonneg h3]
        calc (j.choose i : ℝ) * |iteratedDeriv i f x| * |iteratedDeriv (j - i) g x|
            ≤ (j.choose i : ℝ) * Bf * Bg := by
              refine mul_le_mul (mul_le_mul_of_nonneg_left h1 h3) h2 (abs_nonneg _) (by positivity)
          _ = (j.choose i : ℝ) * (Bf * Bg) := by ring
    _ = Bf * Bg * 2 ^ j := by
        have hsum : (∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ)) = (2:ℝ) ^ j := by
          rw [← Nat.cast_sum, Nat.sum_range_choose]
          norm_num
        rw [← Finset.sum_mul, hsum]
        ring

/-- Leibniz bound for a difference of products, with globally smooth factors. -/
lemma product_sub_bound_sm {f₁ f₂ g₁ g₂ : ℝ → ℝ}
    (hf₁s : ContDiff ℝ (⊤ : ℕ∞) f₁) (hf₂s : ContDiff ℝ (⊤ : ℕ∞) f₂)
    (hg₁s : ContDiff ℝ (⊤ : ℕ∞) g₁) (hg₂s : ContDiff ℝ (⊤ : ℕ∞) g₂)
    {x : ℝ} {j : ℕ} {Bf Bg Df Dg : ℝ}
    (hf : ∀ k ≤ j, |iteratedDeriv k f₁ x| ≤ Bf) (hg : ∀ k ≤ j, |iteratedDeriv k g₂ x| ≤ Bg)
    (hDf : ∀ k ≤ j, |iteratedDeriv k (fun y => f₁ y - f₂ y) x| ≤ Df)
    (hDg : ∀ k ≤ j, |iteratedDeriv k (fun y => g₁ y - g₂ y) x| ≤ Dg)
    (hBf : 0 ≤ Bf) (hBg : 0 ≤ Bg) (hDf0 : 0 ≤ Df) (hDg0 : 0 ≤ Dg) :
    |iteratedDeriv j (fun y => f₁ y * g₁ y) x - iteratedDeriv j (fun y => f₂ y * g₂ y) x| ≤
      (Bf * Dg + Df * Bg) * 2 ^ j := by
  have hEq : (fun y => f₁ y * g₁ y) - (fun y => f₂ y * g₂ y)
      = (fun y => f₁ y * (g₁ y - g₂ y)) + (fun y => (f₁ y - f₂ y) * g₂ y) := by
    funext y
    simp only [Pi.sub_apply, Pi.add_apply]
    ring
  have hcd1 : ContDiffAt ℝ (j : ℕ∞ω) f₁ x :=
    (hf₁s.contDiffAt).of_le (Work.OddVolterra.Existence.coe_nat_le_infty j)
  have hcd2 : ContDiffAt ℝ (j : ℕ∞ω) f₂ x :=
    (hf₂s.contDiffAt).of_le (Work.OddVolterra.Existence.coe_nat_le_infty j)
  have hcd3 : ContDiffAt ℝ (j : ℕ∞ω) g₁ x :=
    (hg₁s.contDiffAt).of_le (Work.OddVolterra.Existence.coe_nat_le_infty j)
  have hcd4 : ContDiffAt ℝ (j : ℕ∞ω) g₂ x :=
    (hg₂s.contDiffAt).of_le (Work.OddVolterra.Existence.coe_nat_le_infty j)
  have hsub := iteratedDeriv_sub (n := j) (x := x) (hcd1.mul hcd3) (hcd2.mul hcd4)
  have hadd := iteratedDeriv_add (n := j) (x := x) (hcd1.mul (hcd3.sub hcd4)) ((hcd1.sub hcd2).mul hcd4)
  rw [← hsub, hEq, hadd]
  refine le_trans (abs_add_le _ _) ?_
  have h1 : |iteratedDeriv j (fun y => f₁ y * (g₁ y - g₂ y)) x| ≤ Bf * Dg * 2 ^ j :=
    product_bound_sm hf₁s (hg₁s.sub hg₂s) (fun k hk => hf k hk) (fun k hk => hDg k hk) hBf hDg0
  have h2 : |iteratedDeriv j (fun y => (f₁ y - f₂ y) * g₂ y) x| ≤ Df * Bg * 2 ^ j :=
    product_bound_sm (hf₁s.sub hf₂s) hg₂s (fun k hk => hDf k hk) (fun k hk => hg k hk) hDf0 hBg
  linarith




lemma contDiff_Rnu_sec {ν : ℝ} {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    {init : ℝ × ℝ × ℝ → ℝ} (hinit : ContDiff ℝ (⊤ : ℕ∞) init) (m : ℕ) (σ t : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun u : ℝ => Rnu ν h init m (u, σ, t)) :=
  (Rnu_contDiff ν hh hinit m).comp (by fun_prop)

lemma contDiff_ZradS_sec {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) (σ t : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun a : ℝ => ZradS h (a, σ, t)) :=
  (contDiff_fderiv_fst (Zrad_contDiff h hh)).comp (by fun_prop)

theorem rnu_bounds (ν : ℝ) (Nj shift : ℕ)
    (initH : (ℝ → ℝ) → ℝ × ℝ × ℝ → ℝ)
    (hinitdiff : ∀ h : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) h → ContDiff ℝ (⊤ : ℕ∞) (initH h))
    (A0 D0 : ℕ → ℝ) (hA0 : ∀ j, 0 ≤ A0 j) (hD0 : ∀ j, 0 ≤ D0 j)
    (hbase : ∀ h : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) h → ∀ δ : ℝ, 0 < δ → δ ≤ 1/100 →
      (∀ k ≤ Nj, ∀ x : ℝ, |iteratedDeriv k h x| ≤ δ) →
      ∀ a ∈ Set.Icc (1/2 : ℝ) 1, ∀ σ ∈ Set.Icc (1/2 : ℝ) 1, ∀ t ∈ Set.Icc (-(3/2) : ℝ) (3/2),
      ∀ j, j + shift ≤ Nj → ∀ k ≤ j,
        |iteratedDeriv k (fun a' : ℝ => initH h (a', σ, t)) a| ≤ A0 j ∧
        |iteratedDeriv k (fun a' : ℝ => initH h (a', σ, t)) a -
          iteratedDeriv k (fun a' : ℝ => initH 0 (a', σ, t)) a| ≤ D0 j * δ) :
    ∀ M : ℕ, M + shift ≤ Nj →
      ∃ A D : ℕ → ℝ, (∀ j, 0 ≤ A j) ∧ (∀ j, 0 ≤ D j) ∧
      ∀ h : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) h → ∀ δ : ℝ, 0 < δ → δ ≤ 1/100 →
      (∀ k ≤ Nj, ∀ x : ℝ, |iteratedDeriv k h x| ≤ δ) →
      ∀ a ∈ Set.Icc (1/2 : ℝ) 1, ∀ σ ∈ Set.Icc (1/2 : ℝ) 1, ∀ t ∈ Set.Icc (-(3/2) : ℝ) (3/2),
      ∀ j, j + M + shift ≤ Nj → ∀ k ≤ j,
        |iteratedDeriv k (fun a' : ℝ => Rnu ν h (initH h) M (a', σ, t)) a| ≤ A j ∧
        |iteratedDeriv k (fun a' : ℝ => Rnu ν h (initH h) M (a', σ, t)) a -
          iteratedDeriv k (fun a' : ℝ => Rnu ν (0 : ℝ → ℝ) (initH 0) M (a', σ, t)) a| ≤ D j * δ := by
  intro M
  induction M with
  | zero =>
      intro hM
      refine ⟨A0, D0, hA0, hD0, ?_⟩
      intro h hh δ hδ hδ1 hjet a ha σ hσ t ht j hj k hk
      have hj' : j + shift ≤ Nj := by omega
      obtain ⟨hb1, hb2⟩ := hbase h hh δ hδ hδ1 hjet a ha σ hσ t ht j hj' k hk
      have hrw : Rnu ν h (initH h) 0 = initH h := Rnu.eq_1 ν h (initH h)
      have hrw0 : Rnu ν (0:ℝ→ℝ) (initH 0) 0 = initH 0 := Rnu.eq_1 ν (0:ℝ→ℝ) (initH 0)
      rw [hrw, hrw0]
      exact ⟨hb1, hb2⟩
  | succ M ih =>
      intro hM
      obtain ⟨Zb, Zd, Zb', Zd', hZb0, hZd0, hZb'0, hZd'0, hZ⟩ := zrad_bounds_uniform Nj (by omega)
      obtain ⟨A, D, hA0', hD0', hAD⟩ := ih (by omega)
      refine ⟨fun j => 2^j * (Zb * A (j+1) + |ν - M| * Zb' * A j),
        fun j => 2^j * (Zb * D (j+1) + Zd * A (j+1) + |ν - M| * (Zb' * D j + Zd' * A j)),
        (fun j => mul_nonneg (pow_nonneg (by norm_num) j)
          (add_nonneg (mul_nonneg hZb0 (hA0' (j+1))) (mul_nonneg (mul_nonneg (abs_nonneg _) hZb'0) (hA0' j)))),
        (fun j => mul_nonneg (pow_nonneg (by norm_num) j)
          (add_nonneg (add_nonneg (mul_nonneg hZb0 (hD0' (j+1))) (mul_nonneg hZd0 (hA0' (j+1))))
            (mul_nonneg (abs_nonneg _) (add_nonneg (mul_nonneg hZb'0 (hD0' j)) (mul_nonneg hZd'0 (hA0' j)))))),
        ?_⟩
      intro h hh δ hδ hδ1 hjet a ha σ hσ t ht j hj k hk
      have ha1 : |a| ≤ 1 := by rw [abs_le]; exact ⟨by linarith [ha.1], ha.2⟩
      have hσ1 : |σ| ≤ 1 := by rw [abs_le]; exact ⟨by linarith [hσ.1], hσ.2⟩
      have ht1 : |t| ≤ 3/2 := by rw [abs_le]; exact ht
      have hjet0 : ∀ k ≤ Nj, ∀ x : ℝ, |iteratedDeriv k (0:ℝ→ℝ) x| ≤ δ := by
        intro k hk x; simp [hδ.le]
      -- the IH at level M, orders up to j+1, for h and for 0
      have hj1 : (j+1) + M + shift ≤ Nj := by omega
      have hIHh := hAD h hh δ hδ hδ1 hjet a ha σ hσ t ht (j+1) hj1
      have hIH0 := hAD (0:ℝ→ℝ) (contDiff_const) δ hδ hδ1 hjet0 a ha σ hσ t ht (j+1) hj1
      -- the recursion identity
      have hRnu_eq : (fun a' : ℝ => Rnu ν h (initH h) (M+1) (a', σ, t))
          = fun a' : ℝ => Zrad h (a', σ, t) * deriv (fun u : ℝ => Rnu ν h (initH h) M (u, σ, t)) a'
              + (ν - M) * (ZradS h (a', σ, t) * Rnu ν h (initH h) M (a', σ, t)) := by
        funext a'
        have hd1 : DifferentiableAt ℝ (Rnu ν h (initH h) M) (a', σ, t) :=
          ((Rnu_contDiff ν hh (hinitdiff h hh) M).differentiable (by simp)) _
        rw [show M + 1 = M.succ from rfl, Rnu.eq_2]
        dsimp only
        rw [fderiv_fst_eq_deriv _ a' σ t hd1]
        simp only [ZradS]
        ring
      have hZall : ∀ i ≤ j, |iteratedDeriv i (fun a' : ℝ => Zrad h (a', σ, t)) a| ≤ Zb :=
        fun i hi => (hZ h hh δ hδ hδ1 hjet a ha σ hσ t ht i (by omega)).1
      have hZdiff : ∀ i ≤ j, |iteratedDeriv i (fun a' : ℝ => Zrad h (a', σ, t)) a -
          iteratedDeriv i (fun a' : ℝ => Zrad (0:ℝ→ℝ) (a', σ, t)) a| ≤ Zd * δ :=
        fun i hi => (hZ h hh δ hδ hδ1 hjet a ha σ hσ t ht i (by omega)).2.1
      have hZ'all : ∀ i ≤ j, |iteratedDeriv i (fun a' : ℝ => ZradS h (a', σ, t)) a| ≤ Zb' :=
        fun i hi => (hZ h hh δ hδ hδ1 hjet a ha σ hσ t ht i (by omega)).2.2.1
      have hZ'diff : ∀ i ≤ j, |iteratedDeriv i (fun a' : ℝ => ZradS h (a', σ, t)) a -
          iteratedDeriv i (fun a' : ℝ => ZradS (0:ℝ→ℝ) (a', σ, t)) a| ≤ Zd' * δ :=
        fun i hi => (hZ h hh δ hδ hδ1 hjet a ha σ hσ t ht i (by omega)).2.2.2
      have hFh : ∀ i ≤ j+1, |iteratedDeriv i (fun u : ℝ => Rnu ν h (initH h) M (u, σ, t)) a| ≤ A (j+1) :=
        fun i hi => (hIHh i hi).1
      have hF0 : ∀ i ≤ j+1, |iteratedDeriv i (fun u : ℝ => Rnu ν (0:ℝ→ℝ) (initH 0) M (u, σ, t)) a| ≤ A (j+1) :=
        fun i hi => (hIH0 i hi).1
      have hDF : ∀ i ≤ j+1, |iteratedDeriv i (fun u : ℝ => Rnu ν h (initH h) M (u, σ, t)) a -
          iteratedDeriv i (fun u : ℝ => Rnu ν (0:ℝ→ℝ) (initH 0) M (u, σ, t)) a| ≤ D (j+1) * δ :=
        fun i hi => (hIHh i hi).2
      have hderivF : ∀ i ≤ j, |iteratedDeriv i (deriv (fun u : ℝ => Rnu ν h (initH h) M (u, σ, t))) a| ≤ A (j+1) := by
        intro i hi
        rw [← iteratedDeriv_succ' (n := i) (f := fun u : ℝ => Rnu ν h (initH h) M (u, σ, t))]
        exact hFh (i+1) (by omega)
      have hderivF0 : ∀ i ≤ j, |iteratedDeriv i (deriv (fun u : ℝ => Rnu ν (0:ℝ→ℝ) (initH 0) M (u, σ, t))) a| ≤ A (j+1) := by
        intro i hi
        rw [← iteratedDeriv_succ' (n := i) (f := fun u : ℝ => Rnu ν (0:ℝ→ℝ) (initH 0) M (u, σ, t))]
        exact hF0 (i+1) (by omega)
      have hderivDF0 : ∀ i ≤ j, |iteratedDeriv i (deriv (fun u : ℝ => Rnu ν h (initH h) M (u, σ, t))) a -
          iteratedDeriv i (deriv (fun u : ℝ => Rnu ν (0:ℝ→ℝ) (initH 0) M (u, σ, t))) a| ≤ D (j+1) * δ := by
        intro i hi
        have hg : (fun u : ℝ => Rnu ν h (initH h) M (u, σ, t)) - (fun u : ℝ => Rnu ν (0:ℝ→ℝ) (initH 0) M (u, σ, t))
            = fun u : ℝ => (Rnu ν h (initH h) M (u, σ, t) - Rnu ν (0:ℝ→ℝ) (initH 0) M (u, σ, t)) := rfl
        have h1 : iteratedDeriv i (deriv (fun u : ℝ => Rnu ν h (initH h) M (u, σ, t)))
              a - iteratedDeriv i (deriv (fun u : ℝ => Rnu ν (0:ℝ→ℝ) (initH 0) M (u, σ, t))) a
            = iteratedDeriv (i+1) (fun u : ℝ => Rnu ν h (initH h) M (u, σ, t)) a
              - iteratedDeriv (i+1) (fun u : ℝ => Rnu ν (0:ℝ→ℝ) (initH 0) M (u, σ, t)) a := by
          rw [← iteratedDeriv_succ' (n := i) (f := fun u : ℝ => Rnu ν h (initH h) M (u, σ, t)),
            ← iteratedDeriv_succ' (n := i) (f := fun u : ℝ => Rnu ν (0:ℝ→ℝ) (initH 0) M (u, σ, t))]
        rw [h1]
        exact hDF (i+1) (by omega)
      -- smoothness facts
      have hZd : ContDiff ℝ (⊤ : ℕ∞) (fun a' : ℝ => Zrad h (a', σ, t)) :=
        (Zrad_contDiff h hh).comp (by fun_prop)
      have hZs : ContDiff ℝ (⊤ : ℕ∞) (fun a' : ℝ => ZradS h (a', σ, t)) :=
        contDiff_ZradS_sec hh σ t
      have hFs : ContDiff ℝ (⊤ : ℕ∞) (fun u : ℝ => Rnu ν h (initH h) M (u, σ, t)) :=
        contDiff_Rnu_sec (ν := ν) (h := h) hh (init := initH h) (hinitdiff h hh) M σ t
      have hdFs : ContDiff ℝ (⊤ : ℕ∞) (deriv (fun u : ℝ => Rnu ν h (initH h) M (u, σ, t))) := by
        have := hFs.iterate_deriv 1
        simpa only [Function.iterate_one] using this
      have hZ0 : ContDiff ℝ (⊤ : ℕ∞) (fun a' : ℝ => Zrad (0:ℝ→ℝ) (a', σ, t)) :=
        (Zrad_contDiff (0:ℝ→ℝ) contDiff_const).comp (by fun_prop)
      have hZs0 : ContDiff ℝ (⊤ : ℕ∞) (fun a' : ℝ => ZradS (0:ℝ→ℝ) (a', σ, t)) :=
        contDiff_ZradS_sec (h := (0:ℝ→ℝ)) contDiff_const σ t
      have hFs0 : ContDiff ℝ (⊤ : ℕ∞) (fun u : ℝ => Rnu ν (0:ℝ→ℝ) (initH 0) M (u, σ, t)) :=
        contDiff_Rnu_sec (ν := ν) (h := (0:ℝ→ℝ)) contDiff_const (init := initH 0)
          (hinitdiff 0 contDiff_const) M σ t
      have hdFs0 : ContDiff ℝ (⊤ : ℕ∞) (deriv (fun u : ℝ => Rnu ν (0:ℝ→ℝ) (initH 0) M (u, σ, t))) := by
        have := hFs0.iterate_deriv 1
        simpa only [Function.iterate_one] using this
      -- telescoped difference bounds (as derivatives of the pointwise differences)
      have hZdiff' : ∀ i ≤ j, |iteratedDeriv i (fun y : ℝ => Zrad h (y, σ, t) - Zrad (0:ℝ→ℝ) (y, σ, t)) a| ≤ Zd * δ := by
        intro i hi
        have hfix : (fun y : ℝ => Zrad h (y, σ, t) - Zrad (0:ℝ→ℝ) (y, σ, t))
            = (fun y : ℝ => Zrad h (y, σ, t)) - (fun y : ℝ => Zrad (0:ℝ→ℝ) (y, σ, t)) := rfl
        rw [hfix, iteratedDeriv_sub (n := i) (x := a)
          (hZd.contDiffAt.of_le (Work.OddVolterra.Existence.coe_nat_le_infty i))
          (hZ0.contDiffAt.of_le (Work.OddVolterra.Existence.coe_nat_le_infty i))]
        exact hZdiff i hi
      have hZ'diff' : ∀ i ≤ j, |iteratedDeriv i (fun y : ℝ => ZradS h (y, σ, t) - ZradS (0:ℝ→ℝ) (y, σ, t)) a| ≤ Zd' * δ := by
        intro i hi
        have hfix : (fun y : ℝ => ZradS h (y, σ, t) - ZradS (0:ℝ→ℝ) (y, σ, t))
            = (fun y : ℝ => ZradS h (y, σ, t)) - (fun y : ℝ => ZradS (0:ℝ→ℝ) (y, σ, t)) := rfl
        rw [hfix, iteratedDeriv_sub (n := i) (x := a)
          (hZs.contDiffAt.of_le (Work.OddVolterra.Existence.coe_nat_le_infty i))
          (hZs0.contDiffAt.of_le (Work.OddVolterra.Existence.coe_nat_le_infty i))]
        exact hZ'diff i hi
      have hZall0 : ∀ i ≤ j, |iteratedDeriv i (fun a' : ℝ => Zrad (0:ℝ→ℝ) (a', σ, t)) a| ≤ Zb :=
        fun i hi => (hZ (0:ℝ→ℝ) contDiff_const δ hδ hδ1 hjet0 a ha σ hσ t ht i (by omega)).1
      have hZ'all0 : ∀ i ≤ j, |iteratedDeriv i (fun a' : ℝ => ZradS (0:ℝ→ℝ) (a', σ, t)) a| ≤ Zb' :=
        fun i hi => (hZ (0:ℝ→ℝ) contDiff_const δ hδ hδ1 hjet0 a ha σ hσ t ht i (by omega)).2.2.1
      have hfj : j + M + shift ≤ Nj := by omega
      have hFj : ∀ i ≤ j, |iteratedDeriv i (fun u : ℝ => Rnu ν h (initH h) M (u, σ, t)) a| ≤ A j :=
        fun i hi => (hAD h hh δ hδ hδ1 hjet a ha σ hσ t ht j hfj i hi).1
      have hF0j : ∀ i ≤ j, |iteratedDeriv i (fun u : ℝ => Rnu ν (0:ℝ→ℝ) (initH 0) M (u, σ, t)) a| ≤ A j :=
        fun i hi => (hAD (0:ℝ→ℝ) contDiff_const δ hδ hδ1 hjet0 a ha σ hσ t ht j hfj i hi).1
      have hDFj : ∀ i ≤ j, |iteratedDeriv i (fun u : ℝ => Rnu ν h (initH h) M (u, σ, t)) a -
          iteratedDeriv i (fun u : ℝ => Rnu ν (0:ℝ→ℝ) (initH 0) M (u, σ, t)) a| ≤ D j * δ :=
        fun i hi => (hAD h hh δ hδ hδ1 hjet a ha σ hσ t ht j hfj i hi).2
      have hDFj' : ∀ i ≤ j, |iteratedDeriv i (fun y : ℝ => Rnu ν h (initH h) M (y, σ, t) -
          Rnu ν (0:ℝ→ℝ) (initH 0) M (y, σ, t)) a| ≤ D j * δ := by
        intro i hi
        have hfix : (fun y : ℝ => Rnu ν h (initH h) M (y, σ, t) - Rnu ν (0:ℝ→ℝ) (initH 0) M (y, σ, t))
            = (fun y : ℝ => Rnu ν h (initH h) M (y, σ, t)) - (fun y : ℝ => Rnu ν (0:ℝ→ℝ) (initH 0) M (y, σ, t)) := rfl
        rw [hfix, iteratedDeriv_sub (n := i) (x := a)
          (hFs.contDiffAt.of_le (Work.OddVolterra.Existence.coe_nat_le_infty i))
          (hFs0.contDiffAt.of_le (Work.OddVolterra.Existence.coe_nat_le_infty i))]
        exact hDFj i hi
      have hderivDF' : ∀ i ≤ j, |iteratedDeriv i (fun y : ℝ => deriv (fun u : ℝ => Rnu ν h (initH h) M (u, σ, t)) y -
          deriv (fun u : ℝ => Rnu ν (0:ℝ→ℝ) (initH 0) M (u, σ, t)) y) a| ≤ D (j+1) * δ := by
        intro i hi
        have hfix : (fun y : ℝ => deriv (fun u : ℝ => Rnu ν h (initH h) M (u, σ, t)) y -
            deriv (fun u : ℝ => Rnu ν (0:ℝ→ℝ) (initH 0) M (u, σ, t)) y)
            = (deriv (fun u : ℝ => Rnu ν h (initH h) M (u, σ, t)))
              - (deriv (fun u : ℝ => Rnu ν (0:ℝ→ℝ) (initH 0) M (u, σ, t))) := rfl
        rw [hfix, iteratedDeriv_sub (n := i) (x := a)
          (hdFs.contDiffAt.of_le (Work.OddVolterra.Existence.coe_nat_le_infty i))
          (hdFs0.contDiffAt.of_le (Work.OddVolterra.Existence.coe_nat_le_infty i))]
        exact hderivDF0 i hi
      -- the value bound
      have hval : |iteratedDeriv k (fun a' : ℝ => Rnu ν h (initH h) (M+1) (a', σ, t)) a|
          ≤ 2^j * (Zb * A (j+1) + |ν - M| * Zb' * A j) := by
        rw [hRnu_eq]
        have hc1 : ContDiffAt ℝ (k : ℕ∞ω) (fun a' : ℝ => Zrad h (a', σ, t) *
            deriv (fun u : ℝ => Rnu ν h (initH h) M (u, σ, t)) a') a :=
          ((hZd.mul hdFs).contDiffAt).of_le
            (Work.OddVolterra.Existence.coe_nat_le_infty k)
        have hc2 : ContDiffAt ℝ (k : ℕ∞ω) (fun a' : ℝ => (ν - M) *
            (ZradS h (a', σ, t) * Rnu ν h (initH h) M (a', σ, t))) a :=
          ((contDiff_const.mul (hZs.mul hFs)).contDiffAt).of_le
            (Work.OddVolterra.Existence.coe_nat_le_infty k)
        have hsum : (fun a' : ℝ => Zrad h (a', σ, t) * deriv (fun u : ℝ => Rnu ν h (initH h) M (u, σ, t)) a'
              + (ν - M) * (ZradS h (a', σ, t) * Rnu ν h (initH h) M (a', σ, t)))
            = (fun a' : ℝ => Zrad h (a', σ, t) * deriv (fun u : ℝ => Rnu ν h (initH h) M (u, σ, t)) a')
              + (fun a' : ℝ => (ν - M) * (ZradS h (a', σ, t) * Rnu ν h (initH h) M (a', σ, t))) := rfl
        rw [hsum, iteratedDeriv_add (n := k) (x := a) hc1 hc2]
        rw [iteratedDeriv_const_mul (n := k) (x := a) (c := ν - M)
          (((hZs.mul hFs).contDiffAt).of_le (Work.OddVolterra.Existence.coe_nat_le_infty k))]
        have hp1 : |iteratedDeriv k (fun a' : ℝ => Zrad h (a', σ, t) *
            deriv (fun u : ℝ => Rnu ν h (initH h) M (u, σ, t)) a') a| ≤ Zb * A (j+1) * 2^k :=
          product_bound_sm (j := k) hZd hdFs (fun i hi => hZall i (le_trans hi hk))
            (fun i hi => hderivF i (le_trans hi hk)) hZb0 (hA0' (j+1))
        have hp2 : |iteratedDeriv k (fun a' : ℝ => ZradS h (a', σ, t) *
            Rnu ν h (initH h) M (a', σ, t)) a| ≤ Zb' * A j * 2^k :=
          product_bound_sm (j := k) hZs hFs (fun i hi => hZ'all i (le_trans hi hk))
            (fun i hi => hFj i (le_trans hi hk)) hZb'0 (hA0' j)
        have hpow : (0:ℝ) ≤ 2^k := by positivity
        have hpowj : (2:ℝ)^k ≤ 2^j := pow_le_pow_right₀ (by norm_num) hk
        have hp1' : |iteratedDeriv k (fun a' : ℝ => Zrad h (a', σ, t) *
            deriv (fun u : ℝ => Rnu ν h (initH h) M (u, σ, t)) a') a| ≤ Zb * A (j+1) * 2^j :=
          le_trans hp1 (mul_le_mul_of_nonneg_left hpowj (mul_nonneg hZb0 (hA0' (j+1))))
        have hp2' : |iteratedDeriv k (fun a' : ℝ => ZradS h (a', σ, t) *
            Rnu ν h (initH h) M (a', σ, t)) a| ≤ Zb' * A j * 2^j :=
          le_trans hp2 (mul_le_mul_of_nonneg_left hpowj (mul_nonneg hZb'0 (hA0' j)))
        refine le_trans (abs_add_le _ _) ?_
        rw [abs_mul]
        have hcomb : Zb * A (j+1) * 2^j + |ν - M| * (Zb' * A j * 2^j)
            ≤ 2^j * (Zb * A (j+1) + |ν - M| * Zb' * A j) := le_of_eq (by ring)
        have hmul := mul_le_mul_of_nonneg_left hp2' (abs_nonneg (ν - M))
        linarith [hp1', hmul, hcomb, abs_add_le
          (iteratedDeriv k (fun a' : ℝ => Zrad h (a', σ, t) *
            deriv (fun u : ℝ => Rnu ν h (initH h) M (u, σ, t)) a') a)
          ((ν - M) * iteratedDeriv k (fun a' : ℝ => ZradS h (a', σ, t) *
            Rnu ν h (initH h) M (a', σ, t)) a),
          abs_mul (ν - M) (iteratedDeriv k (fun a' : ℝ => ZradS h (a', σ, t) *
            Rnu ν h (initH h) M (a', σ, t)) a)]
      -- the difference bound
      have hdiff : |iteratedDeriv k (fun a' : ℝ => Rnu ν h (initH h) (M+1) (a', σ, t)) a -
          iteratedDeriv k (fun a' : ℝ => Rnu ν (0:ℝ→ℝ) (initH 0) (M+1) (a', σ, t)) a|
          ≤ 2^j * (Zb * D (j+1) + Zd * A (j+1) + |ν - M| * (Zb' * D j + Zd' * A j)) * δ := by
        have hRnu_eq0 : (fun a' : ℝ => Rnu ν (0:ℝ→ℝ) (initH 0) (M+1) (a', σ, t))
            = fun a' : ℝ => Zrad (0:ℝ→ℝ) (a', σ, t) *
                deriv (fun u : ℝ => Rnu ν (0:ℝ→ℝ) (initH 0) M (u, σ, t)) a'
                + (ν - M) * (ZradS (0:ℝ→ℝ) (a', σ, t) * Rnu ν (0:ℝ→ℝ) (initH 0) M (a', σ, t)) := by
          funext a'
          have hd1 : DifferentiableAt ℝ (Rnu ν (0:ℝ→ℝ) (initH 0) M) (a', σ, t) :=
            ((Rnu_contDiff ν contDiff_const (hinitdiff 0 contDiff_const) M).differentiable (by simp)) _
          rw [show M + 1 = M.succ from rfl, Rnu.eq_2]
          dsimp only
          rw [fderiv_fst_eq_deriv _ a' σ t hd1]
          simp only [ZradS]
          ring
        rw [hRnu_eq, hRnu_eq0]
        -- split both into sum of two terms
        have hsum1 : (fun a' : ℝ => Zrad h (a', σ, t) * deriv (fun u : ℝ => Rnu ν h (initH h) M (u, σ, t)) a'
              + (ν - M) * (ZradS h (a', σ, t) * Rnu ν h (initH h) M (a', σ, t)))
            = (fun a' : ℝ => Zrad h (a', σ, t) * deriv (fun u : ℝ => Rnu ν h (initH h) M (u, σ, t)) a')
              + (fun a' : ℝ => (ν - M) * (ZradS h (a', σ, t) * Rnu ν h (initH h) M (a', σ, t))) := rfl
        have hsum2 : (fun a' : ℝ => Zrad (0:ℝ→ℝ) (a', σ, t) *
              deriv (fun u : ℝ => Rnu ν (0:ℝ→ℝ) (initH 0) M (u, σ, t)) a'
              + (ν - M) * (ZradS (0:ℝ→ℝ) (a', σ, t) * Rnu ν (0:ℝ→ℝ) (initH 0) M (a', σ, t)))
            = (fun a' : ℝ => Zrad (0:ℝ→ℝ) (a', σ, t) *
                deriv (fun u : ℝ => Rnu ν (0:ℝ→ℝ) (initH 0) M (u, σ, t)) a')
              + (fun a' : ℝ => (ν - M) *
                (ZradS (0:ℝ→ℝ) (a', σ, t) * Rnu ν (0:ℝ→ℝ) (initH 0) M (a', σ, t))) := rfl
        rw [hsum1, hsum2]
        have hA1 : iteratedDeriv k ((fun a' : ℝ => Zrad h (a', σ, t) *
              deriv (fun u : ℝ => Rnu ν h (initH h) M (u, σ, t)) a')
              + (fun a' : ℝ => (ν - M) * (ZradS h (a', σ, t) * Rnu ν h (initH h) M (a', σ, t)))) a
            = iteratedDeriv k (fun a' : ℝ => Zrad h (a', σ, t) *
                deriv (fun u : ℝ => Rnu ν h (initH h) M (u, σ, t)) a') a
              + iteratedDeriv k (fun a' : ℝ => (ν - M) *
                (ZradS h (a', σ, t) * Rnu ν h (initH h) M (a', σ, t))) a :=
          iteratedDeriv_add (n := k) (x := a)
            (((hZd.mul hdFs).contDiffAt).of_le (Work.OddVolterra.Existence.coe_nat_le_infty k))
            (((contDiff_const.mul (hZs.mul hFs)).contDiffAt).of_le (Work.OddVolterra.Existence.coe_nat_le_infty k))
        have hA2 : iteratedDeriv k ((fun a' : ℝ => Zrad (0:ℝ→ℝ) (a', σ, t) *
              deriv (fun u : ℝ => Rnu ν (0:ℝ→ℝ) (initH 0) M (u, σ, t)) a')
              + (fun a' : ℝ => (ν - M) * (ZradS (0:ℝ→ℝ) (a', σ, t) *
                Rnu ν (0:ℝ→ℝ) (initH 0) M (a', σ, t)))) a
            = iteratedDeriv k (fun a' : ℝ => Zrad (0:ℝ→ℝ) (a', σ, t) *
                deriv (fun u : ℝ => Rnu ν (0:ℝ→ℝ) (initH 0) M (u, σ, t)) a') a
              + iteratedDeriv k (fun a' : ℝ => (ν - M) * (ZradS (0:ℝ→ℝ) (a', σ, t) *
                Rnu ν (0:ℝ→ℝ) (initH 0) M (a', σ, t))) a :=
          iteratedDeriv_add (n := k) (x := a)
            (((hZ0.mul hdFs0).contDiffAt).of_le (Work.OddVolterra.Existence.coe_nat_le_infty k))
            (((contDiff_const.mul (hZs0.mul hFs0)).contDiffAt).of_le (Work.OddVolterra.Existence.coe_nat_le_infty k))
        rw [hA1, hA2]
        have hc3 : iteratedDeriv k (fun a' : ℝ => (ν - M) *
            (ZradS h (a', σ, t) * Rnu ν h (initH h) M (a', σ, t))) a
            = (ν - M) * iteratedDeriv k (fun a' : ℝ =>
                ZradS h (a', σ, t) * Rnu ν h (initH h) M (a', σ, t)) a :=
          iteratedDeriv_const_mul (n := k) (x := a) (c := ν - M)
            (((hZs.mul hFs).contDiffAt).of_le (Work.OddVolterra.Existence.coe_nat_le_infty k))
        have hc4 : iteratedDeriv k (fun a' : ℝ => (ν - M) *
            (ZradS (0:ℝ→ℝ) (a', σ, t) * Rnu ν (0:ℝ→ℝ) (initH 0) M (a', σ, t))) a
            = (ν - M) * iteratedDeriv k (fun a' : ℝ =>
                ZradS (0:ℝ→ℝ) (a', σ, t) * Rnu ν (0:ℝ→ℝ) (initH 0) M (a', σ, t)) a :=
          iteratedDeriv_const_mul (n := k) (x := a) (c := ν - M)
            (((hZs0.mul hFs0).contDiffAt).of_le (Work.OddVolterra.Existence.coe_nat_le_infty k))
        rw [hc3, hc4]
        -- bounds for the four pieces
        have hE1 : |iteratedDeriv k (fun a' : ℝ => Zrad h (a', σ, t) *
              deriv (fun u : ℝ => Rnu ν h (initH h) M (u, σ, t)) a') a
            - iteratedDeriv k (fun a' : ℝ => Zrad (0:ℝ→ℝ) (a', σ, t) *
              deriv (fun u : ℝ => Rnu ν (0:ℝ→ℝ) (initH 0) M (u, σ, t)) a') a|
            ≤ (Zb * (D (j+1) * δ) + (Zd * δ) * A (j+1)) * 2^k :=
          product_sub_bound_sm (j := k) (Bf := Zb) (Bg := A (j+1)) (Df := Zd * δ) (Dg := D (j+1) * δ)
            hZd hZ0 hdFs hdFs0
            (fun i hi => hZall i (le_trans hi hk)) (fun i hi => hderivF0 i (le_trans hi hk))
            (fun i hi => hZdiff' i (le_trans hi hk)) (fun i hi => hderivDF' i (le_trans hi hk))
            hZb0 (hA0' (j+1)) (mul_nonneg hZd0 hδ.le) (mul_nonneg (hD0' (j+1)) hδ.le)
        have hE2 : |iteratedDeriv k (fun a' : ℝ => ZradS h (a', σ, t) *
              Rnu ν h (initH h) M (a', σ, t)) a
            - iteratedDeriv k (fun a' : ℝ => ZradS (0:ℝ→ℝ) (a', σ, t) *
              Rnu ν (0:ℝ→ℝ) (initH 0) M (a', σ, t)) a|
            ≤ (Zb' * (D j * δ) + (Zd' * δ) * A j) * 2^k :=
          product_sub_bound_sm (j := k) (Bf := Zb') (Bg := A j) (Df := Zd' * δ) (Dg := D j * δ)
            hZs hZs0 hFs hFs0
            (fun i hi => hZ'all i (le_trans hi hk)) (fun i hi => hF0j i (le_trans hi hk))
            (fun i hi => hZ'diff' i (le_trans hi hk)) (fun i hi => hDFj' i (le_trans hi hk))
            hZb'0 (hA0' j) (mul_nonneg hZd'0 hδ.le) (mul_nonneg (hD0' j) hδ.le)
        have hpow : (0:ℝ) ≤ 2^k := by positivity
        have hpowj : (2:ℝ)^k ≤ 2^j := pow_le_pow_right₀ (by norm_num) hk
        have hE1' : |iteratedDeriv k (fun a' : ℝ => Zrad h (a', σ, t) *
              deriv (fun u : ℝ => Rnu ν h (initH h) M (u, σ, t)) a') a
            - iteratedDeriv k (fun a' : ℝ => Zrad (0:ℝ→ℝ) (a', σ, t) *
              deriv (fun u : ℝ => Rnu ν (0:ℝ→ℝ) (initH 0) M (u, σ, t)) a') a|
            ≤ (Zb * (D (j+1) * δ) + (Zd * δ) * A (j+1)) * 2^j :=
          le_trans hE1 (mul_le_mul_of_nonneg_left hpowj
            (add_nonneg (mul_nonneg hZb0 (mul_nonneg (hD0' (j+1)) hδ.le))
              (mul_nonneg (mul_nonneg hZd0 hδ.le) (hA0' (j+1)))))
        have hE2' : |iteratedDeriv k (fun a' : ℝ => ZradS h (a', σ, t) *
              Rnu ν h (initH h) M (a', σ, t)) a
            - iteratedDeriv k (fun a' : ℝ => ZradS (0:ℝ→ℝ) (a', σ, t) *
              Rnu ν (0:ℝ→ℝ) (initH 0) M (a', σ, t)) a|
            ≤ (Zb' * (D j * δ) + (Zd' * δ) * A j) * 2^j :=
          le_trans hE2 (mul_le_mul_of_nonneg_left hpowj
            (add_nonneg (mul_nonneg hZb'0 (mul_nonneg (hD0' j) hδ.le))
              (mul_nonneg (mul_nonneg hZd'0 hδ.le) (hA0' j))))
        have hgoal : |iteratedDeriv k (fun a' : ℝ => Zrad h (a', σ, t) *
              deriv (fun u : ℝ => Rnu ν h (initH h) M (u, σ, t)) a') a
              + (ν - M) * iteratedDeriv k (fun a' : ℝ =>
                  ZradS h (a', σ, t) * Rnu ν h (initH h) M (a', σ, t)) a
            - (iteratedDeriv k (fun a' : ℝ => Zrad (0:ℝ→ℝ) (a', σ, t) *
                  deriv (fun u : ℝ => Rnu ν (0:ℝ→ℝ) (initH 0) M (u, σ, t)) a') a
              + (ν - M) * iteratedDeriv k (fun a' : ℝ =>
                  ZradS (0:ℝ→ℝ) (a', σ, t) * Rnu ν (0:ℝ→ℝ) (initH 0) M (a', σ, t)) a)|
            ≤ 2^j * (Zb * D (j+1) + Zd * A (j+1) + |ν - M| * (Zb' * D j + Zd' * A j)) * δ := by
          have hsplit : (iteratedDeriv k (fun a' : ℝ => Zrad h (a', σ, t) *
                deriv (fun u : ℝ => Rnu ν h (initH h) M (u, σ, t)) a') a
                + (ν - M) * iteratedDeriv k (fun a' : ℝ =>
                    ZradS h (a', σ, t) * Rnu ν h (initH h) M (a', σ, t)) a
              - (iteratedDeriv k (fun a' : ℝ => Zrad (0:ℝ→ℝ) (a', σ, t) *
                    deriv (fun u : ℝ => Rnu ν (0:ℝ→ℝ) (initH 0) M (u, σ, t)) a') a
                + (ν - M) * iteratedDeriv k (fun a' : ℝ =>
                    ZradS (0:ℝ→ℝ) (a', σ, t) * Rnu ν (0:ℝ→ℝ) (initH 0) M (a', σ, t)) a))
              = ((iteratedDeriv k (fun a' : ℝ => Zrad h (a', σ, t) *
                    deriv (fun u : ℝ => Rnu ν h (initH h) M (u, σ, t)) a') a
                  - iteratedDeriv k (fun a' : ℝ => Zrad (0:ℝ→ℝ) (a', σ, t) *
                    deriv (fun u : ℝ => Rnu ν (0:ℝ→ℝ) (initH 0) M (u, σ, t)) a') a)
                + (ν - M) * (iteratedDeriv k (fun a' : ℝ =>
                    ZradS h (a', σ, t) * Rnu ν h (initH h) M (a', σ, t)) a
                  - iteratedDeriv k (fun a' : ℝ =>
                    ZradS (0:ℝ→ℝ) (a', σ, t) * Rnu ν (0:ℝ→ℝ) (initH 0) M (a', σ, t)) a)) := by
            ring
          rw [hsplit]
          refine le_trans (abs_add_le _ _) ?_
          rw [abs_mul]
          have hfin : (Zb * (D (j+1) * δ) + (Zd * δ) * A (j+1)) * 2^j
              + |ν - M| * ((Zb' * (D j * δ) + (Zd' * δ) * A j) * 2^j)
              ≤ 2^j * (Zb * D (j+1) + Zd * A (j+1) + |ν - M| * (Zb' * D j + Zd' * A j)) * δ :=
            le_of_eq (by ring)
          have hmul2 := mul_le_mul_of_nonneg_left hE2' (abs_nonneg (ν - M))
          have htri := abs_add_le (iteratedDeriv k (fun a' : ℝ => Zrad h (a', σ, t) *
                deriv (fun u : ℝ => Rnu ν h (initH h) M (u, σ, t)) a') a
              - iteratedDeriv k (fun a' : ℝ => Zrad (0:ℝ→ℝ) (a', σ, t) *
                deriv (fun u : ℝ => Rnu ν (0:ℝ→ℝ) (initH 0) M (u, σ, t)) a') a)
            ((ν - M) * (iteratedDeriv k (fun a' : ℝ => ZradS h (a', σ, t) *
                Rnu ν h (initH h) M (a', σ, t)) a
              - iteratedDeriv k (fun a' : ℝ => ZradS (0:ℝ→ℝ) (a', σ, t) *
                Rnu ν (0:ℝ→ℝ) (initH 0) M (a', σ, t)) a))
          have habsm := abs_mul (ν - M) (iteratedDeriv k (fun a' : ℝ => ZradS h (a', σ, t) *
                Rnu ν h (initH h) M (a', σ, t)) a
              - iteratedDeriv k (fun a' : ℝ => ZradS (0:ℝ→ℝ) (a', σ, t) *
                Rnu ν (0:ℝ→ℝ) (initH 0) M (a', σ, t)) a)
          linarith [hE1', hmul2, hfin, htri, habsm]
        exact hgoal
      exact ⟨hval, hdiff⟩





/-- The `k`-th derivative (`k ≥ 1`) of `a ↦ lineSlope h a t`. -/
lemma iteratedDeriv_lineSlope {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤:ℕ∞) h) (t a : ℝ) {k : ℕ}
    (hk : 1 ≤ k) :
    iteratedDeriv k (fun a' : ℝ => lineSlope h a' t) a = iteratedDeriv (k+1) h a := by
  have e : (fun a' : ℝ => lineSlope h a' t) = fun a' : ℝ => t + deriv h a' := by
    funext u; rfl
  have esum : (fun a' : ℝ => t + deriv h a') = (fun _ : ℝ => t) + deriv h := rfl
  have hd : ContDiff ℝ (⊤:ℕ∞) (deriv h) := by
    simpa only [Function.iterate_one] using hh.iterate_deriv 1
  rw [e, esum, iteratedDeriv_add (n := k) (x := a)
    (contDiffAt_const : ContDiffAt ℝ (k:ℕ∞ω) (fun _ : ℝ => t) a)
    ((hd.contDiffAt).of_le (Work.OddVolterra.Existence.coe_nat_le_infty k)),
    iteratedDeriv_const, if_neg (by omega : ¬ k = 0), zero_add,
    ← iteratedDeriv_succ' (n := k) (f := h)]

lemma iteratedDeriv_lineSlope_zero (t a : ℝ) {k : ℕ} (hk : 1 ≤ k) :
    iteratedDeriv k (fun a' : ℝ => lineSlope (0:ℝ→ℝ) a' t) a = 0 := by
  have e : (fun a' : ℝ => lineSlope (0:ℝ→ℝ) a' t) = fun _ : ℝ => t := by
    funext u; unfold lineSlope; simp
  rw [e, iteratedDeriv_const, if_neg (by omega : ¬ k = 0)]

/-- The bounds on `J1M` (and its `a`-derivative) coming from `rnu_bounds`. -/
theorem J1M_bounds (n : ℕ) (hn : 1 ≤ n) :
    ∃ A1 D1 : ℝ, 0 ≤ A1 ∧ 0 ≤ D1 ∧
      ∀ h : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) h → ∀ δ : ℝ, 0 < δ → δ ≤ 1/100 →
      (∀ k ≤ n+2, ∀ x : ℝ, |iteratedDeriv k h x| ≤ δ) →
      ∀ a ∈ Set.Icc (1/2 : ℝ) 1, ∀ σ ∈ Set.Icc (1/2 : ℝ) 1, ∀ t ∈ Set.Icc (-(3/2) : ℝ) (3/2),
        |J1M n h a σ t| ≤ A1 ∧
        |deriv (fun a' : ℝ => J1M n h a' σ t) a| ≤ A1 ∧
        |J1M n h a σ t - J1M n 0 a σ t| ≤ D1 * δ ∧
        |deriv (fun a' : ℝ => J1M n h a' σ t) a - deriv (fun a' : ℝ => J1M n 0 a' σ t) a| ≤ D1 * δ := by
  obtain ⟨A, D, hA0, hD0, hAD⟩ := rnu_bounds (ν := (n:ℝ) + 1/2) (Nj := n+2) (shift := 0)
    (initH := fun _ _ => (1:ℝ))
    (hinitdiff := fun h hh => contDiff_const) (A0 := fun _ => 1) (D0 := fun _ => 0)
    (hA0 := fun _ => by norm_num) (hD0 := fun _ => by norm_num)
    (hbase := fun h hh δ hδ hδ1 hjet a ha σ hσ t ht j hj k hk => by
      have hconst : (fun a' : ℝ => (fun _ _ => (1:ℝ)) h (a', σ, t)) = fun _ : ℝ => (1:ℝ) := by
        funext u; rfl
      rw [hconst]
      constructor
      · rcases Nat.eq_zero_or_pos k with hk0 | hkpos
        · subst hk0; rw [iteratedDeriv_zero]; norm_num
        · rw [iteratedDeriv_const (n := k) (c := (1:ℝ))]
          simp only [if_neg (by omega : ¬ k = 0), abs_zero]; norm_num
      · rw [sub_self, abs_zero]
        exact mul_nonneg (by norm_num) hδ.le) (M := n+1) (by omega)
  refine ⟨max (A 0) (A 1), max (D 0) (D 1), le_trans (hA0 0) (le_max_left _ _),
    le_trans (hD0 0) (le_max_left _ _), ?_⟩
  intro h hh δ hδ hδ1 hjet a ha σ hσ t ht
  have h0 := hAD h hh δ hδ hδ1 hjet a ha σ hσ t ht 0 (by omega)
  have h1 := hAD h hh δ hδ hδ1 hjet a ha σ hσ t ht 1 (by omega)
  have hj0a := (h0 0 (le_refl 0)).1
  have hj0b := (h0 0 (le_refl 0)).2
  have hj1a := (h1 1 (le_refl 1)).1
  have hj1b := (h1 1 (le_refl 1)).2
  have hJ1M : ∀ b : ℝ → ℝ, (fun a' : ℝ => J1M n b a' σ t)
      = fun a' : ℝ => Rnu ((n:ℝ) + 1/2) b (fun _ => (1:ℝ)) (n+1) (a', σ, t) := fun b => rfl
  have hderiv1 : deriv (fun a' : ℝ => Rnu ((n:ℝ) + 1/2) h (fun _ => (1:ℝ)) (n+1) (a', σ, t)) a
      = iteratedDeriv 1 (fun a' : ℝ => Rnu ((n:ℝ) + 1/2) h (fun _ => (1:ℝ)) (n+1) (a', σ, t)) a := by
    rw [iteratedDeriv_one]
  have hderiv0 : deriv (fun a' : ℝ => Rnu ((n:ℝ) + 1/2) (0:ℝ→ℝ) (fun _ => (1:ℝ)) (n+1) (a', σ, t)) a
      = iteratedDeriv 1 (fun a' : ℝ => Rnu ((n:ℝ) + 1/2) (0:ℝ→ℝ) (fun _ => (1:ℝ)) (n+1) (a', σ, t)) a := by
    rw [iteratedDeriv_one]
  rw [hJ1M h, hJ1M 0, hderiv1, hderiv0]
  exact ⟨le_trans hj0a (le_max_left _ _), le_trans hj1a (le_max_right _ _),
    le_trans hj0b (mul_le_mul_of_nonneg_right (le_max_left _ _) hδ.le),
    le_trans hj1b (mul_le_mul_of_nonneg_right (le_max_right _ _) hδ.le)⟩

/-- The bounds on `J2M` (and its `a`-derivative) coming from `rnu_bounds`. -/
theorem J2M_bounds (n : ℕ) (hn : 1 ≤ n) :
    ∃ A2 D2 : ℝ, 0 ≤ A2 ∧ 0 ≤ D2 ∧
      ∀ h : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) h → ∀ δ : ℝ, 0 < δ → δ ≤ 1/100 →
      (∀ k ≤ n+2, ∀ x : ℝ, |iteratedDeriv k h x| ≤ δ) →
      ∀ a ∈ Set.Icc (1/2 : ℝ) 1, ∀ σ ∈ Set.Icc (1/2 : ℝ) 1, ∀ t ∈ Set.Icc (-(3/2) : ℝ) (3/2),
        |J2M n h a σ t| ≤ A2 ∧
        |deriv (fun a' : ℝ => J2M n h a' σ t) a| ≤ A2 ∧
        |J2M n h a σ t - J2M n 0 a σ t| ≤ D2 * δ ∧
        |deriv (fun a' : ℝ => J2M n h a' σ t) a - deriv (fun a' : ℝ => J2M n 0 a' σ t) a| ≤ D2 * δ := by
  obtain ⟨A, D, hA0, hD0, hAD⟩ := rnu_bounds (ν := (n:ℝ) - 1/2) (Nj := n+2) (shift := 1)
    (initH := fun h q => lineSlope h q.1 q.2.2)
    (hinitdiff := fun h hh => by unfold lineSlope; fun_prop) (A0 := fun _ => 2) (D0 := fun _ => 1)
    (hA0 := fun _ => by norm_num) (hD0 := fun _ => by norm_num)
    (hbase := fun h hh δ hδ hδ1 hjet a ha σ hσ t ht j hj k hk => by
      have hk1 : k ≤ n + 1 := by omega
      have hjet1 : |deriv h a| ≤ δ := by simpa [iteratedDeriv_one] using hjet 1 (by omega) a
      constructor
      · rcases Nat.eq_zero_or_pos k with hk0 | hkpos
        · subst hk0
          rw [iteratedDeriv_zero]
          simp only [lineSlope]
          have ht' : |t| ≤ 3/2 := by rw [abs_le]; exact ht
          rw [abs_le] at ht' ⊢
          have h1 := abs_le.mp hjet1
          constructor <;> linarith [ht'.1, ht'.2, h1.1, h1.2]
        · rw [iteratedDeriv_lineSlope hh t a hkpos]
          exact le_trans (hjet (k+1) (by omega) a) (by linarith [hδ1])
      · rcases Nat.eq_zero_or_pos k with hk0 | hkpos
        · subst hk0
          rw [iteratedDeriv_zero, iteratedDeriv_zero]
          have hz : lineSlope (0:ℝ→ℝ) a t = t := by unfold lineSlope; simp
          rw [hz]
          have hh' : lineSlope h a t = t + deriv h a := rfl
          rw [hh']
          have : t + deriv h a - t = deriv h a := by ring
          rw [this]
          calc |deriv h a| ≤ δ := hjet1
            _ = 1 * δ := by ring
        · rw [iteratedDeriv_lineSlope hh t a hkpos, iteratedDeriv_lineSlope_zero t a hkpos, sub_zero]
          calc |iteratedDeriv (k+1) h a| ≤ δ := hjet (k+1) (by omega) a
            _ = 1 * δ := by ring) (M := n) (by omega)
  refine ⟨max (A 0) (A 1), max (D 0) (D 1), le_trans (hA0 0) (le_max_left _ _),
    le_trans (hD0 0) (le_max_left _ _), ?_⟩
  intro h hh δ hδ hδ1 hjet a ha σ hσ t ht
  have h0 := hAD h hh δ hδ hδ1 hjet a ha σ hσ t ht 0 (by omega)
  have h1 := hAD h hh δ hδ hδ1 hjet a ha σ hσ t ht 1 (by omega)
  have hj0a := (h0 0 (le_refl 0)).1
  have hj0b := (h0 0 (le_refl 0)).2
  have hj1a := (h1 1 (le_refl 1)).1
  have hj1b := (h1 1 (le_refl 1)).2
  have hJ2M : ∀ b : ℝ → ℝ, (fun a' : ℝ => J2M n b a' σ t)
      = fun a' : ℝ => Rnu ((n:ℝ) - 1/2) b (fun q => lineSlope b q.1 q.2.2) n (a', σ, t) := fun b => rfl
  have hderiv1 : deriv (fun a' : ℝ => Rnu ((n:ℝ) - 1/2) h (fun q => lineSlope h q.1 q.2.2) n (a', σ, t)) a
      = iteratedDeriv 1 (fun a' : ℝ => Rnu ((n:ℝ) - 1/2) h (fun q => lineSlope h q.1 q.2.2) n (a', σ, t)) a := by
    rw [iteratedDeriv_one]
  have hderiv0 : deriv (fun a' : ℝ => Rnu ((n:ℝ) - 1/2) (0:ℝ→ℝ) (fun q => lineSlope (0:ℝ→ℝ) q.1 q.2.2) n (a', σ, t)) a
      = iteratedDeriv 1 (fun a' : ℝ => Rnu ((n:ℝ) - 1/2) (0:ℝ→ℝ) (fun q => lineSlope (0:ℝ→ℝ) q.1 q.2.2) n (a', σ, t)) a := by
    rw [iteratedDeriv_one]
  rw [hJ2M h, hJ2M 0, hderiv1, hderiv0]
  exact ⟨le_trans hj0a (le_max_left _ _), le_trans hj1a (le_max_right _ _),
    le_trans hj0b (mul_le_mul_of_nonneg_right (le_max_left _ _) hδ.le),
    le_trans hj1b (mul_le_mul_of_nonneg_right (le_max_right _ _) hδ.le)⟩





lemma hquot_zero (a σ : ℝ) : Work.OddVolterra.hquot (0:ℝ→ℝ) a σ = 0 := by
  unfold Work.OddVolterra.hquot
  simp

/-- The basic bounds on `Kden`. -/
lemma Kden_basic {h : ℝ → ℝ} (h0 : ∀ x : ℝ, |h x| ≤ 1/100)
    (h1 : ∀ x : ℝ, |deriv h x| ≤ 1/100)
    {a σ t : ℝ} (ha : (1/4 : ℝ) ≤ a) (ha2 : a ≤ 3/2) (hσ : (1/2 : ℝ) ≤ σ) (hσ1 : σ ≤ 1)
    (ht : (1/5 : ℝ) ≤ |t|) (ht2 : |t| ≤ 3/2) :
    (1/10 : ℝ) ≤ Kden h a σ t ∧ Kden h a σ t ≤ 3 := by
  obtain ⟨hlo, hhi⟩ := krad_region h0 h1 ha ha2 hσ hσ1 ht ht2
  rw [Kden_eq_sqrt_krad]
  constructor
  · have h1' : Real.sqrt (1/100 : ℝ) ≤ Real.sqrt (Work.OddVolterra.krad h σ t a) :=
      Real.sqrt_le_sqrt hlo
    have h2' : Real.sqrt ((1:ℝ)/100) = 1/10 := by
      rw [show ((1:ℝ)/100) = ((1:ℝ)/10)^2 by norm_num, Real.sqrt_sq (by norm_num)]
    linarith
  · have h1' : Real.sqrt (Work.OddVolterra.krad h σ t a) ≤ Real.sqrt 9 :=
      Real.sqrt_le_sqrt (by linarith)
    have h2' : Real.sqrt (9:ℝ) = 3 := by
      rw [show (9:ℝ) = (3:ℝ)^2 by norm_num, Real.sqrt_sq (by norm_num)]
    linarith

/-- The difference of the Abel radicands, in terms of the jet size `δ`. -/
lemma krad_diff_bound {h : ℝ → ℝ} {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1/100)
    (h0 : ∀ x : ℝ, |h x| ≤ δ) (h1 : ∀ x : ℝ, |deriv h x| ≤ δ) {a σ t : ℝ}
    (ha : (1/4 : ℝ) ≤ a) (ha2 : a ≤ 3/2) (hσ : (1/2 : ℝ) ≤ σ) (hσ1 : σ ≤ 1)
    (ht2 : |t| ≤ 3/2) :
    |Work.OddVolterra.krad h σ t a - Work.OddVolterra.krad (0:ℝ→ℝ) σ t a| ≤ 10 * δ := by
  have hq : |Work.OddVolterra.hquot h a σ| ≤ δ :=
    Work.OddVolterra.abs_hquot_le h1 hδ0
  have hha : |h σ + h a| ≤ 2 * δ := by
    have h1' := abs_le.mp (h0 σ)
    have h2' := abs_le.mp (h0 a)
    rw [abs_le]
    constructor <;> linarith [h1'.1, h1'.2, h2'.1, h2'.2]
  have ht' := ht2
  have hk : Work.OddVolterra.krad h σ t a - Work.OddVolterra.krad (0:ℝ→ℝ) σ t a
      = t * (h σ + h a) + Work.OddVolterra.hquot h a σ *
          (Work.OddVolterra.line h σ t + Work.OddVolterra.line h a t) := by
    have e : Work.OddVolterra.line (0:ℝ→ℝ) σ t = σ * t := by simp [Work.OddVolterra.line]
    have e2 : Work.OddVolterra.line (0:ℝ→ℝ) a t = a * t := by simp [Work.OddVolterra.line]
    have hline : Work.OddVolterra.line h σ t + Work.OddVolterra.line h a t
        = (σ + a) * t + (h σ + h a) := by unfold Work.OddVolterra.line; ring
    rw [Work.OddVolterra.krad_apply, Work.OddVolterra.krad_apply, hquot_zero, e, e2, hline]
    ring
  rw [hk]
  have hL : |Work.OddVolterra.line h σ t + Work.OddVolterra.line h a t| ≤ 4 := by
    unfold Work.OddVolterra.line
    have h1' : |σ * t + h σ + (a * t + h a)|
        ≤ (|σ| * |t| + |h σ|) + (|a| * |t| + |h a|) := by
      calc |σ * t + h σ + (a * t + h a)| ≤ |σ * t + h σ| + |a * t + h a| := abs_add_le _ _
        _ ≤ (|σ * t| + |h σ|) + (|a * t| + |h a|) := by
            have h2 := abs_add_le (σ * t) (h σ)
            have h3 := abs_add_le (a * t) (h a)
            linarith
        _ = (|σ| * |t| + |h σ|) + (|a| * |t| + |h a|) := by rw [abs_mul, abs_mul]
    have hσa : |σ| ≤ 1 := by rw [abs_le]; exact ⟨by linarith, hσ1⟩
    have haa : |a| ≤ 3/2 := by rw [abs_le]; exact ⟨by linarith, ha2⟩
    have h1'' : |σ| * |t| ≤ 1 * (3/2) := mul_le_mul hσa ht' (abs_nonneg t) (by norm_num)
    have h2'' : |a| * |t| ≤ (3/2) * (3/2) := mul_le_mul haa ht' (abs_nonneg t) (by norm_num)
    linarith [h1', h1'', h2'', h0 σ, h0 a, hδ1]
  calc |t * (h σ + h a) + Work.OddVolterra.hquot h a σ *
        (Work.OddVolterra.line h σ t + Work.OddVolterra.line h a t)|
      ≤ |t * (h σ + h a)| + |Work.OddVolterra.hquot h a σ *
        (Work.OddVolterra.line h σ t + Work.OddVolterra.line h a t)| := abs_add_le _ _
    _ = |t| * |h σ + h a| + |Work.OddVolterra.hquot h a σ| *
        |Work.OddVolterra.line h σ t + Work.OddVolterra.line h a t| := by rw [abs_mul, abs_mul]
    _ ≤ (3/2) * (2 * δ) + δ * 4 := by
        refine add_le_add ?_ ?_
        · exact mul_le_mul ht' hha (abs_nonneg _) (by norm_num)
        · exact mul_le_mul hq hL (abs_nonneg _) hδ0
    _ ≤ 10 * δ := by nlinarith [hδ0]

/-- The difference of the Abel denominators, in terms of the jet size `δ`. -/
lemma Kden_diff_bound {h : ℝ → ℝ} {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1/100)
    (h0 : ∀ x : ℝ, |h x| ≤ δ) (hh0 : ∀ x : ℝ, |h x| ≤ 1/100)
    (h1 : ∀ x : ℝ, |deriv h x| ≤ δ) (hh1 : ∀ x : ℝ, |deriv h x| ≤ 1/100) {a σ t : ℝ}
    (ha : (1/4 : ℝ) ≤ a) (ha2 : a ≤ 3/2) (hσ : (1/2 : ℝ) ≤ σ) (hσ1 : σ ≤ 1)
    (ht : (1/5 : ℝ) ≤ |t|) (ht2 : |t| ≤ 3/2) :
    |Kden h a σ t - Kden (0:ℝ→ℝ) a σ t| ≤ 100 * δ := by
  have hzh : ∀ x : ℝ, |(0:ℝ→ℝ) x| ≤ 1/100 := fun x => by simp
  have hzd : ∀ x : ℝ, |deriv (0:ℝ→ℝ) x| ≤ 1/100 := fun x => by simp
  have hxh := (krad_region hh0 hh1 ha ha2 hσ hσ1 ht ht2).1
  have hx0 := (krad_region (h := (0:ℝ→ℝ)) hzh hzd ha ha2 hσ hσ1 ht ht2).1
  have hd := krad_diff_bound hδ0 hδ1 h0 h1 ha ha2 hσ hσ1 ht2
  have hxn : (0:ℝ) < Work.OddVolterra.krad h σ t a := by linarith
  have hyn : (0:ℝ) < Work.OddVolterra.krad (0:ℝ→ℝ) σ t a := by linarith
  have hden : (1/5 : ℝ) ≤ Kden h a σ t + Kden (0:ℝ→ℝ) a σ t := by
    rw [Kden_eq_sqrt_krad, Kden_eq_sqrt_krad]
    have h1' : (1/10 : ℝ) ≤ Real.sqrt (Work.OddVolterra.krad h σ t a) := by
      have := Real.sqrt_le_sqrt hxh
      have h2' : Real.sqrt ((1:ℝ)/100) = 1/10 := by
        rw [show ((1:ℝ)/100) = ((1:ℝ)/10)^2 by norm_num, Real.sqrt_sq (by norm_num)]
      linarith
    have h2'' : (1/10 : ℝ) ≤ Real.sqrt (Work.OddVolterra.krad (0:ℝ→ℝ) σ t a) := by
      have := Real.sqrt_le_sqrt hx0
      have h3' : Real.sqrt ((1:ℝ)/100) = 1/10 := by
        rw [show ((1:ℝ)/100) = ((1:ℝ)/10)^2 by norm_num, Real.sqrt_sq (by norm_num)]
      linarith
    linarith
  have hposd : (0:ℝ) < Kden h a σ t + Kden (0:ℝ→ℝ) a σ t := by linarith
  have hsq : (Real.sqrt (Work.OddVolterra.krad h σ t a) - Real.sqrt (Work.OddVolterra.krad (0:ℝ→ℝ) σ t a))
      * (Real.sqrt (Work.OddVolterra.krad h σ t a) + Real.sqrt (Work.OddVolterra.krad (0:ℝ→ℝ) σ t a))
      = Work.OddVolterra.krad h σ t a - Work.OddVolterra.krad (0:ℝ→ℝ) σ t a := by
    have h1' : Real.sqrt (Work.OddVolterra.krad h σ t a) ^ 2 = Work.OddVolterra.krad h σ t a :=
      Real.sq_sqrt (le_of_lt hxn)
    have h2' : Real.sqrt (Work.OddVolterra.krad (0:ℝ→ℝ) σ t a) ^ 2
        = Work.OddVolterra.krad (0:ℝ→ℝ) σ t a := Real.sq_sqrt (le_of_lt hyn)
    linear_combination h1' - h2'
  rw [Kden_eq_sqrt_krad, Kden_eq_sqrt_krad]
  have hD : (0:ℝ) < Real.sqrt (Work.OddVolterra.krad h σ t a)
      + Real.sqrt (Work.OddVolterra.krad (0:ℝ→ℝ) σ t a) := by
    have h1' := Real.sqrt_pos.mpr hxn
    have h2' : (0:ℝ) ≤ Real.sqrt (Work.OddVolterra.krad (0:ℝ→ℝ) σ t a) := Real.sqrt_nonneg _
    linarith
  have hden5 : (1/5 : ℝ) ≤ Real.sqrt (Work.OddVolterra.krad h σ t a)
      + Real.sqrt (Work.OddVolterra.krad (0:ℝ→ℝ) σ t a) := by
    have h1' : (1/10 : ℝ) ≤ Real.sqrt (Work.OddVolterra.krad h σ t a) := by
      have := Real.sqrt_le_sqrt hxh
      have h2' : Real.sqrt ((1:ℝ)/100) = 1/10 := by
        rw [show ((1:ℝ)/100) = ((1:ℝ)/10)^2 by norm_num, Real.sqrt_sq (by norm_num)]
      linarith
    have h2'' : (1/10 : ℝ) ≤ Real.sqrt (Work.OddVolterra.krad (0:ℝ→ℝ) σ t a) := by
      have := Real.sqrt_le_sqrt hx0
      have h3' : Real.sqrt ((1:ℝ)/100) = 1/10 := by
        rw [show ((1:ℝ)/100) = ((1:ℝ)/10)^2 by norm_num, Real.sqrt_sq (by norm_num)]
      linarith
    linarith
  have hkey : |Real.sqrt (Work.OddVolterra.krad h σ t a) - Real.sqrt (Work.OddVolterra.krad (0:ℝ→ℝ) σ t a)|
      = |Work.OddVolterra.krad h σ t a - Work.OddVolterra.krad (0:ℝ→ℝ) σ t a|
        / (Real.sqrt (Work.OddVolterra.krad h σ t a) + Real.sqrt (Work.OddVolterra.krad (0:ℝ→ℝ) σ t a)) := by
    rw [eq_div_iff (ne_of_gt hD)]
    rw [← abs_of_pos hD, ← abs_mul, hsq]
  have hdiv : |Work.OddVolterra.krad h σ t a - Work.OddVolterra.krad (0:ℝ→ℝ) σ t a|
        / (Real.sqrt (Work.OddVolterra.krad h σ t a) + Real.sqrt (Work.OddVolterra.krad (0:ℝ→ℝ) σ t a))
      ≤ (10 * δ) / (1/5) := by
    refine le_trans (div_le_div_of_nonneg_left (abs_nonneg _) (by norm_num : (0:ℝ) < 1/5) hden5) ?_
    exact div_le_div_of_nonneg_right hd (by norm_num)
  calc |Real.sqrt (Work.OddVolterra.krad h σ t a) - Real.sqrt (Work.OddVolterra.krad (0:ℝ→ℝ) σ t a)|
      = |Work.OddVolterra.krad h σ t a - Work.OddVolterra.krad (0:ℝ→ℝ) σ t a|
        / (Real.sqrt (Work.OddVolterra.krad h σ t a) + Real.sqrt (Work.OddVolterra.krad (0:ℝ→ℝ) σ t a)) := hkey
    _ ≤ (10 * δ) / (1/5) := hdiv
    _ = 50 * δ := by ring
    _ ≤ 100 * δ := by linarith [hδ0]





lemma contDiff_hquot_snd {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤:ℕ∞) h) (σ : ℝ) :
    ContDiff ℝ (⊤:ℕ∞) (fun a' : ℝ => Work.OddVolterra.hquot h a' σ) := by
  have hc : ContDiff ℝ (⊤:ℕ∞) (fun p : ℝ × ℝ => Work.OddVolterra.hquot h p.1 p.2) :=
    Work.OddVolterra.Existence.hquot_contDiff hh
  have h2 : ContDiff ℝ (⊤:ℕ∞) (fun a' : ℝ => (a', σ)) := by fun_prop
  exact hc.comp h2

/-- A uniform bound for `L(s,t) + L(a,t)` in terms of the jet size. -/
lemma line_sum_bound {h : ℝ → ℝ} {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1/100)
    (h0 : ∀ x : ℝ, |h x| ≤ δ) {a σ t : ℝ} (ha0 : 0 ≤ a) (ha2 : a ≤ 3/2) (hσ0 : 0 ≤ σ)
    (hσ1 : σ ≤ 1) (ht2 : |t| ≤ 3/2) :
    |Work.OddVolterra.line h σ t + Work.OddVolterra.line h a t| ≤ 4 := by
  unfold Work.OddVolterra.line
  have h1' : |σ * t + h σ + (a * t + h a)| ≤ (|σ| * |t| + |h σ|) + (|a| * |t| + |h a|) := by
    calc |σ * t + h σ + (a * t + h a)| ≤ |σ * t + h σ| + |a * t + h a| := abs_add_le _ _
      _ ≤ (|σ * t| + |h σ|) + (|a * t| + |h a|) := by
          have h2' := abs_add_le (σ * t) (h σ)
          have h3' := abs_add_le (a * t) (h a)
          linarith
      _ = (|σ| * |t| + |h σ|) + (|a| * |t| + |h a|) := by rw [abs_mul, abs_mul]
  have hσa : |σ| ≤ 1 := by rw [abs_le]; exact ⟨by linarith, hσ1⟩
  have haa : |a| ≤ 3/2 := by rw [abs_le]; exact ⟨by linarith, ha2⟩
  have h1'' : |σ| * |t| ≤ 1 * (3/2) := mul_le_mul hσa ht2 (abs_nonneg t) (by norm_num)
  have h2'' : |a| * |t| ≤ (3/2) * (3/2) := mul_le_mul haa ht2 (abs_nonneg t) (by norm_num)
  linarith [h1', h1'', h2'', h0 σ, h0 a, hδ1]

/-- The `a`-derivative of the radicand `krad`. -/
lemma krad_hasDerivAt {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤:ℕ∞) h) (σ t a : ℝ) :
    HasDerivAt (fun a' => Work.OddVolterra.krad h σ t a')
      ((deriv (fun a' => Work.OddVolterra.hquot h a' σ) a)
          * (Work.OddVolterra.line h σ t + Work.OddVolterra.line h a t)
        + (t + Work.OddVolterra.hquot h a σ) * (t + deriv h a)) a := by
  have h1 : HasDerivAt (fun a' => t + Work.OddVolterra.hquot h a' σ)
      (deriv (fun a' => Work.OddVolterra.hquot h a' σ) a) a := by
    have hd : HasDerivAt (fun a' : ℝ => Work.OddVolterra.hquot h a' σ)
        (deriv (fun a' : ℝ => Work.OddVolterra.hquot h a' σ) a) a :=
      ((contDiff_hquot_snd hh σ).differentiable (by simp) a).hasDerivAt
    have hc : HasDerivAt (fun _ : ℝ => t) (0:ℝ) a := hasDerivAt_const a t
    have hsum := hc.add hd
    have heq : (fun a' : ℝ => t + Work.OddVolterra.hquot h a' σ)
        = (fun _ : ℝ => t) + (fun a' : ℝ => Work.OddVolterra.hquot h a' σ) := rfl
    rw [heq]
    simpa using hsum
  have h2 : HasDerivAt (fun a' => Work.OddVolterra.line h σ t + Work.OddVolterra.line h a' t)
      (t + deriv h a) a := by
    have h3 : HasDerivAt (fun a' : ℝ => a' * t) t a := by
      simpa using (hasDerivAt_id a).mul_const t
    have h4 : HasDerivAt (fun a' : ℝ => h a') (deriv h a) a :=
      ((hh.differentiable (by simp)) a).hasDerivAt
    have h5 : HasDerivAt (fun a' : ℝ => a' * t + h a') (t + deriv h a) a := h3.add h4
    have h6 : HasDerivAt (fun a' : ℝ => Work.OddVolterra.line h a' t) (t + deriv h a) a := by
      have he : (fun a' : ℝ => a' * t + h a') = fun a' : ℝ => Work.OddVolterra.line h a' t := by
        funext a'; unfold Work.OddVolterra.line; ring
      rw [he] at h5; exact h5
    exact h6.const_add (Work.OddVolterra.line h σ t)
  have h3 := h1.mul h2
  have he : (fun a' : ℝ => Work.OddVolterra.krad h σ t a')
      = (fun a' : ℝ => t + Work.OddVolterra.hquot h a' σ)
        * (fun a' : ℝ => Work.OddVolterra.line h σ t + Work.OddVolterra.line h a' t) := by
    funext a'
    rw [Pi.mul_apply, Work.OddVolterra.krad_apply]
  rw [he]
  convert h3 using 1

/-- The `a`-derivative of `krad` for the reference `h = 0`. -/
lemma krad_deriv_zero (σ t a : ℝ) :
    deriv (fun a' : ℝ => Work.OddVolterra.krad (0:ℝ→ℝ) σ t a') a = t^2 := by
  have hk : (fun a' : ℝ => Work.OddVolterra.krad (0:ℝ→ℝ) σ t a')
      = fun a' : ℝ => t^2 * a' + t^2 * σ := by
    funext u
    rw [Work.OddVolterra.krad_apply, hquot_zero]
    unfold Work.OddVolterra.line
    simp
    ring
  rw [hk]
  have h1 : HasDerivAt (fun a' : ℝ => t^2 * a' + t^2 * σ) (t^2) a := by
    have := (hasDerivAt_id a).const_mul (t^2)
    simpa using this.add_const (t^2 * σ)
  exact h1.deriv

/-- Bound for the `a`-derivative of `krad` on the region. -/
lemma krad_deriv_bound {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤:ℕ∞) h)
    (h0 : ∀ x : ℝ, |h x| ≤ 1/100) (h1 : ∀ x : ℝ, |deriv h x| ≤ 1/100)
    (h2 : ∀ x : ℝ, |iteratedDeriv 2 h x| ≤ 1/100)
    {a σ t : ℝ} (ha : (1/4 : ℝ) ≤ a) (ha2 : a ≤ 3/2) (hσ : (1/2 : ℝ) ≤ σ) (hσ1 : σ ≤ 1)
    (ht2 : |t| ≤ 3/2) :
    |deriv (fun a' => Work.OddVolterra.krad h σ t a') a| ≤ 3 := by
  rw [(krad_hasDerivAt hh σ t a).deriv]
  have hq : |Work.OddVolterra.hquot h a σ| ≤ 1/100 :=
    Work.OddVolterra.abs_hquot_le h1 (by norm_num)
  have hqd : |deriv (fun a' : ℝ => Work.OddVolterra.hquot h a' σ) a| ≤ 1/100 :=
    hquot_deriv_bound hh (by norm_num) h2 σ a
  have hL : |Work.OddVolterra.line h σ t + Work.OddVolterra.line h a t| ≤ 4 :=
    line_sum_bound (by norm_num) (by norm_num) h0 (by linarith) ha2 (by linarith) hσ1 ht2
  have h2' : |t + deriv h a| ≤ 3/2 + 1/100 := by
    rw [abs_le] at ht2 ⊢
    have := abs_le.mp (h1 a)
    constructor <;> linarith
  calc |deriv (fun a' : ℝ => Work.OddVolterra.hquot h a' σ) a
          * (Work.OddVolterra.line h σ t + Work.OddVolterra.line h a t)
        + (t + Work.OddVolterra.hquot h a σ) * (t + deriv h a)|
      ≤ |deriv (fun a' : ℝ => Work.OddVolterra.hquot h a' σ) a
          * (Work.OddVolterra.line h σ t + Work.OddVolterra.line h a t)|
        + |(t + Work.OddVolterra.hquot h a σ) * (t + deriv h a)| := abs_add_le _ _
    _ = |deriv (fun a' : ℝ => Work.OddVolterra.hquot h a' σ) a|
          * |Work.OddVolterra.line h σ t + Work.OddVolterra.line h a t|
        + |t + Work.OddVolterra.hquot h a σ| * |t + deriv h a| := by rw [abs_mul, abs_mul]
    _ ≤ (1/100) * 4 + (3/2 + 1/100) * (3/2 + 1/100) := by
        refine add_le_add ?_ ?_
        · exact mul_le_mul hqd hL (abs_nonneg _) (by norm_num)
        · refine mul_le_mul ?_ h2' (abs_nonneg _) (by linarith)
          rw [abs_le] at ht2 ⊢
          have := abs_le.mp hq
          constructor <;> linarith
    _ ≤ 3 := by norm_num

/-- Difference bound for the `a`-derivative of `krad`. -/
lemma krad_deriv_diff {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤:ℕ∞) h) {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hδ1 : δ ≤ 1/100)
    (h0 : ∀ x : ℝ, |h x| ≤ δ) (h1 : ∀ x : ℝ, |deriv h x| ≤ δ)
    (h2 : ∀ x : ℝ, |iteratedDeriv 2 h x| ≤ δ) {a σ t : ℝ}
    (ha : (1/4 : ℝ) ≤ a) (ha2 : a ≤ 3/2) (hσ : (1/2 : ℝ) ≤ σ) (hσ1 : σ ≤ 1)
    (ht2 : |t| ≤ 3/2) :
    |deriv (fun a' => Work.OddVolterra.krad h σ t a') a
      - deriv (fun a' => Work.OddVolterra.krad (0:ℝ→ℝ) σ t a') a| ≤ 10 * δ := by
  rw [(krad_hasDerivAt hh σ t a).deriv, krad_deriv_zero σ t a]
  have hq : |Work.OddVolterra.hquot h a σ| ≤ δ := Work.OddVolterra.abs_hquot_le h1 hδ0
  have hqd : |deriv (fun a' : ℝ => Work.OddVolterra.hquot h a' σ) a| ≤ δ :=
    hquot_deriv_bound hh hδ0 h2 σ a
  have hL : |Work.OddVolterra.line h σ t + Work.OddVolterra.line h a t| ≤ 4 :=
    line_sum_bound hδ0 hδ1 h0 (by linarith) ha2 (by linarith) hσ1 ht2
  have h2' : |t + deriv h a| ≤ 3/2 + δ := by
    rw [abs_le] at ht2 ⊢
    have := abs_le.mp (h1 a)
    constructor <;> linarith
  have hkey : deriv (fun a' : ℝ => Work.OddVolterra.hquot h a' σ) a
          * (Work.OddVolterra.line h σ t + Work.OddVolterra.line h a t)
        + (t + Work.OddVolterra.hquot h a σ) * (t + deriv h a) - t^2
      = (deriv (fun a' : ℝ => Work.OddVolterra.hquot h a' σ) a)
          * (Work.OddVolterra.line h σ t + Work.OddVolterra.line h a t)
        + (t * deriv h a + Work.OddVolterra.hquot h a σ * (t + deriv h a)) := by ring
  rw [hkey]
  refine le_trans (abs_add_le _ _) ?_
  have hA : |deriv (fun a' : ℝ => Work.OddVolterra.hquot h a' σ) a
      * (Work.OddVolterra.line h σ t + Work.OddVolterra.line h a t)| ≤ δ * 4 := by
    rw [abs_mul]
    exact mul_le_mul hqd hL (abs_nonneg _) hδ0
  have hB : |t * deriv h a + Work.OddVolterra.hquot h a σ * (t + deriv h a)|
      ≤ (3/2) * δ + δ * (3/2 + δ) := by
    refine le_trans (abs_add_le _ _) ?_
    rw [abs_mul, abs_mul]
    have h1' : |t| * |deriv h a| ≤ (3/2) * δ :=
      mul_le_mul ht2 (h1 a) (abs_nonneg _) (by norm_num)
    have h2'' : |Work.OddVolterra.hquot h a σ| * |t + deriv h a| ≤ δ * (3/2 + δ) :=
      mul_le_mul hq h2' (abs_nonneg _) hδ0
    linarith
  nlinarith [hA, hB, hδ0, hδ1]





/-- The `a`-derivative of `Kden`. -/
lemma Kden_hasDerivAt {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤:ℕ∞) h) {σ t a : ℝ}
    (hpos : 0 < Work.OddVolterra.krad h σ t a) :
    HasDerivAt (fun a' => Kden h a' σ t)
      (((deriv (fun a' => Work.OddVolterra.hquot h a' σ) a)
          * (Work.OddVolterra.line h σ t + Work.OddVolterra.line h a t)
        + (t + Work.OddVolterra.hquot h a σ) * (t + deriv h a)) / (2 * Kden h a σ t)) a := by
  have hs := (krad_hasDerivAt hh σ t a).sqrt (ne_of_gt hpos)
  have h1 : (fun a' : ℝ => Real.sqrt (Work.OddVolterra.krad h σ t a'))
      = fun a' : ℝ => Kden h a' σ t := by
    funext u; rw [Kden_eq_sqrt_krad]
  have h2 : (2 * Real.sqrt (Work.OddVolterra.krad h σ t a)) = 2 * Kden h a σ t := by
    rw [Kden_eq_sqrt_krad]
  rw [h1, h2] at hs
  exact hs

/-- Bound for the explicit `a`-derivative expression of `krad`. -/
lemma krad_expr_bound {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤:ℕ∞) h)
    (h0 : ∀ x : ℝ, |h x| ≤ 1/100) (h1 : ∀ x : ℝ, |deriv h x| ≤ 1/100)
    (h2 : ∀ x : ℝ, |iteratedDeriv 2 h x| ≤ 1/100)
    {a σ t : ℝ} (ha : (1/4 : ℝ) ≤ a) (ha2 : a ≤ 3/2) (hσ : (1/2 : ℝ) ≤ σ) (hσ1 : σ ≤ 1)
    (ht2 : |t| ≤ 3/2) :
    |(deriv (fun a' => Work.OddVolterra.hquot h a' σ) a)
        * (Work.OddVolterra.line h σ t + Work.OddVolterra.line h a t)
      + (t + Work.OddVolterra.hquot h a σ) * (t + deriv h a)| ≤ 3 := by
  rw [← (krad_hasDerivAt hh σ t a).deriv]
  exact krad_deriv_bound hh h0 h1 h2 ha ha2 hσ hσ1 ht2

/-- Bound for the `a`-derivative of `Kden`. -/
lemma Kden_deriv_bound {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤:ℕ∞) h)
    (h0 : ∀ x : ℝ, |h x| ≤ 1/100) (h1 : ∀ x : ℝ, |deriv h x| ≤ 1/100)
    (h2 : ∀ x : ℝ, |iteratedDeriv 2 h x| ≤ 1/100)
    {a σ t : ℝ} (ha : (1/4 : ℝ) ≤ a) (ha2 : a ≤ 3/2) (hσ : (1/2 : ℝ) ≤ σ) (hσ1 : σ ≤ 1)
    (ht : (1/5 : ℝ) ≤ |t|) (ht2 : |t| ≤ 3/2) :
    |deriv (fun a' => Kden h a' σ t) a| ≤ 15 := by
  have hklo := (krad_region h0 h1 ha ha2 hσ hσ1 ht ht2).1
  have hkd := krad_expr_bound hh h0 h1 h2 ha ha2 hσ hσ1 ht2
  have hder := (Kden_hasDerivAt hh (by linarith : 0 < Work.OddVolterra.krad h σ t a)).deriv
  rw [hder]
  have hK : (1/10 : ℝ) ≤ Kden h a σ t := (Kden_basic h0 h1 ha ha2 hσ hσ1 ht ht2).1
  have hKpos : (0:ℝ) < Kden h a σ t := by linarith
  rw [abs_div]
  have hden : |(2:ℝ) * Kden h a σ t| = 2 * Kden h a σ t := by
    rw [abs_of_pos (by linarith : (0:ℝ) < 2 * Kden h a σ t)]
  rw [hden, div_le_iff₀ (by linarith : (0:ℝ) < 2 * Kden h a σ t)]
  linarith [hkd, hK]

/-- Difference bound for the `a`-derivative of `Kden`. -/
lemma Kden_deriv_diff {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤:ℕ∞) h) {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hδ1 : δ ≤ 1/100)
    (h0 : ∀ x : ℝ, |h x| ≤ δ) (hh0 : ∀ x : ℝ, |h x| ≤ 1/100)
    (h1 : ∀ x : ℝ, |deriv h x| ≤ δ) (hh1 : ∀ x : ℝ, |deriv h x| ≤ 1/100)
    (h2 : ∀ x : ℝ, |iteratedDeriv 2 h x| ≤ δ)
    (hh2 : ∀ x : ℝ, |iteratedDeriv 2 h x| ≤ 1/100)
    {a σ t : ℝ} (ha : (1/4 : ℝ) ≤ a) (ha2 : a ≤ 3/2) (hσ : (1/2 : ℝ) ≤ σ) (hσ1 : σ ≤ 1)
    (ht : (1/5 : ℝ) ≤ |t|) (ht2 : |t| ≤ 3/2) :
    |deriv (fun a' => Kden h a' σ t) a - deriv (fun a' => Kden (0:ℝ→ℝ) a' σ t) a| ≤ 20000 * δ := by
  have hzh : ∀ x : ℝ, |(0:ℝ→ℝ) x| ≤ 1/100 := fun x => by simp
  have hzd : ∀ x : ℝ, |deriv (0:ℝ→ℝ) x| ≤ 1/100 := fun x => by simp
  have hz2 : ∀ x : ℝ, |iteratedDeriv 2 (0:ℝ→ℝ) x| ≤ 1/100 := fun x => by simp
  have hklo := (krad_region hh0 hh1 ha ha2 hσ hσ1 ht ht2).1
  have hklo0 := (krad_region (h := (0:ℝ→ℝ)) hzh hzd ha ha2 hσ hσ1 ht ht2).1
  have hkd0 := krad_deriv_bound (h := (0:ℝ→ℝ)) contDiff_const hzh hzd hz2 ha ha2 hσ hσ1 ht2
  have hkdd := krad_deriv_diff hh hδ0 hδ1 h0 h1 h2 ha ha2 hσ hσ1 ht2
  have hK := Kden_basic hh0 hh1 ha ha2 hσ hσ1 ht ht2
  have hK0 := Kden_basic (h := (0:ℝ→ℝ)) hzh hzd ha ha2 hσ hσ1 ht ht2
  have hKd := Kden_diff_bound hδ0 hδ1 h0 hh0 h1 hh1 ha ha2 hσ hσ1 ht ht2
  have hdenk : deriv (fun a' : ℝ => Kden h a' σ t) a
      = deriv (fun a' : ℝ => Work.OddVolterra.krad h σ t a') a / (2 * Kden h a σ t) := by
    rw [(Kden_hasDerivAt hh (by linarith : 0 < Work.OddVolterra.krad h σ t a)).deriv,
      (krad_hasDerivAt hh σ t a).deriv]
  have hdenk0 : deriv (fun a' : ℝ => Kden (0:ℝ→ℝ) a' σ t) a
      = deriv (fun a' : ℝ => Work.OddVolterra.krad (0:ℝ→ℝ) σ t a') a / (2 * Kden (0:ℝ→ℝ) a σ t) := by
    rw [(Kden_hasDerivAt (h := (0:ℝ→ℝ)) contDiff_const
        (by linarith : 0 < Work.OddVolterra.krad (0:ℝ→ℝ) σ t a)).deriv,
      (krad_hasDerivAt (h := (0:ℝ→ℝ)) contDiff_const σ t a).deriv]
  rw [hdenk, hdenk0]
  have hKp : (0:ℝ) < Kden h a σ t := by linarith [hK.1]
  have hKp0 : (0:ℝ) < Kden (0:ℝ→ℝ) a σ t := by linarith [hK0.1]
  have ha1 : deriv (fun a' : ℝ => Work.OddVolterra.krad h σ t a') a
      / (2 * Kden h a σ t) - deriv (fun a' : ℝ => Work.OddVolterra.krad (0:ℝ→ℝ) σ t a') a
      / (2 * Kden (0:ℝ→ℝ) a σ t)
      = (deriv (fun a' : ℝ => Work.OddVolterra.krad h σ t a') a * Kden (0:ℝ→ℝ) a σ t
          - deriv (fun a' : ℝ => Work.OddVolterra.krad (0:ℝ→ℝ) σ t a') a * Kden h a σ t)
        / (2 * Kden h a σ t * Kden (0:ℝ→ℝ) a σ t) := by
    have h1' : Kden h a σ t ≠ 0 := ne_of_gt hKp
    have h2' : Kden (0:ℝ→ℝ) a σ t ≠ 0 := ne_of_gt hKp0
    field_simp
    try ring
  rw [ha1]
  have hden : (0:ℝ) < 2 * Kden h a σ t * Kden (0:ℝ→ℝ) a σ t := by positivity
  rw [abs_div, abs_of_pos hden]
  rw [div_le_iff₀ hden]
  have hnum : |deriv (fun a' : ℝ => Work.OddVolterra.krad h σ t a') a * Kden (0:ℝ→ℝ) a σ t
        - deriv (fun a' : ℝ => Work.OddVolterra.krad (0:ℝ→ℝ) σ t a') a * Kden h a σ t|
      ≤ 330 * δ := by
    have hkey : deriv (fun a' : ℝ => Work.OddVolterra.krad h σ t a') a * Kden (0:ℝ→ℝ) a σ t
          - deriv (fun a' : ℝ => Work.OddVolterra.krad (0:ℝ→ℝ) σ t a') a * Kden h a σ t
        = (deriv (fun a' : ℝ => Work.OddVolterra.krad h σ t a') a
              - deriv (fun a' : ℝ => Work.OddVolterra.krad (0:ℝ→ℝ) σ t a') a) * Kden (0:ℝ→ℝ) a σ t
          + deriv (fun a' : ℝ => Work.OddVolterra.krad (0:ℝ→ℝ) σ t a') a
            * (Kden (0:ℝ→ℝ) a σ t - Kden h a σ t) := by ring
    rw [hkey]
    refine le_trans (abs_add_le _ _) ?_
    rw [abs_mul, abs_mul]
    have hfirst : |deriv (fun a' : ℝ => Work.OddVolterra.krad h σ t a') a
            - deriv (fun a' : ℝ => Work.OddVolterra.krad (0:ℝ→ℝ) σ t a') a| * |Kden (0:ℝ→ℝ) a σ t|
        ≤ 30 * δ := by
      have h4 : |deriv (fun a' : ℝ => Work.OddVolterra.krad h σ t a') a
          - deriv (fun a' : ℝ => Work.OddVolterra.krad (0:ℝ→ℝ) σ t a') a| ≤ 10 * δ := hkdd
      have h5 : |Kden (0:ℝ→ℝ) a σ t| ≤ 3 := by
        rw [abs_of_pos hKp0]; exact hK0.2
      calc |deriv (fun a' : ℝ => Work.OddVolterra.krad h σ t a') a
            - deriv (fun a' : ℝ => Work.OddVolterra.krad (0:ℝ→ℝ) σ t a') a| * |Kden (0:ℝ→ℝ) a σ t|
          ≤ (10 * δ) * 3 := mul_le_mul h4 h5 (abs_nonneg _) (by linarith)
        _ ≤ 30 * δ := by linarith
    have hsecond : |deriv (fun a' : ℝ => Work.OddVolterra.krad (0:ℝ→ℝ) σ t a') a|
            * |Kden (0:ℝ→ℝ) a σ t - Kden h a σ t| ≤ 300 * δ := by
      have h5 : |deriv (fun a' : ℝ => Work.OddVolterra.krad (0:ℝ→ℝ) σ t a') a| ≤ 3 := hkd0
      have h6 : |Kden (0:ℝ→ℝ) a σ t - Kden h a σ t| ≤ 100 * δ := by
        rw [abs_sub_comm]; exact hKd
      calc |deriv (fun a' : ℝ => Work.OddVolterra.krad (0:ℝ→ℝ) σ t a') a|
            * |Kden (0:ℝ→ℝ) a σ t - Kden h a σ t|
          ≤ 3 * (100 * δ) := mul_le_mul h5 h6 (abs_nonneg _) (by norm_num)
        _ ≤ 300 * δ := by linarith
    linarith
  calc |deriv (fun a' : ℝ => Work.OddVolterra.krad h σ t a') a * Kden (0:ℝ→ℝ) a σ t
        - deriv (fun a' : ℝ => Work.OddVolterra.krad (0:ℝ→ℝ) σ t a') a * Kden h a σ t|
      ≤ 330 * δ := hnum
    _ ≤ (20000 * δ) * (2 * Kden h a σ t * Kden (0:ℝ→ℝ) a σ t) := by
        have hprod : (1/100 : ℝ) ≤ Kden h a σ t * Kden (0:ℝ→ℝ) a σ t := by
          nlinarith [hK.1, hK0.1]
        nlinarith [hprod, hδ0]





lemma J1M_hasDerivAt {n : ℕ} {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤:ℕ∞) h) (a σ t : ℝ) :
    HasDerivAt (fun a' : ℝ => J1M n h a' σ t) (deriv (fun a' : ℝ => J1M n h a' σ t) a) a :=
  (((Rnu_contDiff ((n:ℝ)+1/2) hh (init := fun _ => (1:ℝ)) contDiff_const (n+1)).comp
    (by fun_prop : ContDiff ℝ (⊤:ℕ∞) fun a' : ℝ => (a', σ, t))).differentiable (by simp) a).hasDerivAt

lemma J2M_hasDerivAt {n : ℕ} {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤:ℕ∞) h) (a σ t : ℝ) :
    HasDerivAt (fun a' : ℝ => J2M n h a' σ t) (deriv (fun a' : ℝ => J2M n h a' σ t) a) a := by
  have hinit : ContDiff ℝ (⊤:ℕ∞) (fun q : ℝ × ℝ × ℝ => lineSlope h q.1 q.2.2) := by
    unfold lineSlope; fun_prop
  exact (((Rnu_contDiff ((n:ℝ)-1/2) hh (init := fun q : ℝ × ℝ × ℝ => lineSlope h q.1 q.2.2) hinit n).comp
    (by fun_prop : ContDiff ℝ (⊤:ℕ∞) fun a' : ℝ => (a', σ, t))).differentiable (by simp) a).hasDerivAt

/-- Quotient-rule expression for the derivative of `K1M`. -/
lemma K1M_deriv_eq {n : ℕ} {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤:ℕ∞) h) {a σ t : ℝ}
    (hpos : 0 < Work.OddVolterra.krad h σ t a) :
    deriv (fun a' : ℝ => K1M n h a' σ t) a
      = (deriv (fun a' : ℝ => J1M n h a' σ t) a * Kden h a σ t
          - J1M n h a σ t * deriv (fun a' : ℝ => Kden h a' σ t) a) / (Kden h a σ t)^2 := by
  have hdK : HasDerivAt (fun a' : ℝ => Kden h a' σ t) (deriv (fun a' : ℝ => Kden h a' σ t) a) a :=
    (Kden_hasDerivAt hh hpos).differentiableAt.hasDerivAt
  have hne : Kden h a σ t ≠ 0 := by
    rw [Kden_eq_sqrt_krad]; exact ne_of_gt (Real.sqrt_pos.mpr hpos)
  have hthis := ((J1M_hasDerivAt (n := n) hh a σ t).div hdK hne).deriv
  have hfun : (fun a' : ℝ => K1M n h a' σ t)
      = (fun a' : ℝ => J1M n h a' σ t) / (fun a' : ℝ => Kden h a' σ t) := by
    funext u; rw [Pi.div_apply, K1M]
  rw [hfun]
  exact hthis

/-- Quotient-rule expression for the derivative of `K2M`. -/
lemma K2M_deriv_eq {n : ℕ} {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤:ℕ∞) h) {a σ t : ℝ}
    (hpos : 0 < Work.OddVolterra.krad h σ t a) :
    deriv (fun a' : ℝ => K2M n h a' σ t) a
      = (deriv (fun a' : ℝ => J2M n h a' σ t) a * Kden h a σ t
          - J2M n h a σ t * deriv (fun a' : ℝ => Kden h a' σ t) a) / (Kden h a σ t)^2 := by
  have hdK : HasDerivAt (fun a' : ℝ => Kden h a' σ t) (deriv (fun a' : ℝ => Kden h a' σ t) a) a :=
    (Kden_hasDerivAt hh hpos).differentiableAt.hasDerivAt
  have hne : Kden h a σ t ≠ 0 := by
    rw [Kden_eq_sqrt_krad]; exact ne_of_gt (Real.sqrt_pos.mpr hpos)
  have hthis := ((J2M_hasDerivAt (n := n) hh a σ t).div hdK hne).deriv
  have hfun : (fun a' : ℝ => K2M n h a' σ t)
      = (fun a' : ℝ => J2M n h a' σ t) / (fun a' : ℝ => Kden h a' σ t) := by
    funext u; rw [Pi.div_apply, K2M]
  rw [hfun]
  exact hthis

/-- The general estimate for the difference of two quotient-rule derivatives. -/
lemma quot_rule_diff_estimate {dJh Jh Kh dKh dJz Jz Kz dKz A D δ : ℝ}
    (hA : 0 ≤ A) (hD : 0 ≤ D) (hδ : 0 ≤ δ)
    (hJh : |Jh| ≤ A) (hdJh : |dJh| ≤ A) (hJz : |Jz| ≤ A) (hdJz : |dJz| ≤ A)
    (hJd : |Jh - Jz| ≤ D * δ) (hdJd : |dJh - dJz| ≤ D * δ)
    (hKh : (1/10 : ℝ) ≤ Kh) (hKh3 : Kh ≤ 3) (hKz : (1/10 : ℝ) ≤ Kz) (hKz3 : Kz ≤ 3)
    (hKd : |Kh - Kz| ≤ 100 * δ) (hdKh : |dKh| ≤ 15) (hdKz : |dKz| ≤ 15)
    (hdKd : |dKh - dKz| ≤ 20000 * δ) :
    |(dJh * Kh - Jh * dKh) / Kh^2 - (dJz * Kz - Jz * dKz) / Kz^2|
      ≤ ((162 * D + 189900 * A) * 10000) * δ := by
  have hKh0 : Kh ≠ 0 := by linarith
  have hKz0 : Kz ≠ 0 := by linarith
  have hK2 : |Kh^2| = Kh^2 := by rw [abs_of_nonneg (by positivity)]
  have hK2' : |Kz^2| = Kz^2 := by rw [abs_of_nonneg (by positivity)]
  have hden : (1/10000 : ℝ) ≤ Kh^2 * Kz^2 := by
    have h1 : ((1/10:ℝ) * (1/10)) ≤ Kh * Kz := mul_le_mul hKh hKz (by norm_num) (by linarith)
    have h2 : ((1/10:ℝ) * (1/10))^2 ≤ (Kh * Kz)^2 := pow_le_pow_left₀ (by norm_num) h1 2
    have h3 : ((1/10:ℝ) * (1/10))^2 = 1/10000 := by norm_num
    have h4 : (Kh * Kz)^2 = Kh^2 * Kz^2 := by ring
    linarith [h2, h3.le, h4.le]
  have hmain : (dJh * Kh - Jh * dKh) / Kh^2 - (dJz * Kz - Jz * dKz) / Kz^2
      = ((dJh * Kh - Jh * dKh) * Kz^2 - (dJz * Kz - Jz * dKz) * Kh^2) / (Kh^2 * Kz^2) := by
    field_simp
    try ring
  have hposd : (0:ℝ) < Kh^2 * Kz^2 := by linarith [hden]
  rw [hmain, abs_div, abs_of_pos hposd]
  rw [div_le_iff₀ hposd]
  have hkey : (dJh * Kh - Jh * dKh) * Kz^2 - (dJz * Kz - Jz * dKz) * Kh^2
      = (dJh - dJz) * Kh * Kz^2
        + dJz * Kh * Kz * (Kz - Kh)
        - (Jh - Jz) * dKh * Kz^2
        + Jz * ((dKz - dKh) * Kh^2 + dKh * (Kh^2 - Kz^2)) := by ring
  rw [hkey]
  have hKh3' : |Kh| ≤ 3 := by
    rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ Kh)]; exact hKh3
  have hKz3' : |Kz| ≤ 3 := by
    rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ Kz)]; exact hKz3
  have hDδ : (0:ℝ) ≤ D * δ := mul_nonneg hD hδ
  have hA0 : (0:ℝ) ≤ A := hA
  have hK2b : Kz^2 ≤ 9 := by nlinarith [hKz3']
  have hKh2b : Kh^2 ≤ 9 := by nlinarith [hKh3']
  have h1 : |(dJh - dJz) * Kh * Kz^2| ≤ 27 * D * δ := by
    rw [abs_mul, abs_mul, hK2']
    have hb : |dJh - dJz| * |Kh| ≤ D * δ * 3 :=
      le_trans (mul_le_mul hdJd hKh3' (abs_nonneg _) hDδ) (le_of_eq (by ring))
    calc |dJh - dJz| * |Kh| * Kz^2 ≤ (D * δ * 3) * 9 :=
          mul_le_mul hb hK2b (by positivity) (by linarith [hDδ])
      _ = 27 * D * δ := by ring
  have h2 : |dJz * Kh * Kz * (Kz - Kh)| ≤ 900 * A * δ := by
    rw [abs_mul, abs_mul, abs_mul]
    have hKd' : |Kz - Kh| ≤ 100 * δ := by rw [abs_sub_comm]; exact hKd
    have hb : |dJz| * |Kh| * |Kz| ≤ A * 3 * 3 := by
      refine mul_le_mul (mul_le_mul hdJz hKh3' (abs_nonneg _) hA0) hKz3' (abs_nonneg _) (by linarith [hA0])
    calc |dJz| * |Kh| * |Kz| * |Kz - Kh| ≤ (A * 3 * 3) * (100 * δ) :=
          mul_le_mul hb hKd' (abs_nonneg _) (by linarith [hA0])
      _ = 900 * A * δ := by ring
  have h3 : |(Jh - Jz) * dKh * Kz^2| ≤ 135 * D * δ := by
    rw [abs_mul, abs_mul, hK2']
    have hb : |Jh - Jz| * |dKh| ≤ D * δ * 15 :=
      le_trans (mul_le_mul hJd hdKh (abs_nonneg _) hDδ) (le_of_eq (by ring))
    calc |Jh - Jz| * |dKh| * Kz^2 ≤ (D * δ * 15) * 9 :=
          mul_le_mul hb hK2b (by positivity) (by linarith [hDδ])
      _ = 135 * D * δ := by ring
  have h4 : |Jz * ((dKz - dKh) * Kh^2 + dKh * (Kh^2 - Kz^2))| ≤ 189000 * A * δ := by
    rw [abs_mul]
    have hinner : |(dKz - dKh) * Kh^2 + dKh * (Kh^2 - Kz^2)| ≤ 189000 * δ := by
      refine le_trans (abs_add_le _ _) ?_
      rw [abs_mul, abs_mul]
      have hdKd' : |dKz - dKh| ≤ 20000 * δ := by rw [abs_sub_comm]; exact hdKd
      have hfac : |Kh^2 - Kz^2| ≤ 600 * δ := by
        have hfac2 : |Kh^2 - Kz^2| = |Kh - Kz| * |Kh + Kz| := by
          rw [show Kh^2 - Kz^2 = (Kh - Kz) * (Kh + Kz) by ring, abs_mul]
        rw [hfac2]
        have hsum : |Kh + Kz| ≤ 6 := by
          rw [abs_le]; constructor <;> linarith
        calc |Kh - Kz| * |Kh + Kz| ≤ (100 * δ) * 6 := mul_le_mul hKd hsum (abs_nonneg _) (by positivity)
          _ = 600 * δ := by ring
      have hb1 : |dKz - dKh| * |Kh^2| ≤ (20000 * δ) * 9 := by
        rw [abs_of_nonneg (sq_nonneg Kh)]
        exact mul_le_mul hdKd' hKh2b (by positivity) (by linarith [hδ])
      have hb2 : |dKh| * |Kh^2 - Kz^2| ≤ 15 * (600 * δ) :=
        mul_le_mul hdKh hfac (abs_nonneg _) (by norm_num)
      calc |dKz - dKh| * |Kh^2| + |dKh| * |Kh^2 - Kz^2| ≤ (20000 * δ) * 9 + 15 * (600 * δ) :=
            add_le_add hb1 hb2
        _ = 189000 * δ := by ring
    calc |Jz| * |(dKz - dKh) * Kh^2 + dKh * (Kh^2 - Kz^2)| ≤ A * (189000 * δ) :=
          mul_le_mul hJz hinner (abs_nonneg _) hA0
      _ = 189000 * A * δ := by ring
  have htot : |(dJh - dJz) * Kh * Kz^2 + dJz * Kh * Kz * (Kz - Kh)
        - (Jh - Jz) * dKh * Kz^2 + Jz * ((dKz - dKh) * Kh^2 + dKh * (Kh^2 - Kz^2))|
      ≤ (162 * D + 189900 * A) * δ := by
    have hsplit : (dJh - dJz) * Kh * Kz^2 + dJz * Kh * Kz * (Kz - Kh)
          - (Jh - Jz) * dKh * Kz^2 + Jz * ((dKz - dKh) * Kh^2 + dKh * (Kh^2 - Kz^2))
        = ((dJh - dJz) * Kh * Kz^2 + dJz * Kh * Kz * (Kz - Kh))
          + (-((Jh - Jz) * dKh * Kz^2) + Jz * ((dKz - dKh) * Kh^2 + dKh * (Kh^2 - Kz^2))) := by
      ring
    rw [hsplit]
    have hX : |(dJh - dJz) * Kh * Kz^2 + dJz * Kh * Kz * (Kz - Kh)| ≤ 27 * D * δ + 900 * A * δ :=
      le_trans (abs_add_le _ _) (add_le_add h1 h2)
    have hY : |-((Jh - Jz) * dKh * Kz^2) + Jz * ((dKz - dKh) * Kh^2 + dKh * (Kh^2 - Kz^2))|
        ≤ 135 * D * δ + 189000 * A * δ := by
      have hneg : |-((Jh - Jz) * dKh * Kz^2)| ≤ 135 * D * δ := by
        rw [abs_neg]; exact h3
      exact le_trans (abs_add_le _ _) (add_le_add hneg h4)
    linarith [abs_add_le ((dJh - dJz) * Kh * Kz^2 + dJz * Kh * Kz * (Kz - Kh))
      (-((Jh - Jz) * dKh * Kz^2) + Jz * ((dKz - dKh) * Kh^2 + dKh * (Kh^2 - Kz^2))), hX, hY,
      hD, hA, hδ]
  calc |(dJh - dJz) * Kh * Kz^2 + dJz * Kh * Kz * (Kz - Kh)
        - (Jh - Jz) * dKh * Kz^2 + Jz * ((dKz - dKh) * Kh^2 + dKh * (Kh^2 - Kz^2))|
      ≤ (162 * D + 189900 * A) * δ := htot
    _ ≤ ((162 * D + 189900 * A) * 10000) * δ * (Kh^2 * Kz^2) := by
        have h4' : (0:ℝ) ≤ (162 * D + 189900 * A) * δ :=
          mul_nonneg (by linarith [hD, hA]) hδ
        nlinarith [hden, h4', hδ]





/-- **Closeness of the derivative of `K₁` in the perturbation.** -/
theorem K1M_deriv_diff (n : ℕ) (hn : 1 ≤ n) :
    ∃ C : ℝ, 0 < C ∧ ∀ h : ℝ → ℝ, ContDiff ℝ (⊤:ℕ∞) h →
      ∀ δ : ℝ, 0 < δ → δ ≤ 1/100 → (∀ k ≤ n+2, ∀ x : ℝ, |iteratedDeriv k h x| ≤ δ) →
      ∀ a ∈ Set.Icc (1/2 : ℝ) 1, ∀ σ ∈ Set.Icc (1/2 : ℝ) 1, ∀ t : ℝ,
        (1/5 : ℝ) ≤ |t| → |t| ≤ 3/2 →
        |deriv (fun a' : ℝ => K1M n h a' σ t) a - deriv (fun a' : ℝ => K1M n 0 a' σ t) a|
          ≤ C * δ := by
  obtain ⟨A1, D1, hA1, hD1, hJ⟩ := J1M_bounds n hn
  refine ⟨((162 * D1 + 189900 * A1) * 10000) + 1, by nlinarith [hA1, hD1], ?_⟩
  intro h hh δ hδ hδ1 hjet a ha σ hσ t ht ht2
  have ha' : (1/4 : ℝ) ≤ a := by linarith [ha.1]
  have ha2' : a ≤ 3/2 := by linarith [ha.2]
  have htIcc : t ∈ Set.Icc (-(3/2) : ℝ) (3/2) := Set.mem_Icc.mpr (abs_le.mp ht2)
  have hh0 : ∀ x : ℝ, |h x| ≤ 1/100 := fun x => le_trans (hjet 0 (by omega) x) hδ1
  have hh1 : ∀ x : ℝ, |deriv h x| ≤ 1/100 := fun x => by
    simpa [iteratedDeriv_one] using le_trans (hjet 1 (by omega) x) hδ1
  have hh2 : ∀ x : ℝ, |iteratedDeriv 2 h x| ≤ 1/100 := fun x =>
    le_trans (hjet 2 (by omega) x) hδ1
  have h0 : ∀ x : ℝ, |h x| ≤ δ := fun x => hjet 0 (by omega) x
  have h1 : ∀ x : ℝ, |deriv h x| ≤ δ := fun x => by
    simpa [iteratedDeriv_one] using hjet 1 (by omega) x
  have h2 : ∀ x : ℝ, |iteratedDeriv 2 h x| ≤ δ := fun x => hjet 2 (by omega) x
  have hKpos : 0 < Work.OddVolterra.krad h σ t a := by
    have := (krad_region hh0 hh1 ha' ha2' hσ.1 hσ.2 ht ht2).1
    linarith
  have hKpos0 : 0 < Work.OddVolterra.krad (0:ℝ→ℝ) σ t a := by
    have := (krad_region (h := (0:ℝ→ℝ)) (fun x => by norm_num) (fun x => by norm_num)
      ha' ha2' hσ.1 hσ.2 ht ht2).1
    linarith
  have hJz : |J1M n (0:ℝ→ℝ) a σ t| ≤ A1 ∧
      |deriv (fun a' : ℝ => J1M n (0:ℝ→ℝ) a' σ t) a| ≤ A1 ∧
      |J1M n (0:ℝ→ℝ) a σ t - J1M n 0 a σ t| ≤ D1 * δ ∧
      |deriv (fun a' : ℝ => J1M n (0:ℝ→ℝ) a' σ t) a - deriv (fun a' : ℝ => J1M n 0 a' σ t) a|
        ≤ D1 * δ := by
    have := hJ (0:ℝ→ℝ) contDiff_const δ hδ hδ1 (fun k hk x => by simp [hδ.le]) a ha σ hσ t htIcc
    simpa using this
  have hJh := hJ h hh δ hδ hδ1 hjet a ha σ hσ t htIcc
  have hKb := Kden_basic hh0 hh1 ha' ha2' hσ.1 hσ.2 ht ht2
  have hKb0 := Kden_basic (h := (0:ℝ→ℝ)) (fun x => by norm_num) (fun x => by norm_num)
    ha' ha2' hσ.1 hσ.2 ht ht2
  have hKd := Kden_diff_bound hδ.le hδ1 h0 hh0 h1 hh1 ha' ha2' hσ.1 hσ.2 ht ht2
  have hKdb := Kden_deriv_bound hh hh0 hh1 hh2 ha' ha2' hσ.1 hσ.2 ht ht2
  have hKdb0 := Kden_deriv_bound (h := (0:ℝ→ℝ)) contDiff_const (fun x => by norm_num)
    (fun x => by norm_num) (fun x => by norm_num) ha' ha2' hσ.1 hσ.2 ht ht2
  have hKdd := Kden_deriv_diff hh hδ.le hδ1 h0 hh0 h1 hh1 h2 hh2 ha' ha2' hσ.1 hσ.2 ht ht2
  rw [K1M_deriv_eq (n := n) hh hKpos, K1M_deriv_eq (n := n) (h := (0:ℝ→ℝ)) contDiff_const hKpos0]
  refine le_trans (quot_rule_diff_estimate hA1 hD1 hδ.le
    hJh.1 hJh.2.1 hJz.1 hJz.2.1 hJh.2.2.1 hJh.2.2.2
    hKb.1 hKb.2 hKb0.1 hKb0.2 hKd hKdb hKdb0 hKdd) ?_
  nlinarith [hδ.le, hA1, hD1]

/-- **Closeness of the derivative of `K₂` in the perturbation.** -/
theorem K2M_deriv_diff (n : ℕ) (hn : 1 ≤ n) :
    ∃ C : ℝ, 0 < C ∧ ∀ h : ℝ → ℝ, ContDiff ℝ (⊤:ℕ∞) h →
      ∀ δ : ℝ, 0 < δ → δ ≤ 1/100 → (∀ k ≤ n+2, ∀ x : ℝ, |iteratedDeriv k h x| ≤ δ) →
      ∀ a ∈ Set.Icc (1/2 : ℝ) 1, ∀ σ ∈ Set.Icc (1/2 : ℝ) 1, ∀ t : ℝ,
        (1/5 : ℝ) ≤ |t| → |t| ≤ 3/2 →
        |deriv (fun a' : ℝ => K2M n h a' σ t) a - deriv (fun a' : ℝ => K2M n 0 a' σ t) a|
          ≤ C * δ := by
  obtain ⟨A2, D2, hA2, hD2, hJ⟩ := J2M_bounds n hn
  refine ⟨((162 * D2 + 189900 * A2) * 10000) + 1, by nlinarith [hA2, hD2], ?_⟩
  intro h hh δ hδ hδ1 hjet a ha σ hσ t ht ht2
  have ha' : (1/4 : ℝ) ≤ a := by linarith [ha.1]
  have ha2' : a ≤ 3/2 := by linarith [ha.2]
  have htIcc : t ∈ Set.Icc (-(3/2) : ℝ) (3/2) := Set.mem_Icc.mpr (abs_le.mp ht2)
  have hh0 : ∀ x : ℝ, |h x| ≤ 1/100 := fun x => le_trans (hjet 0 (by omega) x) hδ1
  have hh1 : ∀ x : ℝ, |deriv h x| ≤ 1/100 := fun x => by
    simpa [iteratedDeriv_one] using le_trans (hjet 1 (by omega) x) hδ1
  have hh2 : ∀ x : ℝ, |iteratedDeriv 2 h x| ≤ 1/100 := fun x =>
    le_trans (hjet 2 (by omega) x) hδ1
  have h0 : ∀ x : ℝ, |h x| ≤ δ := fun x => hjet 0 (by omega) x
  have h1 : ∀ x : ℝ, |deriv h x| ≤ δ := fun x => by
    simpa [iteratedDeriv_one] using hjet 1 (by omega) x
  have h2 : ∀ x : ℝ, |iteratedDeriv 2 h x| ≤ δ := fun x => hjet 2 (by omega) x
  have hKpos : 0 < Work.OddVolterra.krad h σ t a := by
    have := (krad_region hh0 hh1 ha' ha2' hσ.1 hσ.2 ht ht2).1
    linarith
  have hKpos0 : 0 < Work.OddVolterra.krad (0:ℝ→ℝ) σ t a := by
    have := (krad_region (h := (0:ℝ→ℝ)) (fun x => by norm_num) (fun x => by norm_num)
      ha' ha2' hσ.1 hσ.2 ht ht2).1
    linarith
  have hJz : |J2M n (0:ℝ→ℝ) a σ t| ≤ A2 ∧
      |deriv (fun a' : ℝ => J2M n (0:ℝ→ℝ) a' σ t) a| ≤ A2 ∧
      |J2M n (0:ℝ→ℝ) a σ t - J2M n 0 a σ t| ≤ D2 * δ ∧
      |deriv (fun a' : ℝ => J2M n (0:ℝ→ℝ) a' σ t) a - deriv (fun a' : ℝ => J2M n 0 a' σ t) a|
        ≤ D2 * δ := by
    have := hJ (0:ℝ→ℝ) contDiff_const δ hδ hδ1 (fun k hk x => by simp [hδ.le]) a ha σ hσ t htIcc
    simpa using this
  have hJh := hJ h hh δ hδ hδ1 hjet a ha σ hσ t htIcc
  have hKb := Kden_basic hh0 hh1 ha' ha2' hσ.1 hσ.2 ht ht2
  have hKb0 := Kden_basic (h := (0:ℝ→ℝ)) (fun x => by norm_num) (fun x => by norm_num)
    ha' ha2' hσ.1 hσ.2 ht ht2
  have hKd := Kden_diff_bound hδ.le hδ1 h0 hh0 h1 hh1 ha' ha2' hσ.1 hσ.2 ht ht2
  have hKdb := Kden_deriv_bound hh hh0 hh1 hh2 ha' ha2' hσ.1 hσ.2 ht ht2
  have hKdb0 := Kden_deriv_bound (h := (0:ℝ→ℝ)) contDiff_const (fun x => by norm_num)
    (fun x => by norm_num) (fun x => by norm_num) ha' ha2' hσ.1 hσ.2 ht ht2
  have hKdd := Kden_deriv_diff hh hδ.le hδ1 h0 hh0 h1 hh1 h2 hh2 ha' ha2' hσ.1 hσ.2 ht ht2
  rw [K2M_deriv_eq (n := n) hh hKpos, K2M_deriv_eq (n := n) (h := (0:ℝ→ℝ)) contDiff_const hKpos0]
  refine le_trans (quot_rule_diff_estimate hA2 hD2 hδ.le
    hJh.1 hJh.2.1 hJz.1 hJz.2.1 hJh.2.2.1 hJh.2.2.2
    hKb.1 hKb.2 hKb0.1 hKb0.2 hKd hKdb hKdb0 hKdd) ?_
  nlinarith [hδ.le, hA2, hD2]








/-- The open set of first slots `a` on which the two Abel radicands are positive. -/
def Ksl (b : ℝ → ℝ) (σ : ℝ) (z : St) : Set ℝ :=
  {a : ℝ | 0 < krad b σ (-(z 0)) a ∧ 0 < krad b σ (z 1) a}

/-- The `i`-th component of the manifest kernel, as a function of its first slot. -/
def Kw (n : ℕ) (b : ℝ → ℝ) (σ : ℝ) (z : St) (i : Fin 2) : ℝ → ℝ :=
  fun a : ℝ => (KvecM n b a σ (z 0) (z 1) (z 2) (z 3)) i

lemma Kw_def (n : ℕ) (b : ℝ → ℝ) (σ : ℝ) (z : St) (i : Fin 2) :
    Kw n b σ z i = fun a : ℝ => (KvecM n b a σ (z 0) (z 1) (z 2) (z 3)) i := rfl

/-- `G₂M` is the Abel average of `KvecM`, componentwise. -/
lemma G2M_eq_abelAvg (n : ℕ) (b : ℝ → ℝ) (u σ : ℝ) (z : St) (i : Fin 2) :
    (G2M n b u σ (z 0) (z 1) (z 2) (z 3)) i
      = ∫ τ in (0:ℝ)..1, (Real.sqrt (τ * (1 - τ)))⁻¹ *
          (KvecM n b (u + τ * (σ - u)) σ (z 0) (z 1) (z 2) (z 3)) i := by
  simp only [G2M]
  exact intervalIntegral.integral_congr (fun τ _ => by rw [div_eq_inv_mul])

/-- Continuity of `a ↦ krad b σ t a`. -/
lemma continuous_krad_fst {b : ℝ → ℝ} (hb : ContDiff ℝ (⊤:ℕ∞) b) (σ t : ℝ) :
    Continuous (fun a : ℝ => krad b σ t a) := by
  have hq : Continuous (fun a : ℝ => hquot b a σ) :=
    (Work.OddVolterra.Existence.hquot_contDiff hb).continuous.comp
      (by fun_prop : Continuous fun a : ℝ => (a, σ))
  have hl : Continuous (fun a : ℝ => line b a t) := by
    have h : (fun a : ℝ => line b a t) = fun a : ℝ => a * t + b a := by
      funext a; simp only [line]
    rw [h]
    exact (continuous_id.mul continuous_const).add hb.continuous
  have h : Continuous
      (fun a : ℝ => (t + hquot b a σ) * (line b σ t + line b a t)) :=
    (continuous_const.add hq).mul (continuous_const.add hl)
  simpa only [krad_apply] using h

/-- `Ksl` is open. -/
lemma isOpen_Ksl {b : ℝ → ℝ} (hb : ContDiff ℝ (⊤:ℕ∞) b) (σ : ℝ) (z : St) :
    IsOpen (Ksl b σ z) :=
  (isOpen_lt continuous_const (continuous_krad_fst hb σ (-(z 0)))).inter
    (isOpen_lt continuous_const (continuous_krad_fst hb σ (z 1)))

/-- The component of the manifest kernel is smooth in its first slot where the radicands are
positive. -/
lemma contDiffOn_Kw {n : ℕ} {b : ℝ → ℝ} (hb : ContDiff ℝ (⊤:ℕ∞) b) (σ : ℝ) (z : St)
    (i : Fin 2) : ContDiffOn ℝ (⊤:ℕ∞) (Kw n b σ z i) (Ksl b σ z) := by
  have hKE : ContDiffOn ℝ (⊤:ℕ∞)
      (fun a : ℝ => KvecM n b a σ (z 0) (z 1) (z 2) (z 3)) (Ksl b σ z) :=
    contDiffOn_KvecM_comp (n := n) (hh := hb) (B := Ksl b σ z)
      (s := fun a : ℝ => a) (σ := fun _ : ℝ => σ)
      (x := fun _ : ℝ => z 0) (y := fun _ : ℝ => z 1)
      (x' := fun _ : ℝ => z 2) (y' := fun _ : ℝ => z 3)
      contDiffOn_id contDiffOn_const contDiffOn_const contDiffOn_const contDiffOn_const
      contDiffOn_const (fun a ha => ha.1) (fun a ha => ha.2)
  have hcomp := (contDiffOn_pi.mp hKE) i
  exact hcomp

/-- The radicand is positive on the box `[1/4, 3/2]`. -/
lemma krad_pos_Icc {b : ℝ → ℝ} (hb0 : ∀ x : ℝ, |b x| ≤ 1/100)
    (hb1 : ∀ x : ℝ, |deriv b x| ≤ 1/100) {σ : ℝ} (hσ : σ ∈ Set.Icc (1/2:ℝ) 1)
    {t : ℝ} (ht : (1/5:ℝ) ≤ |t|) (ht2 : |t| ≤ 3/2) :
    ∀ a ∈ Set.Icc (1/4:ℝ) (3/2), 0 < krad b σ t a := by
  intro a ha
  have h1 := (krad_region hb0 hb1 ha.1 ha.2 hσ.1 hσ.2 ht ht2).1
  linarith

/-- The box `[1/4, 3/2]` is contained in the positivity set. -/
lemma Icc_subset_Ksl {b : ℝ → ℝ} (hb0 : ∀ x : ℝ, |b x| ≤ 1/100)
    (hb1 : ∀ x : ℝ, |deriv b x| ≤ 1/100) {σ : ℝ} (hσ : σ ∈ Set.Icc (1/2:ℝ) 1) {z : St}
    (hz0 : (1/5:ℝ) ≤ z 0) (hz1 : (1/5:ℝ) ≤ z 1) (hz3 : ∀ i : Fin 4, |z i| ≤ 3/2) :
    Set.Icc (1/4:ℝ) (3/2) ⊆ Ksl b σ z := by
  intro a ha
  refine ⟨krad_pos_Icc hb0 hb1 hσ ?_ ?_ a ha, krad_pos_Icc hb0 hb1 hσ ?_ ?_ a ha⟩
  · rw [abs_neg, abs_of_nonneg (by linarith)]
    exact hz0
  · rw [abs_neg]
    exact hz3 0
  · rw [abs_of_nonneg (by linarith)]
    exact hz1
  · exact hz3 1

/-- **Local bounds for the manifest kernel in its first slot.**  On the compact set
`[1/4, 3/2]` a component of `KvecM n b · σ z` and of its first-slot derivative are bounded by a
common constant. -/
lemma KvecM_slice_bound {n : ℕ} {b : ℝ → ℝ} (hb : ContDiff ℝ (⊤:ℕ∞) b)
    (hb0 : ∀ x : ℝ, |b x| ≤ 1/100) (hb1 : ∀ x : ℝ, |deriv b x| ≤ 1/100)
    {σ : ℝ} (hσ : σ ∈ Set.Icc (1/2:ℝ) 1) {z : St}
    (hz0 : (1/5:ℝ) ≤ z 0) (hz1 : (1/5:ℝ) ≤ z 1) (hz3 : ∀ i : Fin 4, |z i| ≤ 3/2)
    (i : Fin 2) :
    ∃ M : ℝ, 0 < M ∧ ∀ a ∈ Set.Icc (1/4:ℝ) (3/2),
      ‖Kw n b σ z i a‖ ≤ M ∧ ‖deriv (Kw n b σ z i) a‖ ≤ M := by
  have hopen := isOpen_Ksl hb σ z
  have hsub := Icc_subset_Ksl hb0 hb1 hσ hz0 hz1 hz3
  have hcd := contDiffOn_Kw (n := n) hb σ z i
  have hc1 : ContinuousOn (Kw n b σ z i) (Set.Icc (1/4:ℝ) (3/2)) :=
    hcd.continuousOn.mono hsub
  have hc2 : ContinuousOn (deriv (Kw n b σ z i)) (Set.Icc (1/4:ℝ) (3/2)) :=
    (hcd.continuousOn_deriv_of_isOpen hopen (by norm_num)).mono hsub
  obtain ⟨M1, hM1⟩ := isCompact_Icc.exists_bound_of_continuousOn hc1
  obtain ⟨M2, hM2⟩ := isCompact_Icc.exists_bound_of_continuousOn hc2
  refine ⟨max (max M1 M2) 1, by positivity, fun a ha => ?_⟩
  exact ⟨le_trans (hM1 a ha) (le_max_of_le_left (le_max_left _ _)),
    le_trans (hM2 a ha) (le_max_of_le_left (le_max_right _ _))⟩

/-- **The first-slot derivative of a component of `G₂M` as an Abel-weighted average.** -/
lemma deriv_G2M_eq_integral {n : ℕ} {b : ℝ → ℝ} (hb : ContDiff ℝ (⊤:ℕ∞) b)
    {s σ : ℝ} (z : St) (i : Fin 2) {C : ℝ} (hC : 0 ≤ C)
    (hbdK : ∀ x ∈ Set.Ioo (s - 1/100) (s + 1/100), ∀ τ ∈ Set.Ico (0:ℝ) 1,
      ‖Kw n b σ z i (x + τ * (σ - x))‖ ≤ C)
    (hdiff : ∀ x ∈ Set.Ioo (s - 1/100) (s + 1/100), ∀ τ ∈ Set.Ico (0:ℝ) 1,
      DifferentiableAt ℝ (Kw n b σ z i) (x + τ * (σ - x)))
    (hbound : ∀ x ∈ Set.Ioo (s - 1/100) (s + 1/100), ∀ τ ∈ Set.Icc (0:ℝ) 1,
      ‖(1 - τ) * deriv (Kw n b σ z i) (x + τ * (σ - x))‖ ≤ C) :
    deriv (fun u : ℝ => (G2M n b u σ (z 0) (z 1) (z 2) (z 3)) i) s
      = ∫ τ in (0:ℝ)..1, (Real.sqrt (τ * (1 - τ)))⁻¹ *
          ((1 - τ) * deriv (Kw n b σ z i) (s + τ * (σ - s))) := by
  have hK : Measurable (Kw n b σ z i) := by
    rw [Kw_def]
    have hpi : Measurable (fun f : Fin 2 → ℝ => f i) := measurable_pi_apply i
    exact hpi.comp (Work.OddExistence.Manifest.AW.measurable_KvecM n hb σ z)
  have hmain := Work.OddExistence.Manifest.hasDerivAt_abelAvg_scalar
    (K := Kw n b σ z i) (s := s) (σ := σ) (δ := 1/100) hK
    (by norm_num) hbdK hdiff hbound
  have hfun : (fun u : ℝ => (G2M n b u σ (z 0) (z 1) (z 2) (z 3)) i)
      = fun u : ℝ => ∫ τ in (0:ℝ)..1, (Real.sqrt (τ * (1 - τ)))⁻¹ *
          Kw n b σ z i (u + τ * (σ - u)) := by
    funext u
    rw [G2M_eq_abelAvg n b u σ z i]
    simp only [Kw]
  rw [hfun, hmain.deriv]









/-- **Closeness of the first-slot derivative of a component of `G₂M`.** -/
lemma G2M_deriv_close {n : ℕ} {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤:ℕ∞) h) {δ Ck : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1/100)
    (hjet : ∀ k ≤ n+2, ∀ x : ℝ, |iteratedDeriv k h x| ≤ δ) (hCk : 0 < Ck)
    {s σ : ℝ} (hs : s ∈ Set.Icc (1/2:ℝ) 1) (hσ : σ ∈ Set.Icc (1/2:ℝ) 1) {z : St}
    (hz0 : (1/5:ℝ) ≤ z 0) (hz1 : (1/5:ℝ) ≤ z 1) (hz3 : ∀ i : Fin 4, |z i| ≤ 3/2)
    (i : Fin 2)
    (hd : ∀ τ ∈ Set.Icc (0:ℝ) 1,
      |deriv (Kw n h σ z i) (s + τ * (σ - s)) - deriv (Kw n 0 σ z i) (s + τ * (σ - s))|
        ≤ Ck * δ) :
    |deriv (fun u : ℝ => (G2M n h u σ (z 0) (z 1) (z 2) (z 3)) i) s
      - deriv (fun u : ℝ => (G2M n 0 u σ (z 0) (z 1) (z 2) (z 3)) i) s|
      ≤ (Real.pi * Ck + 1) * δ := by
  have hh0 : ∀ x : ℝ, |h x| ≤ 1/100 := fun x => le_trans (hjet 0 (by omega) x) hδ1
  have hh1 : ∀ x : ℝ, |deriv h x| ≤ 1/100 := fun x => by
    simpa [iteratedDeriv_one] using le_trans (hjet 1 (by omega) x) hδ1
  obtain ⟨Mh, hMh0, hMh⟩ := KvecM_slice_bound hh hh0 hh1 hσ hz0 hz1 hz3 i
  obtain ⟨M0, hM00, hM0⟩ := KvecM_slice_bound (n := n) (b := (0:ℝ→ℝ)) contDiff_const
    (fun x => by norm_num) (fun x => by norm_num) hσ hz0 hz1 hz3 i
  -- the moving point stays in the box `[1/4, 3/2]`
  have hconv : ∀ x ∈ Set.Ioo (s - 1/100) (s + 1/100), ∀ τ ∈ Set.Icc (0:ℝ) 1,
      x + τ * (σ - x) ∈ Set.Icc (1/4:ℝ) (3/2) := by
    intro x hx τ hτ
    have hxlo : (1/4:ℝ) < x := by linarith [hx.1, hs.1]
    have hxhi : x < 3/2 := by linarith [hx.2, hs.2]
    have hσlo : (1/4:ℝ) ≤ σ := by linarith [hσ.1]
    have hσhi : σ ≤ 3/2 := by linarith [hσ.2]
    have h1 : 0 ≤ 1 - τ := by linarith [hτ.2]
    have heq : x + τ * (σ - x) = (1 - τ) * x + τ * σ := by ring
    rw [heq]
    constructor
    · nlinarith [mul_nonneg h1 (by linarith : (0:ℝ) ≤ x - 1/4),
        mul_nonneg hτ.1 (by linarith : (0:ℝ) ≤ σ - 1/4)]
    · nlinarith [mul_nonneg h1 (by linarith : (0:ℝ) ≤ 3/2 - x),
        mul_nonneg hτ.1 (by linarith : (0:ℝ) ≤ 3/2 - σ)]
  have hsIoo : s ∈ Set.Ioo (s - 1/100) (s + 1/100) := ⟨by linarith, by linarith⟩
  -- the analytic hypotheses of the differentiation under the Abel integral
  have hbdK : ∀ x ∈ Set.Ioo (s - 1/100) (s + 1/100), ∀ τ ∈ Set.Ico (0:ℝ) 1,
      ‖Kw n h σ z i (x + τ * (σ - x))‖ ≤ Mh :=
    fun x hx τ hτ => (hMh _ (hconv x hx τ ⟨hτ.1, le_of_lt hτ.2⟩)).1
  have hbdK0 : ∀ x ∈ Set.Ioo (s - 1/100) (s + 1/100), ∀ τ ∈ Set.Ico (0:ℝ) 1,
      ‖Kw n 0 σ z i (x + τ * (σ - x))‖ ≤ M0 :=
    fun x hx τ hτ => (hM0 _ (hconv x hx τ ⟨hτ.1, le_of_lt hτ.2⟩)).1
  have hdiff : ∀ x ∈ Set.Ioo (s - 1/100) (s + 1/100), ∀ τ ∈ Set.Ico (0:ℝ) 1,
      DifferentiableAt ℝ (Kw n h σ z i) (x + τ * (σ - x)) := by
    intro x hx τ hτ
    have hmem := hconv x hx τ ⟨hτ.1, le_of_lt hτ.2⟩
    have hmem' : x + τ * (σ - x) ∈ Ksl h σ z := Icc_subset_Ksl hh0 hh1 hσ hz0 hz1 hz3 hmem
    exact ((contDiffOn_Kw (n := n) hh σ z i).differentiableOn (by simp)).differentiableAt
      ((isOpen_Ksl hh σ z).mem_nhds hmem')
  have hdiff0 : ∀ x ∈ Set.Ioo (s - 1/100) (s + 1/100), ∀ τ ∈ Set.Ico (0:ℝ) 1,
      DifferentiableAt ℝ (Kw n 0 σ z i) (x + τ * (σ - x)) := by
    intro x hx τ hτ
    have hmem := hconv x hx τ ⟨hτ.1, le_of_lt hτ.2⟩
    have hmem' : x + τ * (σ - x) ∈ Ksl 0 σ z :=
      Icc_subset_Ksl (fun x => by norm_num) (fun x => by norm_num) hσ hz0 hz1 hz3 hmem
    exact ((contDiffOn_Kw (n := n) contDiff_const σ z i).differentiableOn (by simp)).differentiableAt
      ((isOpen_Ksl contDiff_const σ z).mem_nhds hmem')
  have hbound : ∀ x ∈ Set.Ioo (s - 1/100) (s + 1/100), ∀ τ ∈ Set.Icc (0:ℝ) 1,
      ‖(1 - τ) * deriv (Kw n h σ z i) (x + τ * (σ - x))‖ ≤ Mh := by
    intro x hx τ hτ
    have hmem := hconv x hx τ hτ
    have h1 : 0 ≤ 1 - τ := by linarith [hτ.2]
    have h2 : (1:ℝ) - τ ≤ 1 := by linarith [hτ.1]
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h1]
    calc (1 - τ) * |deriv (Kw n h σ z i) (x + τ * (σ - x))|
        ≤ 1 * Mh := mul_le_mul h2 (hMh _ hmem).2 (abs_nonneg _) (by norm_num)
      _ = Mh := one_mul Mh
  have hbound0 : ∀ x ∈ Set.Ioo (s - 1/100) (s + 1/100), ∀ τ ∈ Set.Icc (0:ℝ) 1,
      ‖(1 - τ) * deriv (Kw n 0 σ z i) (x + τ * (σ - x))‖ ≤ M0 := by
    intro x hx τ hτ
    have hmem := hconv x hx τ hτ
    have h1 : 0 ≤ 1 - τ := by linarith [hτ.2]
    have h2 : (1:ℝ) - τ ≤ 1 := by linarith [hτ.1]
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h1]
    calc (1 - τ) * |deriv (Kw n 0 σ z i) (x + τ * (σ - x))|
        ≤ 1 * M0 := mul_le_mul h2 (hM0 _ hmem).2 (abs_nonneg _) (by norm_num)
      _ = M0 := one_mul M0
  -- the two derivative identities
  have hDh := deriv_G2M_eq_integral (n := n) (b := h) hh z i hMh0.le hbdK hdiff hbound
  have hD0 := deriv_G2M_eq_integral (n := n) (b := (0:ℝ→ℝ)) contDiff_const z i hM00.le
    hbdK0 hdiff0 hbound0
  rw [hDh, hD0, ← Real.norm_eq_abs]
  -- integrability of the two integrands
  have hwmeas : Measurable (fun τ : ℝ => (Real.sqrt (τ * (1 - τ)))⁻¹) :=
    (Work.OddVolterra.measurable_sqrt_real.comp
      (measurable_id.mul (measurable_const.sub measurable_id))).inv
  have hlinmeas : Measurable (fun τ : ℝ => 1 - τ) := measurable_const.sub measurable_id
  have hFH_int : IntervalIntegrable
      (fun τ : ℝ => (Real.sqrt (τ * (1 - τ)))⁻¹ *
        ((1 - τ) * deriv (Kw n h σ z i) (s + τ * (σ - s)))) volume (0:ℝ) 1 := by
    refine (Work.OddExistence.Manifest.AW.intervalIntegrable_abel_weight_one_sub.mul_const Mh).mono_fun' ?_ ?_
    · refine (hwmeas.mul (hlinmeas.mul ?_)).aestronglyMeasurable
      exact (measurable_deriv (Kw n h σ z i)).comp
        (by fun_prop : Measurable fun τ : ℝ => s + τ * (σ - s))
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_uIoc] with τ hτ
      rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hτ
      have hτIcc : τ ∈ Set.Icc (0:ℝ) 1 := ⟨le_of_lt hτ.1, hτ.2⟩
      have hmem := hconv s hsIoo τ hτIcc
      have h1 : 0 ≤ 1 - τ := by linarith [hτIcc.2]
      have h2 : (1:ℝ) - τ ≤ 1 := by linarith [hτIcc.1]
      have hw : 0 ≤ (Real.sqrt (τ * (1 - τ)))⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
      have hdH : |deriv (Kw n h σ z i) (s + τ * (σ - s))| ≤ Mh := by
        simpa only [Real.norm_eq_abs] using (hMh _ hmem).2
      simp only [Real.norm_eq_abs]
      rw [abs_mul, abs_mul, abs_of_nonneg hw, abs_of_nonneg h1,
        show (Real.sqrt (τ * (1 - τ)))⁻¹ * (1 - τ) * Mh
          = (Real.sqrt (τ * (1 - τ)))⁻¹ * ((1 - τ) * Mh) from by ring]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hdH h1) hw
  have hF0_int : IntervalIntegrable
      (fun τ : ℝ => (Real.sqrt (τ * (1 - τ)))⁻¹ *
        ((1 - τ) * deriv (Kw n 0 σ z i) (s + τ * (σ - s)))) volume (0:ℝ) 1 := by
    refine (Work.OddExistence.Manifest.AW.intervalIntegrable_abel_weight_one_sub.mul_const M0).mono_fun' ?_ ?_
    · refine (hwmeas.mul (hlinmeas.mul ?_)).aestronglyMeasurable
      exact (measurable_deriv (Kw n 0 σ z i)).comp
        (by fun_prop : Measurable fun τ : ℝ => s + τ * (σ - s))
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_uIoc] with τ hτ
      rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hτ
      have hτIcc : τ ∈ Set.Icc (0:ℝ) 1 := ⟨le_of_lt hτ.1, hτ.2⟩
      have hmem := hconv s hsIoo τ hτIcc
      have h1 : 0 ≤ 1 - τ := by linarith [hτIcc.2]
      have h2 : (1:ℝ) - τ ≤ 1 := by linarith [hτIcc.1]
      have hw : 0 ≤ (Real.sqrt (τ * (1 - τ)))⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
      have hdH : |deriv (Kw n 0 σ z i) (s + τ * (σ - s))| ≤ M0 := by
        simpa only [Real.norm_eq_abs] using (hM0 _ hmem).2
      simp only [Real.norm_eq_abs]
      rw [abs_mul, abs_mul, abs_of_nonneg hw, abs_of_nonneg h1,
        show (Real.sqrt (τ * (1 - τ)))⁻¹ * (1 - τ) * M0
          = (Real.sqrt (τ * (1 - τ)))⁻¹ * ((1 - τ) * M0) from by ring]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hdH h1) hw
  have hbound_int : IntervalIntegrable
      (fun τ : ℝ => (Real.sqrt (τ * (1 - τ)))⁻¹ * (1 - τ) * (Ck * δ)) volume (0:ℝ) 1 :=
    (Work.OddExistence.Manifest.AW.intervalIntegrable_abel_weight_one_sub).mul_const (Ck * δ)
  rw [← intervalIntegral.integral_sub hFH_int hF0_int]
  refine le_trans (intervalIntegral.norm_integral_le_of_norm_le (by norm_num : (0:ℝ) ≤ 1)
    (Filter.Eventually.of_forall ?_) hbound_int) ?_
  · intro τ hτ
    rw [Set.mem_Ioc] at hτ
    have hτIcc : τ ∈ Set.Icc (0:ℝ) 1 := ⟨le_of_lt hτ.1, hτ.2⟩
    have h1 : 0 ≤ 1 - τ := by linarith [hτIcc.2]
    have hw : 0 ≤ (Real.sqrt (τ * (1 - τ)))⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
    have hkey : (Real.sqrt (τ * (1 - τ)))⁻¹ * ((1 - τ) * deriv (Kw n h σ z i) (s + τ * (σ - s)))
        - (Real.sqrt (τ * (1 - τ)))⁻¹ * ((1 - τ) * deriv (Kw n 0 σ z i) (s + τ * (σ - s)))
        = (Real.sqrt (τ * (1 - τ)))⁻¹ * ((1 - τ) *
            (deriv (Kw n h σ z i) (s + τ * (σ - s))
              - deriv (Kw n 0 σ z i) (s + τ * (σ - s)))) := by ring
    simp only [Real.norm_eq_abs]
    rw [hkey, abs_mul, abs_mul, abs_of_nonneg hw, abs_of_nonneg h1,
      show (Real.sqrt (τ * (1 - τ)))⁻¹ * (1 - τ) * (Ck * δ)
        = (Real.sqrt (τ * (1 - τ)))⁻¹ * ((1 - τ) * (Ck * δ)) from by ring]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hd τ hτIcc) h1) hw
  · have h1 := Work.OddExistence.Manifest.AW.aw_abel_weight_integral
    rw [intervalIntegral.integral_mul_const]
    have h2 : 0 ≤ Ck * δ := mul_nonneg hCk.le hδ.le
    have h3 := mul_le_mul_of_nonneg_right h1 h2
    have h4 : Real.pi * (Ck * δ) ≤ (Real.pi * Ck + 1) * δ := by
      nlinarith [hδ.le, hCk.le, Real.pi_pos]
    linarith






lemma K1M_hasDerivAt {n : ℕ} {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤:ℕ∞) h) {a σ t : ℝ}
    (hpos : 0 < krad h σ t a) :
    HasDerivAt (fun a' : ℝ => K1M n h a' σ t) (deriv (fun a' : ℝ => K1M n h a' σ t) a) a := by
  have hdK : HasDerivAt (fun a' : ℝ => Kden h a' σ t) (deriv (fun a' : ℝ => Kden h a' σ t) a) a :=
    (Kden_hasDerivAt hh hpos).differentiableAt.hasDerivAt
  have hne : Kden h a σ t ≠ 0 := by
    rw [Kden_eq_sqrt_krad]; exact ne_of_gt (Real.sqrt_pos.mpr hpos)
  have hfun : (fun a' : ℝ => K1M n h a' σ t)
      = (fun a' : ℝ => J1M n h a' σ t) / (fun a' : ℝ => Kden h a' σ t) := by
    funext u; rw [Pi.div_apply, K1M]
  rw [hfun]
  exact ((J1M_hasDerivAt (n := n) hh a σ t).div hdK hne).differentiableAt.hasDerivAt

lemma K2M_hasDerivAt {n : ℕ} {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤:ℕ∞) h) {a σ t : ℝ}
    (hpos : 0 < krad h σ t a) :
    HasDerivAt (fun a' : ℝ => K2M n h a' σ t) (deriv (fun a' : ℝ => K2M n h a' σ t) a) a := by
  have hdK : HasDerivAt (fun a' : ℝ => Kden h a' σ t) (deriv (fun a' : ℝ => Kden h a' σ t) a) a :=
    (Kden_hasDerivAt hh hpos).differentiableAt.hasDerivAt
  have hne : Kden h a σ t ≠ 0 := by
    rw [Kden_eq_sqrt_krad]; exact ne_of_gt (Real.sqrt_pos.mpr hpos)
  have hfun : (fun a' : ℝ => K2M n h a' σ t)
      = (fun a' : ℝ => J2M n h a' σ t) / (fun a' : ℝ => Kden h a' σ t) := by
    funext u; rw [Pi.div_apply, K2M]
  rw [hfun]
  exact ((J2M_hasDerivAt (n := n) hh a σ t).div hdK hne).differentiableAt.hasDerivAt

/-- **Closeness of the first-slot derivative of the manifest kernel.** -/
theorem KvecM_deriv_diff (n : ℕ) (hn : 1 ≤ n) :
    ∃ C : ℝ, 0 < C ∧ ∀ h : ℝ → ℝ, ContDiff ℝ (⊤:ℕ∞) h →
      ∀ δ : ℝ, 0 < δ → δ ≤ 1/100 → (∀ k ≤ n+2, ∀ x : ℝ, |iteratedDeriv k h x| ≤ δ) →
      ∀ a ∈ Set.Icc (1/2 : ℝ) 1, ∀ σ ∈ Set.Icc (1/2 : ℝ) 1,
      ∀ x y x' y' : ℝ, (1/5 : ℝ) ≤ x → (1/5 : ℝ) ≤ y → |x| ≤ 3/2 → |y| ≤ 3/2 →
      |x'| ≤ 3/2 → |y'| ≤ 3/2 →
      ∀ i : Fin 2,
        |deriv (fun a' : ℝ => (KvecM n h a' σ x y x' y') i) a
          - deriv (fun a' : ℝ => (KvecM n 0 a' σ x y x' y') i) a| ≤ C * δ := by
  obtain ⟨C1, hC1, hK1⟩ := K1M_deriv_diff n hn
  obtain ⟨C2, hC2, hK2⟩ := K2M_deriv_diff n hn
  refine ⟨3 * (C1 + C2) + 1, by nlinarith [hC1, hC2], ?_⟩
  intro h hh δ hδ hδ1 hjet a ha σ hσ x y x' y' hx hy hx3 hy3 hx'3 hy'3 i
  have hh0 : ∀ z : ℝ, |h z| ≤ 1/100 := fun z => le_trans (hjet 0 (by omega) z) hδ1
  have hh1 : ∀ z : ℝ, |deriv h z| ≤ 1/100 := fun z => by
    simpa [iteratedDeriv_one] using le_trans (hjet 1 (by omega) z) hδ1
  have ha' : (1/4 : ℝ) ≤ a := by linarith [ha.1]
  have ha2' : a ≤ 3/2 := by linarith [ha.2]
  have hxs : |x| = x := abs_of_nonneg (by linarith)
  have hys : |y| = y := abs_of_nonneg (by linarith)
  have hkx : (1/5 : ℝ) ≤ |x| := by rw [hxs]; exact hx
  have hky : (1/5 : ℝ) ≤ |y| := by rw [hys]; exact hy
  have hxm : |-(x)| ≤ 3/2 := by rw [abs_neg]; exact hx3
  have hxq : (1/5 : ℝ) ≤ |-(x)| := by rw [abs_neg]; exact hkx
  have hposx : 0 < krad h σ (-(x)) a := by
    have := (krad_region hh0 hh1 ha' ha2' hσ.1 hσ.2 hxq hxm).1
    linarith
  have hposy : 0 < krad h σ y a := by
    have := (krad_region hh0 hh1 ha' ha2' hσ.1 hσ.2 hky hy3).1
    linarith
  have hz0 : ∀ z : ℝ, |(0:ℝ→ℝ) z| ≤ 1/100 := fun z => by simp
  have hz1 : ∀ z : ℝ, |deriv (0:ℝ→ℝ) z| ≤ 1/100 := fun z => by simp
  have hposx0 : 0 < krad (0:ℝ→ℝ) σ (-(x)) a := by
    have := (krad_region hz0 hz1 ha' ha2' hσ.1 hσ.2 hxq hxm).1
    linarith
  have hposy0 : 0 < krad (0:ℝ→ℝ) σ y a := by
    have := (krad_region hz0 hz1 ha' ha2' hσ.1 hσ.2 hky hy3).1
    linarith
  have hcase0 : |deriv (fun a' : ℝ => (KvecM n h a' σ x y x' y') 0) a
      - deriv (fun a' : ℝ => (KvecM n 0 a' σ x y x' y') 0) a|
      ≤ (3 * (C1 + C2) + 1) * δ := by
    have hdh : deriv (fun a' : ℝ => (KvecM n h a' σ x y x' y') 0) a
        = -(deriv (fun a' : ℝ => K1M n h a' σ (-x)) a * x'
            + deriv (fun a' : ℝ => K1M n h a' σ y) a * y') := by
      have hdx := K1M_hasDerivAt (n := n) hh (a := a) (σ := σ) (t := -(x)) hposx
      have hdy := K1M_hasDerivAt (n := n) hh (a := a) (σ := σ) (t := y) hposy
      have hsum := (hdx.mul_const x').add (hdy.mul_const y')
      have hfun : (fun a' : ℝ => (KvecM n h a' σ x y x' y') 0)
          = fun a' : ℝ => -(K1M n h a' σ (-x) * x' + K1M n h a' σ y * y') := by
        funext u; simp [KvecM]
      rw [hfun]
      exact hsum.neg.deriv
    have hd0 : deriv (fun a' : ℝ => (KvecM n 0 a' σ x y x' y') 0) a
        = -(deriv (fun a' : ℝ => K1M n 0 a' σ (-x)) a * x'
            + deriv (fun a' : ℝ => K1M n 0 a' σ y) a * y') := by
      have hdx := K1M_hasDerivAt (n := n) (h := (0:ℝ→ℝ)) contDiff_const
        (a := a) (σ := σ) (t := -(x)) hposx0
      have hdy := K1M_hasDerivAt (n := n) (h := (0:ℝ→ℝ)) contDiff_const
        (a := a) (σ := σ) (t := y) hposy0
      have hsum := (hdx.mul_const x').add (hdy.mul_const y')
      have hfun : (fun a' : ℝ => (KvecM n 0 a' σ x y x' y') 0)
          = fun a' : ℝ => -(K1M n 0 a' σ (-x) * x' + K1M n 0 a' σ y * y') := by
        funext u; simp [KvecM]
      rw [hfun]
      exact hsum.neg.deriv
    rw [hdh, hd0]
    have e1 : |deriv (fun a' : ℝ => K1M n h a' σ (-x)) a
        - deriv (fun a' : ℝ => K1M n 0 a' σ (-x)) a| ≤ C1 * δ :=
      hK1 h hh δ hδ hδ1 hjet a ha σ hσ (-x) hxq hxm
    have e2 : |deriv (fun a' : ℝ => K1M n h a' σ y) a
        - deriv (fun a' : ℝ => K1M n 0 a' σ y) a| ≤ C1 * δ :=
      hK1 h hh δ hδ hδ1 hjet a ha σ hσ y hky hy3
    have hkey : -(deriv (fun a' : ℝ => K1M n h a' σ (-x)) a * x'
          + deriv (fun a' : ℝ => K1M n h a' σ y) a * y')
        - (-(deriv (fun a' : ℝ => K1M n 0 a' σ (-x)) a * x'
          + deriv (fun a' : ℝ => K1M n 0 a' σ y) a * y'))
        = (deriv (fun a' : ℝ => K1M n 0 a' σ (-x)) a
            - deriv (fun a' : ℝ => K1M n h a' σ (-x)) a) * x'
          + (deriv (fun a' : ℝ => K1M n 0 a' σ y) a
            - deriv (fun a' : ℝ => K1M n h a' σ y) a) * y' := by ring
    rw [hkey]
    have hA : |(deriv (fun a' : ℝ => K1M n 0 a' σ (-x)) a
            - deriv (fun a' : ℝ => K1M n h a' σ (-x)) a) * x'| ≤ C1 * δ * (3/2) := by
      rw [abs_mul]
      have h1 : |deriv (fun a' : ℝ => K1M n 0 a' σ (-x)) a
          - deriv (fun a' : ℝ => K1M n h a' σ (-x)) a| ≤ C1 * δ := by
        rw [abs_sub_comm]; exact e1
      calc |deriv (fun a' : ℝ => K1M n 0 a' σ (-x)) a
              - deriv (fun a' : ℝ => K1M n h a' σ (-x)) a| * |x'|
          ≤ (C1 * δ) * (3/2) :=
            mul_le_mul h1 hx'3 (abs_nonneg _) (mul_nonneg hC1.le hδ.le)
        _ = C1 * δ * (3/2) := by ring
    have hB : |(deriv (fun a' : ℝ => K1M n 0 a' σ y) a
            - deriv (fun a' : ℝ => K1M n h a' σ y) a) * y'| ≤ C1 * δ * (3/2) := by
      rw [abs_mul]
      have h1 : |deriv (fun a' : ℝ => K1M n 0 a' σ y) a
          - deriv (fun a' : ℝ => K1M n h a' σ y) a| ≤ C1 * δ := by
        rw [abs_sub_comm]; exact e2
      calc |deriv (fun a' : ℝ => K1M n 0 a' σ y) a
              - deriv (fun a' : ℝ => K1M n h a' σ y) a| * |y'|
          ≤ (C1 * δ) * (3/2) :=
            mul_le_mul h1 hy'3 (abs_nonneg _) (mul_nonneg hC1.le hδ.le)
        _ = C1 * δ * (3/2) := by ring
    calc |(deriv (fun a' : ℝ => K1M n 0 a' σ (-x)) a
            - deriv (fun a' : ℝ => K1M n h a' σ (-x)) a) * x'
          + (deriv (fun a' : ℝ => K1M n 0 a' σ y) a
            - deriv (fun a' : ℝ => K1M n h a' σ y) a) * y'|
        ≤ |(deriv (fun a' : ℝ => K1M n 0 a' σ (-x)) a
            - deriv (fun a' : ℝ => K1M n h a' σ (-x)) a) * x'|
          + |(deriv (fun a' : ℝ => K1M n 0 a' σ y) a
            - deriv (fun a' : ℝ => K1M n h a' σ y) a) * y'| := abs_add_le _ _
      _ ≤ C1 * δ * (3/2) + C1 * δ * (3/2) := add_le_add hA hB
      _ ≤ (3 * (C1 + C2) + 1) * δ :=
          by nlinarith [hC1, hC2, hδ.le, mul_nonneg hC1.le hδ.le, mul_nonneg hC2.le hδ.le]
  have hcase1 : |deriv (fun a' : ℝ => (KvecM n h a' σ x y x' y') 1) a
      - deriv (fun a' : ℝ => (KvecM n 0 a' σ x y x' y') 1) a|
      ≤ (3 * (C1 + C2) + 1) * δ := by
    have hdh : deriv (fun a' : ℝ => (KvecM n h a' σ x y x' y') 1) a
        = -(deriv (fun a' : ℝ => K2M n h a' σ (-x)) a * x'
            + deriv (fun a' : ℝ => K2M n h a' σ y) a * y') := by
      have hdx := K2M_hasDerivAt (n := n) hh (a := a) (σ := σ) (t := -(x)) hposx
      have hdy := K2M_hasDerivAt (n := n) hh (a := a) (σ := σ) (t := y) hposy
      have hsum := (hdx.mul_const x').add (hdy.mul_const y')
      have hfun : (fun a' : ℝ => (KvecM n h a' σ x y x' y') 1)
          = fun a' : ℝ => -(K2M n h a' σ (-x) * x' + K2M n h a' σ y * y') := by
        funext u; simp [KvecM]
      rw [hfun]
      exact hsum.neg.deriv
    have hd0 : deriv (fun a' : ℝ => (KvecM n 0 a' σ x y x' y') 1) a
        = -(deriv (fun a' : ℝ => K2M n 0 a' σ (-x)) a * x'
            + deriv (fun a' : ℝ => K2M n 0 a' σ y) a * y') := by
      have hdx := K2M_hasDerivAt (n := n) (h := (0:ℝ→ℝ)) contDiff_const
        (a := a) (σ := σ) (t := -(x)) hposx0
      have hdy := K2M_hasDerivAt (n := n) (h := (0:ℝ→ℝ)) contDiff_const
        (a := a) (σ := σ) (t := y) hposy0
      have hsum := (hdx.mul_const x').add (hdy.mul_const y')
      have hfun : (fun a' : ℝ => (KvecM n 0 a' σ x y x' y') 1)
          = fun a' : ℝ => -(K2M n 0 a' σ (-x) * x' + K2M n 0 a' σ y * y') := by
        funext u; simp [KvecM]
      rw [hfun]
      exact hsum.neg.deriv
    rw [hdh, hd0]
    have e1 : |deriv (fun a' : ℝ => K2M n h a' σ (-x)) a
        - deriv (fun a' : ℝ => K2M n 0 a' σ (-x)) a| ≤ C2 * δ :=
      hK2 h hh δ hδ hδ1 hjet a ha σ hσ (-x) hxq hxm
    have e2 : |deriv (fun a' : ℝ => K2M n h a' σ y) a
        - deriv (fun a' : ℝ => K2M n 0 a' σ y) a| ≤ C2 * δ :=
      hK2 h hh δ hδ hδ1 hjet a ha σ hσ y hky hy3
    have hkey : -(deriv (fun a' : ℝ => K2M n h a' σ (-x)) a * x'
          + deriv (fun a' : ℝ => K2M n h a' σ y) a * y')
        - (-(deriv (fun a' : ℝ => K2M n 0 a' σ (-x)) a * x'
          + deriv (fun a' : ℝ => K2M n 0 a' σ y) a * y'))
        = (deriv (fun a' : ℝ => K2M n 0 a' σ (-x)) a
            - deriv (fun a' : ℝ => K2M n h a' σ (-x)) a) * x'
          + (deriv (fun a' : ℝ => K2M n 0 a' σ y) a
            - deriv (fun a' : ℝ => K2M n h a' σ y) a) * y' := by ring
    rw [hkey]
    have hA : |(deriv (fun a' : ℝ => K2M n 0 a' σ (-x)) a
            - deriv (fun a' : ℝ => K2M n h a' σ (-x)) a) * x'| ≤ C2 * δ * (3/2) := by
      rw [abs_mul]
      have h1 : |deriv (fun a' : ℝ => K2M n 0 a' σ (-x)) a
          - deriv (fun a' : ℝ => K2M n h a' σ (-x)) a| ≤ C2 * δ := by
        rw [abs_sub_comm]; exact e1
      calc |deriv (fun a' : ℝ => K2M n 0 a' σ (-x)) a
              - deriv (fun a' : ℝ => K2M n h a' σ (-x)) a| * |x'|
          ≤ (C2 * δ) * (3/2) :=
            mul_le_mul h1 hx'3 (abs_nonneg _) (mul_nonneg hC2.le hδ.le)
        _ = C2 * δ * (3/2) := by ring
    have hB : |(deriv (fun a' : ℝ => K2M n 0 a' σ y) a
            - deriv (fun a' : ℝ => K2M n h a' σ y) a) * y'| ≤ C2 * δ * (3/2) := by
      rw [abs_mul]
      have h1 : |deriv (fun a' : ℝ => K2M n 0 a' σ y) a
          - deriv (fun a' : ℝ => K2M n h a' σ y) a| ≤ C2 * δ := by
        rw [abs_sub_comm]; exact e2
      calc |deriv (fun a' : ℝ => K2M n 0 a' σ y) a
              - deriv (fun a' : ℝ => K2M n h a' σ y) a| * |y'|
          ≤ (C2 * δ) * (3/2) :=
            mul_le_mul h1 hy'3 (abs_nonneg _) (mul_nonneg hC2.le hδ.le)
        _ = C2 * δ * (3/2) := by ring
    calc |(deriv (fun a' : ℝ => K2M n 0 a' σ (-x)) a
            - deriv (fun a' : ℝ => K2M n h a' σ (-x)) a) * x'
          + (deriv (fun a' : ℝ => K2M n 0 a' σ y) a
            - deriv (fun a' : ℝ => K2M n h a' σ y) a) * y'|
        ≤ |(deriv (fun a' : ℝ => K2M n 0 a' σ (-x)) a
            - deriv (fun a' : ℝ => K2M n h a' σ (-x)) a) * x'|
          + |(deriv (fun a' : ℝ => K2M n 0 a' σ y) a
            - deriv (fun a' : ℝ => K2M n h a' σ y) a) * y'| := abs_add_le _ _
      _ ≤ C2 * δ * (3/2) + C2 * δ * (3/2) := add_le_add hA hB
      _ ≤ (3 * (C1 + C2) + 1) * δ :=
          by nlinarith [hC1, hC2, hδ.le, mul_nonneg hC1.le hδ.le, mul_nonneg hC2.le hδ.le]
  fin_cases i
  · exact hcase0
  · exact hcase1



theorem ThetaM_close (n : ℕ) (hn : 1 ≤ n) :
    ∃ C : ℝ, 0 < C ∧ ∀ h : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) h →
      Function.support h ⊆ Set.Icc (1 - 2 * Work.OddVolterra.tau)
        (1 - Work.OddVolterra.tau) →
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 100 →
      (∀ k : ℕ, k ≤ n + 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ δ) →
      ∀ s ∈ Set.Icc (1 / 2 : ℝ) 1, ∀ σ ∈ Set.Icc (1 / 2 : ℝ) 1,
      ∀ z ∈ Metric.closedBall (Work.OddVolterra.baseState σ) (1 / 2),
        ‖Work.OddVolterra.KernelExt.ThetaM n h s σ z -
          Work.OddVolterra.KernelExt.ThetaM n 0 s σ z‖ ≤ C * δ := by
  obtain ⟨Ck, hCk, hKv⟩ := KvecM_deriv_diff n hn
  refine ⟨Real.pi * Ck + 1, by positivity, ?_⟩
  intro h hh hsupp δ hδ hδ1 hjet s hs σ hσ z hz
  obtain ⟨hz0, hz1, hz3⟩ := z_coords hσ hz
  have hcomp : ∀ i : Fin 4,
      |(ThetaM n h s σ z) i - (ThetaM n 0 s σ z) i| ≤ (Real.pi * Ck + 1) * δ := by
    intro i
    fin_cases i
    · show |(ThetaM n h s σ z) 0 - (ThetaM n 0 s σ z) 0| ≤ (Real.pi * Ck + 1) * δ
      rw [show (ThetaM n h s σ z) 0 = -(z 2) from rfl,
        show (ThetaM n 0 s σ z) 0 = -(z 2) from rfl]
      simp only [sub_self, abs_zero]
      positivity
    · show |(ThetaM n h s σ z) 1 - (ThetaM n 0 s σ z) 1| ≤ (Real.pi * Ck + 1) * δ
      rw [show (ThetaM n h s σ z) 1 = -(z 3) from rfl,
        show (ThetaM n 0 s σ z) 1 = -(z 3) from rfl]
      simp only [sub_self, abs_zero]
      positivity
    · show |(ThetaM n h s σ z) 2 - (ThetaM n 0 s σ z) 2| ≤ (Real.pi * Ck + 1) * δ
      rw [show (ThetaM n h s σ z) 2
          = -(deriv (fun u : ℝ => (G2M n h u σ (z 0) (z 1) (z 2) (z 3)) 0) s) from rfl,
        show (ThetaM n 0 s σ z) 2
          = -(deriv (fun u : ℝ => (G2M n 0 u σ (z 0) (z 1) (z 2) (z 3)) 0) s) from rfl]
      have hd : ∀ τ ∈ Set.Icc (0:ℝ) 1,
          |deriv (Kw n h σ z 0) (s + τ * (σ - s)) - deriv (Kw n 0 σ z 0) (s + τ * (σ - s))|
            ≤ Ck * δ := by
        intro τ hτ
        have ha : s + τ * (σ - s) ∈ Set.Icc (1/2:ℝ) 1 := by
          have h1 : 0 ≤ 1 - τ := by linarith [hτ.2]
          have heq : s + τ * (σ - s) = (1 - τ) * s + τ * σ := by ring
          rw [heq]
          constructor
          · nlinarith [mul_nonneg h1 (by linarith [hs.1] : (0:ℝ) ≤ s - 1/2),
              mul_nonneg hτ.1 (by linarith [hσ.1] : (0:ℝ) ≤ σ - 1/2)]
          · nlinarith [mul_nonneg h1 (by linarith [hs.2] : (0:ℝ) ≤ 1 - s),
              mul_nonneg hτ.1 (by linarith [hσ.2] : (0:ℝ) ≤ 1 - σ)]
        rw [Kw_def, Kw_def]
        exact hKv h hh δ hδ hδ1 hjet (s + τ * (σ - s)) ha σ hσ (z 0) (z 1) (z 2) (z 3)
          hz0 hz1 (hz3 0) (hz3 1) (hz3 2) (hz3 3) 0
      have hkey : -(deriv (fun u : ℝ => (G2M n h u σ (z 0) (z 1) (z 2) (z 3)) 0) s)
          - (-(deriv (fun u : ℝ => (G2M n 0 u σ (z 0) (z 1) (z 2) (z 3)) 0) s))
          = -(deriv (fun u : ℝ => (G2M n h u σ (z 0) (z 1) (z 2) (z 3)) 0) s
              - deriv (fun u : ℝ => (G2M n 0 u σ (z 0) (z 1) (z 2) (z 3)) 0) s) := by ring
      rw [hkey, abs_neg]
      exact G2M_deriv_close hh hδ hδ1 hjet hCk hs hσ hz0 hz1 hz3 0 hd
    · show |(ThetaM n h s σ z) 3 - (ThetaM n 0 s σ z) 3| ≤ (Real.pi * Ck + 1) * δ
      rw [show (ThetaM n h s σ z) 3
          = -(deriv (fun u : ℝ => (G2M n h u σ (z 0) (z 1) (z 2) (z 3)) 1) s) from rfl,
        show (ThetaM n 0 s σ z) 3
          = -(deriv (fun u : ℝ => (G2M n 0 u σ (z 0) (z 1) (z 2) (z 3)) 1) s) from rfl]
      have hd : ∀ τ ∈ Set.Icc (0:ℝ) 1,
          |deriv (Kw n h σ z 1) (s + τ * (σ - s)) - deriv (Kw n 0 σ z 1) (s + τ * (σ - s))|
            ≤ Ck * δ := by
        intro τ hτ
        have ha : s + τ * (σ - s) ∈ Set.Icc (1/2:ℝ) 1 := by
          have h1 : 0 ≤ 1 - τ := by linarith [hτ.2]
          have heq : s + τ * (σ - s) = (1 - τ) * s + τ * σ := by ring
          rw [heq]
          constructor
          · nlinarith [mul_nonneg h1 (by linarith [hs.1] : (0:ℝ) ≤ s - 1/2),
              mul_nonneg hτ.1 (by linarith [hσ.1] : (0:ℝ) ≤ σ - 1/2)]
          · nlinarith [mul_nonneg h1 (by linarith [hs.2] : (0:ℝ) ≤ 1 - s),
              mul_nonneg hτ.1 (by linarith [hσ.2] : (0:ℝ) ≤ 1 - σ)]
        rw [Kw_def, Kw_def]
        exact hKv h hh δ hδ hδ1 hjet (s + τ * (σ - s)) ha σ hσ (z 0) (z 1) (z 2) (z 3)
          hz0 hz1 (hz3 0) (hz3 1) (hz3 2) (hz3 3) 1
      have hkey : -(deriv (fun u : ℝ => (G2M n h u σ (z 0) (z 1) (z 2) (z 3)) 1) s)
          - (-(deriv (fun u : ℝ => (G2M n 0 u σ (z 0) (z 1) (z 2) (z 3)) 1) s))
          = -(deriv (fun u : ℝ => (G2M n h u σ (z 0) (z 1) (z 2) (z 3)) 1) s
              - deriv (fun u : ℝ => (G2M n 0 u σ (z 0) (z 1) (z 2) (z 3)) 1) s) := by ring
      rw [hkey, abs_neg]
      exact G2M_deriv_close hh hδ hδ1 hjet hCk hs hσ hz0 hz1 hz3 1 hd
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr ?_
  intro i
  simpa only [Pi.sub_apply, Real.norm_eq_abs] using hcomp i
end

end Work.Anchor
