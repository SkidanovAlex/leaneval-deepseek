import Mathlib
import Submission.Work.OddVolterra.Defs
import Submission.Work.OddEnvelope.Defs
import Submission.Work.OddEnvelope.Main
import Submission.Work.OddEnvelope.NonDegenerate
import Submission.Work.OddVolterra.KernelExt.Defs
import Submission.Work.OddVolterra.KernelExt.Kden_pos_of_curve
import Submission.Work.OddVolterra.KernelExt.KvecM_eq_Kvec
import Submission.Work.OddVolterra.KernelExt.KvecM_contDiffOn_box
import Submission.Work.OddVolterra.Existence.hquot_contDiff
import Submission.Work.OddVolterra.KernelExt.fderiv_fst_eq_deriv

namespace Work.OddVolterra.Existence

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval
open Commons.Geometry.Ulam (profileX)

noncomputable section

variable {h x y : ℝ → ℝ}

/-!
# Interval-integrability of the `Θ`-integrand of the odd transition-slope system

The last two rows of `Work.OddVolterra.Theta` are the `u`-derivatives at `u = s` of the τ-average
`G2` of the Abel kernel, and the paper's proof needs these to be interval-integrable in `σ` on
`s..1`.  This file proves exactly that (`theta_integrable`), by

* bounding the bump `h` on its window `[4/5, 9/10]` using `IsEnvelopeCurve.mono_x/mono_y`
  together with the `C²`-closeness of `(x,y)` to the semicircle (`abs_h_le`, `abs_deriv_h_le`);
* deducing strict positivity of the Abel denominator `Kden` on the square `[s/2,1]²`
  (`Kden_pos_box`), so that the *manifest* kernel `KvecM` is `C²` there
  (`KernelExt.KvecM_contDiffOn_box`) and agrees with the paper's kernel `Kvec` on `σ ≥ s`
  (`KernelExt.KvecM_eq_Kvec`);
* differentiating the weighted parametric integral under the integral sign
  (`deriv_parametrization_eq`) and showing the result is interval-integrable
  (`theta_deriv_parametrization_integrable`);
* assembling the four components of `Θ` and transferring along the a.e. equality `Θ = ΘM`.
-/

/-! ## The perturbation window -/

variable {h x y : ℝ → ℝ}

/-- The perturbation window `[1 - 2τ, 1 - τ] = [4/5, 9/10]`. -/
lemma one_sub_two_mul_tau_eq : (1 : ℝ) - 2 * Work.OddEnvelope.tau = 4 / 5 := by
  rw [Work.OddEnvelope.tau]; norm_num
lemma one_sub_tau_eq : (1 : ℝ) - Work.OddEnvelope.tau = 9 / 10 := by
  rw [Work.OddEnvelope.tau]; norm_num

lemma h_eq_zero_of_lt (H : Work.OddEnvelope.IsEnvelopeCurve h x y) {z : ℝ} (hz : z < 4 / 5) :
    h z = 0 := by
  by_contra hne
  have hmem := H.h_support hne
  rw [one_sub_two_mul_tau_eq] at hmem
  linarith [hmem.1]

lemma h_eq_zero_of_gt (H : Work.OddEnvelope.IsEnvelopeCurve h x y) {z : ℝ} (hz : 9 / 10 < z) :
    h z = 0 := by
  by_contra hne
  have hmem := H.h_support hne
  rw [one_sub_tau_eq] at hmem
  linarith [hmem.2]

lemma deriv_h_eq_zero_of_lt (H : Work.OddEnvelope.IsEnvelopeCurve h x y) {z : ℝ} (hz : z < 4 / 5) :
    deriv h z = 0 := by
  have hev : h =ᶠ[𝓝 z] (fun _ : ℝ => (0 : ℝ)) := by
    filter_upwards [isOpen_Iio.mem_nhds hz] with u hu
    exact h_eq_zero_of_lt H hu
  rw [hev.deriv_eq]; simp

lemma deriv_h_eq_zero_of_gt (H : Work.OddEnvelope.IsEnvelopeCurve h x y) {z : ℝ} (hz : 9 / 10 < z) :
    deriv h z = 0 := by
  have hev : h =ᶠ[𝓝 z] (fun _ : ℝ => (0 : ℝ)) := by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with u hu
    exact h_eq_zero_of_gt H hu
  rw [hev.deriv_eq]; simp

lemma h_at_left_end (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (H : Work.OddEnvelope.IsEnvelopeCurve h x y) : h (4 / 5) = 0 := by
  have hcont : ContinuousAt h (4 / 5) := hh.continuous.continuousAt
  have hleft : h =ᶠ[𝓝[<] (4 / 5)] (fun _ : ℝ => (0 : ℝ)) := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact h_eq_zero_of_lt H hz
  have h1 : Tendsto h (𝓝[<] (4 / 5)) (𝓝 (h (4 / 5))) :=
    hcont.tendsto.mono_left nhdsWithin_le_nhds
  have h2 : Tendsto h (𝓝[<] (4 / 5)) (𝓝 0) := tendsto_nhds_of_eventually_eq hleft
  exact tendsto_nhds_unique h1 h2

lemma profileX_sq' (z : ℝ) : profileX z ^ 2 = 1 / (1 + z ^ 2) := Work.OddEnvelope.profileX_sq z
lemma profileX_pos' (z : ℝ) : 0 < profileX z := Work.OddEnvelope.profileX_pos z
lemma profileX_antiOn' : AntitoneOn profileX (Set.Ioi 0) :=
  Work.OddEnvelope.profileX_strictAntiOn.antitoneOn

lemma profileX_add_mul_deriv (z : ℝ) :
    profileX z + z * deriv profileX z = profileX z ^ 3 := by
  have hd := Commons.Geometry.Ulam.deriv_profileX_eq z
  have hsq : profileX z ^ 2 = 1 / (1 + z ^ 2) := profileX_sq' z
  rw [hd]
  have hne : (1 : ℝ) + z ^ 2 ≠ 0 := by positivity
  have hkey : profileX z * (1 / (1 + z ^ 2)) = profileX z ^ 3 := by
    rw [← hsq]; ring
  calc profileX z + z * (-(z / (1 + z ^ 2)) * profileX z)
      = profileX z * (1 / (1 + z ^ 2)) := by field_simp; ring
    _ = profileX z ^ 3 := hkey

lemma profileX_cube_le_half {z : ℝ} (hz : 4 / 5 ≤ z) : profileX z ^ 3 ≤ 1 / 2 := by
  have hLe : profileX z ≤ 4 / 5 := by
    have hanti := profileX_antiOn'
    have h1 : profileX z ≤ profileX (4 / 5) :=
      hanti (show (0:ℝ) < 4/5 by norm_num)
        (show (0:ℝ) < z by linarith) hz
    have hsq45 : profileX (4 / 5) ^ 2 = 25 / 41 := by
      rw [profileX_sq']; norm_num
    have hpos : 0 ≤ profileX (4 / 5) := le_of_lt (profileX_pos' _)
    have h2 : profileX (4 / 5) = Real.sqrt (25 / 41) := by
      rw [← Real.sqrt_sq hpos, hsq45]
    have h3 : Real.sqrt (25 / 41) ≤ 4 / 5 := by
      rw [← Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 4 / 5)]
      exact Real.sqrt_le_sqrt (by norm_num)
    linarith
  have h2 : profileX z ^ 2 ≤ 25 / 41 := by
    rw [profileX_sq']
    rw [div_le_iff₀ (by positivity : (0:ℝ) < 1 + z ^ 2)]
    nlinarith
  have h0 : 0 ≤ profileX z := le_of_lt (profileX_pos' z)
  nlinarith [hLe, h2, h0]

lemma profileX_ge_69 {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) : 69 / 100 ≤ profileX σ := by
  have hanti := profileX_antiOn'
  have h1 : profileX 1 ≤ profileX σ :=
    hanti (show (0:ℝ) < σ from hσ) (show (0:ℝ) < 1 by norm_num) hσ1
  have h2 : (69 / 100 : ℝ) ≤ profileX 1 := by
    have hprof : profileX 1 = 1 / Real.sqrt (1 + (1:ℝ) ^ 2) := rfl
    rw [hprof, le_div_iff₀ (Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 1 + (1:ℝ)^2))]
    have h3 : (69 / 100 : ℝ) * Real.sqrt 2 ≤ 1 := by
      have h4 := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
      nlinarith [Real.sqrt_nonneg 2]
    linarith [h3]
  linarith

lemma abs_deriv_h_le (hh : ContDiff ℝ (⊤ : ℕ∞) h) (H : Work.OddEnvelope.IsEnvelopeCurve h x y)
    (hclose : ∀ z : ℝ, 0 < z →
      |x z - profileX z| ≤ 1 / 100 ∧ |deriv x z - deriv profileX z| ≤ 1 / 100 ∧
      |deriv (deriv x) z - deriv (deriv profileX) z| ≤ 1 / 100 ∧
      |y z - profileX z| ≤ 1 / 100 ∧ |deriv y z - deriv profileX z| ≤ 1 / 100 ∧
      |deriv (deriv y) z - deriv (deriv profileX) z| ≤ 1 / 100) :
    ∀ z : ℝ, |deriv h z| ≤ 3 / 5 := by
  intro z
  rcases lt_or_ge z (4 / 5) with hlt | hge
  · rw [deriv_h_eq_zero_of_lt H hlt, abs_zero]; norm_num
  · rcases lt_or_ge (9 / 10 : ℝ) z with hgt | hle
    · rw [deriv_h_eq_zero_of_gt H hgt, abs_zero]; norm_num
    · have hzpos : 0 < z := by linarith
      have hc := hclose z hzpos
      have hub : deriv h z < 3 / 5 := by
        have h1 := H.mono_x z hzpos
        have hx1 := (abs_le.mp hc.1).2
        have hx2 := (abs_le.mp hc.2.1).2
        have hp3 := profileX_cube_le_half hge
        have hkey := profileX_add_mul_deriv z
        nlinarith [h1, hx1, hx2, hp3, hkey, hzpos.le, hle]
      have hlb : -(3 / 5) ≤ deriv h z := by
        have h1 := H.mono_y z hzpos
        have hy1 := (abs_le.mp hc.2.2.2.1).2
        have hy2 := (abs_le.mp hc.2.2.2.2.1).2
        have hp3 := profileX_cube_le_half hge
        have hkey := profileX_add_mul_deriv z
        nlinarith [h1, hy1, hy2, hp3, hkey, hzpos.le, hle]
      rw [abs_le]
      constructor
      · linarith
      · linarith

lemma abs_h_le (hh : ContDiff ℝ (⊤ : ℕ∞) h) (H : Work.OddEnvelope.IsEnvelopeCurve h x y)
    (hclose : ∀ z : ℝ, 0 < z →
      |x z - profileX z| ≤ 1 / 100 ∧ |deriv x z - deriv profileX z| ≤ 1 / 100 ∧
      |deriv (deriv x) z - deriv (deriv profileX) z| ≤ 1 / 100 ∧
      |y z - profileX z| ≤ 1 / 100 ∧ |deriv y z - deriv profileX z| ≤ 1 / 100 ∧
      |deriv (deriv y) z - deriv (deriv profileX) z| ≤ 1 / 100) :
    ∀ z : ℝ, |h z| ≤ 3 / 50 := by
  intro z
  rcases lt_or_ge z (4 / 5) with hlt | hge
  · rw [h_eq_zero_of_lt H hlt, abs_zero]; norm_num
  · rcases lt_or_ge (9 / 10 : ℝ) z with hgt | hle
    · rw [h_eq_zero_of_gt H hgt, abs_zero]; norm_num
    · have hd : ∀ u ∈ Set.Icc (4/5) z, ‖deriv h u‖ ≤ 3 / 5 := by
        intro u _
        rw [Real.norm_eq_abs]
        exact abs_deriv_h_le hh H hclose u
      have hdiff := Convex.norm_image_sub_le_of_norm_deriv_le (f := h) (s := Set.Icc (4/5) z)
        (fun u _ => (hh.differentiable (by simp)) u) hd (convex_Icc _ _) ⟨le_rfl, hge⟩ ⟨hge, le_rfl⟩
      have hz : ‖z - 4 / 5‖ ≤ 1 / 10 := by
        rw [Real.norm_eq_abs, abs_of_nonneg (by linarith)]
        linarith
      calc |h z| = ‖h z - h (4/5)‖ := by rw [h_at_left_end hh H, sub_zero, Real.norm_eq_abs]
        _ ≤ (3 / 5) * ‖z - 4 / 5‖ := hdiff
        _ ≤ (3 / 5) * (1 / 10) := by linarith
        _ = 3 / 50 := by norm_num


/-- **Strict positivity of the Abel denominator on the square `[s/2,1]²`.** -/
theorem Kden_pos_box {s : ℝ} (hs : 0 < s) (hs1 : s < 1)
    (hh : ContDiff ℝ (⊤ : ℕ∞) h) (H : Work.OddEnvelope.IsEnvelopeCurve h x y)
    (hclose : ∀ z : ℝ, 0 < z →
      |x z - profileX z| ≤ 1 / 100 ∧ |deriv x z - deriv profileX z| ≤ 1 / 100 ∧
      |deriv (deriv x) z - deriv (deriv profileX) z| ≤ 1 / 100 ∧
      |y z - profileX z| ≤ 1 / 100 ∧ |deriv y z - deriv profileX z| ≤ 1 / 100 ∧
      |deriv (deriv y) z - deriv (deriv profileX) z| ≤ 1 / 100) :
    (∀ v σ : ℝ, v ∈ Set.Icc (s / 2) 1 → σ ∈ Set.Icc (s / 2) 1 →
        0 < Work.OddVolterra.Kden h v σ (y σ)) ∧
    (∀ v σ : ℝ, v ∈ Set.Icc (s / 2) 1 → σ ∈ Set.Icc (s / 2) 1 →
        0 < Work.OddVolterra.Kden h v σ (-(x σ))) := by
  have hd3 : ∀ z : ℝ, |deriv h z| ≤ 3 / 5 := abs_deriv_h_le hh H hclose
  have hh3 : ∀ z : ℝ, |h z| ≤ 3 / 50 := abs_h_le hh H hclose
  have hq3 : ∀ v σ : ℝ, |Work.OddVolterra.hquot h v σ| ≤ 3 / 5 :=
    fun v σ => Work.OddVolterra.KernelExt.abs_hquot_le hd3 v σ
  constructor
  · intro v σ hv hσ
    have hσpos : 0 < σ := by linarith [hσ.1, hs]
    have hy : (17 : ℝ) / 25 ≤ y σ := by
      have h1 := (abs_le.mp (hclose σ hσpos).2.2.2.1).1
      have h2 := profileX_ge_69 hσpos hσ.2
      linarith
    have hA : 0 < y σ + Work.OddVolterra.hquot h v σ := by
      have h1 := (abs_le.mp (hq3 v σ)).1
      linarith
    have hB : 0 < Work.OddVolterra.line h σ (y σ) + Work.OddVolterra.line h v (y σ) := by
      rw [Work.OddVolterra.line, Work.OddVolterra.line]
      by_cases hcase : (4 : ℝ) / 5 ≤ σ + v
      · have h1 := (abs_le.mp (hh3 σ)).1
        have h2 := (abs_le.mp (hh3 v)).1
        nlinarith [hcase, hy, h1, h2]
      · have hσ0 : h σ = 0 := h_eq_zero_of_lt H (by linarith [hv.1, hs])
        have hv0 : h v = 0 := h_eq_zero_of_lt H (by linarith [hσ.1, hs])
        rw [hσ0, hv0]
        have hpos : 0 < σ + v := by linarith [hσ.1, hv.1, hs]
        nlinarith [hpos, hy]
    rw [Work.OddVolterra.Kden]
    exact Real.sqrt_pos.mpr (mul_pos hA hB)
  · intro v σ hv hσ
    have hσpos : 0 < σ := by linarith [hσ.1, hs]
    have hx : (17 : ℝ) / 25 ≤ x σ := by
      have h1 := (abs_le.mp (hclose σ hσpos).1).1
      have h2 := profileX_ge_69 hσpos hσ.2
      linarith
    have hA : -(x σ) + Work.OddVolterra.hquot h v σ < 0 := by
      have h1 := (abs_le.mp (hq3 v σ)).2
      linarith
    have hB : Work.OddVolterra.line h σ (-(x σ)) + Work.OddVolterra.line h v (-(x σ)) < 0 := by
      rw [Work.OddVolterra.line, Work.OddVolterra.line]
      by_cases hcase : (4 : ℝ) / 5 ≤ σ + v
      · have h1 := (abs_le.mp (hh3 σ)).2
        have h2 := (abs_le.mp (hh3 v)).2
        have hkey : (4 / 5) * (17 / 25) ≤ (σ + v) * x σ :=
          mul_le_mul hcase hx (by norm_num) (by linarith [hσ.1, hv.1, hs])
        nlinarith [hkey, h1, h2]
      · have hσ0 : h σ = 0 := h_eq_zero_of_lt H (by linarith [hv.1, hs])
        have hv0 : h v = 0 := h_eq_zero_of_lt H (by linarith [hσ.1, hs])
        rw [hσ0, hv0]
        have hpos : 0 < σ + v := by linarith [hσ.1, hv.1, hs]
        nlinarith [hpos, hx]
    rw [Work.OddVolterra.Kden]
    exact Real.sqrt_pos.mpr (mul_pos_of_neg_of_neg hA hB)

/-! ## Differentiation under the integral sign for the weighted τ-average -/

lemma fderiv_fst_apply (G : ℝ × ℝ → ℝ) (p : ℝ × ℝ) (hp : DifferentiableAt ℝ G p) :
    (fderiv ℝ G p) (1, 0) = deriv (fun y : ℝ => G (y, p.2)) p.1 := by
  have hcurve : HasDerivAt (fun y : ℝ => (y, p.2)) ((1 : ℝ), (0 : ℝ)) p.1 :=
    (hasDerivAt_id p.1).prodMk (hasDerivAt_const p.1 p.2)
  have h := hp.hasFDerivAt.comp_hasDerivAt p.1 hcurve
  simpa [Function.comp_def] using h.deriv.symm

lemma intervalIntegral_eq_integral_Ioo (f : ℝ → ℝ) :
    (∫ τ in (0 : ℝ)..1, f τ) = ∫ τ, f τ ∂(volume.restrict (Set.Ioo (0 : ℝ) 1)) :=
  (intervalIntegral.integral_of_le zero_le_one).trans integral_Ioc_eq_integral_Ioo

lemma one_div_sqrt_mul_le (τ : ℝ) (hτ : τ ∈ Set.Ioo (0:ℝ) 1) :
    1 / Real.sqrt (τ * (1 - τ)) ≤ 1 / Real.sqrt τ + 1 / Real.sqrt (1 - τ) := by
  have h1 : (0:ℝ) < τ := hτ.1
  have h2 : (0:ℝ) < 1 - τ := by linarith [hτ.2]
  have hsp : 0 < Real.sqrt τ := Real.sqrt_pos.mpr h1
  have hsp2 : 0 < Real.sqrt (1 - τ) := Real.sqrt_pos.mpr h2
  have hsum : (1:ℝ) ≤ Real.sqrt (1 - τ) + Real.sqrt τ := by
    have h4 := Real.sq_sqrt (mul_nonneg h1.le h2.le)
    have h5 := Real.sqrt_mul h1.le (1 - τ)
    have h6 := Real.sq_sqrt h1.le
    have h7 := Real.sq_sqrt h2.le
    nlinarith [Real.sqrt_nonneg τ, Real.sqrt_nonneg (1 - τ)]
  have hs : Real.sqrt (τ * (1 - τ)) = Real.sqrt τ * Real.sqrt (1 - τ) := Real.sqrt_mul h1.le (1 - τ)
  have hA : (0:ℝ) < (Real.sqrt τ)⁻¹ := inv_pos.mpr hsp
  have hB : (0:ℝ) < (Real.sqrt (1 - τ))⁻¹ := inv_pos.mpr hsp2
  have hkey : (Real.sqrt τ)⁻¹ * (Real.sqrt (1 - τ))⁻¹ ≤ (Real.sqrt τ)⁻¹ + (Real.sqrt (1 - τ))⁻¹ := by
    have h := mul_le_mul_of_nonneg_left hsum (le_of_lt (mul_pos hA hB))
    have h2' : (Real.sqrt τ)⁻¹ * (Real.sqrt (1 - τ))⁻¹ * (Real.sqrt (1 - τ) + Real.sqrt τ)
        = (Real.sqrt τ)⁻¹ + (Real.sqrt (1 - τ))⁻¹ := by
      field_simp
    rw [h2'] at h
    simpa using h
  calc 1 / Real.sqrt (τ * (1 - τ)) = (Real.sqrt τ)⁻¹ * (Real.sqrt (1 - τ))⁻¹ := by
        rw [hs, one_div, mul_inv]
    _ ≤ (Real.sqrt τ)⁻¹ + (Real.sqrt (1 - τ))⁻¹ := hkey
    _ = 1 / Real.sqrt τ + 1 / Real.sqrt (1 - τ) := by rw [one_div, one_div]

lemma integrableOn_div_sqrt (c : ℝ) :
    IntegrableOn (fun τ : ℝ => c / Real.sqrt τ) (Set.Ioo (0:ℝ) 1) volume := by
  have hA : IntegrableOn (fun τ : ℝ => τ ^ (-(1 / 2) : ℝ)) (Set.Ioo (0:ℝ) 1) volume :=
    (intervalIntegral.intervalIntegrable_rpow' (a := (0:ℝ)) (b := 1) (r := -(1 / 2))
      (by norm_num)).1.mono_set (fun τ hτ => ⟨hτ.1, le_of_lt hτ.2⟩)
  have hC : Integrable (fun τ : ℝ => c * τ ^ (-(1 / 2) : ℝ))
      (volume.restrict (Set.Ioo (0:ℝ) 1)) := hA.const_mul c
  refine hC.congr ?_
  refine ae_restrict_of_forall_mem measurableSet_Ioo ?_
  intro τ hτ
  have h1 : (0:ℝ) < τ := hτ.1
  show c * τ ^ (-(1 / 2) : ℝ) = c / Real.sqrt τ
  rw [Real.sqrt_eq_rpow, Real.rpow_neg h1.le]
  exact (div_eq_mul_inv c (τ ^ (1 / 2 : ℝ))).symm

lemma integrableOn_div_sqrt_one_sub (c : ℝ) :
    IntegrableOn (fun τ : ℝ => c / Real.sqrt (1 - τ)) (Set.Ioo (0:ℝ) 1) volume := by
  have hbase : IntervalIntegrable (fun x : ℝ => x ^ (-(1 / 2) : ℝ)) volume (0:ℝ) 1 :=
    intervalIntegral.intervalIntegrable_rpow' (a := (0:ℝ)) (b := 1) (r := -(1 / 2)) (by norm_num)
  have hsub : IntegrableOn (fun τ : ℝ => (1 - τ) ^ (-(1 / 2) : ℝ)) (Set.Ioc (0:ℝ) 1) volume := by
    have h2 : IntervalIntegrable (fun τ : ℝ => (1 - τ) ^ (-(1 / 2) : ℝ)) volume (0:ℝ) 1 := by
      simpa using (hbase.comp_sub_left (1 : ℝ)).symm
    exact h2.1
  have hsub' : IntegrableOn (fun τ : ℝ => (1 - τ) ^ (-(1 / 2) : ℝ)) (Set.Ioo (0:ℝ) 1) volume :=
    hsub.mono_set (fun τ hτ => ⟨hτ.1, le_of_lt hτ.2⟩)
  have hC : Integrable (fun τ : ℝ => c * (1 - τ) ^ (-(1 / 2) : ℝ))
      (volume.restrict (Set.Ioo (0:ℝ) 1)) := hsub'.const_mul c
  refine hC.congr ?_
  refine ae_restrict_of_forall_mem measurableSet_Ioo ?_
  intro τ hτ
  have h2 : (0:ℝ) < 1 - τ := by linarith [hτ.2]
  show c * (1 - τ) ^ (-(1 / 2) : ℝ) = c / Real.sqrt (1 - τ)
  rw [Real.sqrt_eq_rpow, Real.rpow_neg h2.le]
  exact (div_eq_mul_inv c ((1 - τ) ^ (1 / 2 : ℝ))).symm

lemma integrableOn_div_sqrt_mul (c : ℝ) :
    IntegrableOn (fun τ : ℝ => c / Real.sqrt (τ * (1 - τ))) (Set.Ioo (0:ℝ) 1) volume := by
  have hsum : IntegrableOn (fun τ : ℝ => |c| / Real.sqrt τ + |c| / Real.sqrt (1 - τ))
      (Set.Ioo (0:ℝ) 1) volume :=
    (integrableOn_div_sqrt |c|).add (integrableOn_div_sqrt_one_sub |c|)
  have hmeas : AEStronglyMeasurable (fun τ : ℝ => c / Real.sqrt (τ * (1 - τ)))
      (volume.restrict (Set.Ioo (0:ℝ) 1)) := by
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioo
    refine ContinuousOn.div continuousOn_const (Real.continuous_sqrt.comp_continuousOn (by fun_prop)) ?_
    intro τ hτ
    exact ne_of_gt (Real.sqrt_pos.mpr (mul_pos hτ.1 (by linarith [hτ.2])))
  refine Integrable.mono' hsum hmeas ?_
  refine ae_restrict_of_forall_mem measurableSet_Ioo (fun τ hτ => ?_)
  have h3 : (0:ℝ) < τ * (1 - τ) := mul_pos hτ.1 (by linarith [hτ.2])
  have hsp : 0 < Real.sqrt (τ * (1 - τ)) := Real.sqrt_pos.mpr h3
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hsp]
  have h := one_div_sqrt_mul_le τ hτ
  calc |c| / Real.sqrt (τ * (1 - τ)) = |c| * (1 / Real.sqrt (τ * (1 - τ))) := by ring
    _ ≤ |c| * (1 / Real.sqrt τ + 1 / Real.sqrt (1 - τ)) :=
        mul_le_mul_of_nonneg_left h (abs_nonneg c)
    _ = |c| / Real.sqrt τ + |c| / Real.sqrt (1 - τ) := by ring


lemma Ioo_ae_eq_Ioc_volume (a b : ℝ) : Set.Ioo a b =ᵐ[volume] Set.Ioc a b := by
  rw [ae_eq_set]
  constructor
  · have h : Set.Ioo a b \ Set.Ioc a b = ∅ := by
      ext x
      simp only [Set.mem_sdiff, Set.mem_Ioo, Set.mem_Ioc, Set.mem_empty_iff_false, iff_false]
      rintro ⟨⟨h1, h2⟩, h3⟩
      exact h3 ⟨h1, h2.le⟩
    rw [h, measure_empty]
  · have hsub : Set.Ioc a b \ Set.Ioo a b ⊆ {b} := by
      intro x hx
      simp only [Set.mem_sdiff, Set.mem_Ioc, Set.mem_Ioo] at hx
      simp only [Set.mem_singleton_iff]
      by_contra hne
      exact hx.2 ⟨hx.1.1, lt_of_le_of_ne hx.1.2 hne⟩
    exact measure_mono_null hsub (by simp)

lemma intervalIntegrable_div_sqrt (c : ℝ) :
    IntervalIntegrable (fun τ : ℝ => c / Real.sqrt τ) volume (0:ℝ) 1 := by
  rw [intervalIntegrable_iff, uIoc_of_le zero_le_one]
  exact (integrableOn_div_sqrt c).congr_set_ae (Ioo_ae_eq_Ioc_volume 0 1).symm

lemma integral_one_div_sqrt : (∫ τ in (0:ℝ)..1, (1:ℝ) / Real.sqrt τ) = 2 := by
  have hcongr : (∫ τ in (0:ℝ)..1, (1:ℝ) / Real.sqrt τ) = ∫ τ in (0:ℝ)..1, τ ^ (-(1/2) : ℝ) := by
    refine intervalIntegral.integral_congr (fun τ hτ => ?_)
    by_cases h0 : τ = 0
    · rw [h0]
      simp
    · have h0' : 0 < τ := lt_of_le_of_ne (by simpa using hτ.1) (Ne.symm h0)
      rw [one_div, Real.sqrt_eq_rpow, Real.rpow_neg h0'.le]
  rw [hcongr, integral_rpow (Or.inl (by norm_num : (-1:ℝ) < -(1/2)))]
  norm_num

/-- The differentiation-under-the-integral-sign formula for the weighted `τ`-average. -/
theorem deriv_parametrization_eq (G : ℝ × ℝ → ℝ) {s σ : ℝ}
    (hG : ContDiffOn ℝ 1 G (Set.Icc (s / 2) 1 ×ˢ Set.Icc (s / 2) 1))
    (hs : 0 < s) (hs1 : s < 1) (hσ : σ ∈ Set.Ioo s 1) :
    deriv (fun u : ℝ => ∫ τ in (0 : ℝ)..1,
        G (u + τ * (σ - u), σ) / Real.sqrt (τ * (1 - τ))) s
      = ∫ τ in (0 : ℝ)..1,
        (fderiv ℝ G (s + τ * (σ - s), σ)) (1, 0) * (1 - τ) / Real.sqrt (τ * (1 - τ)) := by
  classical
  let box : Set (ℝ × ℝ) := Set.Icc (s / 2) 1 ×ˢ Set.Icc (s / 2) 1
  let U : Set (ℝ × ℝ) := Set.Ioo (s / 2) 1 ×ˢ Set.Ioo (s / 2) 1
  let P : Set ℝ := Set.Ioo (s / 2) 1
  have hbox : box = Set.Icc (s / 2) 1 ×ˢ Set.Icc (s / 2) 1 := rfl
  have hU : U = Set.Ioo (s / 2) 1 ×ˢ Set.Ioo (s / 2) 1 := rfl
  have hP : P = Set.Ioo (s / 2) 1 := rfl
  have hUopen : IsOpen U := isOpen_Ioo.prod isOpen_Ioo
  have hsP : s ∈ P := ⟨by linarith, hs1⟩
  have hPmem : P ∈ 𝓝 s := isOpen_Ioo.mem_nhds hsP
  have hUsub : U ⊆ box := fun p hp =>
    ⟨⟨le_of_lt hp.1.1, le_of_lt hp.1.2⟩, ⟨le_of_lt hp.2.1, le_of_lt hp.2.2⟩⟩
  have hGU : ContDiffOn ℝ 1 G U := hG.mono hUsub
  have hGcontU : ContinuousOn G U := hGU.continuousOn
  have hGdiffU : DifferentiableOn ℝ G U := hGU.differentiableOn (by norm_num)
  have hfdcont : ContinuousOn (fun p : ℝ × ℝ => fderiv ℝ G p) U := by
    have h1 : ContDiffOn ℝ 0 (fderivWithin ℝ G U) U :=
      hGU.fderivWithin hUopen.uniqueDiffOn (by norm_num)
    exact (h1.continuousOn).congr (fun p hp => (fderivWithin_of_isOpen hUopen hp).symm)
  obtain ⟨K, hK⟩ := hG.exists_lipschitzOnWith (by simp)
    ((convex_Icc (s/2) 1).prod (convex_Icc (s/2) 1)) (isCompact_Icc.prod isCompact_Icc)
  have hmemU : ∀ x ∈ P, ∀ a ∈ Set.Ioo (0:ℝ) 1, (x + a * (σ - x), σ) ∈ U := by
    intro x hx a ha
    refine ⟨⟨?_, ?_⟩, ⟨by linarith [hσ.1], hσ.2⟩⟩
    · nlinarith [hx.1, ha.1, ha.2, hσ.1]
    · nlinarith [hx.2, ha.1, ha.2, hσ.2]
  obtain ⟨Cg, hCg⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hG.continuousOn
  have hCg0 : 0 ≤ Cg :=
    le_trans (norm_nonneg _) (hCg (s, σ) ⟨⟨by linarith, hs1.le⟩, ⟨by linarith [hσ.1], hσ.2.le⟩⟩)
  set ν : Measure ℝ := volume.restrict (Set.Ioo (0:ℝ) 1) with hν
  have hderiv : HasDerivAt (fun n : ℝ => ∫ a, G (n + a * (σ - n), σ) / Real.sqrt (a * (1 - a)) ∂ν)
      (∫ a, (fderiv ℝ G (s + a * (σ - s), σ)) (1, 0) * (1 - a) / Real.sqrt (a * (1 - a)) ∂ν) s := by
    refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := ν) (x₀ := s) (s := P)
      (F := fun n a => G (n + a * (σ - n), σ) / Real.sqrt (a * (1 - a)))
      (F' := fun x a => (fderiv ℝ G (x + a * (σ - x), σ)) (1, 0) * (1 - a) / Real.sqrt (a * (1 - a)))
      (bound := fun a => (K : ℝ) / Real.sqrt a)
      hPmem ?_ ?_ ?_ ?_ ?_ ?_).2
    · filter_upwards [hPmem] with x hx
      refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioo
      refine ContinuousOn.div ?_ (Real.continuous_sqrt.comp_continuousOn (by fun_prop)) ?_
      · exact hGcontU.comp (by fun_prop) (fun a ha => hmemU x hx a ha)
      · intro a ha
        exact ne_of_gt (Real.sqrt_pos.mpr (mul_pos ha.1 (by linarith [ha.2])))
    · refine Integrable.mono' ((integrableOn_div_sqrt Cg).add (integrableOn_div_sqrt_one_sub Cg)) ?_ ?_
      · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioo
        refine ContinuousOn.div ?_ (Real.continuous_sqrt.comp_continuousOn (by fun_prop)) ?_
        · exact hGcontU.comp (by fun_prop) (fun a ha => hmemU s hsP a ha)
        · intro a ha
          exact ne_of_gt (Real.sqrt_pos.mpr (mul_pos ha.1 (by linarith [ha.2])))
      · refine ae_restrict_of_forall_mem measurableSet_Ioo (fun a ha => ?_)
        have hb : ‖G (s + a * (σ - s), σ)‖ ≤ Cg := hCg _ (hUsub (hmemU s hsP a ha))
        have h3 : (0:ℝ) < a * (1 - a) := mul_pos ha.1 (by linarith [ha.2])
        have hsp : 0 < Real.sqrt (a * (1 - a)) := Real.sqrt_pos.mpr h3
        rw [Real.norm_eq_abs, abs_div, abs_of_pos hsp]
        have h := one_div_sqrt_mul_le a ha
        calc ‖G (s + a * (σ - s), σ)‖ / Real.sqrt (a * (1 - a))
            = ‖G (s + a * (σ - s), σ)‖ * (1 / Real.sqrt (a * (1 - a))) := by ring
          _ ≤ Cg * (1 / Real.sqrt a + 1 / Real.sqrt (1 - a)) :=
              mul_le_mul hb h (by positivity) hCg0
          _ = Cg / Real.sqrt a + Cg / Real.sqrt (1 - a) := by ring
    · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioo
      refine ContinuousOn.div (ContinuousOn.mul ?_ (by fun_prop))
        (Real.continuous_sqrt.comp_continuousOn (by fun_prop)) ?_
      · exact (hfdcont.comp (by fun_prop) (fun a ha => hmemU s hsP a ha)).clm_apply continuousOn_const
      · intro a ha
        exact ne_of_gt (Real.sqrt_pos.mpr (mul_pos ha.1 (by linarith [ha.2])))
    · refine ae_restrict_of_forall_mem measurableSet_Ioo (fun a ha => ?_)
      intro x hx
      have ha1 : (0:ℝ) < a := ha.1
      have ha2 : a < 1 := ha.2
      have hxU : (x + a * (σ - x), σ) ∈ U := hmemU x hx a ha
      have hxP : x + a * (σ - x) ∈ P := by
        refine ⟨?_, ?_⟩
        · nlinarith [hx.1, ha.1, ha.2, hσ.1]
        · nlinarith [hx.2, ha.1, ha.2, hσ.2]
      have hlip : LipschitzOnWith K (fun y : ℝ => G (y, σ)) P := by
        rw [lipschitzOnWith_iff_norm_sub_le]
        intro y hy y' hy'
        have h1 : ((y, σ) : ℝ × ℝ) ∈ box :=
          ⟨⟨le_of_lt hy.1, le_of_lt hy.2⟩, ⟨by linarith [hσ.1], hσ.2.le⟩⟩
        have h2 : ((y', σ) : ℝ × ℝ) ∈ box :=
          ⟨⟨le_of_lt hy'.1, le_of_lt hy'.2⟩, ⟨by linarith [hσ.1], hσ.2.le⟩⟩
        have h := hK.norm_sub_le h1 h2
        have hnorm : ‖((y, σ) : ℝ × ℝ) - (y', σ)‖ = ‖y - y'‖ := by
          rw [Prod.norm_def]
          simp
        rw [hnorm] at h
        simpa using h
      have hb1 : ‖(fderiv ℝ G (x + a * (σ - x), σ)) (1, 0)‖ ≤ (K : ℝ) := by
        rw [fderiv_fst_apply G _ (hGdiffU.differentiableAt (hUopen.mem_nhds hxU))]
        exact norm_deriv_le_of_lipschitzOn (isOpen_Ioo.mem_nhds hxP) hlip
      have hb2 : |1 - a| / Real.sqrt (a * (1 - a)) ≤ 1 / Real.sqrt a := by
        have hsa : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha1
        have hsp : 0 < Real.sqrt (a * (1 - a)) := Real.sqrt_pos.mpr (mul_pos ha1 (by linarith))
        rw [abs_of_pos (by linarith : (0:ℝ) < 1 - a)]
        rw [div_le_div_iff₀ hsp hsa, one_mul]
        rw [Real.sqrt_mul ha1.le (1 - a)]
        have hkey : 1 - a ≤ Real.sqrt (1 - a) := by
          have h1 : (1 - a) ^ 2 ≤ (Real.sqrt (1 - a)) ^ 2 := by
            rw [Real.sq_sqrt (by linarith : (0:ℝ) ≤ 1 - a)]
            nlinarith
          nlinarith [Real.sqrt_nonneg (1 - a)]
        nlinarith [hkey, Real.sqrt_nonneg a]
      calc ‖(fderiv ℝ G (x + a * (σ - x), σ)) (1, 0) * (1 - a) / Real.sqrt (a * (1 - a))‖
          = ‖(fderiv ℝ G (x + a * (σ - x), σ)) (1, 0)‖ * (|1 - a| / Real.sqrt (a * (1 - a))) := by
            rw [Real.norm_eq_abs, abs_div, abs_mul,
              abs_of_pos (Real.sqrt_pos.mpr (mul_pos ha1 (by linarith)))]
            rw [Real.norm_eq_abs]
            ring
        _ ≤ (K : ℝ) * (1 / Real.sqrt a) :=
            mul_le_mul hb1 hb2 (by positivity) (by positivity)
        _ = (K : ℝ) / Real.sqrt a := by rw [mul_one_div]
    · exact (integrableOn_div_sqrt K)
    · refine ae_restrict_of_forall_mem measurableSet_Ioo (fun a ha => ?_)
      intro x hx
      have ha1 : (0:ℝ) < a := ha.1
      have h3 : (0:ℝ) < a * (1 - a) := mul_pos ha1 (by linarith [ha.2])
      have h1 : HasDerivAt (fun y : ℝ => y + a * (σ - y)) (1 - a) x := by
        have h := (hasDerivAt_id x).add (((hasDerivAt_const x σ).sub (hasDerivAt_id x)).const_mul a)
        rw [show (1:ℝ) + a * (0 - 1) = 1 - a from by ring] at h
        exact h
      have hcurve : HasDerivAt (fun y : ℝ => (y + a * (σ - y), σ)) ((1 - a, (0:ℝ))) x :=
        h1.prodMk (hasDerivAt_const x σ)
      have hGd : HasFDerivAt G (fderiv ℝ G (x + a * (σ - x), σ)) (x + a * (σ - x), σ) :=
        (hGdiffU.differentiableAt (hUopen.mem_nhds (hmemU x hx a ha))).hasFDerivAt
      have hcomp := hGd.comp_hasDerivAt x hcurve
      have hval : (fderiv ℝ G (x + a * (σ - x), σ)) ((1 - a, (0:ℝ)))
          = (fderiv ℝ G (x + a * (σ - x), σ)) (1, 0) * (1 - a) := by
        rw [show ((1 - a, (0:ℝ)) : ℝ × ℝ) = (1 - a) • ((1:ℝ), (0:ℝ)) by simp, map_smul]
        ring
      have hfinal := (hcomp.congr_deriv hval).div_const (Real.sqrt (a * (1 - a)))
      simpa using hfinal
  have hL : (fun u : ℝ => ∫ τ in (0 : ℝ)..1, G (u + τ * (σ - u), σ) / Real.sqrt (τ * (1 - τ)))
      = fun u : ℝ => ∫ a, G (u + a * (σ - u), σ) / Real.sqrt (a * (1 - a)) ∂ν := by
    funext u
    exact intervalIntegral_eq_integral_Ioo _
  have hR : (∫ a, (fderiv ℝ G (s + a * (σ - s), σ)) (1, 0) * (1 - a) / Real.sqrt (a * (1 - a)) ∂ν)
      = ∫ τ in (0 : ℝ)..1,
          (fderiv ℝ G (s + τ * (σ - s), σ)) (1, 0) * (1 - τ) / Real.sqrt (τ * (1 - τ)) :=
    (intervalIntegral_eq_integral_Ioo _).symm
  rw [hL, hderiv.deriv, hR]

/-- **Interval integrability of the weighted parametrized derivative.** -/
theorem theta_deriv_parametrization_integrable (G : ℝ × ℝ → ℝ) {s : ℝ}
    (hG : ContDiffOn ℝ 1 G (Set.Icc (s / 2) 1 ×ˢ Set.Icc (s / 2) 1))
    (hs : 0 < s) (hs1 : s < 1) :
    IntervalIntegrable
      (fun σ : ℝ => deriv (fun u : ℝ =>
        ∫ τ in (0 : ℝ)..1, G (u + τ * (σ - u), σ) / Real.sqrt (τ * (1 - τ))) s)
      volume s 1 := by
  classical
  let box : Set (ℝ × ℝ) := Set.Icc (s / 2) 1 ×ˢ Set.Icc (s / 2) 1
  let U : Set (ℝ × ℝ) := Set.Ioo (s / 2) 1 ×ˢ Set.Ioo (s / 2) 1
  have hUopen : IsOpen U := isOpen_Ioo.prod isOpen_Ioo
  have hUsub : U ⊆ box := fun p hp =>
    ⟨⟨le_of_lt hp.1.1, le_of_lt hp.1.2⟩, ⟨le_of_lt hp.2.1, le_of_lt hp.2.2⟩⟩
  have hGU : ContDiffOn ℝ 1 G U := hG.mono hUsub
  have hGdiffU : DifferentiableOn ℝ G U := hGU.differentiableOn (by norm_num)
  have hfdcont : ContinuousOn (fun p : ℝ × ℝ => fderiv ℝ G p) U := by
    have h1 : ContDiffOn ℝ 0 (fderivWithin ℝ G U) U :=
      hGU.fderivWithin hUopen.uniqueDiffOn (by norm_num)
    exact (h1.continuousOn).congr (fun p hp => (fderivWithin_of_isOpen hUopen hp).symm)
  obtain ⟨K, hK⟩ := hG.exists_lipschitzOnWith (by simp)
    ((convex_Icc (s/2) 1).prod (convex_Icc (s/2) 1)) (isCompact_Icc.prod isCompact_Icc)
  have hmemU : ∀ x ∈ Set.Ioo (s/2) 1, ∀ σ ∈ Set.Ioo s 1, ∀ a ∈ Set.Ioo (0:ℝ) 1,
      (x + a * (σ - x), σ) ∈ U := by
    intro x hx σ hσ a ha
    refine ⟨⟨?_, ?_⟩, ⟨by linarith [hσ.1], hσ.2⟩⟩
    · nlinarith [hx.1, ha.1, ha.2, hσ.1]
    · nlinarith [hx.2, ha.1, ha.2, hσ.2]
  have hsP : s ∈ Set.Ioo (s/2) 1 := ⟨by linarith, hs1⟩
  -- ## Step 1: the pointwise bound
  have hbd : ∀ σ ∈ Set.Ioo s 1,
      ‖deriv (fun u : ℝ => ∫ τ in (0 : ℝ)..1,
        G (u + τ * (σ - u), σ) / Real.sqrt (τ * (1 - τ))) s‖ ≤ 2 * (K : ℝ) := by
    intro σ hσ
    rw [deriv_parametrization_eq G hG hs hs1 hσ]
    have hpoint : ∀ τ ∈ Set.Ioo (0:ℝ) 1,
        ‖(fderiv ℝ G (s + τ * (σ - s), σ)) (1, 0) * (1 - τ) / Real.sqrt (τ * (1 - τ))‖
          ≤ (K : ℝ) / Real.sqrt τ := by
      intro τ hτ
      have hτ1 : (0:ℝ) < τ := hτ.1
      have hxU : (s + τ * (σ - s), σ) ∈ U := hmemU s hsP σ hσ τ hτ
      have hxP : s + τ * (σ - s) ∈ Set.Ioo (s/2) 1 := by
        refine ⟨?_, ?_⟩
        · nlinarith [hτ.1, hs, hσ.1]
        · nlinarith [hτ.2, hs1, hσ.2]
      have hlip : LipschitzOnWith K (fun y : ℝ => G (y, σ)) (Set.Ioo (s/2) 1) := by
        rw [lipschitzOnWith_iff_norm_sub_le]
        intro y hy y' hy'
        have h1 : ((y, σ) : ℝ × ℝ) ∈ box :=
          ⟨⟨le_of_lt hy.1, le_of_lt hy.2⟩, ⟨by linarith [hσ.1], hσ.2.le⟩⟩
        have h2 : ((y', σ) : ℝ × ℝ) ∈ box :=
          ⟨⟨le_of_lt hy'.1, le_of_lt hy'.2⟩, ⟨by linarith [hσ.1], hσ.2.le⟩⟩
        have h := hK.norm_sub_le h1 h2
        have hnorm : ‖((y, σ) : ℝ × ℝ) - (y', σ)‖ = ‖y - y'‖ := by
          rw [Prod.norm_def]
          simp
        rw [hnorm] at h
        simpa using h
      have hb1 : ‖(fderiv ℝ G (s + τ * (σ - s), σ)) (1, 0)‖ ≤ (K : ℝ) := by
        rw [fderiv_fst_apply G _ (hGdiffU.differentiableAt (hUopen.mem_nhds hxU))]
        exact norm_deriv_le_of_lipschitzOn (isOpen_Ioo.mem_nhds hxP) hlip
      have hb2 : |1 - τ| / Real.sqrt (τ * (1 - τ)) ≤ 1 / Real.sqrt τ := by
        have hsa : 0 < Real.sqrt τ := Real.sqrt_pos.mpr hτ1
        have hsp : 0 < Real.sqrt (τ * (1 - τ)) := Real.sqrt_pos.mpr (mul_pos hτ1 (by linarith [hτ.2]))
        rw [abs_of_pos (by linarith [hτ.2] : (0:ℝ) < 1 - τ)]
        rw [div_le_div_iff₀ hsp hsa, one_mul]
        rw [Real.sqrt_mul hτ1.le (1 - τ)]
        have hkey : 1 - τ ≤ Real.sqrt (1 - τ) := by
          have hs2 : (Real.sqrt (1 - τ)) ^ 2 = 1 - τ :=
            Real.sq_sqrt (by linarith [hτ.2] : (0:ℝ) ≤ 1 - τ)
          have hs1 : Real.sqrt (1 - τ) ≤ 1 := by
            nlinarith [Real.sqrt_nonneg (1 - τ)]
          nlinarith [Real.sqrt_nonneg (1 - τ)]
        nlinarith [hkey, Real.sqrt_nonneg τ]
      calc ‖(fderiv ℝ G (s + τ * (σ - s), σ)) (1, 0) * (1 - τ) / Real.sqrt (τ * (1 - τ))‖
          = ‖(fderiv ℝ G (s + τ * (σ - s), σ)) (1, 0)‖
              * (|1 - τ| / Real.sqrt (τ * (1 - τ))) := by
            rw [Real.norm_eq_abs, abs_div, abs_mul,
              abs_of_pos (Real.sqrt_pos.mpr (mul_pos hτ1 (by linarith [hτ.2])))]
            rw [Real.norm_eq_abs]
            ring
        _ ≤ (K : ℝ) * (1 / Real.sqrt τ) :=
            mul_le_mul hb1 hb2 (by positivity) (by positivity)
        _ = (K : ℝ) / Real.sqrt τ := by rw [mul_one_div]
    have hmono : (∫ τ in (0:ℝ)..1,
        ‖(fderiv ℝ G (s + τ * (σ - s), σ)) (1, 0) * (1 - τ) / Real.sqrt (τ * (1 - τ))‖)
        ≤ ∫ τ in (0:ℝ)..1, (K : ℝ) / Real.sqrt τ := by
      refine intervalIntegral.integral_mono_on zero_le_one ?_
        (intervalIntegrable_div_sqrt K) ?_
      · rw [intervalIntegrable_iff, uIoc_of_le zero_le_one]
        have hIoo : IntegrableOn (fun τ : ℝ =>
            ‖(fderiv ℝ G (s + τ * (σ - s), σ)) (1, 0) * (1 - τ) / Real.sqrt (τ * (1 - τ))‖)
            (Set.Ioo (0:ℝ) 1) volume := by
          have hF'cont_σ : ContinuousOn (fun τ : ℝ =>
              (fderiv ℝ G (s + τ * (σ - s), σ)) (1, 0) * (1 - τ) / Real.sqrt (τ * (1 - τ)))
              (Set.Ioo (0:ℝ) 1) := by
            refine ContinuousOn.div (ContinuousOn.mul ?_ (by fun_prop))
              (Real.continuous_sqrt.comp_continuousOn (by fun_prop)) ?_
            · exact (hfdcont.comp (by fun_prop)
                (fun a ha => hmemU s hsP σ hσ a ha)).clm_apply continuousOn_const
            · intro a ha
              exact ne_of_gt (Real.sqrt_pos.mpr (mul_pos ha.1 (by linarith [ha.2])))
          refine Integrable.mono' (integrableOn_div_sqrt K) ?_ ?_
          · exact hF'cont_σ.norm.aestronglyMeasurable measurableSet_Ioo
          · refine ae_restrict_of_forall_mem measurableSet_Ioo (fun τ hτ => ?_)
            rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
            exact hpoint τ hτ
        exact hIoo.congr_set_ae (Ioo_ae_eq_Ioc_volume 0 1).symm
      · intro τ hτ
        rcases eq_or_lt_of_le hτ.1 with h0 | h0
        · subst h0
          simp
        · rcases eq_or_lt_of_le hτ.2 with h1 | h1
          · subst h1
            simp
          · exact hpoint τ ⟨h0, h1⟩
    have h3 : (∫ τ in (0:ℝ)..1, (K : ℝ) / Real.sqrt τ) = 2 * (K : ℝ) := by
      have hc : (∫ τ in (0:ℝ)..1, (K : ℝ) / Real.sqrt τ)
          = (K : ℝ) * ∫ τ in (0:ℝ)..1, (1:ℝ) / Real.sqrt τ := by
        rw [← intervalIntegral.integral_const_mul]
        exact intervalIntegral.integral_congr (fun τ _ => by ring)
      rw [hc, integral_one_div_sqrt]
      ring
    calc ‖(∫ τ in (0:ℝ)..1,
            (fderiv ℝ G (s + τ * (σ - s), σ)) (1, 0) * (1 - τ) / Real.sqrt (τ * (1 - τ)))‖
        ≤ ∫ τ in (0:ℝ)..1,
            ‖(fderiv ℝ G (s + τ * (σ - s), σ)) (1, 0) * (1 - τ) / Real.sqrt (τ * (1 - τ))‖ :=
          intervalIntegral.norm_integral_le_integral_norm zero_le_one
      _ ≤ ∫ τ in (0:ℝ)..1, (K : ℝ) / Real.sqrt τ := hmono
      _ = 2 * (K : ℝ) := h3
  -- ## Step 2: measurability
  have hF'cont : ContinuousOn (fun p : ℝ × ℝ =>
      (fderiv ℝ G (s + p.2 * (p.1 - s), p.1)) (1, 0) * (1 - p.2)
        / Real.sqrt (p.2 * (1 - p.2))) (Set.Ioo s 1 ×ˢ Set.Ioo (0:ℝ) 1) := by
    refine ContinuousOn.div (ContinuousOn.mul ?_ (by fun_prop))
      (Real.continuous_sqrt.comp_continuousOn (by fun_prop)) ?_
    · exact (hfdcont.comp (by fun_prop)
        (fun p hp => hmemU s hsP p.1 hp.1 p.2 hp.2)).clm_apply continuousOn_const
    · intro p hp
      exact ne_of_gt (Real.sqrt_pos.mpr (mul_pos hp.2.1 (by linarith [hp.2.2])))
  have hΦ : AEStronglyMeasurable (fun σ : ℝ => deriv (fun u : ℝ =>
      ∫ τ in (0 : ℝ)..1, G (u + τ * (σ - u), σ) / Real.sqrt (τ * (1 - τ))) s)
      (volume.restrict (Set.Ioo s 1)) := by
    have hjoint : AEStronglyMeasurable (fun p : ℝ × ℝ =>
        (fderiv ℝ G (s + p.2 * (p.1 - s), p.1)) (1, 0) * (1 - p.2)
          / Real.sqrt (p.2 * (1 - p.2)))
        ((volume.restrict (Set.Ioo s 1)).prod (volume.restrict (Set.Ioo (0:ℝ) 1))) := by
      rw [Measure.prod_restrict]
      exact hF'cont.aestronglyMeasurable (measurableSet_Ioo.prod measurableSet_Ioo)
    have hparam := hjoint.integral_prod_right'
    refine hparam.congr ?_
    refine ae_restrict_of_forall_mem measurableSet_Ioo (fun σ hσ => ?_)
    show (∫ τ, (fderiv ℝ G (s + τ * (σ - s), σ)) (1, 0) * (1 - τ) / Real.sqrt (τ * (1 - τ))
        ∂(volume.restrict (Set.Ioo (0:ℝ) 1))) = deriv (fun u : ℝ => ∫ τ in (0:ℝ)..1,
          G (u + τ * (σ - u), σ) / Real.sqrt (τ * (1 - τ))) s
    rw [deriv_parametrization_eq G hG hs hs1 hσ]
    exact (intervalIntegral_eq_integral_Ioo _).symm
  -- ## Step 3: assembly
  have hmeas' : AEStronglyMeasurable (fun σ : ℝ => deriv (fun u : ℝ =>
      ∫ τ in (0 : ℝ)..1, G (u + τ * (σ - u), σ) / Real.sqrt (τ * (1 - τ))) s)
      (volume.restrict (Set.Ioc s 1)) := by
    rw [show volume.restrict (Set.Ioc s 1) = volume.restrict (Set.Ioo s 1) from
      Measure.restrict_congr_set (Ioo_ae_eq_Ioc_volume s 1).symm]
    exact hΦ
  have hbdd : ∀ᵐ σ ∂(volume.restrict (Set.Ioc s 1)),
      ‖deriv (fun u : ℝ => ∫ τ in (0 : ℝ)..1,
        G (u + τ * (σ - u), σ) / Real.sqrt (τ * (1 - τ))) s‖ ≤ 2 * (K : ℝ) := by
    rw [show volume.restrict (Set.Ioc s 1) = volume.restrict (Set.Ioo s 1) from
      Measure.restrict_congr_set (Ioo_ae_eq_Ioc_volume s 1).symm]
    exact ae_restrict_of_forall_mem measurableSet_Ioo (fun σ hσ => hbd σ hσ)
  have hint : IntegrableOn (fun σ : ℝ => deriv (fun u : ℝ =>
      ∫ τ in (0 : ℝ)..1, G (u + τ * (σ - u), σ) / Real.sqrt (τ * (1 - τ))) s)
      (Set.Ioc s 1) volume := by
    refine IntegrableOn.of_bound ?_ hmeas' (2 * (K : ℝ)) hbdd
    refine lt_of_le_of_lt (measure_mono (Set.Ioc_subset_Icc_self)) ?_
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_lt_top
  rw [intervalIntegrable_iff, uIoc_of_le hs1.le]
  exact hint


/-! ## The main theorem -/

/-- **Interval-integrability of the `Θ`-integrand of the odd transition-slope system.** -/
theorem theta_integrable (n : ℕ) (hn : 1 ≤ n) {h x y : ℝ → ℝ}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (H : Work.OddEnvelope.IsEnvelopeCurve h x y)
    (hmeF : ∀ s : ℝ, 0 < s → s ≤ 1 →
      Work.OddVolterra.momentF n h x y (Work.OddEnvelope.envelopeProfile h x y) s =
        Commons.Geometry.Ulam.oddSemicircleMomentConstant n / Real.sqrt (1 + s ^ 2))
    (hmeH : ∀ s : ℝ, 0 < s → s ≤ 1 →
      Work.OddVolterra.momentH n h x y (Work.OddEnvelope.envelopeProfile h x y) s = 0)
    (hclose : ∀ s : ℝ, 0 < s →
      |x s - Commons.Geometry.Ulam.profileX s| ≤ 1 / 100 ∧
      |deriv x s - deriv Commons.Geometry.Ulam.profileX s| ≤ 1 / 100 ∧
      |deriv (deriv x) s - deriv (deriv Commons.Geometry.Ulam.profileX) s| ≤ 1 / 100 ∧
      |y s - Commons.Geometry.Ulam.profileX s| ≤ 1 / 100 ∧
      |deriv y s - deriv Commons.Geometry.Ulam.profileX s| ≤ 1 / 100 ∧
      |deriv (deriv y) s - deriv (deriv Commons.Geometry.Ulam.profileX) s| ≤ 1 / 100) :
    ∀ s ∈ Set.Ioo (0:ℝ) 1,
      IntervalIntegrable (fun σ : ℝ =>
        Work.OddVolterra.Theta n h s σ (Work.OddVolterra.stateOf x y σ)) volume s 1 := by
  intro s hs
  obtain ⟨hs0, hs1⟩ := hs
  obtain ⟨hposy, hposx⟩ := Kden_pos_box hs0 hs1 hh H hclose
  -- the manifest kernel is `C²` on the square `[s/2,1]²`
  have hbox2 : ContDiffOn ℝ 2 (fun p : ℝ × ℝ =>
      Work.OddVolterra.KernelExt.KvecM n h p.1 p.2 (x p.2) (y p.2) (deriv x p.2) (deriv y p.2))
      (Set.Icc (s / 2) 1 ×ˢ Set.Icc (s / 2) 1) :=
    Work.OddVolterra.KernelExt.KvecM_contDiffOn_box n hh H.smooth_x H.smooth_y
      (by linarith) le_rfl hposy hposx
  have hGfun : ∀ i : Fin 2, ContDiffOn ℝ 1 (fun p : ℝ × ℝ =>
      (Work.OddVolterra.KernelExt.KvecM n h p.1 p.2 (x p.2) (y p.2) (deriv x p.2)
        (deriv y p.2)) i) (Set.Icc (s / 2) 1 ×ˢ Set.Icc (s / 2) 1) := by
    intro i
    have h1 := hbox2.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
    exact ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) i).contDiff.comp_contDiffOn
      h1).of_le (by norm_num)
  -- the last two rows of `ΘM`, via the parametric differentiation lemma
  have hrow : ∀ i : Fin 2, IntervalIntegrable (fun σ : ℝ => deriv (fun u : ℝ =>
      ∫ τ in (0 : ℝ)..1, (Work.OddVolterra.KernelExt.KvecM n h (u + τ * (σ - u)) σ
        (x σ) (y σ) (deriv x σ) (deriv y σ)) i / Real.sqrt (τ * (1 - τ))) s) volume s 1 :=
    fun i => theta_deriv_parametrization_integrable _ (hGfun i) hs0 hs1
  -- the manifest integrand is interval-integrable
  have hintM : IntervalIntegrable (fun σ : ℝ =>
      Work.OddVolterra.KernelExt.ThetaM n h s σ (Work.OddVolterra.stateOf x y σ))
      volume s 1 := by
    rw [intervalIntegrable_iff, uIoc_of_le hs1.le]
    have hiff : IntegrableOn (fun σ : ℝ =>
        Work.OddVolterra.KernelExt.ThetaM n h s σ (Work.OddVolterra.stateOf x y σ))
        (Set.Ioc s 1) volume ↔
        ∀ i : Fin 4, IntegrableOn (fun σ : ℝ =>
          (Work.OddVolterra.KernelExt.ThetaM n h s σ (Work.OddVolterra.stateOf x y σ)) i)
          (Set.Ioc s 1) volume := by
      show Integrable (fun σ : ℝ =>
          Work.OddVolterra.KernelExt.ThetaM n h s σ (Work.OddVolterra.stateOf x y σ))
          (volume.restrict (Set.Ioc s 1)) ↔
        ∀ i : Fin 4, Integrable (fun σ : ℝ =>
          (Work.OddVolterra.KernelExt.ThetaM n h s σ (Work.OddVolterra.stateOf x y σ)) i)
          (volume.restrict (Set.Ioc s 1))
      exact integrable_pi_iff
    rw [hiff]
    intro i
    fin_cases i
    · have hcont : ContinuousOn (fun σ : ℝ => -deriv x σ) (Set.uIcc s 1) := by
        refine ContinuousOn.neg ?_
        refine (Work.OddVolterra.KernelExt.contDiffOn_deriv_Ioi H.smooth_x).continuousOn.mono ?_
        intro σ hσ
        exact lt_of_lt_of_le hs0 (by simpa [min_eq_left hs1.le] using hσ.1)
      refine (hcont.intervalIntegrable).1.congr_fun (fun σ _ => ?_) measurableSet_Ioc
      simp [Work.OddVolterra.KernelExt.ThetaM, Work.OddVolterra.stateOf]
    · have hcont : ContinuousOn (fun σ : ℝ => -deriv y σ) (Set.uIcc s 1) := by
        refine ContinuousOn.neg ?_
        refine (Work.OddVolterra.KernelExt.contDiffOn_deriv_Ioi H.smooth_y).continuousOn.mono ?_
        intro σ hσ
        exact lt_of_lt_of_le hs0 (by simpa [min_eq_left hs1.le] using hσ.1)
      refine (hcont.intervalIntegrable).1.congr_fun (fun σ _ => ?_) measurableSet_Ioc
      simp [Work.OddVolterra.KernelExt.ThetaM, Work.OddVolterra.stateOf]
    · have hmain : IntervalIntegrable (fun σ : ℝ => -deriv (fun u : ℝ =>
          (Work.OddVolterra.KernelExt.G2M n h u σ (x σ) (y σ) (deriv x σ) (deriv y σ)) 0) s)
          volume s 1 := (hrow 0).neg
      refine hmain.1.congr_fun (fun σ _ => ?_) measurableSet_Ioc
      simp [Work.OddVolterra.KernelExt.ThetaM, Work.OddVolterra.stateOf]
    · have hmain : IntervalIntegrable (fun σ : ℝ => -deriv (fun u : ℝ =>
          (Work.OddVolterra.KernelExt.G2M n h u σ (x σ) (y σ) (deriv x σ) (deriv y σ)) 1) s)
          volume s 1 := (hrow 1).neg
      refine hmain.1.congr_fun (fun σ _ => ?_) measurableSet_Ioc
      simp [Work.OddVolterra.KernelExt.ThetaM, Work.OddVolterra.stateOf]
  -- `G2` and `G2M` agree eventually in the `u`-slot at `u = s`
  have hG2eq : ∀ (σ : ℝ) (i : Fin 2), σ ∈ Set.Ioo s 1 →
      (fun u : ℝ => (Work.OddVolterra.G2 n h u σ (x σ) (y σ) (deriv x σ) (deriv y σ)) i)
        =ᶠ[𝓝 s] (fun u : ℝ =>
          (Work.OddVolterra.KernelExt.G2M n h u σ (x σ) (y σ) (deriv x σ) (deriv y σ)) i) := by
    intro σ i hσ
    filter_upwards [isOpen_Ioo.mem_nhds
      (show s ∈ Set.Ioo (s / 2) σ from ⟨by linarith, hσ.1⟩)] with u hu
    simp only [Work.OddVolterra.G2, Work.OddVolterra.KernelExt.G2M]
    refine intervalIntegral.integral_congr (fun τ hτ => ?_)
    have hτ0 : (0:ℝ) ≤ τ := by simpa using hτ.1
    have hτ1 : τ ≤ 1 := by simpa using hτ.2
    have hv : u + τ * (σ - u) ∈ Set.Icc (s / 2) 1 := by
      constructor
      · nlinarith [hu.1, hτ0, hτ1, hσ.1]
      · nlinarith [hu.2, hτ0, hτ1, hσ.2]
    have hσI : σ ∈ Set.Icc (s / 2) 1 := ⟨by linarith [hσ.1], hσ.2.le⟩
    have hR1 : 0 < (y σ + Work.OddVolterra.hquot h (u + τ * (σ - u)) σ) *
        (Work.OddVolterra.line h σ (y σ) + Work.OddVolterra.line h (u + τ * (σ - u)) (y σ)) :=
      Real.sqrt_pos.mp (hposy (u + τ * (σ - u)) σ hv hσI)
    have hR2 : 0 < (-(x σ) + Work.OddVolterra.hquot h (u + τ * (σ - u)) σ) *
        (Work.OddVolterra.line h σ (-(x σ))
          + Work.OddVolterra.line h (u + τ * (σ - u)) (-(x σ))) :=
      Real.sqrt_pos.mp (hposx (u + τ * (σ - u)) σ hv hσI)
    have hK := Work.OddVolterra.KernelExt.KvecM_eq_Kvec (s := u + τ * (σ - u)) (σ := σ)
      n hn hh (by nlinarith [hu.2, hτ0, hτ1]) (x σ) (y σ) (deriv x σ) (deriv y σ) hR1 hR2
    rw [hK]
  -- `Θ` and `ΘM` agree on the open interval
  have heq : Set.EqOn (fun σ : ℝ =>
      Work.OddVolterra.Theta n h s σ (Work.OddVolterra.stateOf x y σ))
      (fun σ : ℝ => Work.OddVolterra.KernelExt.ThetaM n h s σ (Work.OddVolterra.stateOf x y σ))
      (Set.Ioo s 1) := by
    intro σ hσ
    show Work.OddVolterra.Theta n h s σ (Work.OddVolterra.stateOf x y σ)
      = Work.OddVolterra.KernelExt.ThetaM n h s σ (Work.OddVolterra.stateOf x y σ)
    funext i
    fin_cases i
    · simp [Work.OddVolterra.Theta, Work.OddVolterra.KernelExt.ThetaM,
        Work.OddVolterra.stateOf]
    · simp [Work.OddVolterra.Theta, Work.OddVolterra.KernelExt.ThetaM,
        Work.OddVolterra.stateOf]
    · show (Work.OddVolterra.Theta n h s σ (Work.OddVolterra.stateOf x y σ)) 2
        = (Work.OddVolterra.KernelExt.ThetaM n h s σ (Work.OddVolterra.stateOf x y σ)) 2
      have h1 : (Work.OddVolterra.Theta n h s σ (Work.OddVolterra.stateOf x y σ)) 2
          = -(deriv (fun u : ℝ => (Work.OddVolterra.G2 n h u σ (x σ) (y σ)
              (deriv x σ) (deriv y σ)) 0) s) := by
        simp [Work.OddVolterra.Theta, Work.OddVolterra.stateOf]
      have h2 : (Work.OddVolterra.KernelExt.ThetaM n h s σ
            (Work.OddVolterra.stateOf x y σ)) 2
          = -(deriv (fun u : ℝ => (Work.OddVolterra.KernelExt.G2M n h u σ (x σ) (y σ)
              (deriv x σ) (deriv y σ)) 0) s) := by
        simp [Work.OddVolterra.KernelExt.ThetaM, Work.OddVolterra.stateOf]
      rw [h1, h2]
      congr 1
      exact Filter.EventuallyEq.deriv_eq (hG2eq σ 0 hσ)
    · show (Work.OddVolterra.Theta n h s σ (Work.OddVolterra.stateOf x y σ)) 3
        = (Work.OddVolterra.KernelExt.ThetaM n h s σ (Work.OddVolterra.stateOf x y σ)) 3
      have h1 : (Work.OddVolterra.Theta n h s σ (Work.OddVolterra.stateOf x y σ)) 3
          = -(deriv (fun u : ℝ => (Work.OddVolterra.G2 n h u σ (x σ) (y σ)
              (deriv x σ) (deriv y σ)) 1) s) := by
        simp [Work.OddVolterra.Theta, Work.OddVolterra.stateOf]
      have h2 : (Work.OddVolterra.KernelExt.ThetaM n h s σ
            (Work.OddVolterra.stateOf x y σ)) 3
          = -(deriv (fun u : ℝ => (Work.OddVolterra.KernelExt.G2M n h u σ (x σ) (y σ)
              (deriv x σ) (deriv y σ)) 1) s) := by
        simp [Work.OddVolterra.KernelExt.ThetaM, Work.OddVolterra.stateOf]
      rw [h1, h2]
      congr 1
      exact Filter.EventuallyEq.deriv_eq (hG2eq σ 1 hσ)
  refine hintM.congr_uIoo ?_
  rw [Set.uIoo_of_le hs1.le]
  exact heq.symm

end

end Work.OddVolterra.Existence
