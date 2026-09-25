import Mathlib
import Submission.Commons.Analysis.Complex.hadamard_three_lines
import Submission.Commons.Analysis.CalderonZygmund.cz_shift
import Submission.Commons.Analysis.Fourier.fourier_eq_zero_of_not_integrable
import Submission.Commons.Analysis.Real.rpow_mul_abs_log_bounded
import Submission.Commons.Analysis.Fourier.boundary_layer_l2
import Submission.Commons.MeasureTheory.Function.eLpNorm_eq_iSup_lintegral_mul_sigmaFinite

open MeasureTheory FourierTransform
open scoped FourierTransform RealInnerProductSpace ENNReal Topology

set_option maxHeartbeats 2000000

namespace Commons.Analysis.Fourier

/-!
# Hausdorff–Young inequality on `ℝ`

For `1 < p ≤ 2` and every `f : ℝ → ℂ`,
`‖𝓕 f‖_{p/(p-1)} ≤ ‖f‖_p`, where `𝓕` is the Euclidean Fourier transform.

The proof here is the classical interpolation argument (Riesz–Thorin / Stein): one interpolates
the trivial `L¹ → L^∞` bound against Plancherel `L² → L²` along the analytic amplitude family
`u_z = |u|^{p(1-z/2)} · (u/|u|)`, using Hadamard's three-lines theorem
(`Commons.Analysis.Complex.hadamard_three_lines`).
-/

/-- The amplitude family used in the interpolation proof.  For real `z` this is
`|u|^{p(1-z/2)} · (u/|u|)` (with value `0` where `u = 0`); in particular at `z = 2(p-1)/p` it is
`u` itself, at `z = 0` its modulus is `|u|^p` and at `z = 1` its modulus is `|u|^{p/2}`. -/
noncomputable def hyFam (p : ℝ) (u : ℝ → ℂ) (z : ℂ) (x : ℝ) : ℂ :=
  (((‖u x‖ : ℝ) ^ (p - 1) : ℝ) : ℂ) * Complex.exp (-(p / 2) * (Real.log ‖u x‖ : ℂ) * z) * u x

lemma hyFam_norm (p : ℝ) (hp : 1 < p) (u : ℝ → ℂ) {z : ℂ} (hz : z.re < 2) (x : ℝ) :
    ‖hyFam p u z x‖ = ‖u x‖ ^ (p * (1 - z.re / 2)) := by
  have hnp : (0:ℝ) < p - 1 := by linarith
  have hz1 : (0:ℝ) < 1 - z.re / 2 := by linarith
  have hexp_re : (-(p / 2) * (Real.log ‖u x‖ : ℂ) * z).re = -(p / 2) * Real.log ‖u x‖ * z.re := by
    simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  rw [hyFam, norm_mul, norm_mul, Complex.norm_exp, hexp_re, Complex.norm_real,
    Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
  rcases eq_or_lt_of_le (norm_nonneg (u x)) with h0 | hpos
  · rw [← h0, Real.zero_rpow (ne_of_gt hnp), zero_mul, zero_mul,
      Real.zero_rpow (ne_of_gt (mul_pos (by linarith) hz1))]
  · have h1 : Real.exp (-(p / 2) * Real.log ‖u x‖ * z.re) = ‖u x‖ ^ (-(p / 2) * z.re) := by
      rw [show -(p / 2) * Real.log ‖u x‖ * z.re = Real.log ‖u x‖ * (-(p / 2) * z.re) by ring]
      rw [← Real.rpow_def_of_pos hpos]
    rw [h1, ← Real.rpow_add hpos (p - 1) (-(p / 2) * z.re),
      ← Real.rpow_add_one (ne_of_gt hpos)]
    congr 1
    ring

/-- At the interpolation parameter `θ = 2(p-1)/p` the family returns the original function. -/
lemma hyFam_theta (p : ℝ) (hp : 1 < p) (u : ℝ → ℂ) (x : ℝ) :
    hyFam p u ((2 * (p - 1) / p : ℝ) : ℂ) x = u x := by
  have hnp : (0:ℝ) < p - 1 := by linarith
  have hp0 : (0:ℝ) < p := by linarith
  have hc : -(p / 2) * (Real.log ‖u x‖ : ℂ) * ((2 * (p - 1) / p : ℝ) : ℂ)
      = ((-(p / 2) * Real.log ‖u x‖ * (2 * (p - 1) / p) : ℝ) : ℂ) := by
    push_cast; ring
  rcases eq_or_lt_of_le (norm_nonneg (u x)) with h0 | hpos
  · have hu0 : u x = 0 := norm_eq_zero.mp h0.symm
    rw [hyFam, ← h0, Real.zero_rpow (ne_of_gt hnp), Complex.ofReal_zero, zero_mul,
      zero_mul, hu0]
  · have h1 : Real.exp (-(p / 2) * Real.log ‖u x‖ * (2 * (p - 1) / p)) = ‖u x‖ ^ (-(p - 1)) := by
      rw [show -(p / 2) * Real.log ‖u x‖ * (2 * (p - 1) / p)
            = Real.log ‖u x‖ * (-(p - 1)) by field_simp]
      rw [← Real.rpow_def_of_pos hpos]
    rw [hyFam, hc, ← Complex.ofReal_exp, h1, ← Complex.ofReal_mul,
      ← Real.rpow_add hpos (p - 1) (-(p - 1)), show p - 1 + -(p - 1) = 0 by ring,
      Real.rpow_zero, Complex.ofReal_one, one_mul]

/-- Function-level form of `hyFam_theta`. -/
lemma hyFam_theta_fun (p : ℝ) (hp : 1 < p) (u : ℝ → ℂ) :
    hyFam p u ((2 * (p - 1) / p : ℝ) : ℂ) = u :=
  funext fun x => hyFam_theta p hp u x

lemma hyFam_measurable (p : ℝ) (hp1 : 1 ≤ p) (u : ℝ → ℂ) (z : ℂ) (hu : Measurable u) :
    Measurable (hyFam p u z) := by
  have h1 : Measurable (fun x : ℝ => (((‖u x‖ : ℝ) ^ (p - 1) : ℝ) : ℂ)) :=
    Complex.measurable_ofReal.comp
      ((Real.continuous_rpow_const (by linarith : (0:ℝ) ≤ p - 1)).measurable.comp hu.norm)
  have hlog : Measurable (fun x : ℝ => (Real.log ‖u x‖ : ℂ)) :=
    Complex.measurable_ofReal.comp (Real.measurable_log.comp hu.norm)
  have h2 : Measurable (fun x : ℝ => Complex.exp (-(p / 2) * (Real.log ‖u x‖ : ℂ) * z)) :=
    Complex.measurable_exp.comp ((measurable_const.mul hlog).mul measurable_const)
  exact (h1.mul h2).mul hu

lemma hyFam_hasDerivAt (p : ℝ) (u : ℝ → ℂ) (z : ℂ) (x : ℝ) :
    HasDerivAt (fun w => hyFam p u w x)
      (hyFam p u z x * (-(p / 2) * (Real.log ‖u x‖ : ℂ))) z := by
  have h2 : HasDerivAt
      (fun w : ℂ => Complex.exp ((-(p / 2) * (Real.log ‖u x‖ : ℂ)) * w))
      (Complex.exp ((-(p / 2) * (Real.log ‖u x‖ : ℂ)) * z)
        * (-(p / 2) * (Real.log ‖u x‖ : ℂ))) z := by
    have h1 : HasDerivAt (fun w : ℂ => (-(p / 2) * (Real.log ‖u x‖ : ℂ)) * w)
        (-(p / 2) * (Real.log ‖u x‖ : ℂ)) z := by
      simpa using (hasDerivAt_id z).const_mul (-(p / 2) * (Real.log ‖u x‖ : ℂ))
    simpa using h1.cexp
  have h3 := h2.const_mul ((((‖u x‖ : ℝ) ^ (p - 1) : ℝ) : ℂ) * u x)
  simpa only [hyFam, mul_assoc, mul_comm, mul_left_comm] using h3

/-- A "nice" function on `ℝ`: measurable, bounded and compactly supported. -/
structure Nice (u : ℝ → ℂ) : Prop where
  meas : Measurable u
  bound : ∃ M : ℝ, 0 < M ∧ ∀ x, ‖u x‖ ≤ M
  supp : ∃ R : ℝ, 0 < R ∧ ∀ x, R ≤ |x| → u x = 0

namespace Nice

lemma aestronglyMeasurable {u : ℝ → ℂ} (hu : Nice u) : AEStronglyMeasurable u volume :=
  hu.meas.aestronglyMeasurable

end Nice

/-- `hyFam p u z` is integrable when `u` is nice and `z` stays in the strip `[-2, 3/2]`. -/
lemma hyFam_integrable {u : ℝ → ℂ} (hu : Nice u) (p : ℝ) (hp : 1 < p) {z : ℂ}
    (hz0 : -2 ≤ z.re) (hz1 : z.re ≤ 3 / 2) : Integrable (hyFam p u z) volume := by
  obtain ⟨M, hM, hMb⟩ := hu.bound
  obtain ⟨R, hR, hRs⟩ := hu.supp
  have hCnn : (0:ℝ) ≤ (max 1 M) ^ (2 * p) := Real.rpow_nonneg (le_trans zero_le_one (le_max_left 1 M)) _
  refine Integrable.mono' (g := fun x => (max 1 M) ^ (2 * p) *
      Set.indicator (Set.Icc (-R) R) (fun _ => (1:ℝ)) x) ?_ ?_ ?_
  · have hs : volume (Set.Icc (-R) R) ≠ ∞ := by
      rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
    have h1 : Integrable (Set.indicator (Set.Icc (-R) R) (fun _ : ℝ => (1:ℝ))) volume :=
      (integrableOn_const hs).integrable_indicator measurableSet_Icc
    exact h1.const_mul _
  · exact (hyFam_measurable p (le_of_lt hp) u z hu.meas).aestronglyMeasurable
  · filter_upwards with x
    rcases lt_or_ge |x| R with hx | hx
    · have hxmem : x ∈ Set.Icc (-R) R := by
        rw [Set.mem_Icc]
        rw [abs_lt] at hx
        exact ⟨hx.1.le, hx.2.le⟩
      have ha_lo : 0 < p * (1 - z.re / 2) := by
        have : 0 < 1 - z.re / 2 := by linarith
        positivity
      have ha_hi : p * (1 - z.re / 2) ≤ 2 * p := by
        have : 1 - z.re / 2 ≤ 2 := by linarith
        nlinarith [hp]
      have hmax : (1:ℝ) ≤ max 1 M := le_max_left _ _
      have hMmax : M ≤ max 1 M := le_max_right _ _
      rw [hyFam_norm p hp u (by linarith : z.re < 2) x, Set.indicator_of_mem hxmem, mul_one]
      rcases lt_or_ge 1 ‖u x‖ with h | h
      · calc ‖u x‖ ^ (p * (1 - z.re / 2)) ≤ M ^ (p * (1 - z.re / 2)) :=
              Real.rpow_le_rpow (norm_nonneg _) (hMb x) (le_of_lt ha_lo)
          _ ≤ (max 1 M) ^ (p * (1 - z.re / 2)) :=
              Real.rpow_le_rpow (le_trans (norm_nonneg _) (hMb x)) hMmax (le_of_lt ha_lo)
          _ ≤ (max 1 M) ^ (2 * p) := Real.rpow_le_rpow_of_exponent_le hmax ha_hi
      · calc ‖u x‖ ^ (p * (1 - z.re / 2)) ≤ 1 ^ (p * (1 - z.re / 2)) :=
              Real.rpow_le_rpow (norm_nonneg _) h (le_of_lt ha_lo)
          _ = 1 := Real.one_rpow _
          _ ≤ (max 1 M) ^ (2 * p) := Real.one_le_rpow hmax (by positivity)
    · have hx0 : u x = 0 := hRs x hx
      rw [hyFam, hx0, mul_zero, norm_zero]
      exact mul_nonneg hCnn (Set.indicator_nonneg (fun _ _ => zero_le_one) x)


/-! ### The analytic function used in the interpolation -/

/-- The kernel `e^{-2πi x y}` as a complex number. -/
noncomputable def hyK (x y : ℝ) : ℂ := Complex.exp (-(2 * Real.pi) * Complex.I * ((x * y : ℝ) : ℂ))

lemma continuous_hyK : Continuous (fun q : ℝ × ℝ => hyK q.1 q.2) := by
  unfold hyK
  exact Complex.continuous_exp.comp (by fun_prop)

lemma norm_hyK (x y : ℝ) : ‖hyK x y‖ = 1 := by
  rw [hyK, Complex.norm_exp]
  simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]

/-- The analytic function whose three-lines interpolation yields Hausdorff–Young: for real `z` it
is `∫∫ |f_x|^{p(1-z/2)}(f_x/|f_x|)\, |g_y|^{p(1-z/2)}(g_y/|g_y|)\, e^{-2πi x y}`. -/
noncomputable def hyPhi (p : ℝ) (f g : ℝ → ℂ) (z : ℂ) : ℂ :=
  ∫ q : ℝ × ℝ, hyFam p f z q.1 * hyFam p g z q.2 * hyK q.1 q.2 ∂(volume.prod volume)

/-- The `z`-derivative of the integrand defining `hyPhi`. -/
noncomputable def hyPhi' (p : ℝ) (f g : ℝ → ℂ) (z : ℂ) (q : ℝ × ℝ) : ℂ :=
  hyFam p f z q.1 * hyFam p g z q.2 * hyK q.1 q.2 *
    (-(p / 2) * (Real.log ‖f q.1‖ : ℂ) + (-(p / 2) * (Real.log ‖g q.2‖ : ℂ)))

lemma hyPhi_integrand_measurable {p : ℝ} (hp1 : 1 ≤ p) {f g : ℝ → ℂ} (hf : Measurable f)
    (hg : Measurable g) (z : ℂ) :
    AEStronglyMeasurable (fun q : ℝ × ℝ => hyFam p f z q.1 * hyFam p g z q.2 * hyK q.1 q.2)
      (volume.prod volume) :=
  (((hyFam_measurable p hp1 f z hf).comp measurable_fst).mul
    ((hyFam_measurable p hp1 g z hg).comp measurable_snd)).mul
      continuous_hyK.measurable |>.aestronglyMeasurable

lemma hyPhi'_measurable {p : ℝ} (hp1 : 1 ≤ p) {f g : ℝ → ℂ} (hf : Measurable f)
    (hg : Measurable g) (z : ℂ) :
    AEStronglyMeasurable (hyPhi' p f g z) (volume.prod volume) := by
  have hc : Measurable (fun q : ℝ × ℝ =>
      (-(p / 2) * (Real.log ‖f q.1‖ : ℂ) + (-(p / 2) * (Real.log ‖g q.2‖ : ℂ)))) := by
    refine Measurable.add ?_ ?_
    · exact measurable_const.mul (Complex.measurable_ofReal.comp
        (Real.measurable_log.comp (hf.norm.comp measurable_fst)))
    · exact measurable_const.mul (Complex.measurable_ofReal.comp
        (Real.measurable_log.comp (hg.norm.comp measurable_snd)))
  exact ((((hyFam_measurable p hp1 f z hf).comp measurable_fst).mul
    ((hyFam_measurable p hp1 g z hg).comp measurable_snd)).mul
      continuous_hyK.measurable).mul hc |>.aestronglyMeasurable

/-- Integrability of the integrand of `hyPhi` in the strip. -/
lemma hyPhi_integrand_integrable {p : ℝ} (hp : 1 < p) {f g : ℝ → ℂ} (hf : Nice f) (hg : Nice g)
    {z : ℂ} (hz0 : -2 ≤ z.re) (hz1 : z.re ≤ 3 / 2) :
    Integrable (fun q : ℝ × ℝ => hyFam p f z q.1 * hyFam p g z q.2 * hyK q.1 q.2)
      (volume.prod volume) := by
  have hfi : Integrable (fun x => ‖hyFam p f z x‖) volume := (hyFam_integrable hf p hp hz0 hz1).norm
  have hgi : Integrable (fun y => ‖hyFam p g z y‖) volume := (hyFam_integrable hg p hp hz0 hz1).norm
  have hprod := hfi.mul_prod hgi
  refine Integrable.mono' hprod (hyPhi_integrand_measurable (le_of_lt hp) hf.meas hg.meas z) ?_
  filter_upwards with q
  rw [norm_mul, norm_mul, norm_hyK, mul_one]

/-- For `z` in the closed strip the family has a uniform bound. -/
lemma hyFam_bound {p : ℝ} (hp : 1 < p) {u : ℝ → ℂ} (hu : Nice u) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (z : ℂ) (x : ℝ), z.re ∈ Set.Icc (-2) (3 / 2) →
      ‖hyFam p u z x‖ ≤ A := by
  obtain ⟨M, hM, hMb⟩ := hu.bound
  refine ⟨(max 1 M) ^ (2 * p), Real.rpow_nonneg (le_trans zero_le_one (le_max_left 1 M)) _, ?_⟩
  intro z x hz
  rw [hyFam_norm p hp u (by linarith [hz.2] : z.re < 2) x]
  have ha_lo : 0 < p * (1 - z.re / 2) := by
    have : 0 < 1 - z.re / 2 := by linarith [hz.2]
    positivity
  have ha_hi : p * (1 - z.re / 2) ≤ 2 * p := by
    have : 1 - z.re / 2 ≤ 2 := by linarith [hz.1]
    nlinarith [hp]
  have hmax : (1:ℝ) ≤ max 1 M := le_max_left _ _
  have hMmax : M ≤ max 1 M := le_max_right _ _
  rcases lt_or_ge 1 ‖u x‖ with h | h
  · calc ‖u x‖ ^ (p * (1 - z.re / 2)) ≤ M ^ (p * (1 - z.re / 2)) :=
          Real.rpow_le_rpow (norm_nonneg _) (hMb x) (le_of_lt ha_lo)
      _ ≤ (max 1 M) ^ (p * (1 - z.re / 2)) :=
          Real.rpow_le_rpow (le_trans (norm_nonneg _) (hMb x)) hMmax (le_of_lt ha_lo)
      _ ≤ (max 1 M) ^ (2 * p) := Real.rpow_le_rpow_of_exponent_le hmax ha_hi
  · calc ‖u x‖ ^ (p * (1 - z.re / 2)) ≤ 1 ^ (p * (1 - z.re / 2)) :=
          Real.rpow_le_rpow (norm_nonneg _) h (le_of_lt ha_lo)
      _ = 1 := Real.one_rpow _
      _ ≤ (max 1 M) ^ (2 * p) := Real.one_le_rpow hmax (by positivity)

/-- For `z` in the closed strip, the `z`-derivative of the family has a uniform bound. -/
lemma hyFam_deriv_bound {p : ℝ} (hp : 1 < p) {u : ℝ → ℂ} (hu : Nice u) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (z : ℂ) (x : ℝ), z.re ∈ Set.Icc (-2) (3 / 2) →
      ‖hyFam p u z x‖ * ((p / 2) * |Real.log ‖u x‖|) ≤ C := by
  obtain ⟨M, hM, hMb⟩ := hu.bound
  obtain ⟨K1, hK1nn, hK1⟩ :=
    Commons.Analysis.Real.rpow_mul_abs_log_bounded (a := p / 4) (M := 1) (by positivity) one_pos
  obtain ⟨K2, hK2nn, hK2⟩ :=
    Commons.Analysis.Real.rpow_mul_abs_log_bounded (a := 2 * p) (M := max 1 M)
      (by positivity) (lt_of_lt_of_le one_pos (le_max_left 1 M))
  refine ⟨(p / 2) * (K1 + K2), by positivity, ?_⟩
  intro z x hz
  rw [hyFam_norm p hp u (by linarith [hz.2] : z.re < 2) x]
  have ha_lo : 0 < p * (1 - z.re / 2) := by
    have : 0 < 1 - z.re / 2 := by linarith [hz.2]
    positivity
  have ha_hi : p * (1 - z.re / 2) ≤ 2 * p := by
    have : 1 - z.re / 2 ≤ 2 := by linarith [hz.1]
    nlinarith [hp]
  have ht0 : 0 ≤ ‖u x‖ := norm_nonneg _
  have hle : ‖u x‖ ≤ max 1 M := le_trans (hMb x) (le_max_right 1 M)
  have hLnn : (0:ℝ) ≤ |Real.log ‖u x‖| := abs_nonneg _
  have hkey : ‖u x‖ ^ (p * (1 - z.re / 2)) * |Real.log ‖u x‖| ≤ K1 + K2 := by
    rcases lt_or_ge 1 ‖u x‖ with h1 | h1
    · have hb := hK2 ‖u x‖ (lt_trans one_pos h1) hle
      have h3 : ‖u x‖ ^ (p * (1 - z.re / 2)) ≤ ‖u x‖ ^ (2 * p) :=
        Real.rpow_le_rpow_of_exponent_le (le_of_lt h1) ha_hi
      have := mul_le_mul_of_nonneg_right h3 hLnn
      linarith
    · have ha_ge : p / 4 ≤ p * (1 - z.re / 2) := by
        have : (1:ℝ) / 4 ≤ 1 - z.re / 2 := by linarith [hz.2]
        nlinarith [hp, this]
      by_cases h0 : ‖u x‖ = 0
      · rw [h0, Real.zero_rpow (ne_of_gt ha_lo), Real.log_zero, abs_zero, mul_zero]
        linarith [hK1nn, hK2nn]
      · have htpos : 0 < ‖u x‖ := lt_of_le_of_ne ht0 (Ne.symm h0)
        have hb := hK1 ‖u x‖ htpos h1
        have h3 : ‖u x‖ ^ (p * (1 - z.re / 2)) ≤ ‖u x‖ ^ (p / 4) :=
          Real.rpow_le_rpow_of_exponent_ge' ht0 h1 (by positivity) ha_ge
        have := mul_le_mul_of_nonneg_right h3 hLnn
        linarith
  have hrw : ‖u x‖ ^ (p * (1 - z.re / 2)) * (p / 2 * |Real.log ‖u x‖|)
      = (p / 2) * (‖u x‖ ^ (p * (1 - z.re / 2)) * |Real.log ‖u x‖|) := by ring
  rw [hrw]
  nlinarith [hkey, hp]


lemma hasDerivAt_hyPhi_integrand (p : ℝ) (f g : ℝ → ℂ) (z : ℂ) (q : ℝ × ℝ) :
    HasDerivAt (fun w => hyFam p f w q.1 * hyFam p g w q.2 * hyK q.1 q.2)
      (hyPhi' p f g z q) z := by
  have hA := hyFam_hasDerivAt p f z q.1
  have hB := hyFam_hasDerivAt p g z q.2
  have h := (hA.mul hB).mul_const (hyK q.1 q.2)
  have h2 : HasDerivAt (fun y => ((fun w => hyFam p f w q.1) * fun w => hyFam p g w q.2) y
      * hyK q.1 q.2) (hyPhi' p f g z q) z :=
    h.congr_deriv (by rw [hyPhi']; ring)
  simpa only [Pi.mul_apply] using h2

/-- A uniform dominating function for the `z`-derivative of the integrand. -/
lemma hyPhi'_le_bound {p : ℝ} (hp : 1 < p) {f g : ℝ → ℂ} (hf : Nice f) (hg : Nice g) :
    ∃ bound : ℝ × ℝ → ℝ, Integrable bound (volume.prod volume) ∧
      ∀ (z : ℂ) (q : ℝ × ℝ), z.re ∈ Set.Icc (-2) (3 / 2) → ‖hyPhi' p f g z q‖ ≤ bound q := by
  obtain ⟨Rf, hRf, hRfs⟩ := hf.supp
  obtain ⟨Rg, hRg, hRgs⟩ := hg.supp
  obtain ⟨Af, hAf, hAfb⟩ := hyFam_bound hp hf
  obtain ⟨Cf, hCf, hCfb⟩ := hyFam_deriv_bound hp hf
  obtain ⟨Ag, hAg, hAgb⟩ := hyFam_bound hp hg
  obtain ⟨Cg, hCg, hCgb⟩ := hyFam_deriv_bound hp hg
  have hSmeas : MeasurableSet (Set.Icc (-Rf) Rf ×ˢ Set.Icc (-Rg) Rg) :=
    measurableSet_Icc.prod measurableSet_Icc
  have hSfin : (volume.prod volume) (Set.Icc (-Rf) Rf ×ˢ Set.Icc (-Rg) Rg) ≠ ∞ := by
    rw [Measure.prod_prod, Real.volume_Icc, Real.volume_Icc]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  refine ⟨fun q => (Cf * Ag + Af * Cg) *
      Set.indicator (Set.Icc (-Rf) Rf ×ˢ Set.Icc (-Rg) Rg) (fun _ => (1:ℝ)) q, ?_, ?_⟩
  · have h1 : Integrable (Set.indicator (Set.Icc (-Rf) Rf ×ˢ Set.Icc (-Rg) Rg)
        (fun _ : ℝ × ℝ => (1:ℝ))) (volume.prod volume) :=
      (integrableOn_const hSfin).integrable_indicator hSmeas
    exact h1.const_mul _
  · intro z q hz
    by_cases hq : q ∈ Set.Icc (-Rf) Rf ×ˢ Set.Icc (-Rg) Rg
    · show ‖hyPhi' p f g z q‖ ≤ (Cf * Ag + Af * Cg) *
        Set.indicator (Set.Icc (-Rf) Rf ×ˢ Set.Icc (-Rg) Rg) (fun _ => (1:ℝ)) q
      rw [Set.indicator_of_mem hq, mul_one]
      have hp2 : (0:ℝ) ≤ p / 2 := by linarith
      have hcast : (-(p / 2) : ℂ) = ((-(p / 2) : ℝ) : ℂ) := by push_cast; ring
      have hconst : ‖((-(p / 2) : ℝ) : ℂ)‖ = p / 2 := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_nonneg hp2]
      have hc1 : ‖(-(p / 2) * (Real.log ‖f q.1‖ : ℂ))‖ = (p / 2) * |Real.log ‖f q.1‖| := by
        rw [hcast, norm_mul, hconst, Complex.norm_real, Real.norm_eq_abs]
      have hc2 : ‖(-(p / 2) * (Real.log ‖g q.2‖ : ℂ))‖ = (p / 2) * |Real.log ‖g q.2‖| := by
        rw [hcast, norm_mul, hconst, Complex.norm_real, Real.norm_eq_abs]
      have hcd : ‖(-(p / 2) * (Real.log ‖f q.1‖ : ℂ)) + (-(p / 2) * (Real.log ‖g q.2‖ : ℂ))‖
          ≤ (p / 2) * |Real.log ‖f q.1‖| + (p / 2) * |Real.log ‖g q.2‖| := by
        calc ‖(-(p / 2) * (Real.log ‖f q.1‖ : ℂ)) + (-(p / 2) * (Real.log ‖g q.2‖ : ℂ))‖
            ≤ ‖(-(p / 2) * (Real.log ‖f q.1‖ : ℂ))‖ + ‖(-(p / 2) * (Real.log ‖g q.2‖ : ℂ))‖ :=
              norm_add_le _ _
          _ = (p / 2) * |Real.log ‖f q.1‖| + (p / 2) * |Real.log ‖g q.2‖| := by rw [hc1, hc2]
      have hAnnn : 0 ≤ ‖hyFam p f z q.1‖ := norm_nonneg _
      have hBnnn : 0 ≤ ‖hyFam p g z q.2‖ := norm_nonneg _
      have hL1 : 0 ≤ (p / 2) * |Real.log ‖f q.1‖| := by positivity
      have hL2 : 0 ≤ (p / 2) * |Real.log ‖g q.2‖| := by positivity
      calc ‖hyPhi' p f g z q‖
          = ‖hyFam p f z q.1‖ * ‖hyFam p g z q.2‖ *
              ‖(-(p / 2) * (Real.log ‖f q.1‖ : ℂ)) + (-(p / 2) * (Real.log ‖g q.2‖ : ℂ))‖ := by
            simp only [hyPhi', norm_mul, norm_hyK, mul_one]
        _ ≤ ‖hyFam p f z q.1‖ * ‖hyFam p g z q.2‖ *
              ((p / 2) * |Real.log ‖f q.1‖| + (p / 2) * |Real.log ‖g q.2‖|) := by
            refine mul_le_mul_of_nonneg_left hcd (by positivity)
        _ = (‖hyFam p f z q.1‖ * ((p / 2) * |Real.log ‖f q.1‖|)) * ‖hyFam p g z q.2‖
              + ‖hyFam p f z q.1‖ * (‖hyFam p g z q.2‖ * ((p / 2) * |Real.log ‖g q.2‖|)) := by
            ring
        _ ≤ Cf * Ag + Af * Cg := by
            refine add_le_add ?_ ?_
            · exact mul_le_mul (hCfb z q.1 hz) (hAgb z q.2 hz) hBnnn hCf
            · exact mul_le_mul (hAfb z q.1 hz) (hCgb z q.2 hz) (mul_nonneg hBnnn hL2) hAf
    · show ‖hyPhi' p f g z q‖ ≤ (Cf * Ag + Af * Cg) *
        Set.indicator (Set.Icc (-Rf) Rf ×ˢ Set.Icc (-Rg) Rg) (fun _ => (1:ℝ)) q
      rw [Set.indicator_of_notMem hq, mul_zero]
      have hzero : hyPhi' p f g z q = 0 := by
        rw [Set.mem_prod, not_and_or] at hq
        rcases hq with hq1 | hq2
        · have h0 : f q.1 = 0 := by
            apply hRfs
            rw [Set.mem_Icc, not_and_or, not_le, not_le] at hq1
            rcases hq1 with h1 | h1
            · rw [abs_of_neg (by linarith)]; linarith
            · rw [abs_of_pos (by linarith)]; linarith
          have hz0 : hyFam p f z q.1 = 0 := by rw [hyFam, h0]; ring
          rw [hyPhi', hz0]; ring
        · have h0 : g q.2 = 0 := by
            apply hRgs
            rw [Set.mem_Icc, not_and_or, not_le, not_le] at hq2
            rcases hq2 with h1 | h1
            · rw [abs_of_neg (by linarith)]; linarith
            · rw [abs_of_pos (by linarith)]; linarith
          have hz0 : hyFam p g z q.2 = 0 := by rw [hyFam, h0]; ring
          rw [hyPhi', hz0]; ring
      rw [hzero, norm_zero]


lemma hyPhi_differentiableOn (p : ℝ) (hp : 1 < p) {f g : ℝ → ℂ} (hf : Nice f) (hg : Nice g) :
    DifferentiableOn ℂ (hyPhi p f g) (Complex.HadamardThreeLines.verticalStrip 0 1) := by
  obtain ⟨bound, hbound_int, hbound⟩ := hyPhi'_le_bound (p := p) hp hf hg
  intro z₀ hz₀
  have hz₀re : 0 < z₀.re ∧ z₀.re < 1 := by
    simpa [Complex.HadamardThreeLines.verticalStrip] using hz₀
  have hball : ∀ z ∈ Metric.ball z₀ (1 / 2), z.re ∈ Set.Icc (-2) (3 / 2) := by
    intro z hz
    rw [Metric.mem_ball, dist_eq_norm] at hz
    have h1 : |z.re - z₀.re| ≤ ‖z - z₀‖ := by
      simpa [Complex.sub_re] using Complex.abs_re_le_norm (z - z₀)
    have h2 := abs_le.mp h1
    constructor <;> linarith [h2.1, h2.2, hz₀re.1, hz₀re.2]
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.prod volume)
    (F := fun (z : ℂ) (q : ℝ × ℝ) => hyFam p f z q.1 * hyFam p g z q.2 * hyK q.1 q.2)
    (F' := fun (z : ℂ) (q : ℝ × ℝ) => hyPhi' p f g z q)
    (x₀ := z₀) (s := Metric.ball z₀ (1 / 2)) (bound := bound)
    (Metric.ball_mem_nhds z₀ (by norm_num))
    (Filter.Eventually.of_forall fun z => hyPhi_integrand_measurable (le_of_lt hp) hf.meas hg.meas z)
    (hyPhi_integrand_integrable hp hf hg (by linarith [hz₀re.1]) (by linarith [hz₀re.2]))
    (hyPhi'_measurable (le_of_lt hp) hf.meas hg.meas z₀)
    (Filter.Eventually.of_forall fun q z hz => hbound z q (hball z hz))
    hbound_int
    (Filter.Eventually.of_forall fun q z _ => hasDerivAt_hyPhi_integrand p f g z q)
  have hd : HasDerivAt (fun z => ∫ q, hyFam p f z q.1 * hyFam p g z q.2 * hyK q.1 q.2
      ∂(volume.prod volume)) (∫ q, hyPhi' p f g z₀ q ∂(volume.prod volume)) z₀ := key.2
  have hd2 : DifferentiableAt ℂ (fun z => ∫ q, hyFam p f z q.1 * hyFam p g z q.2 * hyK q.1 q.2
      ∂(volume.prod volume)) z₀ := hd.differentiableAt
  exact hd2.differentiableWithinAt

lemma hyPhi_continuousOn (p : ℝ) (hp : 1 < p) {f g : ℝ → ℂ} (hf : Nice f) (hg : Nice g) :
    ContinuousOn (hyPhi p f g) (Complex.HadamardThreeLines.verticalStrip 0 1) :=
  (hyPhi_differentiableOn p hp hf hg).continuousOn


lemma hyK_eq (x y : ℝ) : hyK x y = ((Real.fourierChar (-(inner ℝ x y)) : Circle) : ℂ) := by
  rw [hyK, Real.fourierChar_apply, Real.inner_apply]
  congr 1
  push_cast
  ring

/-- Fubini: `hyPhi` as a single integral against the Fourier transform. -/
lemma hyPhi_eq_integral_fourier (p : ℝ) (hp : 1 < p) {f g : ℝ → ℂ} (hf : Nice f) (hg : Nice g)
    {z : ℂ} (hz0 : -2 ≤ z.re) (hz1 : z.re ≤ 3 / 2) :
    hyPhi p f g z = ∫ y, (𝓕 (hyFam p f z)) y * hyFam p g z y ∂volume := by
  have hInt := hyPhi_integrand_integrable hp hf hg hz0 hz1
  rw [hyPhi, integral_prod_symm _ hInt]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  show (∫ x, hyFam p f z x * hyFam p g z y * hyK x y) = 𝓕 (hyFam p f z) y * hyFam p g z y
  rw [show (∫ x, hyFam p f z x * hyFam p g z y * hyK x y) =
      (∫ x, hyFam p f z x * hyK x y) * hyFam p g z y from by
    rw [← integral_mul_const]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)]
  rw [Real.fourier_eq]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only []
  rw [hyK_eq, Circle.smul_def]
  ring


/-- Real-integral form of the `ℒ²` norm as the `toReal` of a lintegral. -/
lemma integral_norm_sq_eq_toReal_lintegral {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℂ} (hf : AEStronglyMeasurable f μ) :
    (∫ x, ‖f x‖ ^ 2 ∂μ) = (∫⁻ x, ‖f x‖ₑ ^ (2:ℝ) ∂μ).toReal := by
  have hmeas : AEStronglyMeasurable (fun x => ‖f x‖ ^ 2) μ := hf.norm.pow 2
  have hnn : ∀ x, ENNReal.ofReal (‖f x‖ ^ 2) = ‖f x‖ₑ ^ (2:ℝ) := fun x => by
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm, ENNReal.rpow_ofNat]
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun x => sq_nonneg _) hmeas]
  congr 1
  exact lintegral_congr_ae (Filter.Eventually.of_forall fun x => hnn x)

/-- Plancherel in real-integral form, for `u ∈ L¹ ∩ L²`. -/
lemma fourier_norm_sq_eq {u : ℝ → ℂ} (h1 : MemLp u 1 volume) (h2 : MemLp u 2 volume) :
    ∫ x, ‖𝓕 u x‖ ^ (2:ℝ) ∂volume = ∫ x, ‖u x‖ ^ (2:ℝ) ∂volume := by
  have huInt : Integrable u volume := memLp_one_iff_integrable.mp h1
  have hEq : eLpNorm (𝓕 u) (ENNReal.ofReal 2) volume = eLpNorm u (ENNReal.ofReal 2) volume :=
    Commons.Analysis.CalderonZygmund.eLpNorm_fourier_eq u huInt h2
  have hlin1 := Commons.Analysis.MeasureTheory.eLpNorm_rpow_toReal
    (μ := volume) (p := ENNReal.ofReal (2:ℝ)) (by simp) ENNReal.ofReal_ne_top (𝓕 u)
    (Commons.Analysis.Fourier.BoundaryLayer.measurable_fourier h1).aestronglyMeasurable
  have hlin2 := Commons.Analysis.MeasureTheory.eLpNorm_rpow_toReal
    (μ := volume) (p := ENNReal.ofReal (2:ℝ)) (by simp) ENNReal.ofReal_ne_top u h2.aestronglyMeasurable
  rw [show (ENNReal.ofReal (2:ℝ)).toReal = 2 by norm_num] at hlin1 hlin2
  have hlin : ∫⁻ x, ‖𝓕 u x‖ₑ ^ (2:ℝ) = ∫⁻ x, ‖u x‖ₑ ^ (2:ℝ) := by
    rw [← hlin1, ← hlin2, hEq]
  simp_rw [Real.rpow_two]
  rw [integral_norm_sq_eq_toReal_lintegral
        (Commons.Analysis.Fourier.BoundaryLayer.measurable_fourier h1).aestronglyMeasurable,
      integral_norm_sq_eq_toReal_lintegral h2.aestronglyMeasurable, hlin]


/-- A bounded measurable function with compact support lies in every `L^r`, `r > 0`. -/
lemma memLp_of_bound_supp {u : ℝ → ℂ} {r M R : ℝ} (hr : 0 < r) (hM : 1 ≤ M) (hR : 0 < R)
    (hu : AEStronglyMeasurable u volume) (hMb : ∀ x, ‖u x‖ ≤ M)
    (hRs : ∀ x, R ≤ |x| → u x = 0) : MemLp u (ENNReal.ofReal r) volume := by
  rw [memLp_iff, eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by positivity) ENNReal.ofReal_ne_top hu,
    ENNReal.toReal_ofReal hr.le]
  have hfin : (∫⁻ x, (Set.Icc (-R) R).indicator (fun _ => ENNReal.ofReal (M ^ r)) x
      ∂volume) < ⊤ := by
    rw [MeasureTheory.lintegral_indicator_const measurableSet_Icc, Real.volume_Icc]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
  refine lt_of_le_of_lt (lintegral_mono fun x => ?_) hfin
  by_cases hx : x ∈ Set.Icc (-R) R
  · rw [Set.indicator_of_mem hx]
    exact (ENNReal.rpow_le_rpow
      (by rw [← ofReal_norm]; exact ENNReal.ofReal_le_ofReal (hMb x)) hr.le).trans_eq
      (ENNReal.ofReal_rpow_of_nonneg (by linarith) hr.le)
  · rw [Set.indicator_of_notMem hx]
    have hx' : R ≤ |x| := by
      rw [Set.mem_Icc, not_and_or, not_le, not_le] at hx
      rcases hx with h | h
      · rw [abs_of_neg (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; linarith
    rw [hRs x hx', enorm_zero, ENNReal.zero_rpow_of_pos hr]

/-- Membership of the interpolation family in `L²` when `z.re = 1`. -/
lemma memLp_hyFam_two {u : ℝ → ℂ} (hu : Nice u) (p : ℝ) (hp : 1 < p) {z : ℂ} (hz : z.re = 1) :
    MemLp (hyFam p u z) (ENNReal.ofReal 2) volume := by
  obtain ⟨M, hM, hMb⟩ := hu.bound
  obtain ⟨R, hR, hRs⟩ := hu.supp
  rw [memLp_iff, eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) ENNReal.ofReal_ne_top
      (hyFam_measurable p (le_of_lt hp) u z hu.meas).aestronglyMeasurable,
    show (ENNReal.ofReal (2:ℝ)).toReal = 2 by norm_num]
  have hmemp : MemLp u (ENNReal.ofReal p) volume :=
    memLp_of_bound_supp (by linarith) (le_max_left 1 M) hR hu.aestronglyMeasurable
      (fun x => le_trans (hMb x) (le_max_right 1 M)) hRs
  have hfin := hmemp.eLpNorm_lt_top
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (ENNReal.ofReal_pos.mpr (by linarith)).ne'
    ENNReal.ofReal_ne_top hmemp.aestronglyMeasurable, ENNReal.toReal_ofReal (by linarith : (0:ℝ) ≤ p)] at hfin
  refine lt_of_eq_of_lt ?_ hfin
  refine lintegral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only []
  nth_rewrite 1 [← ofReal_norm]
  rw [hyFam_norm p hp u (by rw [hz]; norm_num) x, hz, ← ofReal_norm]
  have h1 : p * (1 - (1:ℝ) / 2) = p / 2 := by ring
  rw [h1, ← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by positivity : (0:ℝ) ≤ p / 2),
    ← ENNReal.rpow_mul]
  congr 1
  ring


/-- The boundary bound on the line `re z = 0`: the trivial `L¹ × L¹` estimate. -/
lemma hyPhi_bound_re_zero (p : ℝ) (hp : 1 < p) {f g : ℝ → ℂ} (hf : Nice f) (hg : Nice g) :
    ∀ z : ℂ, z.re = 0 →
      ‖hyPhi p f g z‖ ≤ (∫ x, ‖f x‖ ^ p ∂volume) * (∫ x, ‖g x‖ ^ p ∂volume) := by
  intro z hz
  have hzlt : z.re < 2 := by rw [hz]; norm_num
  calc ‖hyPhi p f g z‖
      ≤ ∫ q : ℝ × ℝ, ‖hyFam p f z q.1 * hyFam p g z q.2 * hyK q.1 q.2‖
          ∂(volume.prod volume) := norm_integral_le_integral_norm _
    _ = ∫ q : ℝ × ℝ, ‖hyFam p f z q.1‖ * ‖hyFam p g z q.2‖ ∂(volume.prod volume) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
        simp only [norm_mul, norm_hyK, mul_one]
    _ = (∫ x, ‖hyFam p f z x‖ ∂volume) * (∫ y, ‖hyFam p g z y‖ ∂volume) :=
        integral_prod_mul (f := fun x => ‖hyFam p f z x‖) (g := fun y => ‖hyFam p g z y‖)
    _ = (∫ x, ‖f x‖ ^ p ∂volume) * (∫ y, ‖g y‖ ^ p ∂volume) := by
        congr 1
        · refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
          simp only []
          rw [hyFam_norm p hp f hzlt x, hz]
          norm_num
        · refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
          simp only []
          rw [hyFam_norm p hp g hzlt x, hz]
          norm_num

/-- The boundary bound on the line `re z = 1`: Plancherel plus Cauchy–Schwarz. -/
lemma hyPhi_bound_re_one (p : ℝ) (hp : 1 < p) (hp2 : p ≤ 2) {f g : ℝ → ℂ}
    (hf : Nice f) (hg : Nice g) :
    ∀ z : ℂ, z.re = 1 →
      ‖hyPhi p f g z‖ ≤ (∫ x, ‖f x‖ ^ p ∂volume) ^ ((1:ℝ) / 2)
        * (∫ x, ‖g x‖ ^ p ∂volume) ^ ((1:ℝ) / 2) := by
  intro z hz
  rw [hyPhi_eq_integral_fourier p hp hf hg (by rw [hz]; norm_num) (by rw [hz]; norm_num)]
  have hzf1 : -2 ≤ z.re := by rw [hz]; norm_num
  have hzf2 : z.re ≤ 3 / 2 := by rw [hz]; norm_num
  have hu1 : MemLp (hyFam p f z) 1 volume :=
    memLp_one_iff_integrable.mpr (hyFam_integrable hf p hp hzf1 hzf2)
  have hu2 : MemLp (hyFam p f z) (ENNReal.ofReal 2) volume := memLp_hyFam_two hf p hp hz
  have hv2 : MemLp (hyFam p g z) (ENNReal.ofReal 2) volume := memLp_hyFam_two hg p hp hz
  have hu2' : MemLp (hyFam p f z) 2 volume := by simpa using hu2
  have hU2 : MemLp (𝓕 (hyFam p f z)) (ENNReal.ofReal 2) volume := by
    have h := Commons.Analysis.Fourier.BoundaryLayer.memLp_fourier hu1 hu2'
    simpa using h
  have hA : ∫ x, ‖𝓕 (hyFam p f z) x‖ ^ (2:ℝ) ∂volume = ∫ x, ‖f x‖ ^ p ∂volume := by
    rw [fourier_norm_sq_eq hu1 hu2']
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only []
    rw [hyFam_norm p hp f (by rw [hz]; norm_num) x, hz]
    have h1 : p * (1 - (1:ℝ) / 2) = p / 2 := by ring
    rw [h1, ← Real.rpow_mul (norm_nonneg _)]
    congr 1
    ring
  have hB : ∫ x, ‖hyFam p g z x‖ ^ (2:ℝ) ∂volume = ∫ x, ‖g x‖ ^ p ∂volume := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only []
    rw [hyFam_norm p hp g (by rw [hz]; norm_num) x, hz]
    have h1 : p * (1 - (1:ℝ) / 2) = p / 2 := by ring
    rw [h1, ← Real.rpow_mul (norm_nonneg _)]
    congr 1
    ring
  have hHolder : ∫ y, ‖𝓕 (hyFam p f z) y‖ * ‖hyFam p g z y‖ ∂volume
      ≤ (∫ y, ‖𝓕 (hyFam p f z) y‖ ^ (2:ℝ) ∂volume) ^ ((1:ℝ) / 2)
        * (∫ y, ‖hyFam p g z y‖ ^ (2:ℝ) ∂volume) ^ ((1:ℝ) / 2) :=
    integral_mul_norm_le_Lp_mul_Lq
      (Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩) hU2 hv2
  calc ‖∫ y, (𝓕 (hyFam p f z)) y * hyFam p g z y‖
      ≤ ∫ y, ‖(𝓕 (hyFam p f z)) y * hyFam p g z y‖ ∂volume := norm_integral_le_integral_norm _
    _ = ∫ y, ‖𝓕 (hyFam p f z) y‖ * ‖hyFam p g z y‖ ∂volume := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
        simp only [norm_mul]
    _ ≤ (∫ y, ‖𝓕 (hyFam p f z) y‖ ^ (2:ℝ) ∂volume) ^ ((1:ℝ) / 2)
          * (∫ y, ‖hyFam p g z y‖ ^ (2:ℝ) ∂volume) ^ ((1:ℝ) / 2) := hHolder
    _ = (∫ x, ‖f x‖ ^ p ∂volume) ^ ((1:ℝ) / 2) * (∫ x, ‖g x‖ ^ p ∂volume) ^ ((1:ℝ) / 2) := by
        rw [hA, hB]


lemma integral_indicator_Icc_const (C R : ℝ) (hR : 0 ≤ R) :
    ∫ x, C * (Set.Icc (-R) R).indicator (fun _ => (1:ℝ)) x ∂volume = C * (2 * R) := by
  rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_indicator measurableSet_Icc,
    MeasureTheory.integral_const, smul_eq_mul, mul_one, measureReal_def,
    Measure.restrict_apply_univ, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]
  ring

/-- Bound of the interpolation family on the closed strip. -/
lemma hyFam_le_of_mem_closedStrip {u : ℝ → ℂ} {p M R : ℝ} (hp : 1 < p) (hM : 1 ≤ M)
    (hR : 0 ≤ R) (hMb : ∀ x, ‖u x‖ ≤ M) (hRs : ∀ x, R ≤ |x| → u x = 0)
    {z : ℂ} (hz0 : 0 ≤ z.re) (hz1 : z.re ≤ 1) (x : ℝ) :
    ‖hyFam p u z x‖ ≤ M ^ p * (Set.Icc (-R) R).indicator (fun _ => (1:ℝ)) x := by
  have hzlt : z.re < 2 := by linarith
  by_cases hx : x ∈ Set.Icc (-R) R
  · rw [Set.indicator_of_mem hx, mul_one, hyFam_norm p hp u hzlt x]
    have h1 : p * (1 - z.re / 2) ≤ p := by
      have : 0 ≤ z.re / 2 := by linarith
      nlinarith [hp]
    have h2 : 0 < p * (1 - z.re / 2) := by
      have : 0 < 1 - z.re / 2 := by linarith
      positivity
    rcases lt_or_ge 1 (‖u x‖) with h | h
    · calc ‖u x‖ ^ (p * (1 - z.re / 2)) ≤ M ^ (p * (1 - z.re / 2)) :=
            Real.rpow_le_rpow (norm_nonneg _) (hMb x) h2.le
        _ ≤ M ^ p := Real.rpow_le_rpow_of_exponent_le hM h1
    · exact (Real.rpow_le_one (norm_nonneg _) h h2.le).trans (Real.one_le_rpow hM (by positivity))
  · rw [Set.indicator_of_notMem hx, mul_zero]
    have hx' : R ≤ |x| := by
      rw [Set.mem_Icc, not_and_or, not_le, not_le] at hx
      rcases hx with h | h
      · rw [abs_of_neg (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; linarith
    have hz0 : hyFam p u z x = 0 := by rw [hyFam, hRs x hx']; ring
    rw [hz0, norm_zero]

/-- `hyPhi` is bounded on the closed strip. -/
lemma hyPhi_bddAbove (p : ℝ) (hp1 : 1 < p) {f g : ℝ → ℂ} (hf : Nice f) (hg : Nice g) :
    BddAbove ((norm ∘ hyPhi p f g) ''
      Complex.HadamardThreeLines.verticalClosedStrip 0 1) := by
  obtain ⟨Mf, hMf, hMfb⟩ := hf.bound
  obtain ⟨Rf, hRf, hRfs⟩ := hf.supp
  obtain ⟨Mg, hMg, hMgb⟩ := hg.bound
  obtain ⟨Rg, hRg, hRgs⟩ := hg.supp
  refine ⟨(max 1 Mf) ^ p * (2 * Rf) * ((max 1 Mg) ^ p * (2 * Rg)), ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  simp only [Complex.HadamardThreeLines.verticalClosedStrip, Set.mem_preimage, Set.mem_Icc,
    Function.comp_apply] at hz
  have hIntf : ∫ x, ‖hyFam p f z x‖ ∂volume ≤ (max 1 Mf) ^ p * (2 * Rf) := by
    have hIcc : Integrable (fun x => (max 1 Mf) ^ p *
        (Set.Icc (-Rf) Rf).indicator (fun _ => (1:ℝ)) x) volume :=
      ((integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)).integrable_indicator
        measurableSet_Icc).const_mul _
    calc ∫ x, ‖hyFam p f z x‖ ∂volume
        ≤ ∫ x, (max 1 Mf) ^ p * (Set.Icc (-Rf) Rf).indicator (fun _ => (1:ℝ)) x ∂volume := by
          refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => norm_nonneg _) hIcc
            (Filter.Eventually.of_forall fun x =>
              hyFam_le_of_mem_closedStrip hp1 (le_max_left 1 Mf) hRf.le
                (fun x => le_trans (hMfb x) (le_max_right 1 Mf)) hRfs hz.1 hz.2 x)
        _ = (max 1 Mf) ^ p * (2 * Rf) := integral_indicator_Icc_const _ _ hRf.le
  have hIntg : ∫ x, ‖hyFam p g z x‖ ∂volume ≤ (max 1 Mg) ^ p * (2 * Rg) := by
    have hIcc : Integrable (fun x => (max 1 Mg) ^ p *
        (Set.Icc (-Rg) Rg).indicator (fun _ => (1:ℝ)) x) volume :=
      ((integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)).integrable_indicator
        measurableSet_Icc).const_mul _
    calc ∫ x, ‖hyFam p g z x‖ ∂volume
        ≤ ∫ x, (max 1 Mg) ^ p * (Set.Icc (-Rg) Rg).indicator (fun _ => (1:ℝ)) x ∂volume := by
          refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => norm_nonneg _) hIcc
            (Filter.Eventually.of_forall fun x =>
              hyFam_le_of_mem_closedStrip hp1 (le_max_left 1 Mg) hRg.le
                (fun x => le_trans (hMgb x) (le_max_right 1 Mg)) hRgs hz.1 hz.2 x)
        _ = (max 1 Mg) ^ p * (2 * Rg) := integral_indicator_Icc_const _ _ hRg.le
  calc ‖hyPhi p f g z‖
      ≤ ∫ q : ℝ × ℝ, ‖hyFam p f z q.1 * hyFam p g z q.2 * hyK q.1 q.2‖
          ∂(volume.prod volume) := norm_integral_le_integral_norm _
    _ = ∫ q : ℝ × ℝ, ‖hyFam p f z q.1‖ * ‖hyFam p g z q.2‖ ∂(volume.prod volume) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
        simp only [norm_mul, norm_hyK, mul_one]
    _ = (∫ x, ‖hyFam p f z x‖ ∂volume) * (∫ y, ‖hyFam p g z y‖ ∂volume) :=
        integral_prod_mul (f := fun x => ‖hyFam p f z x‖) (g := fun y => ‖hyFam p g z y‖)
    _ ≤ ((max 1 Mf) ^ p * (2 * Rf)) * ((max 1 Mg) ^ p * (2 * Rg)) :=
        mul_le_mul hIntf hIntg (integral_nonneg fun x => norm_nonneg _) (by positivity)


/-- Continuity of `hyPhi` on the closed strip. -/
lemma hyPhi_continuousOn_closed (p : ℝ) (hp1 : 1 < p) {f g : ℝ → ℂ}
    (hf : Nice f) (hg : Nice g) :
    ContinuousOn (hyPhi p f g) (Complex.HadamardThreeLines.verticalClosedStrip 0 1) := by
  obtain ⟨Mf, hMf, hMfb⟩ := hf.bound
  obtain ⟨Rf, hRf, hRfs⟩ := hf.supp
  obtain ⟨Mg, hMg, hMgb⟩ := hg.bound
  obtain ⟨Rg, hRg, hRgs⟩ := hg.supp
  have hBf : Integrable (fun x => (max 1 Mf) ^ p *
      (Set.Icc (-Rf) Rf).indicator (fun _ => (1:ℝ)) x) volume :=
    ((integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)).integrable_indicator
      measurableSet_Icc).const_mul _
  have hBg : Integrable (fun y => (max 1 Mg) ^ p *
      (Set.Icc (-Rg) Rg).indicator (fun _ => (1:ℝ)) y) volume :=
    ((integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)).integrable_indicator
      measurableSet_Icc).const_mul _
  have hcont_hyFam : ∀ (u : ℝ → ℂ) (x : ℝ), Continuous (fun z : ℂ => hyFam p u z x) := by
    intro u x
    have : (fun z : ℂ => hyFam p u z x) = fun z => ((((‖u x‖ : ℝ) ^ (p - 1) : ℝ) : ℂ) * u x)
        * Complex.exp ((-(p / 2) * (Real.log ‖u x‖ : ℂ)) * z) := by
      funext z; rw [hyFam]; ring
    rw [this]
    exact continuous_const.mul (Complex.continuous_exp.comp (continuous_const.mul continuous_id))
  refine continuousOn_of_dominated
    (F := fun (z : ℂ) (q : ℝ × ℝ) => hyFam p f z q.1 * hyFam p g z q.2 * hyK q.1 q.2)
    (bound := fun q : ℝ × ℝ => ((max 1 Mf) ^ p *
        (Set.Icc (-Rf) Rf).indicator (fun _ => (1:ℝ)) q.1)
      * ((max 1 Mg) ^ p * (Set.Icc (-Rg) Rg).indicator (fun _ => (1:ℝ)) q.2))
    (fun z _ => hyPhi_integrand_measurable (le_of_lt hp1) hf.meas hg.meas z)
    (fun z hz => Filter.Eventually.of_forall fun q => ?_)
    (hBf.mul_prod hBg)
    (Filter.Eventually.of_forall fun q =>
      (((hcont_hyFam f q.1).mul (hcont_hyFam g q.2)).mul continuous_const).continuousOn)
  · simp only [Complex.HadamardThreeLines.verticalClosedStrip, Set.mem_preimage, Set.mem_Icc] at hz
    rw [norm_mul, norm_mul, norm_hyK, mul_one]
    exact mul_le_mul (hyFam_le_of_mem_closedStrip hp1 (le_max_left 1 Mf) hRf.le
        (fun x => le_trans (hMfb x) (le_max_right 1 Mf)) hRfs hz.1 hz.2 q.1)
      (hyFam_le_of_mem_closedStrip hp1 (le_max_left 1 Mg) hRg.le
        (fun x => le_trans (hMgb x) (le_max_right 1 Mg)) hRgs hz.1 hz.2 q.2)
      (norm_nonneg _)
      (mul_nonneg (by positivity) (Set.indicator_nonneg (fun _ _ => zero_le_one) _))


lemma integral_norm_rpow_eq_toReal' {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℂ}
    {r : ℝ} (hr : 0 < r) (hf : AEMeasurable f μ) :
    (∫ x, ‖f x‖ ^ r ∂μ) = (∫⁻ x, ‖f x‖ₑ ^ r ∂μ).toReal := by
  have hmeas : AEStronglyMeasurable (fun x => ‖f x‖ ^ r) μ :=
    ((Real.continuous_rpow_const hr.le).measurable.comp_aemeasurable hf.norm).aestronglyMeasurable
  rw [integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall fun x => Real.rpow_nonneg (norm_nonneg _) _) hmeas]
  congr 1
  refine lintegral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only []
  rw [← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hr.le, ofReal_norm]

lemma ofReal_integral_norm_rpow_eq_lintegral {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℂ} {r : ℝ} (hr : 0 < r) (hf : Integrable (fun x => ‖f x‖ ^ r) μ) :
    ENNReal.ofReal (∫ x, ‖f x‖ ^ r ∂μ) = ∫⁻ x, ‖f x‖ₑ ^ r ∂μ := by
  rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal hf
    (Filter.Eventually.of_forall fun x => Real.rpow_nonneg (norm_nonneg _) _)]
  refine lintegral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only []
  rw [← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hr.le, ofReal_norm]

lemma eLpNorm_eq_ofReal_integral_norm_rpow {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℂ} {r : ℝ} (hr : 0 < r) (hf : Integrable (fun x => ‖f x‖ ^ r) μ)
    (hfm : AEStronglyMeasurable f μ) :
    eLpNorm f (ENNReal.ofReal r) μ
      = ENNReal.ofReal ((∫ x, ‖f x‖ ^ r ∂μ) ^ ((1:ℝ) / r)) := by
  rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (by positivity) ENNReal.ofReal_ne_top hfm,
    ENNReal.toReal_ofReal hr.le]
  rw [← ofReal_integral_norm_rpow_eq_lintegral hr hf,
    ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity)]

/-- The core interpolation inequality (Riesz–Thorin, via Hadamard three lines). -/
theorem hy_interp_core (p : ℝ) (hp1 : 1 < p) (hp2 : p ≤ 2) {f g : ℝ → ℂ}
    (hf : Nice f) (hg : Nice g) :
    ‖∫ y, (𝓕 f) y * g y ∂volume‖
      ≤ (∫ x, ‖f x‖ ^ p ∂volume) ^ ((1:ℝ) / p)
        * (∫ x, ‖g x‖ ^ p ∂volume) ^ ((1:ℝ) / p) := by
  set θ : ℝ := 2 * (p - 1) / p with hθdef
  have hp0 : 0 < p := by linarith
  have hθ0 : 0 ≤ θ := by rw [hθdef]; positivity
  have hθ1 : θ ≤ 1 := by
    rw [hθdef, div_le_one hp0]
    linarith
  have hθmem : ((θ : ℝ) : ℂ) ∈ Complex.HadamardThreeLines.verticalClosedStrip 0 1 := by
    rw [Complex.HadamardThreeLines.verticalClosedStrip, Set.mem_preimage, Set.mem_Icc]
    exact ⟨hθ0, hθ1⟩
  have hd : DiffContOnCl ℂ (hyPhi p f g) (Complex.HadamardThreeLines.verticalStrip 0 1) := by
    refine ⟨hyPhi_differentiableOn p hp1 hf hg, ?_⟩
    have hcl : closure (Complex.HadamardThreeLines.verticalStrip 0 1)
        = Complex.HadamardThreeLines.verticalClosedStrip 0 1 := by
      rw [Complex.HadamardThreeLines.verticalStrip, Complex.HadamardThreeLines.verticalClosedStrip,
        Complex.closure_preimage_re, closure_Ioo (by norm_num : (0:ℝ) ≠ 1)]
    rw [hcl]
    exact hyPhi_continuousOn_closed p hp1 hf hg
  have hbound := Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip₀₁'
    (f := hyPhi p f g) hθmem hd (hyPhi_bddAbove p hp1 hf hg)
    (fun z hz => hyPhi_bound_re_zero p hp1 hf hg z (by simpa [Set.mem_preimage] using hz))
    (fun z hz => hyPhi_bound_re_one p hp1 hp2 hf hg z (by simpa [Set.mem_preimage] using hz))
  have hrepr : ‖hyPhi p f g ((θ : ℝ) : ℂ)‖ = ‖∫ y, (𝓕 f) y * g y ∂volume‖ := by
    rw [hyPhi_eq_integral_fourier p hp1 hf hg (by rw [Complex.ofReal_re]; linarith)
      (by rw [Complex.ofReal_re]; linarith)]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only []
    rw [show (hyFam p f ((θ : ℝ) : ℂ)) = hyFam p f ((2 * (p - 1) / p : ℝ) : ℂ) by
        rw [hθdef], hyFam_theta_fun p hp1 f, hyFam_theta_fun p hp1 g]
  rw [hrepr] at hbound
  simp only [Complex.ofReal_re] at hbound
  have h1 : ((1:ℝ) / 2) * θ = θ / 2 := by ring
  have h2 : 1 - θ + θ / 2 = (1:ℝ) / p := by
    rw [hθdef]; field_simp; ring
  have heq : ((∫ x, ‖f x‖ ^ p ∂volume) * (∫ x, ‖g x‖ ^ p ∂volume)) ^ (1 - θ)
        * (((∫ x, ‖f x‖ ^ p ∂volume) ^ ((1:ℝ) / 2))
            * ((∫ x, ‖g x‖ ^ p ∂volume) ^ ((1:ℝ) / 2))) ^ θ
      = (∫ x, ‖f x‖ ^ p ∂volume) ^ ((1:ℝ) / p)
        * (∫ x, ‖g x‖ ^ p ∂volume) ^ ((1:ℝ) / p) := by
    set A : ℝ := ∫ x, ‖f x‖ ^ p ∂volume with hA
    set B : ℝ := ∫ x, ‖g x‖ ^ p ∂volume with hB
    have hAnn : 0 ≤ A := by rw [hA]; exact integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) _
    have hBnn : 0 ≤ B := by rw [hB]; exact integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) _
    rw [Real.mul_rpow hAnn hBnn,
      Real.mul_rpow (Real.rpow_nonneg hAnn _) (Real.rpow_nonneg hBnn _),
      ← Real.rpow_mul hAnn, ← Real.rpow_mul hBnn, h1,
      show A ^ (1 - θ) * B ^ (1 - θ) * (A ^ (θ / 2) * B ^ (θ / 2))
          = (A ^ (1 - θ) * A ^ (θ / 2)) * (B ^ (1 - θ) * B ^ (θ / 2)) by ring,
      ]
    rw [← Real.rpow_add' hAnn (by rw [h2]; positivity),
      ← Real.rpow_add' hBnn (by rw [h2]; positivity), h2]
  exact hbound.trans heq.le


/-- The phased modulus `|z|/z` has norm at most one. -/
lemma norm_norm_div_le_one (z : ℂ) : ‖((‖z‖ : ℝ) : ℂ) / z‖ ≤ 1 := by
  rcases eq_or_ne z 0 with h | h
  · rw [h, div_zero, norm_zero]; norm_num
  · rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _),
      div_self (norm_ne_zero_iff.mpr h)]



set_option maxHeartbeats 2000000 in
/-- The modulus form of the interpolation core: for nice `f` and `g`,
`∫ ‖𝓕 f‖ ‖g‖ ≤ ‖f‖_p · ‖g‖_p`.  This is `hy_interp_core` tested against the phase-corrected
modulus `‖g‖ · (‖𝓕 f‖ / 𝓕 f)`, which makes the integrand of the pairing real and nonnegative. -/
lemma hy_interp_core_abs (p : ℝ) (hp1 : 1 < p) (hp2 : p ≤ 2) {f g : ℝ → ℂ}
    (hf : Nice f) (hg : Nice g) :
    ∫ y, ‖(𝓕 f) y‖ * ‖g y‖ ∂volume
      ≤ (∫ x, ‖f x‖ ^ p ∂volume) ^ ((1:ℝ) / p)
        * (∫ x, ‖g x‖ ^ p ∂volume) ^ ((1:ℝ) / p) := by
  have hp0 : (0:ℝ) < p := by linarith
  obtain ⟨Mf, hMf, hMfb⟩ := hf.bound
  obtain ⟨Rf, hRf, hRfs⟩ := hf.supp
  obtain ⟨Mg, hMg, hMgb⟩ := hg.bound
  obtain ⟨Rg, hRg, hRgs⟩ := hg.supp
  have hfL1 : MemLp f 1 volume := by
    have h := memLp_of_bound_supp (u := f) (r := 1) (M := max 1 Mf) (R := Rf) one_pos
      (le_max_left 1 Mf) hRf hf.aestronglyMeasurable
      (fun x => le_trans (hMfb x) (le_max_right 1 Mf)) hRfs
    simpa using h
  have hfm : Measurable (fun y => (𝓕 f) y) :=
    Commons.Analysis.Fourier.BoundaryLayer.measurable_fourier hfL1
  set G : ℝ → ℂ := fun y => ((‖g y‖ : ℝ) : ℂ) * (((‖(𝓕 f) y‖ : ℝ) : ℂ) / (𝓕 f) y) with hGdef
  have hG_bound : ∀ y, ‖G y‖ ≤ ‖g y‖ := by
    intro y
    have h1 : ‖G y‖ = ‖g y‖ * ‖(((‖(𝓕 f) y‖ : ℝ) : ℂ) / (𝓕 f) y)‖ := by
      rw [hGdef]
      simp only []
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg (g y))]
    rw [h1]
    calc ‖g y‖ * ‖(((‖(𝓕 f) y‖ : ℝ) : ℂ) / (𝓕 f) y)‖
        ≤ ‖g y‖ * 1 := mul_le_mul_of_nonneg_left (norm_norm_div_le_one _) (norm_nonneg (g y))
      _ = ‖g y‖ := mul_one _
  have hG_supp : ∀ x, Rg ≤ |x| → G x = 0 := by
    intro x hx
    rw [hGdef]
    simp only []
    rw [hRgs x hx]
    simp
  have hG_nice : Nice G := by
    refine ⟨?_, ?_, ?_⟩
    · rw [hGdef]
      exact (Complex.measurable_ofReal.comp hg.meas.norm).mul
        ((Complex.measurable_ofReal.comp hfm.norm).div hfm)
    · exact ⟨max 1 Mg, lt_of_lt_of_le one_pos (le_max_left 1 Mg),
        fun y => le_trans (hG_bound y) (le_trans (hMgb y) (le_max_right 1 Mg))⟩
    · exact ⟨Rg, hRg, hG_supp⟩
  have hfg_int : Integrable (fun y => ‖(𝓕 f) y‖ * ‖g y‖) volume := by
    have hgL1 : Integrable g volume := memLp_one_iff_integrable.mp (by
      have h := memLp_of_bound_supp (u := g) (r := 1) (M := max 1 Mg) (R := Rg) one_pos
        (le_max_left 1 Mg) hRg hg.aestronglyMeasurable
        (fun x => le_trans (hMgb x) (le_max_right 1 Mg)) hRgs
      simpa using h)
    refine Integrable.mono' (hgL1.norm.const_mul (∫ x, ‖f x‖ ∂volume)) ?_ ?_
    · exact (hfm.norm.mul hg.meas.norm).aestronglyMeasurable
    · filter_upwards with y
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
      exact mul_le_mul_of_nonneg_right (Commons.Analysis.CalderonZygmund.norm_fourier_le f y) (norm_nonneg _)
  have hprod : ∀ y, (𝓕 f) y * G y = (((‖(𝓕 f) y‖ * ‖g y‖) : ℝ) : ℂ) := by
    intro y
    rw [hGdef]
    simp only []
    rw [Complex.ofReal_mul]
    rcases eq_or_ne ((𝓕 f) y) 0 with hz | hz
    · simp [hz]
    · field_simp
  have hint_eq : (∫ y, (𝓕 f) y * G y ∂volume)
      = (((∫ y, ‖(𝓕 f) y‖ * ‖g y‖ ∂volume) : ℝ) : ℂ) := by
    have hOfReal : (∫ x, (((fun y => ‖(𝓕 f) y‖ * ‖g y‖) x : ℝ) : ℂ) ∂volume)
        = (((∫ x, ‖(𝓕 f) x‖ * ‖g x‖ ∂volume) : ℝ) : ℂ) := integral_ofReal
    rw [← hOfReal]
    exact integral_congr_ae (Filter.Eventually.of_forall fun y => hprod y)
  have hnorm_eq : ‖∫ y, (𝓕 f) y * G y ∂volume‖ = ∫ y, ‖(𝓕 f) y‖ * ‖g y‖ ∂volume := by
    rw [hint_eq, Complex.norm_real,
      Real.norm_of_nonneg (integral_nonneg fun y => mul_nonneg (norm_nonneg _) (norm_nonneg _))]
  have hG_le : (∫ x, ‖G x‖ ^ p ∂volume) ≤ (∫ x, ‖g x‖ ^ p ∂volume) := by
    have hg_mem : MemLp g (ENNReal.ofReal p) volume :=
      memLp_of_bound_supp hp0 (le_max_left 1 Mg) hRg hg.aestronglyMeasurable
        (fun x => le_trans (hMgb x) (le_max_right 1 Mg)) hRgs
    have hG_mem : MemLp G (ENNReal.ofReal p) volume :=
      memLp_of_bound_supp hp0 (le_max_left 1 Mg) hRg hG_nice.aestronglyMeasurable
        (fun x => le_trans (hG_bound x) (le_trans (hMgb x) (le_max_right 1 Mg))) hG_supp
    have hgi : Integrable (fun x => ‖g x‖ ^ p) volume := by
      have h := hg_mem.integrable_norm_rpow (ENNReal.ofReal_pos.mpr hp0).ne' ENNReal.ofReal_ne_top
      simpa [ENNReal.toReal_ofReal hp0.le] using h
    have hGi : Integrable (fun x => ‖G x‖ ^ p) volume := by
      have h := hG_mem.integrable_norm_rpow (ENNReal.ofReal_pos.mpr hp0).ne' ENNReal.ofReal_ne_top
      simpa [ENNReal.toReal_ofReal hp0.le] using h
    exact integral_mono hGi hgi (fun x => Real.rpow_le_rpow (norm_nonneg _) (hG_bound x) hp0.le)
  refine hnorm_eq.symm.trans_le ?_
  refine (hy_interp_core p hp1 hp2 hf hG_nice).trans ?_
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) _) hG_le
      (by positivity))
    (Real.rpow_nonneg (integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) _) _)


/-- Truncation of the modulus of a complex function: `min ‖G y‖ m` on `[-m, m]`, and `0`
outside.  These truncations are bounded, compactly supported and increase to `‖G‖` as `m → ∞`. -/
noncomputable def hyTrunc (G : ℝ → ℂ) (m : ℕ) (y : ℝ) : ℝ :=
  if y ∈ Set.Icc (-(m : ℝ)) (m : ℝ) then min ‖G y‖ (m : ℝ) else 0

/-- The complex-valued version of `hyTrunc`, used as a test function. -/
noncomputable def hyTruncC (G : ℝ → ℂ) (m : ℕ) (y : ℝ) : ℂ := ((hyTrunc G m y : ℝ) : ℂ)

lemma hyTrunc_nonneg (G : ℝ → ℂ) (m : ℕ) (y : ℝ) : 0 ≤ hyTrunc G m y := by
  rw [hyTrunc]
  split_ifs with h
  · exact le_min (norm_nonneg _) (Nat.cast_nonneg m)
  · exact le_rfl

lemma hyTrunc_le (G : ℝ → ℂ) (m : ℕ) (y : ℝ) : hyTrunc G m y ≤ ‖G y‖ := by
  rw [hyTrunc]
  split_ifs with h
  · exact min_le_left _ _
  · exact norm_nonneg _

lemma hyTrunc_le_cast (G : ℝ → ℂ) (m : ℕ) (y : ℝ) : hyTrunc G m y ≤ (m : ℝ) := by
  rw [hyTrunc]
  split_ifs with h
  · exact min_le_right _ _
  · exact Nat.cast_nonneg m

lemma hyTrunc_measurable {G : ℝ → ℂ} (hG : Measurable G) (m : ℕ) :
    Measurable (hyTrunc G m) := by
  change Measurable (fun y : ℝ =>
    if y ∈ Set.Icc (-(m : ℝ)) (m : ℝ) then min ‖G y‖ (m : ℝ) else 0)
  exact Measurable.ite measurableSet_Icc (hG.norm.min measurable_const) measurable_const

lemma hyTrunc_mono (G : ℝ → ℂ) {m m' : ℕ} (h : m ≤ m') (y : ℝ) :
    hyTrunc G m y ≤ hyTrunc G m' y := by
  by_cases hy : y ∈ Set.Icc (-(m : ℝ)) (m : ℝ)
  · have hy' : y ∈ Set.Icc (-(m' : ℝ)) (m' : ℝ) := by
      rw [Set.mem_Icc] at hy ⊢
      have hmm : (m : ℝ) ≤ (m' : ℝ) := Nat.cast_le.mpr h
      exact ⟨by linarith [hy.1], by linarith [hy.2]⟩
    rw [hyTrunc, if_pos hy, hyTrunc, if_pos hy']
    exact min_le_min le_rfl (Nat.cast_le.mpr h)
  · rw [hyTrunc, if_neg hy]
    exact hyTrunc_nonneg G m' y

lemma hyTrunc_supp (G : ℝ → ℂ) (m : ℕ) {y : ℝ} (h : (m : ℝ) < |y|) : hyTrunc G m y = 0 := by
  rw [hyTrunc, if_neg]
  intro hy
  rw [Set.mem_Icc] at hy
  rcases lt_abs.mp h with h' | h' <;> linarith [hy.1, hy.2]

/-- The truncations increase to the modulus: `⨆_m ofReal (hyTrunc G m y) = ‖G y‖ₑ`. -/
lemma hyTrunc_sup (G : ℝ → ℂ) (y : ℝ) :
    (⨆ m : ℕ, ENNReal.ofReal (hyTrunc G m y)) = ENNReal.ofReal ‖G y‖ := by
  refine le_antisymm (iSup_le fun m => ENNReal.ofReal_le_ofReal (hyTrunc_le G m y)) ?_
  set M : ℕ := ⌈|y|⌉₊ + ⌈‖G y‖⌉₊ with hM
  have hM1 : |y| ≤ (M : ℝ) := by
    rw [hM]; push_cast
    exact le_trans (Nat.le_ceil _) (le_add_of_nonneg_right (Nat.cast_nonneg _))
  have hM2 : ‖G y‖ ≤ (M : ℝ) := by
    rw [hM]; push_cast
    exact le_trans (Nat.le_ceil _) (le_add_of_nonneg_left (Nat.cast_nonneg _))
  have hval : hyTrunc G M y = ‖G y‖ := by
    rw [hyTrunc, if_pos (Set.mem_Icc.mpr (abs_le.mp hM1)), min_eq_left hM2]
  rw [← hval]
  exact le_iSup (fun m : ℕ => ENNReal.ofReal (hyTrunc G m y)) M

lemma hyTruncC_norm (G : ℝ → ℂ) (m : ℕ) (y : ℝ) : ‖hyTruncC G m y‖ = hyTrunc G m y := by
  rw [hyTruncC, Complex.norm_real, Real.norm_of_nonneg (hyTrunc_nonneg G m y)]

lemma hyTruncC_le (G : ℝ → ℂ) (m : ℕ) (y : ℝ) : ‖hyTruncC G m y‖ ≤ ‖G y‖ := by
  rw [hyTruncC_norm]; exact hyTrunc_le G m y

lemma hyTruncC_le_cast (G : ℝ → ℂ) (m : ℕ) (y : ℝ) : ‖hyTruncC G m y‖ ≤ (m : ℝ) := by
  rw [hyTruncC_norm]; exact hyTrunc_le_cast G m y

lemma hyTruncC_measurable {G : ℝ → ℂ} (hG : Measurable G) (m : ℕ) :
    Measurable (hyTruncC G m) := by
  change Measurable (fun y : ℝ => ((hyTrunc G m y : ℝ) : ℂ))
  exact Complex.measurable_ofReal.comp (hyTrunc_measurable hG m)

lemma hyTruncC_supp (G : ℝ → ℂ) (m : ℕ) {y : ℝ} (h : (m : ℝ) < |y|) : hyTruncC G m y = 0 := by
  simp [hyTruncC, hyTrunc_supp G m h]

/-- The truncated test functions are `Nice`. -/
lemma hyTruncC_nice {G : ℝ → ℂ} (hG : Measurable G) (m : ℕ) : Nice (hyTruncC G m) := by
  refine ⟨hyTruncC_measurable hG m, ?_, ?_⟩
  · refine ⟨max 1 (m : ℝ), lt_of_lt_of_le one_pos (le_max_left 1 (m : ℝ)), fun y => ?_⟩
    exact le_trans (hyTruncC_le_cast G m y) (le_max_right 1 (m : ℝ))
  · refine ⟨(m : ℝ) + 1, by positivity, fun y hy => ?_⟩
    exact hyTruncC_supp G m (lt_of_lt_of_le (lt_add_one (m : ℝ)) hy)

lemma hyTruncC_memLp (G : ℝ → ℂ) (hG : Measurable G) (m : ℕ) {r : ℝ} (hr : 0 < r) :
    MemLp (hyTruncC G m) (ENNReal.ofReal r) volume := by
  refine memLp_of_bound_supp hr (le_max_left 1 (m : ℝ)) (by positivity : (0:ℝ) < (m:ℝ) + 1)
    (hyTruncC_nice hG m).aestronglyMeasurable
    (fun y => le_trans (hyTruncC_le_cast G m y) (le_max_right 1 (m : ℝ))) ?_
  intro y hy
  exact hyTruncC_supp G m (lt_of_lt_of_le (lt_add_one (m : ℝ)) hy)

/-- The duality step: for nice `f` and `g` with `‖g‖_{Lᵖ} ≤ 1` (a.e. measurable),
`∫⁻ ‖𝓕 f‖ₑ ‖g‖ₑ ≤ ‖f‖_{Lᵖ}`.  The test function is truncated to a `Nice` function, which is
where the modulus form `hy_interp_core_abs` of the interpolation core applies. -/
lemma hy_lintegral_mul_le (p : ℝ) (hp1 : 1 < p) (hp2 : p ≤ 2) {f : ℝ → ℂ} (hf : Nice f)
    {g : ℝ → ℂ} (hgm : AEMeasurable g volume)
    (hg1 : eLpNorm g (ENNReal.ofReal p) volume ≤ 1) :
    ∫⁻ y, ‖(𝓕 f) y‖ₑ * ‖g y‖ₑ ∂volume ≤ eLpNorm f (ENNReal.ofReal p) volume := by
  have hp0 : (0:ℝ) < p := by linarith
  obtain ⟨Mf, hMf, hMfb⟩ := hf.bound
  obtain ⟨Rf, hRf, hRfs⟩ := hf.supp
  obtain ⟨G, hGmeas, hGae⟩ := hgm
  have hfeLp : eLpNorm f (ENNReal.ofReal p) volume
      = ENNReal.ofReal ((∫ x, ‖f x‖ ^ p ∂volume) ^ ((1:ℝ) / p)) := by
    refine eLpNorm_eq_ofReal_integral_norm_rpow hp0 ?_ hf.aestronglyMeasurable
    have hmem : MemLp f (ENNReal.ofReal p) volume :=
      memLp_of_bound_supp hp0 (le_max_left 1 Mf) hRf hf.aestronglyMeasurable
        (fun x => le_trans (hMfb x) (le_max_right 1 Mf)) hRfs
    have h := hmem.integrable_norm_rpow (ENNReal.ofReal_pos.mpr hp0).ne' ENNReal.ofReal_ne_top
    simpa [ENNReal.toReal_ofReal hp0.le] using h
  have hfm : Measurable (fun y => (𝓕 f) y) :=
    Commons.Analysis.Fourier.BoundaryLayer.measurable_fourier (by
      have h := memLp_of_bound_supp (u := f) (r := 1) (M := max 1 Mf) (R := Rf) one_pos
        (le_max_left 1 Mf) hRf hf.aestronglyMeasurable
        (fun x => le_trans (hMfb x) (le_max_right 1 Mf)) hRfs
      simpa using h)
  rw [hfeLp]
  have hlink1 : (∫⁻ y, ‖(𝓕 f) y‖ₑ * ‖g y‖ₑ ∂volume)
      = ∫⁻ y, ‖(𝓕 f) y‖ₑ * ‖G y‖ₑ ∂volume :=
    lintegral_congr_ae (hGae.mono fun y hy => by simp only []; rw [hy])
  rw [hlink1]
  have hlink2 : (∫⁻ y, ‖(𝓕 f) y‖ₑ * ‖G y‖ₑ ∂volume)
      = ∫⁻ y, (⨆ m : ℕ, ‖(𝓕 f) y‖ₑ * ENNReal.ofReal (hyTrunc G m y)) ∂volume :=
    lintegral_congr fun y => by
      have hGy : ‖G y‖ₑ = ⨆ m : ℕ, ENNReal.ofReal (hyTrunc G m y) := by
        rw [(ofReal_norm (G y)).symm, ← hyTrunc_sup G y]
      rw [hGy, ENNReal.mul_iSup]
  rw [hlink2]
  have hMCT : (∫⁻ y, (⨆ m : ℕ, ‖(𝓕 f) y‖ₑ * ENNReal.ofReal (hyTrunc G m y)) ∂volume)
      = ⨆ m : ℕ, ∫⁻ y, ‖(𝓕 f) y‖ₑ * ENNReal.ofReal (hyTrunc G m y) ∂volume :=
    lintegral_iSup (μ := (volume : Measure ℝ))
      (f := fun m y => ‖(𝓕 f) y‖ₑ * ENNReal.ofReal (hyTrunc G m y))
      (fun m => (hfm.enorm).mul (ENNReal.measurable_ofReal.comp (hyTrunc_measurable hGmeas m)))
      (fun m m' hmm y => mul_le_mul_of_nonneg_left (ENNReal.ofReal_mono (hyTrunc_mono G hmm y))
        (by simp))
  rw [hMCT]
  refine iSup_le fun m => ?_
  have hmem : MemLp (hyTruncC G m) (ENNReal.ofReal p) volume := hyTruncC_memLp G hGmeas m hp0
  have hInt : Integrable (fun y => ‖(𝓕 f) y‖ * hyTrunc G m y) volume := by
    have hnorm : Integrable (fun y => ‖hyTruncC G m y‖) volume :=
      (memLp_one_iff_integrable.mp (by
        simpa using hyTruncC_memLp G hGmeas m one_pos)).norm
    refine Integrable.mono' (hnorm.const_mul (∫ x, ‖f x‖ ∂volume)) ?_ ?_
    · exact ((hfm.norm).mul (hyTrunc_measurable hGmeas m)).aestronglyMeasurable
    · filter_upwards with y
      rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (hyTrunc_nonneg G m y)), hyTruncC_norm]
      exact mul_le_mul_of_nonneg_right
        (Commons.Analysis.CalderonZygmund.norm_fourier_le f y) (hyTrunc_nonneg G m y)
  have hlink : (∫⁻ y, ENNReal.ofReal (‖(𝓕 f) y‖ * hyTrunc G m y) ∂volume)
      = ∫⁻ y, ‖(𝓕 f) y‖ₑ * ENNReal.ofReal (hyTrunc G m y) ∂volume :=
    lintegral_congr fun y => by
      rw [ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm]
  have hbound : (∫ x, ‖hyTruncC G m x‖ ^ p ∂volume) ^ ((1:ℝ) / p) ≤ 1 := by
    have hIntp : Integrable (fun x => ‖hyTruncC G m x‖ ^ p) volume := by
      have h := hmem.integrable_norm_rpow (ENNReal.ofReal_pos.mpr hp0).ne' ENNReal.ofReal_ne_top
      simpa [ENNReal.toReal_ofReal hp0.le] using h
    have heq := eLpNorm_eq_ofReal_integral_norm_rpow (μ := volume)
      (f := hyTruncC G m) hp0 hIntp hmem.aestronglyMeasurable
    have hle : eLpNorm (hyTruncC G m) (ENNReal.ofReal p) volume ≤ 1 :=
      calc eLpNorm (hyTruncC G m) (ENNReal.ofReal p) volume
          ≤ eLpNorm G (ENNReal.ofReal p) volume :=
            eLpNorm_mono hmem.aestronglyMeasurable fun y => by rw [hyTruncC_norm]; exact hyTrunc_le G m y
        _ = eLpNorm g (ENNReal.ofReal p) volume := eLpNorm_congr_ae hGae.symm
        _ ≤ 1 := hg1
    rw [heq] at hle
    exact ENNReal.ofReal_le_one.mp hle
  calc
    ∫⁻ y, ‖(𝓕 f) y‖ₑ * ENNReal.ofReal (hyTrunc G m y) ∂volume
        = ENNReal.ofReal (∫ y, ‖(𝓕 f) y‖ * hyTrunc G m y ∂volume) := by
          rw [← hlink, MeasureTheory.ofReal_integral_eq_lintegral_ofReal hInt
            (Filter.Eventually.of_forall fun y =>
              mul_nonneg (norm_nonneg _) (hyTrunc_nonneg G m y))]
      _ ≤ ENNReal.ofReal ((∫ x, ‖f x‖ ^ p ∂volume) ^ ((1:ℝ) / p)
            * (∫ x, ‖hyTruncC G m x‖ ^ p ∂volume) ^ ((1:ℝ) / p)) := by
          have htriv : (∫ y, ‖(𝓕 f) y‖ * hyTrunc G m y ∂volume)
              = ∫ y, ‖(𝓕 f) y‖ * ‖hyTruncC G m y‖ ∂volume :=
            integral_congr_ae (Filter.Eventually.of_forall fun y => by simp only [hyTruncC_norm])
          rw [htriv]
          exact ENNReal.ofReal_le_ofReal (hy_interp_core_abs p hp1 hp2 hf (hyTruncC_nice hGmeas m))
      _ = ENNReal.ofReal ((∫ x, ‖f x‖ ^ p ∂volume) ^ ((1:ℝ) / p))
            * ENNReal.ofReal ((∫ x, ‖hyTruncC G m x‖ ^ p ∂volume) ^ ((1:ℝ) / p)) :=
          ENNReal.ofReal_mul (Real.rpow_nonneg
            (integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) _) _)
      _ ≤ ENNReal.ofReal ((∫ x, ‖f x‖ ^ p ∂volume) ^ ((1:ℝ) / p)) * 1 :=
          mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_one.mpr hbound) (by simp)
      _ = ENNReal.ofReal ((∫ x, ‖f x‖ ^ p ∂volume) ^ ((1:ℝ) / p)) := mul_one _

/-- Hausdorff–Young for nice `f`: `‖𝓕 f‖_{p'} ≤ ‖f‖_p`, via `Lᵖ`–`Lᵠ` duality. -/
theorem hy_eLpNorm_fourier_le_of_nice (p : ℝ) (hp1 : 1 < p) (hp2 : p ≤ 2) {f : ℝ → ℂ}
    (hf : Nice f) :
    eLpNorm (𝓕 f) (ENNReal.ofReal (p / (p - 1))) volume ≤ eLpNorm f (ENNReal.ofReal p) volume := by
  have hp0 : (0:ℝ) < p := by linarith
  obtain ⟨Mf, hMf, hMfb⟩ := hf.bound
  obtain ⟨Rf, hRf, hRfs⟩ := hf.supp
  have hq1 : (1:ℝ) < p / (p - 1) := by
    rw [one_lt_div (by linarith)]; linarith
  have hfm : AEMeasurable (fun y => (𝓕 f) y) volume :=
    (Commons.Analysis.Fourier.BoundaryLayer.measurable_fourier (by
      have h := memLp_of_bound_supp (u := f) (r := 1) (M := max 1 Mf) (R := Rf) one_pos
        (le_max_left 1 Mf) hRf hf.aestronglyMeasurable
        (fun x => le_trans (hMfb x) (le_max_right 1 Mf)) hRfs
      simpa using h)).aemeasurable
  have hpq : (ENNReal.ofReal (p / (p - 1)))⁻¹ + (ENNReal.ofReal p)⁻¹ = 1 := by
    rw [← ENNReal.ofReal_inv_of_pos (x := p / (p - 1)) (by positivity),
      ← ENNReal.ofReal_inv_of_pos (x := p) hp0,
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    have harg : (p / (p - 1))⁻¹ + p⁻¹ = (1 : ℝ) := by
      rw [inv_div, ← one_div]
      field_simp
      ring
    rw [harg, ENNReal.ofReal_one]
  rw [Commons.MeasureTheory.Function.eLpNorm_eq_iSup_lintegral_mul_sigmaFinite
    (μ := (volume : Measure ℝ)) (p := ENNReal.ofReal (p / (p - 1))) (q := ENNReal.ofReal p)
    hpq (ENNReal.one_lt_ofReal.mpr hq1) (ENNReal.one_lt_ofReal.mpr hp1) hfm]
  refine iSup_le fun g => ?_
  have hpair : MeasureTheory.lintegral (volume : Measure ℝ)
        (fun x => ENNReal.ofReal ‖(𝓕 f) x * g.1 x‖)
      = ∫⁻ y, ‖(𝓕 f) y‖ₑ * ‖g.1 y‖ₑ ∂volume :=
    lintegral_congr fun y => by rw [ofReal_norm, enorm_mul]
  rw [hpair]
  exact hy_lintegral_mul_le p hp1 hp2 hf g.2.1 g.2.2

/-- Fatou's lemma for `eLpNorm`: if the pointwise `enorm` of `U` is a.e. dominated by the pointwise
`liminf` of the `enorm`s of a sequence, then `eLpNorm U q ≤ liminf eLpNorm (u n) q`. -/
theorem eLpNorm_le_liminf_of_enorm_le_liminf_of_ae {α : Type*} [MeasurableSpace α]
    {μ : MeasureTheory.Measure α} {E : Type*} [MeasurableSpace E] [SeminormedAddCommGroup E]
    [OpensMeasurableSpace E]
    {q : ℝ} (hq : 0 < q) {u : ℕ → α → E} {U : α → E}
    (hU : ∀ᵐ x ∂μ, ‖U x‖ₑ ≤ Filter.liminf (fun n => ‖u n x‖ₑ) Filter.atTop)
    (hu : ∀ n, AEMeasurable (u n) μ) (hUm : AEStronglyMeasurable U μ) :
    MeasureTheory.eLpNorm U (ENNReal.ofReal q) μ
      ≤ Filter.liminf (fun n => MeasureTheory.eLpNorm (u n) (ENNReal.ofReal q) μ)
          Filter.atTop := by
  have hqne0 : ENNReal.ofReal q ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hq
  have hqnetop : ENNReal.ofReal q ≠ ⊤ := ENNReal.ofReal_ne_top
  have hptw : ∀ n, (∫⁻ x, ‖u n x‖ₑ ^ q ∂μ) ^ (1 / q)
      ≤ MeasureTheory.eLpNorm (u n) (ENNReal.ofReal q) μ := by
    intro n
    by_cases hn : AEStronglyMeasurable (u n) μ
    · rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal hqne0 hqnetop hn,
        ENNReal.toReal_ofReal hq.le]
    · rw [MeasureTheory.eLpNorm_of_not_aestronglyMeasurable hn]; exact le_top
  refine le_trans ?_ (Filter.liminf_le_liminf (Filter.Eventually.of_forall hptw))
  rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal hqne0 hqnetop hUm,
    ENNReal.toReal_ofReal hq.le]
  have hLM : (∫⁻ x, ‖U x‖ₑ ^ q ∂μ)
      ≤ Filter.liminf (fun n => ∫⁻ x, ‖u n x‖ₑ ^ q ∂μ) Filter.atTop := by
    calc (∫⁻ x, ‖U x‖ₑ ^ q ∂μ)
        ≤ ∫⁻ x, (Filter.liminf (fun n => ‖u n x‖ₑ) Filter.atTop) ^ q ∂μ :=
          lintegral_mono_ae (hU.mono fun x hx => ENNReal.rpow_le_rpow hx hq.le)
      _ = ∫⁻ x, Filter.liminf (fun n => ‖u n x‖ₑ ^ q) Filter.atTop ∂μ := by
          apply lintegral_congr
          intro x
          have key : ENNReal.orderIsoRpow q hq (Filter.liminf (fun n => ‖u n x‖ₑ) Filter.atTop)
              = Filter.liminf (fun n => ENNReal.orderIsoRpow q hq (‖u n x‖ₑ)) Filter.atTop := by
            refine (ENNReal.orderIsoRpow q hq).liminf_apply ?_ ?_ ?_ ?_
            all_goals isBoundedDefault
          simpa only [ENNReal.orderIsoRpow_apply] using key
      _ ≤ Filter.liminf (fun n => ∫⁻ x, ‖u n x‖ₑ ^ q ∂μ) Filter.atTop := by
          apply lintegral_liminf_le'
          intro n
          exact (hu n).enorm.pow_const q
  calc (∫⁻ x, ‖U x‖ₑ ^ q ∂μ) ^ (1 / q)
      ≤ (Filter.liminf (fun n => ∫⁻ x, ‖u n x‖ₑ ^ q ∂μ) Filter.atTop) ^ (1 / q) :=
        ENNReal.rpow_le_rpow hLM (by positivity)
    _ = Filter.liminf (fun n => (∫⁻ x, ‖u n x‖ₑ ^ q ∂μ) ^ (1 / q)) Filter.atTop := by
        have key : ENNReal.orderIsoRpow (1 / q) (by positivity)
              (Filter.liminf (fun n => ∫⁻ x, ‖u n x‖ₑ ^ q ∂μ) Filter.atTop)
            = Filter.liminf (fun n => ENNReal.orderIsoRpow (1 / q) (by positivity)
                (∫⁻ x, ‖u n x‖ₑ ^ q ∂μ)) Filter.atTop := by
          refine (ENNReal.orderIsoRpow (1 / q) (by positivity)).liminf_apply ?_ ?_ ?_ ?_
          all_goals isBoundedDefault
        simpa only [ENNReal.orderIsoRpow_apply] using key

/-- Truncation of a measurable function to `[-n, n]` and to values of norm at most `n`. -/
noncomputable def hyFTrunc (F : ℝ → ℂ) (n : ℕ) (x : ℝ) : ℂ :=
  if x ∈ Set.Icc (-(n : ℝ)) (n : ℝ) ∧ ‖F x‖ ≤ (n : ℝ) then F x else 0

lemma hyFTrunc_measurable {F : ℝ → ℂ} (hF : Measurable F) (n : ℕ) :
    Measurable (hyFTrunc F n) := by
  change Measurable (fun x : ℝ =>
    if x ∈ Set.Icc (-(n : ℝ)) (n : ℝ) ∧ ‖F x‖ ≤ (n : ℝ) then F x else 0)
  exact Measurable.ite
    (measurableSet_Icc.inter (measurableSet_le hF.norm
      (measurable_const : Measurable (fun _ : ℝ => (n : ℝ))))) hF
    (measurable_const : Measurable (fun _ : ℝ => (0 : ℂ)))

lemma hyFTrunc_le (F : ℝ → ℂ) (n : ℕ) (x : ℝ) : ‖hyFTrunc F n x‖ ≤ ‖F x‖ := by
  rw [hyFTrunc]
  split_ifs with h
  · exact le_rfl
  · exact le_trans (le_of_eq (norm_zero (E := ℂ))) (norm_nonneg (F x))

lemma hyFTrunc_bound (F : ℝ → ℂ) (n : ℕ) (x : ℝ) : ‖hyFTrunc F n x‖ ≤ max 1 (n : ℝ) := by
  rw [hyFTrunc]
  split_ifs with h
  · exact le_trans h.2 (le_max_right 1 (n : ℝ))
  · exact le_trans (le_of_eq (norm_zero (E := ℂ)))
      (le_trans (by norm_num : (0:ℝ) ≤ 1) (le_max_left 1 (n : ℝ)))

lemma hyFTrunc_supp (F : ℝ → ℂ) (n : ℕ) {x : ℝ} (h : (n : ℝ) < |x|) : hyFTrunc F n x = 0 := by
  rw [hyFTrunc, if_neg]
  intro hx
  rw [Set.mem_Icc] at hx
  rcases lt_abs.mp h with h' | h' <;> linarith [hx.1, hx.2]

lemma hyFTrunc_nice {F : ℝ → ℂ} (hF : Measurable F) (n : ℕ) : Nice (hyFTrunc F n) := by
  refine ⟨hyFTrunc_measurable hF n, ?_, ?_⟩
  · exact ⟨max 1 (n : ℝ), lt_of_lt_of_le one_pos (le_max_left 1 (n : ℝ)), hyFTrunc_bound F n⟩
  · exact ⟨(n : ℝ) + 1, by positivity,
      fun x hx => hyFTrunc_supp F n (lt_of_lt_of_le (lt_add_one (n : ℝ)) hx)⟩

lemma hyFTrunc_tendsto (F : ℝ → ℂ) (x : ℝ) :
    Filter.Tendsto (fun n => hyFTrunc F n x) Filter.atTop (𝓝 (F x)) := by
  have hev : ∀ᶠ n in Filter.atTop, hyFTrunc F n x = F x := by
    filter_upwards [Filter.eventually_ge_atTop (max ⌈|x|⌉₊ ⌈‖F x‖⌉₊)] with n hn
    have hmm : (max ⌈|x|⌉₊ ⌈‖F x‖⌉₊ : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    rw [hyFTrunc, if_pos]
    exact ⟨Set.mem_Icc.mpr (abs_le.mp (le_trans (Nat.le_ceil |x|)
      (le_trans (le_max_left _ _) hmm))),
      le_trans (Nat.le_ceil ‖F x‖) (le_trans (le_max_right _ _) hmm)⟩
  exact Filter.Tendsto.congr' (hev.mono fun n hn => hn.symm) tendsto_const_nhds

lemma hyFTrunc_memLp_one {F : ℝ → ℂ} (hF : Measurable F) (n : ℕ) :
    MemLp (hyFTrunc F n) 1 volume := by
  have h := memLp_of_bound_supp (u := hyFTrunc F n) (r := 1) (M := max 1 (n : ℝ))
    (R := (n : ℝ) + 1) one_pos (le_max_left 1 (n : ℝ)) (by positivity)
    (hyFTrunc_nice hF n).aestronglyMeasurable (hyFTrunc_bound F n)
    (fun x hx => hyFTrunc_supp F n (lt_of_lt_of_le (lt_add_one (n : ℝ)) hx))
  simpa using h

/-- `𝓕 g y` as an integral against the kernel `hyK`. -/
lemma fourier_eq_integral_hyK (g : ℝ → ℂ) (y : ℝ) : 𝓕 g y = ∫ x, hyK x y * g x ∂volume := by
  rw [Real.fourier_eq]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only []
  rw [Circle.smul_def, smul_eq_mul, hyK_eq]

/-- The Fourier transforms of the truncations converge pointwise to the Fourier transform. -/
lemma hyFTrunc_fourier_tendsto {F : ℝ → ℂ} (hF : Measurable F) (hFint : Integrable F volume)
    (y : ℝ) :
    Filter.Tendsto (fun n => (𝓕 (hyFTrunc F n)) y) Filter.atTop (𝓝 ((𝓕 F) y)) := by
  have hphase : Measurable (fun x : ℝ => hyK x y) :=
    (continuous_hyK.comp (Continuous.prodMk continuous_id continuous_const)).measurable
  have hDCT : Filter.Tendsto (fun n => ∫ x, hyK x y * hyFTrunc F n x ∂volume) Filter.atTop
      (𝓝 (∫ x, hyK x y * F x ∂volume)) :=
    MeasureTheory.tendsto_integral_of_dominated_convergence (fun x => ‖F x‖)
      (fun n => ((hphase.mul (hyFTrunc_measurable hF n))).aestronglyMeasurable)
      hFint.norm
      (fun n => Filter.Eventually.of_forall fun x => by
        rw [norm_mul, norm_hyK, one_mul]
        exact hyFTrunc_le F n x)
      (Filter.Eventually.of_forall fun x =>
        (hyFTrunc_tendsto F x).const_mul (hyK x y))
  simpa only [fourier_eq_integral_hyK] using hDCT

/-- Hausdorff–Young on `ℝ`: `‖𝓕 f‖_{p/(p-1)} ≤ ‖f‖_p` for `1 < p ≤ 2`. -/
theorem hausdorff_young_real (p : ℝ) (hp1 : 1 < p) (hp2 : p ≤ 2) (f : ℝ → ℂ) :
    MeasureTheory.eLpNorm (FourierTransform.fourier f) (ENNReal.ofReal (p / (p - 1)))
        (MeasureTheory.volume : MeasureTheory.Measure ℝ)
      ≤ MeasureTheory.eLpNorm f (ENNReal.ofReal p) (MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
  by_cases hfint : Integrable f volume
  · obtain ⟨F, hFmeas, hFae⟩ := hfint.aestronglyMeasurable.aemeasurable
    have hFint : Integrable F volume := hfint.congr hFae
    have hqpos : (0:ℝ) < p / (p - 1) := by positivity
    have hbdd : ∀ n, eLpNorm (𝓕 (hyFTrunc F n)) (ENNReal.ofReal (p / (p - 1))) volume
        ≤ eLpNorm f (ENNReal.ofReal p) volume := by
      intro n
      calc eLpNorm (𝓕 (hyFTrunc F n)) (ENNReal.ofReal (p / (p - 1))) volume
          ≤ eLpNorm (hyFTrunc F n) (ENNReal.ofReal p) volume :=
            hy_eLpNorm_fourier_le_of_nice p hp1 hp2 (hyFTrunc_nice hFmeas n)
        _ ≤ eLpNorm F (ENNReal.ofReal p) volume := eLpNorm_mono (hyFTrunc_memLp_one hFmeas n).aestronglyMeasurable
            (fun x => hyFTrunc_le F n x)
        _ = eLpNorm f (ENNReal.ofReal p) volume := (eLpNorm_congr_ae hFae).symm
    have hFatou : eLpNorm (𝓕 F) (ENNReal.ofReal (p / (p - 1))) volume
        ≤ Filter.liminf (fun n => eLpNorm (𝓕 (hyFTrunc F n))
            (ENNReal.ofReal (p / (p - 1))) volume) Filter.atTop := by
      refine eLpNorm_le_liminf_of_enorm_le_liminf_of_ae (μ := (volume : Measure ℝ))
        (q := p / (p - 1)) hqpos ?_ ?_
        (Commons.Analysis.Fourier.BoundaryLayer.measurable_fourier
          (memLp_one_iff_integrable.mpr hFint)).aestronglyMeasurable
      · filter_upwards with y
        have hc : Filter.Tendsto (fun n => ‖(𝓕 (hyFTrunc F n)) y‖ₑ) Filter.atTop
            (𝓝 ‖(𝓕 F) y‖ₑ) :=
          (continuous_enorm.tendsto ((𝓕 F) y)).comp (hyFTrunc_fourier_tendsto hFmeas hFint y)
        rw [hc.liminf_eq]
      · intro n
        exact (Commons.Analysis.Fourier.BoundaryLayer.measurable_fourier
          (hyFTrunc_memLp_one hFmeas n)).aemeasurable
    calc eLpNorm (𝓕 f) (ENNReal.ofReal (p / (p - 1))) volume
        = eLpNorm (𝓕 F) (ENNReal.ofReal (p / (p - 1))) volume :=
          eLpNorm_congr_ae (Filter.Eventually.of_forall (Real.fourier_congr_ae hFae))
      _ ≤ Filter.liminf (fun n => eLpNorm (𝓕 (hyFTrunc F n))
            (ENNReal.ofReal (p / (p - 1))) volume) Filter.atTop := hFatou
      _ ≤ eLpNorm f (ENNReal.ofReal p) volume := by
          refine Filter.liminf_le_of_le ⟨0, Filter.Eventually.of_forall fun n => by simp⟩ ?_
          intro b hb
          obtain ⟨n, hn⟩ := hb.exists
          exact le_trans hn (hbdd n)
  · rw [Commons.Analysis.Fourier.fourier_eq_zero_of_not_integrable hfint]
    simp


end Commons.Analysis.Fourier
