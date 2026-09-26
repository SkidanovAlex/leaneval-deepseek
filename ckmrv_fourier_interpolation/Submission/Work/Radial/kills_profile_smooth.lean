import Mathlib
import Submission.Work.Radial.Basic
import Submission.Work.Core.Basic
import Submission.Work.Core.Gaussian
import Submission.Work.Radial.seminorm_bound
import Submission.Work.Radial.riemann_sum_error
import Submission.Work.Radial.fourier_bounds
import Submission.Work.Radial.fourier_iteratedDeriv
import Submission.Work.Radial.profile_seminorm_bound

/-!
# Killing the de-Gaussed profile of a compactly supported smooth profile

This file proves `Work.Radial.kills_profile_smooth`: a continuous linear functional `Λ` on the
complex Schwartz space on `ℝⁿ` which vanishes on every complex Gaussian
`x ↦ exp (π i τ ‖x‖²)` with `Im τ = y > 0` vanishes on

`x ↦ exp (-π y ‖x‖²) h (‖x‖²)`

for every compactly supported `C^∞` profile `h`.

The proof follows the argument of CKMRV Lemma 3.3 (density of the complex Gaussians).  Writing
`H = 𝓕 h` for the (one dimensional) Fourier transform of `h`, Fourier inversion gives

`h s = ∫ H u * exp (2 π i u s) du`,

so that, for `T > 0` and `N > 0`, the difference between `F` and the finite linear combination

`A = ∑_{k < N} (2T/N) * H (-T + 2Tk/N) • (x ↦ exp (π i (2(-T + 2Tk/N) + i y) ‖x‖²))`

of Gaussians with `Im τ = y` is the profile

`x ↦ exp (-π y ‖x‖²) * (h (‖x‖²) - ∑_{k<N} (2T/N) H(t_k) exp (2 π i t_k ‖x‖²))`.

The term in brackets is the difference between the integral `∫ H u exp (2πiu·) du` and its left
Riemann sum, so it is estimated by the truncation error `∫_{|u| > T} |H u| |2πu|^i du` plus the
quadrature error `M (2T)²/(2N)` of `Work.Radial.riemann_sum_error`.  Both are controlled by the
rapid decay of `H`, giving the required bound on the weighted derivatives of the profile, which
`Work.Radial.profile_seminorm_bound` converts into a Schwartz seminorm bound.

## Main result

* `Work.Radial.kills_profile_smooth`
-/

open Filter MeasureTheory
open scoped ContDiff FourierTransform Topology SchwartzMap
open LeanEval.Analysis.CKMRVInterpolation

namespace Work.Radial

variable {n : ℕ} [NeZero n]

/-! ### Auxiliary lemmas -/

/-- The supremum of finitely many seminorms is bounded by their sum. -/
lemma finset_sup_apply_le_sum {ι : Type*} (s : Finset ι)
    (q : ι → Seminorm ℝ 𝓢(EuclideanSpace ℝ (Fin n), ℂ))
    (x : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) :
    (s.sup q) x ≤ ∑ i ∈ s, q i x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sup_insert, Seminorm.sup_apply, Finset.sum_insert ha]
      refine max_le ?_ ?_
      · exact le_add_of_nonneg_right (Finset.sum_nonneg fun i _ => apply_nonneg _ _)
      · linarith [ih, apply_nonneg (q a) x]

/-- Every natural number, viewed in `ℕ∞ω`, is at most `∞`. -/
lemma natCast_le_smooth (m : ℕ) : ((m : ℕ∞ω)) ≤ ∞ := by
  rw [show (∞ : ℕ∞ω) = ((⊤ : ℕ∞) : ℕ∞ω) from rfl]
  exact WithTop.coe_le_coe.mpr le_top

/-- The Gaussian weight `t ↦ (1 + t)^m * exp (-π y t)` is bounded on `[0, ∞)`. -/
lemma exists_exp_weight_bound (y : ℝ) (hy : 0 < y) (m : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t : ℝ, 0 ≤ t → (1 + t) ^ m * Real.exp (-(Real.pi * y * t)) ≤ B := by
  have hcont : Continuous (fun t : ℝ => (1 + t) ^ m * Real.exp (-(Real.pi * y * t))) := by
    fun_prop
  have hlim : Tendsto (fun t : ℝ => (1 + t) ^ m * Real.exp (-(Real.pi * y * t)))
      atTop (𝓝 0) := by
    have hc : 0 < Real.pi * y := mul_pos Real.pi_pos hy
    have h1 : Tendsto (fun t : ℝ => t ^ m * Real.exp (-(Real.pi * y * t))) atTop (𝓝 0) := by
      have h2 := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (m : ℝ) (Real.pi * y) hc
      simpa [Real.rpow_natCast] using h2
    refine squeeze_zero' (g := fun t : ℝ => 2 ^ m * (t ^ m * Real.exp (-(Real.pi * y * t))))
      ?_ ?_ ?_
    · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
      positivity
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
      have h2 : (1 + t) ^ m ≤ (2 * t) ^ m := pow_le_pow_left₀ (by linarith) (by linarith) m
      calc (1 + t) ^ m * Real.exp (-(Real.pi * y * t))
          ≤ (2 * t) ^ m * Real.exp (-(Real.pi * y * t)) :=
            mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
        _ = 2 ^ m * (t ^ m * Real.exp (-(Real.pi * y * t))) := by rw [mul_pow]; ring
    · simpa using h1.const_mul (2 ^ m)
  obtain ⟨X, hX⟩ := eventually_atTop.mp
    (hlim.eventually (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)))
  obtain ⟨B₀, hB₀⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := max X 0)).exists_bound_of_continuousOn
    hcont.continuousOn
  have hB₀' : ∀ t ∈ Set.Icc (0 : ℝ) (max X 0),
      (1 + t) ^ m * Real.exp (-(Real.pi * y * t)) ≤ B₀ := by
    intro t ht
    have h := hB₀ t ht
    have hnn : (0 : ℝ) ≤ (1 + t) ^ m * Real.exp (-(Real.pi * y * t)) :=
      mul_nonneg (pow_nonneg (by linarith [ht.1] : (0 : ℝ) ≤ 1 + t) m) (Real.exp_pos _).le
    rw [Real.norm_eq_abs, abs_of_nonneg hnn] at h
    exact h
  refine ⟨max B₀ 1, le_trans (by norm_num : (0 : ℝ) ≤ 1) (le_max_right B₀ 1), fun t ht => ?_⟩
  rcases lt_or_ge t (max X 0) with h | h
  · exact le_trans (hB₀' t ⟨ht, h.le⟩) (le_max_left _ _)
  · exact le_trans (le_of_lt (hX t (le_trans (le_max_left _ _) h))) (le_max_right _ _)

/-! ### The frequency parameter and the Gaussians -/

/-- The frequency `2u + iy`, whose imaginary part is `y`. -/
noncomputable def freq (y u : ℝ) : ℂ := 2 * ↑u + ↑y * Complex.I

lemma freq_im (y u : ℝ) : (freq y u).im = y := by
  simp [freq, Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im]

/-- The complex Gaussian of frequency `2u + iy` is `exp (-π y ‖x‖²)` times the oscillating
factor `exp (2 π i u ‖x‖²)`. -/
lemma gaussianFun_freq (y u : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    Work.Core.gaussianFun n (freq y u) x =
      Complex.exp (-(↑Real.pi * ↑y * ↑(‖x‖ ^ 2))) *
        Complex.exp (2 * ↑Real.pi * Complex.I * ↑u * ↑(‖x‖ ^ 2)) := by
  rw [Work.Core.gaussianFun, freq]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

/-- The finite linear combination of Gaussians with frequencies `2 t_k + i y` (`k < N`), with
coefficients the left Riemann sum weights of the Fourier transform of the profile. -/
noncomputable def gaussApprox {y : ℝ} (hy : 0 < y) (H : ℝ → ℂ) (T : ℝ) (N : ℕ) :
    𝓢(EuclideanSpace ℝ (Fin n), ℂ) :=
  ∑ k ∈ Finset.range N, ((2 * T / N) * H (-T + k * (2 * T / N))) •
    Work.Core.gaussianSchwartz n (freq y (-T + k * (2 * T / N))) (by rw [freq_im]; exact hy)

lemma gaussApprox_apply {y : ℝ} (hy : 0 < y) (H : ℝ → ℂ) (T : ℝ) (N : ℕ)
    (x : EuclideanSpace ℝ (Fin n)) :
    gaussApprox (n := n) hy H T N x =
      ∑ k ∈ Finset.range N, ((2 * T / N) * H (-T + k * (2 * T / N))) *
        (Complex.exp (-(↑Real.pi * ↑y * ↑(‖x‖ ^ 2))) *
          Complex.exp (2 * ↑Real.pi * Complex.I * ↑(-T + k * (2 * T / N)) *
            ↑(‖x‖ ^ 2))) := by
  rw [gaussApprox, sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [smul_apply, Work.Core.gaussianSchwartz_apply, gaussianFun_freq, smul_eq_mul]

/-- Every Gaussian in the approximant has `Im τ = y`, so the approximant is killed by `Λ`. -/
lemma gaussApprox_killed {y : ℝ} (hy : 0 < y)
    (Λ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ) →L[ℂ] ℂ)
    (hkills : ∀ (τ : ℂ), τ.im = y → ∀ F : 𝓢(EuclideanSpace ℝ (Fin n), ℂ),
      (∀ x, F x = Work.Core.gaussianFun n τ x) → Λ F = 0)
    (H : ℝ → ℂ) (T : ℝ) (N : ℕ) : Λ (gaussApprox (n := n) hy H T N) = 0 := by
  rw [gaussApprox, map_sum]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [map_smul,
    hkills (freq y (-T + k * (2 * T / N))) (freq_im y _) _ (fun x => ?_), smul_zero]
  rw [Work.Core.gaussianSchwartz_apply]

/-! ### The profile of the difference -/

/-- The profile `h s - ∑_{k<N} Δ H(t_k) exp (2 π i t_k s)` of the difference between the
de-Gaussed function and its Gaussian approximation. -/
noncomputable def riemannProfile (h H : ℝ → ℂ) (T : ℝ) (N : ℕ) : ℝ → ℂ :=
  fun s => h s - ∑ k ∈ Finset.range N, ((2 * T / N) * H (-T + k * (2 * T / N))) *
      Complex.exp (2 * ↑Real.pi * Complex.I * ↑(-T + k * (2 * T / N)) * ↑s)

/-- The profile of `F - A`: the above profile multiplied by the Gaussian weight. -/
noncomputable def gaussProfile (y : ℝ) (h H : ℝ → ℂ) (T : ℝ) (N : ℕ) : ℝ → ℂ :=
  fun s => Complex.exp (-(↑Real.pi * ↑y * ↑s)) * riemannProfile h H T N s

lemma contDiff_gaussProfile {y : ℝ} {h H : ℝ → ℂ} (hh : ContDiff ℝ ∞ h)
    (hH : ContDiff ℝ ∞ H) (T : ℝ) (N : ℕ) : ContDiff ℝ ∞ (gaussProfile y h H T N) := by
  have ofReal : ContDiff ℝ ∞ (fun s : ℝ => (s : ℂ)) := Complex.ofRealCLM.contDiff
  have hlin : ContDiff ℝ ∞ (fun s : ℝ => (↑Real.pi * ↑y : ℂ) * (s : ℂ)) :=
    (contDiff_const (c := (↑Real.pi * ↑y : ℂ))).mul ofReal
  have hexp : ContDiff ℝ ∞ (fun s : ℝ => Complex.exp (-(↑Real.pi * ↑y * ↑s))) :=
    Complex.contDiff_exp.comp (contDiff_neg.comp hlin)
  have hsum : ContDiff ℝ ∞ (fun s : ℝ => ∑ k ∈ Finset.range N,
      ((2 * T / N) * H (-T + k * (2 * T / N))) *
        Complex.exp ((2 * ↑Real.pi * Complex.I * ↑(-T + k * (2 * T / N))) * (s : ℂ))) := by
    refine ContDiff.sum fun k _ => ?_
    let a : ℂ := 2 * ↑Real.pi * Complex.I * ↑(-T + k * (2 * T / N))
    have hc : ContDiff ℝ ∞ (fun s : ℝ => Complex.exp (a * (s : ℂ))) :=
      Complex.contDiff_exp.comp ((contDiff_const (c := a)).mul ofReal)
    exact (contDiff_const (c := ((2 * T / N) * H (-T + k * (2 * T / N))))).mul hc
  unfold gaussProfile riemannProfile
  exact hexp.mul (hh.sub hsum)

/-- Pointwise, `F - A` is the Gaussian weight times the profile above. -/
lemma sub_gaussApprox_apply {y : ℝ} (hy : 0 < y) {h : ℝ → ℂ} (H : ℝ → ℂ) (T : ℝ) (N : ℕ)
    {F : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)}
    (hF : ∀ x, F x = gaussianTimesProfile y h x) (x : EuclideanSpace ℝ (Fin n)) :
    (F - gaussApprox (n := n) hy H T N) x = gaussProfile y h H T N (‖x‖ ^ 2) := by
  rw [sub_apply, hF x, gaussApprox_apply, gaussianTimesProfile, gaussianWeight, gaussProfile,
    riemannProfile]
  rw [mul_sub, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun k _ => by ring

/-! ### The Fourier integrand and its derivative -/

noncomputable def twoPiI : ℂ := 2 * ↑Real.pi * Complex.I

lemma norm_twoPiI : ‖twoPiI‖ = 2 * Real.pi := by
  rw [show twoPiI = ((2 * Real.pi : ℝ) : ℂ) * Complex.I by
    simp only [twoPiI]; push_cast; ring, norm_mul, Complex.norm_I, mul_one,
    show ‖(((2 * Real.pi : ℝ)) : ℂ)‖ = |(2 * Real.pi : ℝ)| by simp]
  exact abs_of_nonneg (by positivity)

lemma norm_complex_ofReal' (u : ℝ) : ‖((u : ℝ) : ℂ)‖ = |u| := by simp

lemma deriv_ofReal_complex (u : ℝ) : deriv (fun v : ℝ => (v : ℂ)) u = 1 :=
  (HasDerivAt.comp_ofReal (hasDerivAt_id (u : ℂ))).deriv

lemma differentiableAt_ofReal_complex (u : ℝ) :
    DifferentiableAt ℝ (fun v : ℝ => (v : ℂ)) u :=
  Complex.ofRealCLM.differentiableAt

lemma deriv_twoPiI_mul (u : ℝ) : deriv (fun v : ℝ => twoPiI * (v : ℂ)) u = twoPiI := by
  rw [deriv_const_mul twoPiI (differentiableAt_ofReal_complex u), deriv_ofReal_complex u, mul_one]

lemma differentiableAt_twoPiI_mul (u : ℝ) :
    DifferentiableAt ℝ (fun v : ℝ => twoPiI * (v : ℂ)) u :=
  (differentiableAt_ofReal_complex u).const_mul twoPiI

lemma deriv_pow_twoPiI_mul (i : ℕ) (u : ℝ) :
    deriv (fun v : ℝ => (twoPiI * (v : ℂ)) ^ i) u
      = (i : ℂ) * (twoPiI * (u : ℂ)) ^ (i - 1) * twoPiI := by
  have hfun : (fun v : ℝ => (twoPiI * (v : ℂ)) ^ i) = ((fun v : ℝ => twoPiI * (v : ℂ)) ^ i) := by
    funext v; rfl
  rw [hfun, deriv_pow (differentiableAt_twoPiI_mul u) i, deriv_twoPiI_mul u]

lemma deriv_exp_twoPiI_mul (u t : ℝ) :
    deriv (fun v : ℝ => Complex.exp (twoPiI * ↑v * ↑t)) u
      = (twoPiI * ↑t) * Complex.exp (twoPiI * ↑u * ↑t) := by
  have h1 : HasDerivAt (fun z : ℂ => Complex.exp (twoPiI * z * ↑t))
      (Complex.exp (twoPiI * ↑u * ↑t) * (twoPiI * ↑t)) (↑u) := by
    have h2 : HasDerivAt (fun z : ℂ => twoPiI * z) twoPiI (↑u) := by
      simpa [mul_one] using (hasDerivAt_id (↑u)).const_mul twoPiI
    simpa [mul_assoc] using (h2.mul_const (↑t)).cexp
  rw [h1.comp_ofReal.deriv, mul_comm]

lemma differentiableAt_exp_twoPiI_mul (u t : ℝ) :
    DifferentiableAt ℝ (fun v : ℝ => Complex.exp (twoPiI * ↑v * ↑t)) u := by
  have h1 : HasDerivAt (fun z : ℂ => Complex.exp (twoPiI * z * ↑t))
      (Complex.exp (twoPiI * ↑u * ↑t) * (twoPiI * ↑t)) (↑u) := by
    have h2 : HasDerivAt (fun z : ℂ => twoPiI * z) twoPiI (↑u) := by
      simpa [mul_one] using (hasDerivAt_id (↑u)).const_mul twoPiI
    simpa [mul_assoc] using (h2.mul_const (↑t)).cexp
  exact h1.comp_ofReal.differentiableAt

noncomputable def riemannIntegrand (H : ℝ → ℂ) (i : ℕ) (u t : ℝ) : ℂ :=
  (twoPiI * ↑u) ^ i * H u * Complex.exp (twoPiI * ↑u * ↑t)

noncomputable def riemannIntegrandDeriv (H : ℝ → ℂ) (i : ℕ) (u t : ℝ) : ℂ :=
  (i : ℂ) * twoPiI * (twoPiI * ↑u) ^ (i - 1) * H u * Complex.exp (twoPiI * ↑u * ↑t)
    + (twoPiI * ↑u) ^ i * deriv H u * Complex.exp (twoPiI * ↑u * ↑t)
    + (twoPiI * ↑u) ^ i * H u * (Complex.exp (twoPiI * ↑u * ↑t) * (twoPiI * ↑t))

lemma deriv_riemannIntegrand {H : ℝ → ℂ} (hH : ContDiff ℝ ∞ H) (i : ℕ) (u t : ℝ) :
    deriv (fun v : ℝ => riemannIntegrand H i v t) u = riemannIntegrandDeriv H i u t := by
  have hdH : DifferentiableAt ℝ H u := (hH.contDiffAt.differentiableAt (by simp : (∞ : ℕ∞ω) ≠ 0))
  have hdpow : DifferentiableAt ℝ (fun v : ℝ => (twoPiI * (v : ℂ)) ^ i) u :=
    (differentiableAt_twoPiI_mul u).pow i
  have hdexp : DifferentiableAt ℝ (fun v : ℝ => Complex.exp (twoPiI * ↑v * ↑t)) u :=
    differentiableAt_exp_twoPiI_mul u t
  have hfun : (fun v : ℝ => riemannIntegrand H i v t)
      = fun v : ℝ => (twoPiI * (v : ℂ)) ^ i * H v * Complex.exp (twoPiI * ↑v * ↑t) := rfl
  have hconv : (fun v : ℝ => (twoPiI * (v : ℂ)) ^ i * H v * Complex.exp (twoPiI * ↑v * ↑t))
      = ((fun v : ℝ => (twoPiI * (v : ℂ)) ^ i) * H) *
          (fun v : ℝ => Complex.exp (twoPiI * ↑v * ↑t)) := by
    funext v; rfl
  rw [hfun, hconv, deriv_mul (hdpow.mul hdH) hdexp,
    deriv_mul hdpow hdH, deriv_pow_twoPiI_mul, deriv_exp_twoPiI_mul]
  simp only [riemannIntegrandDeriv, Pi.mul_apply]
  ring

lemma hasDerivAt_riemannIntegrand {H : ℝ → ℂ} (hH : ContDiff ℝ ∞ H) (i : ℕ) (u t : ℝ) :
    HasDerivAt (fun v : ℝ => riemannIntegrand H i v t) (riemannIntegrandDeriv H i u t) u := by
  have hcont : ContDiff ℝ ∞ (fun v : ℝ => riemannIntegrand H i v t) := by
    have hlin : ContDiff ℝ ∞ (fun v : ℝ => twoPiI * (v : ℂ)) :=
      (contDiff_const (c := twoPiI)).mul Complex.ofRealCLM.contDiff
    have hexp : ContDiff ℝ ∞ (fun v : ℝ => Complex.exp (twoPiI * ↑v * ↑t)) :=
      Complex.contDiff_exp.comp (((contDiff_const (c := twoPiI)).mul
        Complex.ofRealCLM.contDiff).mul (contDiff_const (c := (↑t : ℂ))))
    have hfun : (fun v : ℝ => riemannIntegrand H i v t)
        = fun v : ℝ => (twoPiI * (v : ℂ)) ^ i * H v * Complex.exp (twoPiI * ↑v * ↑t) := rfl
    rw [hfun]
    exact ((hlin.pow i).mul hH).mul hexp
  rw [← deriv_riemannIntegrand hH i u t]
  exact (hcont.contDiffAt.differentiableAt (by simp : (∞ : ℕ∞ω) ≠ 0)).hasDerivAt

lemma norm_twoPiI_mul (u : ℝ) : ‖twoPiI * ((u:ℝ) : ℂ)‖ = 2 * Real.pi * |u| := by
  rw [norm_mul, norm_twoPiI, norm_complex_ofReal']

lemma norm_exp_twoPiI_mul (u t : ℝ) : ‖Complex.exp (twoPiI * ↑u * ↑t)‖ = 1 := by
  rw [Complex.norm_exp]
  have harg : (twoPiI * ↑u * ↑t : ℂ) = ((((2 * Real.pi) * u * t : ℝ)) : ℂ) * Complex.I := by
    simp only [twoPiI]; push_cast; ring
  have hre : (twoPiI * ↑u * ↑t : ℂ).re = 0 := by
    rw [harg, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  rw [hre, Real.exp_zero]

lemma norm_riemannIntegrandDeriv_le {H : ℝ → ℂ} {T A D : ℝ} (hT : 1 ≤ T)
    (hA0 : 0 ≤ A) (hD0 : 0 ≤ D)
    (hA : ∀ u ∈ Set.Icc (-T) T, ‖H u‖ ≤ A) (hD : ∀ u ∈ Set.Icc (-T) T, ‖deriv H u‖ ≤ D)
    {i J : ℕ} (hi : i ≤ J) {t : ℝ} (ht : 0 ≤ t) {u : ℝ} (hu : u ∈ Set.Icc (-T) T) :
    ‖riemannIntegrandDeriv H i u t‖ ≤
      3 * (2 * Real.pi * T + 2) ^ J * ((J : ℝ) + 1) * (2 * Real.pi + 1) ^ 2 * (A + D + 1) *
        (1 + t) := by
  have hβ1 : 1 ≤ 2 * Real.pi * T + 2 := by nlinarith [Real.pi_pos, hT]
  have hβ0 : 0 ≤ 2 * Real.pi * T + 2 := le_trans (by norm_num) hβ1
  have hβJ : 0 ≤ (2 * Real.pi * T + 2) ^ J := pow_nonneg hβ0 J
  have huT : |u| ≤ T := abs_le.mpr ⟨hu.1, hu.2⟩
  have hq : ‖twoPiI * (↑u : ℂ)‖ ≤ 2 * Real.pi * T + 2 := by
    rw [norm_twoPiI_mul u]; nlinarith [Real.pi_pos, huT]
  have hq0 : 0 ≤ ‖twoPiI * (↑u : ℂ)‖ := norm_nonneg _
  have hE : ‖Complex.exp (twoPiI * ↑u * ↑t)‖ = 1 := norm_exp_twoPiI_mul u t
  have hqpow1 : ‖twoPiI * (↑u : ℂ)‖ ^ (i - 1) ≤ (2 * Real.pi * T + 2) ^ J :=
    (pow_le_pow_left₀ hq0 hq _).trans (pow_le_pow_right₀ hβ1 (by omega))
  have hqpow2 : ‖twoPiI * (↑u : ℂ)‖ ^ i ≤ (2 * Real.pi * T + 2) ^ J :=
    (pow_le_pow_left₀ hq0 hq _).trans (pow_le_pow_right₀ hβ1 hi)
  have hn : ‖(i : ℂ)‖ = (i : ℝ) := by simp [Complex.norm_natCast]
  have htval : ‖(↑t : ℂ)‖ = t := by rw [show ‖(↑t : ℂ)‖ = |t| by simp, abs_of_nonneg ht]
  have hiJ1 : ((i : ℝ)) ≤ (J : ℝ) + 1 := by
    have : i ≤ J + 1 := Nat.le_trans hi (Nat.le_succ J)
    exact_mod_cast this
  have hA' : ‖H u‖ ≤ A := hA u hu
  have hD' : ‖deriv H u‖ ≤ D := hD u hu
  have hP0 : 0 ≤ ((J : ℝ) + 1) * (2 * Real.pi + 1) := by positivity
  have ht1 : ‖(i : ℂ) * twoPiI * (twoPiI * ↑u) ^ (i - 1) * H u *
      Complex.exp (twoPiI * ↑u * ↑t)‖
      ≤ (2 * Real.pi * T + 2) ^ J * (((J : ℝ) + 1) * (2 * Real.pi + 1)) * A := by
    calc ‖(i : ℂ) * twoPiI * (twoPiI * ↑u) ^ (i - 1) * H u *
            Complex.exp (twoPiI * ↑u * ↑t)‖
        = ‖(i : ℂ)‖ * ‖twoPiI‖ * ‖(twoPiI * ↑u) ^ (i - 1)‖ * ‖H u‖ *
            ‖Complex.exp (twoPiI * ↑u * ↑t)‖ := by rw [norm_mul, norm_mul, norm_mul, norm_mul]
      _ = ((i : ℝ) * (2 * Real.pi)) * (‖twoPiI * (↑u : ℂ)‖ ^ (i - 1) * ‖H u‖) := by
          rw [hn, norm_twoPiI, norm_pow, hE, mul_one]; ring
      _ ≤ (((J : ℝ) + 1) * (2 * Real.pi + 1)) * ((2 * Real.pi * T + 2) ^ J * A) :=
          mul_le_mul (mul_le_mul hiJ1 (by linarith [Real.pi_pos]) (by positivity) (by positivity))
            (mul_le_mul hqpow1 hA' (norm_nonneg _) hβJ) (by positivity) (by positivity)
      _ = (2 * Real.pi * T + 2) ^ J * (((J : ℝ) + 1) * (2 * Real.pi + 1)) * A := by ring_nf
  have ht2 : ‖(twoPiI * ↑u) ^ i * deriv H u * Complex.exp (twoPiI * ↑u * ↑t)‖
      ≤ (2 * Real.pi * T + 2) ^ J * (((J : ℝ) + 1) * (2 * Real.pi + 1)) * (A + D + 1) := by
    calc ‖(twoPiI * ↑u) ^ i * deriv H u * Complex.exp (twoPiI * ↑u * ↑t)‖
        = ‖(twoPiI * ↑u) ^ i‖ * ‖deriv H u‖ * ‖Complex.exp (twoPiI * ↑u * ↑t)‖ := by
          rw [norm_mul, norm_mul]
      _ = ‖twoPiI * (↑u : ℂ)‖ ^ i * ‖deriv H u‖ := by rw [norm_pow, hE, mul_one]
      _ ≤ (2 * Real.pi * T + 2) ^ J * D := mul_le_mul hqpow2 hD' (norm_nonneg _) hβJ
      _ ≤ (2 * Real.pi * T + 2) ^ J * (((J : ℝ) + 1) * (2 * Real.pi + 1)) * (A + D + 1) := by
          have h1 : 1 ≤ ((J : ℝ) + 1) * (2 * Real.pi + 1) := by
            have h2 : 1 ≤ (J : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) J]
            have h3 : 1 ≤ 2 * Real.pi + 1 := by linarith [Real.pi_pos]
            calc (1:ℝ) = 1 * 1 := by ring
              _ ≤ ((J : ℝ) + 1) * (2 * Real.pi + 1) := mul_le_mul h2 h3 (by norm_num) (by linarith)
          have hDle : D ≤ ((J : ℝ) + 1) * (2 * Real.pi + 1) * (A + D + 1) := by
            calc D ≤ A + D + 1 := by linarith
              _ ≤ ((J : ℝ) + 1) * (2 * Real.pi + 1) * (A + D + 1) := by
                  have h4 : 0 ≤ A + D + 1 := by linarith
                  calc A + D + 1 = 1 * (A + D + 1) := by ring
                    _ ≤ ((J : ℝ) + 1) * (2 * Real.pi + 1) * (A + D + 1) :=
                        mul_le_mul_of_nonneg_right h1 h4
          calc (2 * Real.pi * T + 2) ^ J * D
              ≤ (2 * Real.pi * T + 2) ^ J * (((J : ℝ) + 1) * (2 * Real.pi + 1) * (A + D + 1)) :=
                mul_le_mul_of_nonneg_left hDle hβJ
            _ = (2 * Real.pi * T + 2) ^ J * (((J : ℝ) + 1) * (2 * Real.pi + 1)) * (A + D + 1) := by
                ring_nf
  have ht3 : ‖(twoPiI * ↑u) ^ i * H u * (Complex.exp (twoPiI * ↑u * ↑t) * (twoPiI * ↑t))‖
      ≤ (2 * Real.pi * T + 2) ^ J * (((J : ℝ) + 1) * (2 * Real.pi + 1)) * A * ((2 * Real.pi) * t) := by
    have hP1 : 1 ≤ ((J : ℝ) + 1) * (2 * Real.pi + 1) := by
      have h2 : 1 ≤ (J : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) J]
      have h3 : 1 ≤ 2 * Real.pi + 1 := by linarith [Real.pi_pos]
      calc (1:ℝ) = 1 * 1 := by ring
        _ ≤ ((J : ℝ) + 1) * (2 * Real.pi + 1) := mul_le_mul h2 h3 (by norm_num) (by linarith)
    have hbase : ‖(twoPiI * ↑u) ^ i * H u * (Complex.exp (twoPiI * ↑u * ↑t) * (twoPiI * ↑t))‖
        ≤ (2 * Real.pi * T + 2) ^ J * A * ((2 * Real.pi) * t) := by
      calc ‖(twoPiI * ↑u) ^ i * H u * (Complex.exp (twoPiI * ↑u * ↑t) * (twoPiI * ↑t))‖
          = ‖(twoPiI * ↑u) ^ i‖ * ‖H u‖ *
              (‖Complex.exp (twoPiI * ↑u * ↑t)‖ * ‖twoPiI * ↑t‖) := by
            rw [norm_mul, norm_mul, norm_mul]
        _ = ‖twoPiI * (↑u : ℂ)‖ ^ i * ‖H u‖ * ((2 * Real.pi) * t) := by
            have ht2' : ‖twoPiI * (↑t : ℂ)‖ = (2 * Real.pi) * t := by
              rw [norm_twoPiI_mul t, abs_of_nonneg ht]
            rw [norm_pow, hE, one_mul, ht2']
        _ ≤ (2 * Real.pi * T + 2) ^ J * A * ((2 * Real.pi) * t) :=
            mul_le_mul (mul_le_mul hqpow2 hA' (norm_nonneg _) hβJ) le_rfl (by positivity) (by positivity)
    calc ‖(twoPiI * ↑u) ^ i * H u * (Complex.exp (twoPiI * ↑u * ↑t) * (twoPiI * ↑t))‖
        ≤ (2 * Real.pi * T + 2) ^ J * A * ((2 * Real.pi) * t) := hbase
      _ ≤ (2 * Real.pi * T + 2) ^ J * (((J : ℝ) + 1) * (2 * Real.pi + 1)) * A * ((2 * Real.pi) * t) := by
          have hnn : 0 ≤ (2 * Real.pi * T + 2) ^ J * A * ((2 * Real.pi) * t) := by positivity
          calc (2 * Real.pi * T + 2) ^ J * A * ((2 * Real.pi) * t)
              = ((2 * Real.pi * T + 2) ^ J * A * ((2 * Real.pi) * t)) * 1 := by ring
            _ ≤ ((2 * Real.pi * T + 2) ^ J * A * ((2 * Real.pi) * t)) *
                  (((J : ℝ) + 1) * (2 * Real.pi + 1)) := mul_le_mul_of_nonneg_left hP1 hnn
            _ = (2 * Real.pi * T + 2) ^ J * (((J : ℝ) + 1) * (2 * Real.pi + 1)) * A *
                  ((2 * Real.pi) * t) := by ring_nf
  rw [riemannIntegrandDeriv]
  refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add ht1 ht2)) ht3) |>.trans ?_
  have hbr : A + (A + D + 1) + A * (2 * Real.pi * t)
      ≤ 3 * ((2 * Real.pi + 1) * (A + D + 1) * (1 + t)) := by
    have hQ1 : 1 ≤ 2 * Real.pi + 1 := by linarith [Real.pi_pos]
    have hAD0 : (0:ℝ) ≤ A + D + 1 := by linarith
    have h1t : (1:ℝ) ≤ 1 + t := by linarith
    have hADt : (0:ℝ) ≤ (A + D + 1) * (1 + t) := mul_nonneg hAD0 (by linarith)
    have hA2 : A + D + 1 ≤ (A + D + 1) * (1 + t) := by
      have := mul_le_mul_of_nonneg_left h1t hAD0
      simpa using this
    have hA3 : (A + D + 1) * (1 + t) ≤ (2 * Real.pi + 1) * ((A + D + 1) * (1 + t)) := by
      have := mul_le_mul_of_nonneg_right hQ1 hADt
      simpa using this
    have hA4 : (2 * Real.pi + 1) * ((A + D + 1) * (1 + t))
        = (2 * Real.pi + 1) * (A + D + 1) * (1 + t) := by ring
    have h1 : A ≤ (2 * Real.pi + 1) * (A + D + 1) * (1 + t) := by
      have hA1 : A ≤ A + D + 1 := by linarith
      linarith [hA1, hA2, hA3, hA4]
    have h2 : A + D + 1 ≤ (2 * Real.pi + 1) * (A + D + 1) * (1 + t) := by
      linarith [hA2, hA3, hA4]
    have h3 : A * (2 * Real.pi * t) ≤ (2 * Real.pi + 1) * (A + D + 1) * (1 + t) := by
      have hkey : 2 * Real.pi * t ≤ (2 * Real.pi + 1) * (1 + t) := by
        have hexp : (2 * Real.pi + 1) * (1 + t) = 2 * Real.pi * t + (2 * Real.pi + 1 + t) := by ring
        linarith [hexp, ht, Real.pi_pos]
      have hstep1 : A * (2 * Real.pi * t) ≤ A * ((2 * Real.pi + 1) * (1 + t)) :=
        mul_le_mul_of_nonneg_left hkey hA0
      have hstep2 : A * ((2 * Real.pi + 1) * (1 + t)) ≤
          (A + D + 1) * ((2 * Real.pi + 1) * (1 + t)) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      have hstep3 : (A + D + 1) * ((2 * Real.pi + 1) * (1 + t))
          = (2 * Real.pi + 1) * (A + D + 1) * (1 + t) := by ring
      linarith [hstep1, hstep2, hstep3]
    linarith [h1, h2, h3]
  calc (2 * Real.pi * T + 2) ^ J * (((J : ℝ) + 1) * (2 * Real.pi + 1)) * A
      + (2 * Real.pi * T + 2) ^ J * (((J : ℝ) + 1) * (2 * Real.pi + 1)) * (A + D + 1)
      + (2 * Real.pi * T + 2) ^ J * (((J : ℝ) + 1) * (2 * Real.pi + 1)) * A * ((2 * Real.pi) * t)
      = (2 * Real.pi * T + 2) ^ J * (((J : ℝ) + 1) * (2 * Real.pi + 1)) *
          (A + (A + D + 1) + A * (2 * Real.pi * t)) := by ring_nf
    _ ≤ (2 * Real.pi * T + 2) ^ J * (((J : ℝ) + 1) * (2 * Real.pi + 1)) *
          (3 * ((2 * Real.pi + 1) * (A + D + 1) * (1 + t))) :=
        mul_le_mul_of_nonneg_left hbr (by positivity)
    _ = 3 * (2 * Real.pi * T + 2) ^ J * ((J : ℝ) + 1) * (2 * Real.pi + 1) ^ 2 * (A + D + 1) *
          (1 + t) := by ring_nf


/-! ### Derivatives of finite sums of exponentials, and the Riemann-sum identity -/

lemma hasDerivAt_exp_mul_real (a : ℂ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => Complex.exp (a * ↑s)) (a * Complex.exp (a * ↑t)) t := by
  have h : HasDerivAt (fun z : ℂ => Complex.exp (a * z)) (a * Complex.exp (a * ↑t)) (↑t) := by
    have h2 : HasDerivAt (fun z : ℂ => a * z) a (↑t) := by
      simpa [mul_one] using (hasDerivAt_id (↑t)).const_mul a
    simpa [mul_comm] using h2.cexp
  exact h.comp_ofReal

lemma deriv_exp_mul_real (a : ℂ) (t : ℝ) :
    deriv (fun s : ℝ => Complex.exp (a * ↑s)) t = a * Complex.exp (a * ↑t) :=
  (hasDerivAt_exp_mul_real a t).deriv

lemma differentiableAt_exp_mul_real (a : ℂ) (t : ℝ) :
    DifferentiableAt ℝ (fun s : ℝ => Complex.exp (a * ↑s)) t :=
  (hasDerivAt_exp_mul_real a t).differentiableAt

lemma contDiff_sum_mul_exp {ι : Type*} (s : Finset ι) (c a : ι → ℂ) :
    ContDiff ℝ ∞ (fun t : ℝ => ∑ k ∈ s, c k * Complex.exp (a k * ↑t)) := by
  refine ContDiff.sum fun k _ => ?_
  exact (contDiff_const (c := c k)).mul
    (Complex.contDiff_exp.comp ((contDiff_const (c := a k)).mul Complex.ofRealCLM.contDiff))

lemma iteratedDeriv_sum_mul_exp {ι : Type*} (s : Finset ι) (c a : ι → ℂ) (i : ℕ) (t : ℝ) :
    iteratedDeriv i (fun t : ℝ => ∑ k ∈ s, c k * Complex.exp (a k * ↑t)) t
      = ∑ k ∈ s, c k * (a k) ^ i * Complex.exp (a k * ↑t) := by
  induction i generalizing t with
  | zero => simp
  | succ i ih =>
    have hfun : (fun t : ℝ => ∑ k ∈ s, c k * (a k) ^ i * Complex.exp (a k * ↑t))
        = ∑ k ∈ s, (fun t : ℝ => c k * (a k) ^ i * Complex.exp (a k * ↑t)) := by
      funext t; rw [Finset.sum_apply]
    rw [iteratedDeriv_succ,
      show iteratedDeriv i (fun t : ℝ => ∑ k ∈ s, c k * Complex.exp (a k * ↑t))
          = fun t : ℝ => ∑ k ∈ s, c k * (a k) ^ i * Complex.exp (a k * ↑t) from funext ih,
      hfun, deriv_sum]
    · refine Finset.sum_congr rfl fun k _ => ?_
      rw [deriv_const_mul (c k * (a k) ^ i) (differentiableAt_exp_mul_real (a k) t),
        deriv_exp_mul_real (a k) t, pow_succ]
      ring
    · intro k _
      exact (differentiableAt_exp_mul_real (a k) t).const_mul (c k * (a k) ^ i)

set_option maxHeartbeats 2000000 in
/-- The `i`-th derivative of the Riemann profile is the integral minus its left Riemann sum. -/
lemma iteratedDeriv_riemannProfile {h : ℝ → ℂ} (hh : ContDiff ℝ ∞ h)
    (hsupp : ∃ R : ℝ, ∀ t : ℝ, R ≤ |t| → h t = 0) (T : ℝ) (N : ℕ) (i : ℕ) (t : ℝ) :
    iteratedDeriv i (riemannProfile h (𝓕 h) T N) t =
      (∫ u : ℝ, riemannIntegrand (𝓕 h) i u t) -
        ∑ k ∈ Finset.range N, ((2 * T / N) * (𝓕 h) (-T + k * (2 * T / N))) *
          (2 * ↑Real.pi * Complex.I * ↑(-T + k * (2 * T / N))) ^ i *
          Complex.exp (2 * ↑Real.pi * Complex.I * ↑(-T + k * (2 * T / N)) * ↑t) := by
  have hs1 : iteratedDeriv i (fun s : ℝ => h s) t = ∫ u : ℝ, riemannIntegrand (𝓕 h) i u t := by
    rw [fourier_iteratedDeriv hh hsupp i t]
    apply integral_congr_ae
    filter_upwards with u
    simp only [riemannIntegrand, twoPiI]
  have hsum : iteratedDeriv i (fun t : ℝ => ∑ k ∈ Finset.range N,
      ((2 * T / N) * (𝓕 h) (-T + k * (2 * T / N))) *
        Complex.exp (2 * ↑Real.pi * Complex.I * ↑(-T + k * (2 * T / N)) * ↑t)) t =
      ∑ k ∈ Finset.range N, ((2 * T / N) * (𝓕 h) (-T + k * (2 * T / N))) *
        (2 * ↑Real.pi * Complex.I * ↑(-T + k * (2 * T / N))) ^ i *
        Complex.exp (2 * ↑Real.pi * Complex.I * ↑(-T + k * (2 * T / N)) * ↑t) := by
    exact iteratedDeriv_sum_mul_exp (Finset.range N)
      (fun k => (2 * T / N) * (𝓕 h) (-T + k * (2 * T / N)))
      (fun k => 2 * ↑Real.pi * Complex.I * ↑(-T + k * (2 * T / N))) i t
  have hfun : riemannProfile h (𝓕 h) T N
      = (fun s : ℝ => h s) - (fun t : ℝ => ∑ k ∈ Finset.range N,
          ((2 * T / N) * (𝓕 h) (-T + k * (2 * T / N))) *
            Complex.exp (2 * ↑Real.pi * Complex.I * ↑(-T + k * (2 * T / N)) * ↑t)) := by
    funext s; rfl
  rw [hfun, iteratedDeriv_sub (hh.contDiffAt.of_le (natCast_le_smooth i))
    ((contDiff_sum_mul_exp _ _ _).contDiffAt.of_le (natCast_le_smooth i)), hs1, hsum]

/-- Splitting an integral over `ℝ` into the interval `[-T,T]` and the complementary region
`{T < |u|}`. -/
lemma integral_eq_Icc_add (T : ℝ) (hT : 0 ≤ T) (f : ℝ → ℂ) (hf : Integrable f) :
    ∫ u : ℝ, f u = (∫ u in Set.Icc (-T) T, f u) + ∫ u in {u : ℝ | T < |u|}, f u := by
  have hcompl : (Set.Icc (-T) T)ᶜ = {u : ℝ | T < |u|} := by
    ext u
    simp only [Set.mem_compl_iff, Set.mem_Icc, Set.mem_setOf_eq]
    constructor
    · intro h
      rcases le_total 0 u with h0 | h0
      · rw [abs_of_nonneg h0]
        by_contra hcon
        exact h ⟨by linarith, le_of_not_gt hcon⟩
      · rw [abs_of_nonpos h0]
        by_contra hcon
        exact h ⟨le_of_not_gt (by linarith), by linarith⟩
    · intro h hI
      rcases le_total 0 u with h0 | h0
      · rw [abs_of_nonneg h0] at h; linarith [hI.2]
      · rw [abs_of_nonpos h0] at h; linarith [hI.1]
  rw [← hcompl, ← integral_add_compl measurableSet_Icc hf]

/-- The interval integral over `[-T,T]` is the set integral over `Set.Icc (-T) T`. -/
lemma intervalIntegral_eq_setIntegral_Icc {a b : ℝ} (hab : a ≤ b) (f : ℝ → ℂ)
    (hf : Integrable f) :
    (∫ u in a..b, f u) = ∫ u in Set.Icc a b, f u := by
  rw [intervalIntegral.integral_of_le hab, ← Set.Ioc_union_left hab]
  rw [setIntegral_union (Set.disjoint_left.mpr fun x hx hx2 => by
      rw [Set.mem_singleton_iff] at hx2
      exact absurd hx2 (ne_of_gt (Set.mem_Ioc.mp hx).1))
    (measurableSet_singleton a) hf.integrableOn hf.integrableOn]
  rw [show (∫ u in {a}, f u) = 0 from setIntegral_measure_zero f (measure_singleton a)]
  ring

set_option maxHeartbeats 4000000 in
/-- Bound for the `i`-th derivative of the Riemann profile. -/
lemma norm_iteratedDeriv_riemannProfile_le {h : ℝ → ℂ} (hh : ContDiff ℝ ∞ h)
    (hsupp : ∃ R : ℝ, ∀ t : ℝ, R ≤ |t| → h t = 0) (hHsm : ContDiff ℝ ∞ (𝓕 h))
    {J : ℕ} {T : ℝ} (hT : 1 ≤ T) {N : ℕ} (hN : 0 < N) {K : ℝ} (hK0 : 0 ≤ K)
    (hderivb : ∀ i : ℕ, i ≤ J → ∀ t : ℝ, 0 ≤ t → ∀ u ∈ Set.Icc (-T) T,
      ‖riemannIntegrandDeriv (𝓕 h) i u t‖ ≤ K * (1 + t))
    {i : ℕ} (hi : i ≤ J) {t : ℝ} (ht : 0 ≤ t) :
    ‖iteratedDeriv i (riemannProfile h (𝓕 h) T N) t‖ ≤
      (∫ u in {u : ℝ | T < |u|}, (2 * Real.pi * |u|) ^ J * ‖(𝓕 h) u‖) +
        K * (1 + t) * (2 * T ^ 2 / N) := by
  obtain ⟨hHsm', hHdec, hHint, hHtail⟩ := fourier_bounds (h := h) hh hsupp
  have hT0 : (0:ℝ) ≤ T := le_trans (by norm_num) hT
  -- integrability of the integrand
  have hint : Integrable (fun u : ℝ => riemannIntegrand (𝓕 h) i u t) := by
    have hmaj : Integrable (fun u : ℝ => (2 * Real.pi * |u|) ^ i * ‖(𝓕 h) u‖) := hHint i
    refine hmaj.mono' ?_ ?_
    · have hlin : Continuous fun u : ℝ => twoPiI * (u : ℂ) :=
        continuous_const.mul Complex.continuous_ofReal
      have hcont : Continuous fun u : ℝ => riemannIntegrand (𝓕 h) i u t := by
        unfold riemannIntegrand
        exact ((hlin.pow i).mul hHsm.continuous).mul
          (Complex.continuous_exp.comp (hlin.mul continuous_const))
      exact hcont.aestronglyMeasurable
    · filter_upwards with u
      rw [riemannIntegrand, norm_mul, norm_mul, norm_pow, norm_twoPiI_mul, norm_exp_twoPiI_mul,
        mul_one]
  -- rewrite the sum in the Riemann-sum form
  have hsum_eq : (∑ k ∈ Finset.range N, ((2 * T / N) * (𝓕 h) (-T + k * (2 * T / N))) *
        (2 * ↑Real.pi * Complex.I * ↑(-T + k * (2 * T / N))) ^ i *
        Complex.exp (2 * ↑Real.pi * Complex.I * ↑(-T + k * (2 * T / N)) * ↑t)) =
      ∑ k ∈ Finset.range N,
        ((2 * T / N) * riemannIntegrand (𝓕 h) i (-T + k * (2 * T / N)) t) := by
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [riemannIntegrand]
    simp only [twoPiI]
    ring
  -- the quadrature error
  have hquad : ‖(∫ u in Set.Icc (-T) T, riemannIntegrand (𝓕 h) i u t) -
      ∑ k ∈ Finset.range N,
        ((2 * T / N) * riemannIntegrand (𝓕 h) i (-T + k * (2 * T / N)) t)‖ ≤
      K * (1 + t) * (2 * T ^ 2 / N) := by
    have hRS := riemann_sum_error (fun u : ℝ => riemannIntegrand (𝓕 h) i u t)
      (fun u : ℝ => riemannIntegrandDeriv (𝓕 h) i u t)
      (a := -T) (b := T) (M := K * (1 + t)) (by linarith) (by positivity) hN
      (fun u _ => hasDerivAt_riemannIntegrand hHsm' i u t)
      (fun u hu => hderivb i hi t ht u hu)
    have h2 : (∫ u in -T..T, riemannIntegrand (𝓕 h) i u t) - (2 * T / N) *
        ∑ k ∈ Finset.range N, riemannIntegrand (𝓕 h) i (-T + k * (2 * T / N)) t =
        (∫ u in Set.Icc (-T) T, riemannIntegrand (𝓕 h) i u t) -
          ∑ k ∈ Finset.range N,
            ((2 * T / N) * riemannIntegrand (𝓕 h) i (-T + k * (2 * T / N)) t) := by
      rw [intervalIntegral_eq_setIntegral_Icc (by linarith) _ hint, Finset.mul_sum]
    have h3 : (T - -T) ^ 2 / (2 * ↑N) * (K * (1 + t)) = K * (1 + t) * (2 * T ^ 2 / N) := by
      field_simp
      ring
    have h' : ‖(∫ u in -T..T, riemannIntegrand (𝓕 h) i u t) - (2 * T / N) *
        ∑ k ∈ Finset.range N, riemannIntegrand (𝓕 h) i (-T + k * (2 * T / N)) t‖ ≤
        K * (1 + t) * (T - -T) ^ 2 / (2 * ↑N) := by
      have hcoef : (2:ℂ) * (T:ℂ) / (N:ℂ) = ((T:ℂ) - (((-T : ℝ)) : ℂ)) / (N:ℂ) := by
        push_cast; ring
      have hsumk : (∑ k ∈ Finset.range N, riemannIntegrand (𝓕 h) i (-T + k * (2 * T / N)) t)
          = ∑ k ∈ Finset.range N,
              riemannIntegrand (𝓕 h) i (-T + k * ((T - -T) / N)) t := by
        refine Finset.sum_congr rfl fun k _ => ?_
        congr 1
        ring
      rw [hsumk, hcoef]
      exact hRS
    calc ‖(∫ u in Set.Icc (-T) T, riemannIntegrand (𝓕 h) i u t) -
          ∑ k ∈ Finset.range N,
            ((2 * T / N) * riemannIntegrand (𝓕 h) i (-T + k * (2 * T / N)) t)‖
        = ‖(∫ u in -T..T, riemannIntegrand (𝓕 h) i u t) - (2 * T / N) *
            ∑ k ∈ Finset.range N, riemannIntegrand (𝓕 h) i (-T + k * (2 * T / N)) t‖ := by
          rw [h2]
      _ ≤ K * (1 + t) * (T - -T) ^ 2 / (2 * ↑N) := h'
      _ = K * (1 + t) * (2 * T ^ 2 / N) := by field_simp; ring
  -- the tail
  have htail : ‖∫ u in {u : ℝ | T < |u|}, riemannIntegrand (𝓕 h) i u t‖ ≤
      ∫ u in {u : ℝ | T < |u|}, (2 * Real.pi * |u|) ^ J * ‖(𝓕 h) u‖ := by
    have hsm : MeasurableSet {u : ℝ | T < |u|} :=
      measurableSet_lt measurable_const continuous_abs.measurable
    refine (norm_integral_le_integral_norm _).trans ?_
    have h1 : (∫ u in {u : ℝ | T < |u|}, ‖riemannIntegrand (𝓕 h) i u t‖) =
        ∫ u in {u : ℝ | T < |u|}, (2 * Real.pi * |u|) ^ i * ‖(𝓕 h) u‖ :=
      setIntegral_congr_fun hsm fun u _ => by
        rw [riemannIntegrand, norm_mul, norm_mul, norm_pow, norm_twoPiI_mul,
          norm_exp_twoPiI_mul, mul_one]
    rw [h1]
    refine setIntegral_mono_on (hHint i).integrableOn (hHint J).integrableOn hsm fun u hu => ?_
    have hu' : T < |u| := hu
    have hu1 : 1 ≤ |u| := by linarith [hu', hT]
    have h1 : (1:ℝ) ≤ 2 * Real.pi * |u| := by nlinarith [Real.pi_pos, Real.pi_gt_three, hu1]
    have h2 : (2 * Real.pi * |u|) ^ i ≤ (2 * Real.pi * |u|) ^ J :=
      pow_le_pow_right₀ h1 hi
    exact mul_le_mul h2 le_rfl (norm_nonneg _) (by positivity)
  -- combine
  have hsplit := integral_eq_Icc_add T hT0 (fun u : ℝ => riemannIntegrand (𝓕 h) i u t) hint
  rw [iteratedDeriv_riemannProfile hh hsupp T N i t, hsum_eq]
  rw [show (∫ u : ℝ, riemannIntegrand (𝓕 h) i u t) =
      (∫ u in Set.Icc (-T) T, riemannIntegrand (𝓕 h) i u t) +
        ∫ u in {u : ℝ | T < |u|}, riemannIntegrand (𝓕 h) i u t from hsplit]
  rw [show (∫ u in Set.Icc (-T) T, riemannIntegrand (𝓕 h) i u t) +
        (∫ u in {u : ℝ | T < |u|}, riemannIntegrand (𝓕 h) i u t) -
        (∑ k ∈ Finset.range N,
          ((2 * T / N) * riemannIntegrand (𝓕 h) i (-T + k * (2 * T / N)) t)) =
      ((∫ u in Set.Icc (-T) T, riemannIntegrand (𝓕 h) i u t) -
        (∑ k ∈ Finset.range N,
          ((2 * T / N) * riemannIntegrand (𝓕 h) i (-T + k * (2 * T / N)) t))) +
      (∫ u in {u : ℝ | T < |u|}, riemannIntegrand (𝓕 h) i u t) from by ring]
  conv_rhs => rw [add_comm]
  exact (norm_add_le _ _).trans (add_le_add hquad htail)

lemma iteratedDeriv_exp_mul_real (a : ℂ) (l : ℕ) (t : ℝ) :
    iteratedDeriv l (fun s : ℝ => Complex.exp (a * ↑s)) t = a ^ l * Complex.exp (a * ↑t) := by
  induction l generalizing t with
  | zero => simp
  | succ l ih =>
    rw [iteratedDeriv_succ,
      show iteratedDeriv l (fun s : ℝ => Complex.exp (a * ↑s))
        = fun t : ℝ => a ^ l * Complex.exp (a * ↑t) from funext ih,
      deriv_const_mul (a ^ l) (differentiableAt_exp_mul_real a t), deriv_exp_mul_real a t,
      pow_succ]
    ring

set_option maxHeartbeats 8000000 in
/-- The main estimate: for every `δ > 0` there are `T ≥ 1`, `N > 0` such that the weighted
derivatives of the profile of `F - A` are bounded by `δ`. -/
theorem exists_gaussProfile_bound {y : ℝ} (hy : 0 < y) {h : ℝ → ℂ} (hh : ContDiff ℝ ∞ h)
    (hsupp : ∃ R : ℝ, ∀ t : ℝ, R ≤ |t| → h t = 0) (J M : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ T : ℝ, 1 ≤ T ∧ ∃ N : ℕ, 0 < N ∧
      ∀ j : ℕ, j ≤ J → ∀ t : ℝ, 0 ≤ t →
        (1 + t) ^ M * ‖iteratedDeriv j (gaussProfile y h (𝓕 h) T N) t‖ ≤ δ := by
  obtain ⟨hHsm, hHdec, hHint, hHtail⟩ := fourier_bounds (h := h) hh hsupp
  obtain ⟨B, hB0, hB⟩ := exists_exp_weight_bound y hy M
  obtain ⟨B₁, hB₁0, hB₁⟩ := exists_exp_weight_bound y hy (M + 1)
  have hπy : 0 < Real.pi * y := mul_pos Real.pi_pos hy
  have hπy1 : 1 ≤ 1 + Real.pi * y := by linarith
  -- choose `T`
  have hεpos : 0 < δ / 2 / ((1 + Real.pi * y) ^ J * B + 1) := by positivity
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp
    ((hHtail J).eventually (eventually_lt_nhds hεpos))
  refine ⟨max T₀ 1, le_max_right _ _, ?_⟩
  set T : ℝ := max T₀ 1 with hTdef
  have hT1 : 1 ≤ T := le_max_right _ _
  have hT0le : T₀ ≤ T := le_max_left _ _
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT1
  have htailT : (1 + Real.pi * y) ^ J * B *
      (∫ u in {u : ℝ | T < |u|}, (2 * Real.pi * |u|) ^ J * ‖(𝓕 h) u‖) ≤ δ / 2 := by
    have h1 := hT₀ T hT0le
    have h2 : (1 + Real.pi * y) ^ J * B *
        (∫ u in {u : ℝ | T < |u|}, (2 * Real.pi * |u|) ^ J * ‖(𝓕 h) u‖)
        ≤ (1 + Real.pi * y) ^ J * B * (δ / 2 / ((1 + Real.pi * y) ^ J * B + 1)) :=
      mul_le_mul_of_nonneg_left h1.le (by positivity)
    have h3 : (1 + Real.pi * y) ^ J * B * (δ / 2 / ((1 + Real.pi * y) ^ J * B + 1)) ≤ δ / 2 := by
      rw [mul_div_assoc']
      rw [div_le_iff₀ (by positivity)]
      nlinarith [hδ, hB0, pow_nonneg (by linarith : (0:ℝ) ≤ 1 + Real.pi * y) J]
    linarith
  -- sup bounds on `[-T,T]`
  obtain ⟨Ac, hAc⟩ := (isCompact_Icc (a := -T) (b := T)).exists_bound_of_continuousOn
    hHsm.continuous.continuousOn
  have hderiv_cont : Continuous (deriv (𝓕 h)) := by
    rw [← iteratedDeriv_one]
    exact hHsm.continuous_iteratedDeriv 1 (natCast_le_smooth 1)
  obtain ⟨Dc, hDc⟩ := (isCompact_Icc (a := -T) (b := T)).exists_bound_of_continuousOn
    hderiv_cont.continuousOn
  set A : ℝ := max Ac 0 with hAdef
  set D : ℝ := max Dc 0 with hDdef
  have hA0 : 0 ≤ A := le_max_right _ _
  have hD0 : 0 ≤ D := le_max_right _ _
  have hAu : ∀ u ∈ Set.Icc (-T) T, ‖(𝓕 h) u‖ ≤ A := fun u hu =>
    le_trans (hAc u hu) (le_max_left _ _)
  have hDu : ∀ u ∈ Set.Icc (-T) T, ‖deriv (𝓕 h) u‖ ≤ D := fun u hu =>
    le_trans (hDc u hu) (le_max_left _ _)
  set K : ℝ := 3 * (2 * Real.pi * T + 2) ^ J * ((J : ℝ) + 1) * (2 * Real.pi + 1) ^ 2 *
    (A + D + 1) with hKdef
  have hK0 : 0 ≤ K := by rw [hKdef]; positivity
  have hderivb : ∀ i : ℕ, i ≤ J → ∀ t : ℝ, 0 ≤ t → ∀ u ∈ Set.Icc (-T) T,
      ‖riemannIntegrandDeriv (𝓕 h) i u t‖ ≤ K * (1 + t) := by
    intro i hi t ht u hu
    have h := norm_riemannIntegrandDeriv_le (H := 𝓕 h) (T := T) (A := A) (D := D) hT1 hA0
      hD0 hAu hDu hi ht hu
    rw [hKdef]
    exact h
  -- choose `N`
  obtain ⟨N, hN⟩ := exists_nat_gt ((1 + Real.pi * y) ^ J * B₁ * K * (2 * T ^ 2) / (δ / 2))
  have hNpos : 0 < N := by
    have h1 : 0 ≤ (1 + Real.pi * y) ^ J * B₁ * K * (2 * T ^ 2) / (δ / 2) := by positivity
    have h2 : (0:ℝ) < (N : ℝ) := lt_of_le_of_lt h1 hN
    exact_mod_cast h2
  refine ⟨N, hNpos, ?_⟩
  have hquadT : (1 + Real.pi * y) ^ J * K * B₁ * (2 * T ^ 2 / N) ≤ δ / 2 := by
    have hNpos' : (0:ℝ) < (N : ℝ) := by exact_mod_cast hNpos
    have h1 : (1 + Real.pi * y) ^ J * B₁ * K * (2 * T ^ 2) < (N : ℝ) * (δ / 2) := by
      have := (div_lt_iff₀ (by positivity : (0:ℝ) < δ / 2)).mp hN
      linarith [this]
    have h2 : (1 + Real.pi * y) ^ J * B₁ * K * (2 * T ^ 2) / (N : ℝ) ≤ δ / 2 := by
      rw [div_le_iff₀ hNpos']
      linarith [h1]
    calc (1 + Real.pi * y) ^ J * K * B₁ * (2 * T ^ 2 / N)
        = (1 + Real.pi * y) ^ J * B₁ * K * (2 * T ^ 2) / (N : ℝ) := by ring
      _ ≤ δ / 2 := h2
  intro j hj t ht
  -- the weight and the profile
  set W : ℝ → ℂ := fun s : ℝ => Complex.exp (-(↑Real.pi * ↑y * ↑s)) with hWdef
  set R : ℝ → ℂ := riemannProfile h (𝓕 h) T N with hRdef
  have hWcd : ContDiff ℝ ∞ W := by
    rw [hWdef]
    refine Complex.contDiff_exp.comp ?_
    have hlin : ContDiff ℝ ∞ (fun s : ℝ => (↑Real.pi * ↑y : ℂ) * (s : ℂ)) :=
      (contDiff_const (c := (↑Real.pi * ↑y : ℂ))).mul Complex.ofRealCLM.contDiff
    exact contDiff_neg.comp hlin
  have hRcd : ContDiff ℝ ∞ R := by
    rw [hRdef]
    have hsum : ContDiff ℝ ∞ (fun t : ℝ => ∑ k ∈ Finset.range N,
        ((2 * T / N) * (𝓕 h) (-T + k * (2 * T / N))) *
          Complex.exp (2 * ↑Real.pi * Complex.I * ↑(-T + k * (2 * T / N)) * ↑t)) :=
      contDiff_sum_mul_exp (Finset.range N)
        (fun k => (2 * T / N) * (𝓕 h) (-T + k * (2 * T / N)))
        (fun k => 2 * ↑Real.pi * Complex.I * ↑(-T + k * (2 * T / N)))
    have hfun : riemannProfile h (𝓕 h) T N
        = (fun s : ℝ => h s) - (fun t : ℝ => ∑ k ∈ Finset.range N,
            ((2 * T / N) * (𝓕 h) (-T + k * (2 * T / N))) *
              Complex.exp (2 * ↑Real.pi * Complex.I * ↑(-T + k * (2 * T / N)) * ↑t)) := by
      funext s; rfl
    rw [hfun]
    exact hh.sub hsum
  have hleib : iteratedDeriv j (gaussProfile y h (𝓕 h) T N) t =
      ∑ l ∈ Finset.range (j + 1), ((j.choose l : ℕ) : ℂ) * iteratedDeriv l W t *
        iteratedDeriv (j - l) R t := by
    have hfun : gaussProfile y h (𝓕 h) T N = W * R := by
      rw [hWdef, hRdef]
      funext s; rfl
    rw [hfun, iteratedDeriv_mul (hWcd.contDiffAt.of_le (natCast_le_smooth j))
      (hRcd.contDiffAt.of_le (natCast_le_smooth j))]
  rw [hleib]
  have hWnorm : ∀ l : ℕ, ‖iteratedDeriv l W t‖ =
      (Real.pi * y) ^ l * Real.exp (-(Real.pi * y * t)) := by
    intro l
    have hform : W = fun s : ℝ => Complex.exp ((-(↑Real.pi * ↑y)) * ↑s) := by
      rw [hWdef]; funext s; congr 1; ring
    rw [hform, iteratedDeriv_exp_mul_real (-(↑Real.pi * ↑y)) l t, norm_mul, norm_pow,
      show ‖((-(↑Real.pi * ↑y)) : ℂ)‖ = Real.pi * y by
        rw [show ((-(↑Real.pi * ↑y)) : ℂ) = (((-(Real.pi * y)) : ℝ) : ℂ) by push_cast; ring,
          show ‖((((-(Real.pi * y)) : ℝ)) : ℂ)‖ = |-(Real.pi * y)| by simp, abs_neg,
          abs_of_nonneg (by positivity)]]
    congr 1
    have harg : ((-(↑Real.pi * ↑y)) * ↑t : ℂ) = ((-(Real.pi * y * t)) : ℝ) := by push_cast; ring
    rw [harg, Complex.norm_exp, Complex.ofReal_re]
  have hterm : ∀ l ∈ Finset.range (j + 1),
      (1 + t) ^ M * ‖((j.choose l : ℕ) : ℂ) * iteratedDeriv l W t *
        iteratedDeriv (j - l) R t‖ ≤
      ((j.choose l : ℕ) : ℝ) * (Real.pi * y) ^ l * (1 + t) ^ M *
        Real.exp (-(Real.pi * y * t)) *
        ((∫ u in {u : ℝ | T < |u|}, (2 * Real.pi * |u|) ^ J * ‖(𝓕 h) u‖) +
          K * (1 + t) * (2 * T ^ 2 / N)) := by
    intro l hl
    have hl' : l ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)
    have hR := norm_iteratedDeriv_riemannProfile_le hh hsupp hHsm hT1 hNpos hK0 hderivb
      (le_trans (Nat.sub_le j l) hj) ht
    have hch : ‖((j.choose l : ℕ) : ℂ)‖ = ((j.choose l : ℕ) : ℝ) := by simp
    have hstep : ‖((j.choose l : ℕ) : ℂ) * iteratedDeriv l W t *
        iteratedDeriv (j - l) R t‖ ≤
        ((j.choose l : ℕ) : ℝ) * ((Real.pi * y) ^ l * Real.exp (-(Real.pi * y * t))) *
          ((∫ u in {u : ℝ | T < |u|}, (2 * Real.pi * |u|) ^ J * ‖(𝓕 h) u‖) +
            K * (1 + t) * (2 * T ^ 2 / N)) := by
      have hRnn : 0 ≤ ((j.choose l : ℕ) : ℝ) *
          ((Real.pi * y) ^ l * Real.exp (-(Real.pi * y * t))) := by positivity
      have e1 : ‖((j.choose l : ℕ) : ℂ) * iteratedDeriv l W t * iteratedDeriv (j - l) R t‖ =
          ((j.choose l : ℕ) : ℝ) * ((Real.pi * y) ^ l * Real.exp (-(Real.pi * y * t))) *
            ‖iteratedDeriv (j - l) R t‖ := by
        rw [norm_mul, norm_mul, hch, hWnorm l]
      rw [e1]
      exact mul_le_mul_of_nonneg_left hR hRnn
    have h1 : (1 + t) ^ M * ‖((j.choose l : ℕ) : ℂ) * iteratedDeriv l W t *
        iteratedDeriv (j - l) R t‖ ≤
        (1 + t) ^ M * (((j.choose l : ℕ) : ℝ) * ((Real.pi * y) ^ l *
          Real.exp (-(Real.pi * y * t))) *
          ((∫ u in {u : ℝ | T < |u|}, (2 * Real.pi * |u|) ^ J * ‖(𝓕 h) u‖) +
            K * (1 + t) * (2 * T ^ 2 / N))) :=
      mul_le_mul_of_nonneg_left hstep (by positivity : (0:ℝ) ≤ (1 + t) ^ M)
    have h2 : (1 + t) ^ M * (((j.choose l : ℕ) : ℝ) * ((Real.pi * y) ^ l *
          Real.exp (-(Real.pi * y * t))) *
          ((∫ u in {u : ℝ | T < |u|}, (2 * Real.pi * |u|) ^ J * ‖(𝓕 h) u‖) +
            K * (1 + t) * (2 * T ^ 2 / N))) =
        ((j.choose l : ℕ) : ℝ) * (Real.pi * y) ^ l * (1 + t) ^ M *
          Real.exp (-(Real.pi * y * t)) *
          ((∫ u in {u : ℝ | T < |u|}, (2 * Real.pi * |u|) ^ J * ‖(𝓕 h) u‖) +
            K * (1 + t) * (2 * T ^ 2 / N)) := by ring_nf
    exact h1.trans (le_of_eq h2)
  have hsum_bound : (1 + t) ^ M * ‖∑ l ∈ Finset.range (j + 1), ((j.choose l : ℕ) : ℂ) *
        iteratedDeriv l W t * iteratedDeriv (j - l) R t‖ ≤
      (1 + Real.pi * y) ^ j * ((1 + t) ^ M * Real.exp (-(Real.pi * y * t)) *
        ((∫ u in {u : ℝ | T < |u|}, (2 * Real.pi * |u|) ^ J * ‖(𝓕 h) u‖) +
          K * (1 + t) * (2 * T ^ 2 / N))) := by
    have h1 : (1 + t) ^ M * ‖∑ l ∈ Finset.range (j + 1), ((j.choose l : ℕ) : ℂ) *
        iteratedDeriv l W t * iteratedDeriv (j - l) R t‖ ≤
        (1 + t) ^ M * ∑ l ∈ Finset.range (j + 1), ‖((j.choose l : ℕ) : ℂ) *
          iteratedDeriv l W t * iteratedDeriv (j - l) R t‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity : (0:ℝ) ≤ (1 + t) ^ M)
    have h2 : (1 + t) ^ M * ∑ l ∈ Finset.range (j + 1), ‖((j.choose l : ℕ) : ℂ) *
        iteratedDeriv l W t * iteratedDeriv (j - l) R t‖ =
        ∑ l ∈ Finset.range (j + 1), (1 + t) ^ M * ‖((j.choose l : ℕ) : ℂ) *
          iteratedDeriv l W t * iteratedDeriv (j - l) R t‖ := Finset.mul_sum _ _ _
    have h3 : (∑ l ∈ Finset.range (j + 1), (1 + t) ^ M * ‖((j.choose l : ℕ) : ℂ) *
        iteratedDeriv l W t * iteratedDeriv (j - l) R t‖) ≤
        ∑ l ∈ Finset.range (j + 1), ((j.choose l : ℕ) : ℝ) * (Real.pi * y) ^ l *
          (1 + t) ^ M * Real.exp (-(Real.pi * y * t)) *
          ((∫ u in {u : ℝ | T < |u|}, (2 * Real.pi * |u|) ^ J * ‖(𝓕 h) u‖) +
            K * (1 + t) * (2 * T ^ 2 / N)) := Finset.sum_le_sum hterm
    have h4 : (∑ l ∈ Finset.range (j + 1), ((j.choose l : ℕ) : ℝ) * (Real.pi * y) ^ l *
          (1 + t) ^ M * Real.exp (-(Real.pi * y * t)) *
          ((∫ u in {u : ℝ | T < |u|}, (2 * Real.pi * |u|) ^ J * ‖(𝓕 h) u‖) +
            K * (1 + t) * (2 * T ^ 2 / N))) =
        (∑ l ∈ Finset.range (j + 1), ((j.choose l : ℕ) : ℝ) * (Real.pi * y) ^ l) *
          ((1 + t) ^ M * Real.exp (-(Real.pi * y * t)) *
            ((∫ u in {u : ℝ | T < |u|}, (2 * Real.pi * |u|) ^ J * ‖(𝓕 h) u‖) +
              K * (1 + t) * (2 * T ^ 2 / N))) := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun l _ => ?_
      ring
    have h5 : (∑ l ∈ Finset.range (j + 1), ((j.choose l : ℕ) : ℝ) * (Real.pi * y) ^ l) =
        (1 + Real.pi * y) ^ j := by
      have h := add_pow (Real.pi * y) 1 j
      rw [show ((Real.pi * y) + 1 : ℝ) = 1 + Real.pi * y by ring] at h
      rw [h]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [one_pow, mul_one]
      ring
    refine le_trans h1 ?_
    rw [h2]
    refine le_trans h3 ?_
    rw [h4, h5]
  -- conclude
  have hpos : (0:ℝ) < (1 + Real.pi * y) ^ J := by positivity
  have hX : (1 + t) ^ M * Real.exp (-(Real.pi * y * t)) *
      ((∫ u in {u : ℝ | T < |u|}, (2 * Real.pi * |u|) ^ J * ‖(𝓕 h) u‖) +
        K * (1 + t) * (2 * T ^ 2 / N)) ≤ δ / (1 + Real.pi * y) ^ J := by
    have h1 : (1 + t) ^ M * Real.exp (-(Real.pi * y * t)) *
        (∫ u in {u : ℝ | T < |u|}, (2 * Real.pi * |u|) ^ J * ‖(𝓕 h) u‖) ≤
        B * (∫ u in {u : ℝ | T < |u|}, (2 * Real.pi * |u|) ^ J * ‖(𝓕 h) u‖) :=
      mul_le_mul_of_nonneg_right (hB t ht) (by positivity)
    have h3 : (1 + t) ^ M * Real.exp (-(Real.pi * y * t)) * (1 + t) =
        (1 + t) ^ (M + 1) * Real.exp (-(Real.pi * y * t)) := by rw [pow_succ]; ring
    have h2 : (1 + t) ^ M * Real.exp (-(Real.pi * y * t)) * (K * (1 + t) * (2 * T ^ 2 / N)) =
        ((1 + t) ^ (M + 1) * Real.exp (-(Real.pi * y * t))) * (K * (2 * T ^ 2 / N)) := by
      rw [← h3]; ring
    have h4 : B * (∫ u in {u : ℝ | T < |u|}, (2 * Real.pi * |u|) ^ J * ‖(𝓕 h) u‖) ≤
        δ / 2 / (1 + Real.pi * y) ^ J := by
      rw [le_div_iff₀ hpos]
      nlinarith [htailT]
    have h5 : B₁ * (K * (2 * T ^ 2 / N)) ≤ δ / 2 / (1 + Real.pi * y) ^ J := by
      rw [le_div_iff₀ hpos]
      nlinarith [hquadT]
    calc (1 + t) ^ M * Real.exp (-(Real.pi * y * t)) *
          ((∫ u in {u : ℝ | T < |u|}, (2 * Real.pi * |u|) ^ J * ‖(𝓕 h) u‖) +
            K * (1 + t) * (2 * T ^ 2 / N))
        = (1 + t) ^ M * Real.exp (-(Real.pi * y * t)) *
            (∫ u in {u : ℝ | T < |u|}, (2 * Real.pi * |u|) ^ J * ‖(𝓕 h) u‖) +
          (1 + t) ^ M * Real.exp (-(Real.pi * y * t)) *
            (K * (1 + t) * (2 * T ^ 2 / N)) := by ring
      _ ≤ B * (∫ u in {u : ℝ | T < |u|}, (2 * Real.pi * |u|) ^ J * ‖(𝓕 h) u‖) +
          B₁ * (K * (2 * T ^ 2 / N)) := by
          rw [h2]
          exact add_le_add h1 (mul_le_mul_of_nonneg_right (hB₁ t ht) (by positivity))
      _ ≤ δ / 2 / (1 + Real.pi * y) ^ J + δ / 2 / (1 + Real.pi * y) ^ J := add_le_add h4 h5
      _ = δ / (1 + Real.pi * y) ^ J := by ring
  have hfinal : (1 + Real.pi * y) ^ j * (δ / (1 + Real.pi * y) ^ J) ≤ δ := by
    have hle : (1 + Real.pi * y) ^ j ≤ (1 + Real.pi * y) ^ J :=
      pow_le_pow_right₀ (by linarith) hj
    rw [mul_div_assoc', div_le_iff₀ hpos]
    nlinarith [hle, hδ]
  exact hsum_bound.trans (mul_le_mul_of_nonneg_left hX (by positivity)) |>.trans hfinal

open scoped ContDiff in
theorem kills_profile_smooth (n : ℕ) [NeZero n] {y : ℝ} (hy : 0 < y)
    (Λ : SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ →L[ℂ] ℂ)
    (hkills : ∀ (τ : ℂ), τ.im = y → ∀ F : SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ,
      (∀ x, F x = Work.Core.gaussianFun n τ x) → Λ F = 0)
    {h : ℝ → ℂ} (hh : ContDiff ℝ ∞ h) (hsupp : ∃ R : ℝ, ∀ t : ℝ, R ≤ |t| → h t = 0)
    {F : SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ}
    (hF : ∀ x, F x = Work.Radial.gaussianTimesProfile y h x) :
    Λ F = 0 := by
  obtain ⟨s, C₀, hC₀, hΛbnd⟩ := exists_seminorm_bound n Λ
  set J : ℕ := s.sup (fun i : ℕ × ℕ => i.2) with hJdef
  set M : ℕ := s.sup (fun i : ℕ × ℕ => i.1 + i.2) with hMdef
  have hsum_le : ∀ G : 𝓢(EuclideanSpace ℝ (Fin n), ℂ),
      (s.sup (schwartzSeminormFamily ℝ (EuclideanSpace ℝ (Fin n)) ℂ)) G
        ≤ ∑ i ∈ s, SchwartzMap.seminorm ℂ i.1 i.2 G :=
    fun G => finset_sup_apply_le_sum (n := n) s _ G
  suffices hmain : ∀ δ : ℝ, 0 < δ →
      ‖Λ F‖ ≤ C₀ * (∑ i ∈ s, ((Nat.factorial i.2 : ℕ) : ℝ) * 4 ^ i.2) * δ by
    have h0 : ‖Λ F‖ ≤ 0 := by
      by_contra hne
      have hpos : 0 < ‖Λ F‖ := not_le.mp hne
      have hCnn : 0 ≤ C₀ * (∑ i ∈ s, ((Nat.factorial i.2 : ℕ) : ℝ) * 4 ^ i.2) := by positivity
      have hδpos : 0 < ‖Λ F‖ / (2 * (C₀ * (∑ i ∈ s, ((Nat.factorial i.2 : ℕ) : ℝ) * 4 ^ i.2) + 1)) := by
        positivity
      have h1 := hmain _ hδpos
      have h2 : C₀ * (∑ i ∈ s, ((Nat.factorial i.2 : ℕ) : ℝ) * 4 ^ i.2) *
          (‖Λ F‖ / (2 * (C₀ * (∑ i ∈ s, ((Nat.factorial i.2 : ℕ) : ℝ) * 4 ^ i.2) + 1))) ≤ ‖Λ F‖ / 2 := by
        rw [mul_div_assoc', div_le_iff₀ (by positivity)]
        nlinarith [hCnn, norm_nonneg (Λ F)]
      linarith
    exact norm_eq_zero.mp (le_antisymm h0 (norm_nonneg _))
  intro δ hδ
  obtain ⟨T, hT1, N, hNpos, hbound⟩ := exists_gaussProfile_bound hy hh hsupp J M hδ
  have hpt : ∀ x, (F - gaussApprox (n := n) hy (𝓕 h) T N) x
      = gaussProfile y h (𝓕 h) T N (‖x‖ ^ 2) :=
    fun x => sub_gaussApprox_apply (n := n) hy (𝓕 h) T N hF x
  have hΛA : Λ (gaussApprox (n := n) hy (𝓕 h) T N) = 0 :=
    gaussApprox_killed (n := n) hy Λ hkills (𝓕 h) T N
  have hcd : ContDiff ℝ ∞ (gaussProfile y h (𝓕 h) T N) :=
    contDiff_gaussProfile hh (fourier_bounds (h := h) hh hsupp).1 T N
  have hsemi : ∀ i ∈ s,
      SchwartzMap.seminorm ℂ i.1 i.2 (F - gaussApprox (n := n) hy (𝓕 h) T N)
        ≤ ((Nat.factorial i.2 : ℕ) : ℝ) * 4 ^ i.2 * δ := by
    intro i hi
    have hiJ : i.2 ≤ J := by
      have h1 := Finset.le_sup (f := fun i : ℕ × ℕ => i.2) hi
      rwa [← hJdef] at h1
    have hiM : i.1 + i.2 ≤ M := by
      have h1 := Finset.le_sup (f := fun i : ℕ × ℕ => i.1 + i.2) hi
      rwa [← hMdef] at h1
    refine SchwartzMap.seminorm_le_bound ℂ i.1 i.2
      (F - gaussApprox (n := n) hy (𝓕 h) T N) (by positivity) ?_
    intro x
    have hb := profile_seminorm_bound (n := n) i.1 i.2 (hΨ := hcd) (L := δ) ?_ x
    · rw [show (⇑(F - gaussApprox (n := n) hy (𝓕 h) T N))
          = fun x => gaussProfile y h (𝓕 h) T N (‖x‖ ^ 2) from funext hpt]
      refine hb.trans (le_of_eq ?_)
      ring
    · intro j hj t ht
      have hjJ : j ≤ J := le_trans hj hiJ
      have h1 := hbound j hjJ t ht
      have h2 : (1 + t) ^ (i.1 + i.2) ≤ (1 + t) ^ M := pow_le_pow_right₀ (by linarith) hiM
      calc (1 + t) ^ (i.1 + i.2) * ‖iteratedDeriv j (gaussProfile y h (𝓕 h) T N) t‖
          ≤ (1 + t) ^ M * ‖iteratedDeriv j (gaussProfile y h (𝓕 h) T N) t‖ :=
            mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
        _ ≤ δ := h1
  calc ‖Λ F‖ = ‖Λ (F - gaussApprox (n := n) hy (𝓕 h) T N)‖ := by
        rw [map_sub, hΛA, sub_zero]
    _ ≤ C₀ * (s.sup (schwartzSeminormFamily ℝ (EuclideanSpace ℝ (Fin n)) ℂ))
          (F - gaussApprox (n := n) hy (𝓕 h) T N) := hΛbnd _
    _ ≤ C₀ * ∑ i ∈ s,
          SchwartzMap.seminorm ℂ i.1 i.2 (F - gaussApprox (n := n) hy (𝓕 h) T N) :=
        mul_le_mul_of_nonneg_left (hsum_le _) hC₀
    _ ≤ C₀ * ∑ i ∈ s, ((Nat.factorial i.2 : ℕ) : ℝ) * 4 ^ i.2 * δ :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hsemi) hC₀
    _ = C₀ * (∑ i ∈ s, ((Nat.factorial i.2 : ℕ) : ℝ) * 4 ^ i.2) * δ := by
        rw [← Finset.sum_mul]
        ring

end Work.Radial
