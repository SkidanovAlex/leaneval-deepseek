import Submission.FUP.LocalizeMain
import Submission.FUP.LocalizeScaleAux
import Submission.Commons.Analysis.Fourier.convolution_sq_le_hsNorm
import Submission.Commons.Analysis.Fourier.fourier_convFun_ae
import Submission.Commons.Analysis.Fourier.fourier_toLp_eq_fourier_integral
import Submission.Commons.Analysis.Fourier.truncation_high_le
import Submission.Commons.Analysis.Fourier.truncation_low_le
import Submission.Commons.Analysis.Fourier.strip_lintegral_entire_le
import Submission.Commons.Analysis.Fourier.LogvinenkoSereda.bandlimited_entire_extension_cube

open FractalUncertainty MeasureTheory Metric Set Complex Filter FourierTransform
open scoped ENNReal BigOperators Topology FourierTransform

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-!
# P4: the single-window estimate (`lem:mainlem`)

This module proves the per-window estimate of Han–Schlag's Lemma 4.3: for a kernel `φ` whose
Fourier transform is the damping multiplier, and a function `f` whose Fourier support lies in the
decay region, the `η`-window of `‖𝓕φ · 𝓕f(·-η)‖²` is controlled by the `κ`-interpolated bound
between `hsq(1_S f)` and `hsq f`, plus a small high-frequency term.
-/

namespace Submission.FUP

variable {d : ℕ}
local notation "ℝᵈ" => EuclideanSpace ℝ (Fin d)

/-- The truncation constant `e^{-c₃Θ(R)R}⟨R⟩^d`. -/
noncomputable def truncBeta (d : ℕ) (c₃ α R : ℝ) : ℝ :=
  Real.exp (-(c₃ * R / (Real.log (2 + R)) ^ α)) * (1 + R ^ 2) ^ ((d : ℝ) / 2)

/-- The strip half-width `Q = η q + r` of the lens estimate. -/
noncomputable def windowQ (η q r : ℝ) : ℝ := η * q + r

/-- The middle constant `D = (ηφ(1)+r+1)^d (πr²)^{-d}` of the lens estimate. -/
noncomputable def windowD (d : ℕ) (q ε η r : ℝ) : ℝ :=
  (η * phiLens q ε 1 + r + 1) ^ d * ((Real.pi * r ^ 2) ^ d)⁻¹

/-- The modulation loss constant `C_W = (40(d+1))^d`. -/
noncomputable def windowCW (d : ℕ) : ℝ := (40 * ((d : ℝ) + 1)) ^ d

lemma truncBeta_nonneg (d : ℕ) (c₃ α R : ℝ) : 0 ≤ truncBeta d c₃ α R := by
  rw [truncBeta]; positivity

lemma truncBeta_sq_le_self (d : ℕ) {c₃ α R : ℝ} (h : truncBeta d c₃ α R ≤ 1) :
    (truncBeta d c₃ α R) ^ 2 ≤ truncBeta d c₃ α R := by
  have h0 := truncBeta_nonneg d c₃ α R
  nlinarith

lemma windowCW_pos (d : ℕ) : 0 < windowCW d := by
  rw [windowCW]; positivity

lemma windowCW_nonneg (d : ℕ) : 0 ≤ windowCW d := le_of_lt (windowCW_pos d)

lemma windowD_pos {d : ℕ} {q ε η r : ℝ} (hη : 0 < η) (hr : 0 < r) (hq : 0 < q) (hε0 : 0 < ε)
    (hε1 : ε < 1) : 0 < windowD d q ε η r := by
  rw [windowD]
  have h1 : 0 < η * phiLens q ε 1 + r + 1 := by
    have h2 : 0 < phiLens q ε 1 := by
      rw [phiLens]
      refine mul_pos (div_pos (mul_pos (by norm_num) hq) Real.pi_pos) ?_
      apply Real.log_pos
      rw [one_lt_div (by linarith)]
      nlinarith
    nlinarith [mul_pos hη h2]
  exact mul_pos (pow_pos h1 d) (inv_pos.mpr (pow_pos (mul_pos Real.pi_pos (pow_pos hr 2)) d))

/-- `hsq` invariance: the `H^{-d}` norm of the modulated function is the shifted integral. -/
lemma hsq_modEta_eq {η : ℝᵈ} (f : Lp ℂ 2 (volume : Measure ℝᵈ)) :
    hsq ((memLp_modEta (Lp.memLp f)).toLp (modEta η (f : ℝᵈ → ℂ)))
      = ∫ ξ, (1 + ‖ξ‖ ^ 2) ^ (-(d : ℝ)) *
          ‖((𝓕 f : Lp ℂ 2 (volume : Measure ℝᵈ)) : ℝᵈ → ℂ) (ξ - η)‖ ^ 2 := by
  rw [hsq]
  refine integral_congr_ae ?_
  filter_upwards [fourier_modEta (η := η) (Lp.memLp f)] with ξ hξ
  rw [hξ, Lp.toLp_coeFn f (Lp.memLp f)]


/-! ## The low-frequency window -/

/-- The multiplier `𝓕φ` (pointwise Fourier transform of the kernel). -/
noncomputable def winW (φ : ℝᵈ → ℂ) (ξ : ℝᵈ) : ℂ := 𝓕 φ ξ

/-- The shifted Fourier transform `𝓕f(·-η)`. -/
noncomputable def winP (f : Lp ℂ 2 (volume : Measure ℝᵈ)) (η : ℝᵈ) (ξ : ℝᵈ) : ℂ :=
  ((𝓕 f : Lp ℂ 2 (volume : Measure ℝᵈ)) : ℝᵈ → ℂ) (ξ - η)

/-- The low-frequency part of the window integrand. -/
noncomputable def winG1 (f : Lp ℂ 2 (volume : Measure ℝᵈ)) (φ : ℝᵈ → ℂ) (η : ℝᵈ) (R : ℝ) :
    ℝᵈ → ℂ := fun ξ => if l1norm ξ ≤ R then winP f η ξ * winW φ ξ else 0

/-- The high-frequency part of the window integrand. -/
noncomputable def winG2 (f : Lp ℂ 2 (volume : Measure ℝᵈ)) (φ : ℝᵈ → ℂ) (η : ℝᵈ) (R : ℝ) :
    ℝᵈ → ℂ := fun ξ => if R < l1norm ξ then winP f η ξ * winW φ ξ else 0

lemma measurable_l1norm : Measurable (l1norm : ℝᵈ → ℝ) := by
  rw [show (l1norm : ℝᵈ → ℝ) = fun ξ : ℝᵈ => ∑ i : Fin d, ‖ξ i‖ from rfl]
  fun_prop

lemma measurableSet_le_l1norm (R : ℝ) : MeasurableSet {ξ : ℝᵈ | l1norm ξ ≤ R} :=
  measurableSet_le measurable_l1norm measurable_const

lemma measurableSet_lt_l1norm (R : ℝ) : MeasurableSet {ξ : ℝᵈ | R < l1norm ξ} :=
  measurableSet_lt measurable_const measurable_l1norm

lemma winW_memLp {φ : ℝᵈ → ℂ} (hφ1 : MemLp φ 1 (volume : Measure ℝᵈ))
    (hφ2 : MemLp φ 2 (volume : Measure ℝᵈ)) : MemLp (winW φ) 2 (volume : Measure ℝᵈ) := by
  have h := Commons.Analysis.Fourier.fourier_toLp_ae_eq_fourier_of_memLp (V := ℝᵈ) hφ1 hφ2
  have h' : ((𝓕 (hφ2.toLp φ) : Lp ℂ 2 (volume : Measure ℝᵈ)) : ℝᵈ → ℂ) =ᵐ[volume] winW φ := by
    refine h.trans (Filter.EventuallyEq.of_eq ?_)
    funext ξ
    exact show 𝓕 φ ξ = winW φ ξ from rfl
  exact (Lp.memLp (𝓕 (hφ2.toLp φ))).ae_eq h'

lemma winP_memLp (f : Lp ℂ 2 (volume : Measure ℝᵈ)) (η : ℝᵈ) :
    MemLp (winP f η) 2 (volume : Measure ℝᵈ) := by
  have h := fourier_modEta (η := η) (Lp.memLp f)
  have h2 : ((𝓕 ((Lp.memLp f).toLp (f : ℝᵈ → ℂ)) :
      Lp ℂ 2 (volume : Measure ℝᵈ)) : ℝᵈ → ℂ)
      = ((𝓕 f : Lp ℂ 2 (volume : Measure ℝᵈ)) : ℝᵈ → ℂ) := by
    rw [Lp.toLp_coeFn f (Lp.memLp f)]
  have hae : ((𝓕 ((memLp_modEta (η := η) (Lp.memLp f)).toLp
      (modEta η (f : ℝᵈ → ℂ))) : Lp ℂ 2 (volume : Measure ℝᵈ)) : ℝᵈ → ℂ)
      =ᵐ[volume] winP f η := by
    refine h.trans (Filter.EventuallyEq.of_eq ?_)
    funext ξ
    rw [h2]
    exact show ((𝓕 f : Lp ℂ 2 (volume : Measure ℝᵈ)) : ℝᵈ → ℂ) (ξ - η) = winP f η ξ from rfl
  exact (Lp.memLp _).ae_eq hae

lemma winW_bound {φ : ℝᵈ → ℂ}
    (hφw : ∀ᵐ ξ ∂(volume : Measure ℝᵈ), ‖winW φ ξ‖ ≤ (1 + ‖ξ‖ ^ 2) ^ (-(d : ℝ) / 2)) :
    ∀ᵐ ξ ∂(volume : Measure ℝᵈ), ‖winW φ ξ‖ ≤ 1 := by
  filter_upwards [hφw] with ξ hξ
  refine hξ.trans ?_
  calc (1 + ‖ξ‖ ^ 2) ^ (-(d : ℝ) / 2) ≤ (1 + ‖ξ‖ ^ 2) ^ (0 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith [sq_nonneg ‖ξ‖]) (by
          linarith [Nat.cast_nonneg (α := ℝ) d])
    _ = 1 := Real.rpow_zero _

/-- The a.e. `H^{-d}` bound upgrades to an all-`ξ` bound, by continuity of `𝓕φ` for
`φ ∈ L¹`. -/
lemma winW_le_one {φ : ℝᵈ → ℂ} (hφ1 : MemLp φ 1 (volume : Measure ℝᵈ))
    (hφw : ∀ᵐ ξ ∂(volume : Measure ℝᵈ), ‖winW φ ξ‖ ≤ (1 + ‖ξ‖ ^ 2) ^ (-(d : ℝ) / 2)) :
    ∀ ξ : ℝᵈ, ‖winW φ ξ‖ ≤ 1 := by
  have hcont : Continuous (fun ξ : ℝᵈ => 𝓕 φ ξ) :=
    VectorFourier.fourierIntegral_continuous (E := ℂ) (V := ℝᵈ) (W := ℝᵈ)
      (e := Real.fourierChar) (μ := (volume : Measure ℝᵈ)) (L := innerₗ ℝᵈ)
      Real.continuous_fourierChar continuous_inner (memLp_one_iff_integrable.mp hφ1)
  have hweight : Continuous (fun ξ : ℝᵈ => (1 + ‖ξ‖ ^ 2) ^ (-(d : ℝ) / 2)) :=
    (continuous_const.add (continuous_norm.pow 2)).rpow_const
      (fun x => Or.inl (by
        have h : (0 : ℝ) < 1 + ‖x‖ ^ 2 := by positivity
        simpa only [Pi.add_apply, Pi.pow_apply] using ne_of_gt h))
  have hclosed : IsClosed {ξ : ℝᵈ | ‖𝓕 φ ξ‖ ≤ (1 + ‖ξ‖ ^ 2) ^ (-(d : ℝ) / 2)} :=
    isClosed_le (continuous_norm.comp hcont) hweight
  have hae : {ξ : ℝᵈ | ‖𝓕 φ ξ‖ ≤ (1 + ‖ξ‖ ^ 2) ^ (-(d : ℝ) / 2)} =ᵐ[volume] univ := by
    have h : ∀ᵐ ξ ∂(volume : Measure ℝᵈ),
        ξ ∈ {ξ : ℝᵈ | ‖𝓕 φ ξ‖ ≤ (1 + ‖ξ‖ ^ 2) ^ (-(d : ℝ) / 2)} := by
      filter_upwards [hφw] with ξ hξ
      simpa only [winW] using hξ
    exact (ae_eq_univ).mpr ((ae_iff).mp h)
  have hall := (hclosed.ae_eq_univ_iff_eq).mp hae
  intro ξ
  have hξ : ξ ∈ {ξ : ℝᵈ | ‖𝓕 φ ξ‖ ≤ (1 + ‖ξ‖ ^ 2) ^ (-(d : ℝ) / 2)} := by
    rw [hall]; trivial
  refine hξ.trans ?_
  calc (1 + ‖ξ‖ ^ 2) ^ (-(d : ℝ) / 2) ≤ (1 + ‖ξ‖ ^ 2) ^ (0 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith [sq_nonneg ‖ξ‖]) (by
          linarith [Nat.cast_nonneg (α := ℝ) d])
    _ = 1 := Real.rpow_zero _

lemma winPW_memLp {f : Lp ℂ 2 (volume : Measure ℝᵈ)} {φ : ℝᵈ → ℂ} {η : ℝᵈ}
    (hP : MemLp (winP f η) 2 (volume : Measure ℝᵈ))
    (hW : MemLp (winW φ) 2 (volume : Measure ℝᵈ))
    (hWb : ∀ᵐ ξ ∂(volume : Measure ℝᵈ), ‖winW φ ξ‖ ≤ 1) :
    MemLp (fun ξ => winP f η ξ * winW φ ξ) 2 (volume : Measure ℝᵈ) := by
  refine MemLp.of_le hP (hP.aestronglyMeasurable.mul hW.aestronglyMeasurable) ?_
  filter_upwards [hWb] with ξ hξ
  rw [norm_mul]
  calc ‖winP f η ξ‖ * ‖winW φ ξ‖ ≤ ‖winP f η ξ‖ * 1 :=
        mul_le_mul_of_nonneg_left hξ (norm_nonneg _)
    _ = ‖winP f η ξ‖ := mul_one _

lemma winG1_eq_indicator (f : Lp ℂ 2 (volume : Measure ℝᵈ)) (φ : ℝᵈ → ℂ) (η : ℝᵈ) (R : ℝ) :
    winG1 f φ η R
      = {ξ : ℝᵈ | l1norm ξ ≤ R}.indicator (fun ξ => winP f η ξ * winW φ ξ) := by
  funext ξ
  rw [winG1, Set.indicator_apply]
  by_cases h : ξ ∈ {ξ : ℝᵈ | l1norm ξ ≤ R}
  · rw [if_pos h, if_pos (show l1norm ξ ≤ R from h)]
  · rw [if_neg h, if_neg (show ¬(l1norm ξ ≤ R) from h)]

lemma winG2_eq_indicator (f : Lp ℂ 2 (volume : Measure ℝᵈ)) (φ : ℝᵈ → ℂ) (η : ℝᵈ) (R : ℝ) :
    winG2 f φ η R
      = {ξ : ℝᵈ | R < l1norm ξ}.indicator (fun ξ => winP f η ξ * winW φ ξ) := by
  funext ξ
  rw [winG2, Set.indicator_apply]
  by_cases h : ξ ∈ {ξ : ℝᵈ | R < l1norm ξ}
  · rw [if_pos h, if_pos (show R < l1norm ξ from h)]
  · rw [if_neg h, if_neg (show ¬(R < l1norm ξ) from h)]

lemma winG_split (f : Lp ℂ 2 (volume : Measure ℝᵈ)) (φ : ℝᵈ → ℂ) (η : ℝᵈ) (R : ℝ) :
    ∀ ξ, winG1 f φ η R ξ + winG2 f φ η R ξ = winP f η ξ * winW φ ξ := by
  intro ξ
  rw [winG1, winG2]
  by_cases hξ : l1norm ξ ≤ R
  · rw [if_pos hξ, if_neg (not_lt.mpr hξ), add_zero]
  · rw [if_neg hξ, if_pos (not_le.mp hξ), zero_add]

lemma winG_normSq_split (f : Lp ℂ 2 (volume : Measure ℝᵈ)) (φ : ℝᵈ → ℂ) (η : ℝᵈ) (R : ℝ) :
    ∀ ξ, ‖winG1 f φ η R ξ + winG2 f φ η R ξ‖ ^ 2
      = ‖winG1 f φ η R ξ‖ ^ 2 + ‖winG2 f φ η R ξ‖ ^ 2 := by
  intro ξ
  rw [winG1, winG2]
  by_cases hξ : l1norm ξ ≤ R
  · rw [if_pos hξ, if_neg (not_lt.mpr hξ), add_zero, norm_zero]
    ring
  · rw [if_neg hξ, if_pos (not_le.mp hξ), zero_add, norm_zero]
    ring

lemma winG1_eq_zero {f : Lp ℂ 2 (volume : Measure ℝᵈ)} {φ : ℝᵈ → ℂ} {η : ℝᵈ} {R : ℝ} {ξ : ℝᵈ}
    (h : R < l1norm ξ) : winG1 f φ η R ξ = 0 := by
  rw [winG1]; exact if_neg (not_le.mpr h)

lemma winG2_eq_zero {f : Lp ℂ 2 (volume : Measure ℝᵈ)} {φ : ℝᵈ → ℂ} {η : ℝᵈ} {R : ℝ} {ξ : ℝᵈ}
    (h : l1norm ξ ≤ R) : winG2 f φ η R ξ = 0 := by
  rw [winG2]; exact if_neg (not_lt.mpr h)

/-- The high-frequency part of the window integrand is bounded by the truncation constant
`e^{-c₃Θ(R)R}⟨R⟩^d`, modulo the `H^{-d}` norm of the modulated function. -/
theorem window_high_le {c₃ α R : ℝ} (hc₃ : 0 < c₃) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hR : (2 * (d : ℝ) / c₃) ^ 2 ≤ R)
    {φ : ℝᵈ → ℂ} (hφ1 : MemLp φ 1 (volume : Measure ℝᵈ))
    (hφ2 : MemLp φ 2 (volume : Measure ℝᵈ))
    (hφw : ∀ᵐ ξ ∂(volume : Measure ℝᵈ), ‖winW φ ξ‖ ≤ (1 + ‖ξ‖ ^ 2) ^ (-(d : ℝ) / 2))
    {f : Lp ℂ 2 (volume : Measure ℝᵈ)} {η : ℝᵈ}
    (hdec : ∀ᵐ ξ ∂(volume : Measure ℝᵈ), winP f η ξ ≠ 0 →
        ‖winW φ ξ‖ ≤ Real.exp (-(c₃ * l1norm ξ / (Real.log (2 + l1norm ξ)) ^ α))) :
    ∫ ξ, ‖winG2 f φ η R ξ‖ ^ 2
      ≤ (truncBeta d c₃ α R) ^ 2 *
        hsq ((memLp_modEta (η := η) (Lp.memLp f)).toLp (modEta η (f : ℝᵈ → ℂ))) := by
  classical
  set g : Lp ℂ 2 (volume : Measure ℝᵈ) :=
    (memLp_modEta (η := η) (Lp.memLp f)).toLp (modEta η (f : ℝᵈ → ℂ)) with hg
  have hP : MemLp (winP f η) 2 (volume : Measure ℝᵈ) := winP_memLp f η
  have hW : MemLp (winW φ) 2 (volume : Measure ℝᵈ) := winW_memLp hφ1 hφ2
  have hWb : ∀ᵐ ξ ∂(volume : Measure ℝᵈ), ‖winW φ ξ‖ ≤ 1 := winW_bound (d := d) hφw
  have hPW : MemLp (fun ξ => winP f η ξ * winW φ ξ) 2 (volume : Measure ℝᵈ) :=
    winPW_memLp hP hW hWb
  have hPdec : ∀ᵐ ξ ∂(volume : Measure ℝᵈ), winP f η ξ ≠ 0 →
      ‖winW φ ξ‖ ≤ Real.exp (-(c₃ * (∑ i : Fin d, |ξ i|) /
        (Real.log (2 + (∑ i : Fin d, |ξ i|))) ^ α)) := by
    filter_upwards [hdec] with ξ hξ hne
    exact hξ hne
  have hmain := Commons.Analysis.Fourier.truncation_high_le (d := d) hc₃ hα0 hα1 hR
    (winP f η) (winW φ) hP hPW hPdec
  have hae : ((𝓕 g : Lp ℂ 2 (volume : Measure ℝᵈ)) : ℝᵈ → ℂ) =ᵐ[volume] winP f η := by
    have h := fourier_modEta (η := η) (Lp.memLp f)
    have h2 : ((𝓕 ((Lp.memLp f).toLp (f : ℝᵈ → ℂ)) :
        Lp ℂ 2 (volume : Measure ℝᵈ)) : ℝᵈ → ℂ)
        = ((𝓕 f : Lp ℂ 2 (volume : Measure ℝᵈ)) : ℝᵈ → ℂ) := by
      rw [Lp.toLp_coeFn f (Lp.memLp f)]
    refine h.trans (Filter.EventuallyEq.of_eq ?_)
    funext ξ
    rw [h2]
    exact show ((𝓕 f : Lp ℂ 2 (volume : Measure ℝᵈ)) : ℝᵈ → ℂ) (ξ - η) = winP f η ξ from rfl
  have hB : (∫ ξ, (1 + ‖ξ‖ ^ 2) ^ (-(d : ℝ)) * ‖winP f η ξ‖ ^ 2) = hsq g := by
    rw [hsq]
    refine integral_congr_ae ?_
    filter_upwards [hae] with ξ hξ
    rw [hξ]
  have hbeta : truncBeta d c₃ α R
      = Real.exp (-(c₃ * R / (Real.log (2 + R)) ^ α)) * (1 + R ^ 2) ^ ((d : ℝ) / 2) := rfl
  have hsq2 : (∫ ξ, ‖winG2 f φ η R ξ‖ ^ 2)
      = ∫ ξ, ‖(if R < (∑ i : Fin d, |ξ i|) then winP f η ξ * winW φ ξ else 0)‖ ^ 2 := by
    congr 1
  rw [hsq2, ← hB, hbeta]
  exact hmain

/-! ## The low-frequency part -/


/-- `‖(r : ℂ) * z‖² = r²‖z‖²` for `0 ≤ r`. -/
@[simp] lemma normSq_ofReal_mul {r : ℝ} (hr : 0 ≤ r) (z : ℂ) :
    ‖((r : ℝ) : ℂ) * z‖ ^ 2 = r ^ 2 * ‖z‖ ^ 2 := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr, mul_pow]

/-- **P4, low-frequency part.**  The `H^{-d}`-type `κ`-interpolated bound for
`∫ ‖winG1‖²`. -/
theorem window_low_le {q ε δ H ηL r c₁ c₃ α R : ℝ} (hd : 1 ≤ d)
    (hq : 0 < q) (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 2) (hδ0 : 0 < δ) (hδ3 : δ < 1 / 3)
    (hH0 : 0 < H) (hH1 : H ≤ 1) (hηL0 : 0 < ηL) (hc₁ : 0 < c₁) (hr0 : 0 < r)
    (hητ : 1 ≤ ηL * phiLens q ε (1 - 3 * δ))
    (hIbig : ENNReal.ofReal ((ηL * zpLamMax q ε) ^ d * (2 * (20 ^ d * H)))
      ≤ ENNReal.ofReal ((c₁ / 2) ^ d))
    (hc₃ : 0 < c₃) (hα0 : 0 < α) (hα1 : α ≤ 1) (hR0 : 0 < R) (hR1 : 1 ≤ R)
    (hRc : (2 * (d : ℝ) / c₃) ^ 2 ≤ R)
    (hQ4 : 4 * Real.pi * windowQ ηL q r ≤ c₃ * (Real.log (2 + R)) ^ (-α))
    {φ : ℝᵈ → ℂ} (hφ1 : MemLp φ 1 (volume : Measure ℝᵈ)) (hφ2 : MemLp φ 2 (volume : Measure ℝᵈ))
    (hφsupp : ∀ᵐ z ∂(volume : Measure ℝᵈ), (∃ i : Fin d, c₁ / 2 < |z i|) → φ z = 0)
    (hφw : ∀ᵐ ξ ∂(volume : Measure ℝᵈ), ‖winW φ ξ‖ ≤ (1 + ‖ξ‖ ^ 2) ^ (-(d : ℝ) / 2))
    {f : Lp ℂ 2 (volume : Measure ℝᵈ)} {ηm : ℝᵈ} (hηm : ∀ i : Fin d, |ηm i| ≤ 2)
    (hdec : ∀ᵐ ξ ∂(volume : Measure ℝᵈ), winP f ηm ξ ≠ 0 →
        ‖winW φ ξ‖ ≤ Real.exp (-(c₃ * l1norm ξ / (Real.log (2 + l1norm ξ)) ^ α)))
    {γ : ℝᵈ} {a : (Fin d → ℤ) → Fin d → ℝ}
    (ha : ∀ n : Fin d → ℤ, ∀ i : Fin d,
      2 * (n i : ℝ) + γ i ≤ a n i ∧ a n i + 2 * c₁ ≤ 2 * (n i : ℝ) + γ i + 2) :
    ∫ ξ, ‖winG1 f φ ηm R ξ‖ ^ 2
      ≤ cellZConst q ε δ H ηL (c₁ / 4) d
        * (windowD d q ε ηL r * ((2 * windowQ ηL q r) ^ d * ((1 + R ^ 2) ^ d
            * (windowCW d * hsq f)))) ^ (1 - zpKappa δ H d)
        * (2 * (windowCW d) ^ 2 * hsq (subLp (locCubes c₁ a) f (measurableSet_locCubes c₁ a))
            + 2 * (truncBeta d c₃ α R) ^ 2 * (windowCW d) ^ 2 * hsq f) ^ (zpKappa δ H d) := by
  classical
  set Q : ℝ := windowQ ηL q r with hQdef
  have hQpos : 0 < Q := by rw [hQdef, windowQ]; positivity
  have hκ0 : 0 < zpKappa δ H d := by
    rw [zpKappa]; exact pow_pos (twoConstKappa_mem hδ0 hδ3 hH0 hH1).1 d
  have hκ1' : zpKappa δ H d ≤ 1 := by
    rw [zpKappa]
    calc twoConstKappa δ H ^ d ≤ 1 ^ d :=
          pow_le_pow_left₀ (le_of_lt (twoConstKappa_mem hδ0 hδ3 hH0 hH1).1)
            (twoConstKappa_mem hδ0 hδ3 hH0 hH1).2 d
      _ = 1 := one_pow d
  have hSmeas : MeasurableSet (locCubes c₁ a) := measurableSet_locCubes c₁ a
  -- ### the basic L² classes
  have hP : MemLp (winP f ηm) 2 (volume : Measure ℝᵈ) := winP_memLp f ηm
  have hW : MemLp (winW φ) 2 (volume : Measure ℝᵈ) := winW_memLp hφ1 hφ2
  have hWb : ∀ᵐ ξ ∂(volume : Measure ℝᵈ), ‖winW φ ξ‖ ≤ 1 := winW_bound (d := d) hφw
  have hW1 : ∀ ξ : ℝᵈ, ‖winW φ ξ‖ ≤ 1 := winW_le_one hφ1 hφw
  have hPW : MemLp (fun ξ => winP f ηm ξ * winW φ ξ) 2 (volume : Measure ℝᵈ) :=
    winPW_memLp hP hW hWb
  have hG1 : MemLp (winG1 f φ ηm R) 2 (volume : Measure ℝᵈ) := by
    rw [winG1_eq_indicator]; exact hPW.indicator (measurableSet_le_l1norm R)
  have hG2 : MemLp (winG2 f φ ηm R) 2 (volume : Measure ℝᵈ) := by
    rw [winG2_eq_indicator]; exact hPW.indicator (measurableSet_lt_l1norm R)
  set g : Lp ℂ 2 (volume : Measure ℝᵈ) :=
    (memLp_modEta (η := ηm) (Lp.memLp f)).toLp (modEta ηm (f : ℝᵈ → ℂ)) with hg
  have hPae : ((𝓕 g : Lp ℂ 2 (volume : Measure ℝᵈ)) : ℝᵈ → ℂ) =ᵐ[volume] winP f ηm := by
    have h := fourier_modEta (η := ηm) (Lp.memLp f)
    have h2 : ((𝓕 ((Lp.memLp f).toLp (f : ℝᵈ → ℂ)) : Lp ℂ 2 (volume : Measure ℝᵈ)) : ℝᵈ → ℂ)
        = ((𝓕 f : Lp ℂ 2 (volume : Measure ℝᵈ)) : ℝᵈ → ℂ) := by
      rw [Lp.toLp_coeFn f (Lp.memLp f)]
    rw [hg]
    refine h.trans (Filter.EventuallyEq.of_eq ?_)
    funext ξ
    rw [h2]
    exact show ((𝓕 f : Lp ℂ 2 (volume : Measure ℝᵈ)) : ℝᵈ → ℂ) (ξ - ηm) = winP f ηm ξ from rfl
  have hPq : (∫ ξ, (1 + ‖ξ‖ ^ 2) ^ (-(d : ℝ)) * ‖winP f ηm ξ‖ ^ 2) = hsq g := by
    rw [hsq]
    refine integral_congr_ae ?_
    filter_upwards [hPae] with ξ hξ
    rw [hξ]
  have hgsq : hsq g ≤ windowCW d * hsq f := by
    have h := hsq_modEta_le (η := ηm) hηm f
    rw [hg, windowCW]
    exact h
  -- ### the two halves
  set G1lp : Lp ℂ 2 (volume : Measure ℝᵈ) := hG1.toLp (winG1 f φ ηm R) with hG1lp
  set G2lp : Lp ℂ 2 (volume : Measure ℝᵈ) := hG2.toLp (winG2 f φ ηm R) with hG2lp
  set ELp : Lp ℂ 2 (volume : Measure ℝᵈ) := 𝓕⁻ G1lp with hELp
  set E2Lp : Lp ℂ 2 (volume : Measure ℝᵈ) := 𝓕⁻ G2lp with hE2Lp
  have hELp_ft : (𝓕 ELp : Lp ℂ 2 (volume : Measure ℝᵈ)) = G1lp := by
    rw [hELp]; exact fourier_fourierInv_eq G1lp
  have hE2Lp_ft : (𝓕 E2Lp : Lp ℂ 2 (volume : Measure ℝᵈ)) = G2lp := by
    rw [hE2Lp]; exact fourier_fourierInv_eq G2lp
  have hELp_coe : ((𝓕 ELp : Lp ℂ 2 (volume : Measure ℝᵈ)) : ℝᵈ → ℂ)
      =ᵐ[volume] winG1 f φ ηm R := by
    rw [hELp_ft, hG1lp]; exact MemLp.coeFn_toLp hG1
  have hE2Lp_coe : ((𝓕 E2Lp : Lp ℂ 2 (volume : Measure ℝᵈ)) : ℝᵈ → ℂ)
      =ᵐ[volume] winG2 f φ ηm R := by
    rw [hE2Lp_ft, hG2lp]; exact MemLp.coeFn_toLp hG2
  -- ### the convolution class
  set cLp : Lp ℂ 2 (volume : Measure ℝᵈ) :=
    (Commons.Analysis.Fourier.memLp_convFun_two (Lp.memLp g)
      (integrable_of_memLp_one hφ1)).toLp (Commons.Analysis.Fourier.convFun (g : ℝᵈ → ℂ) φ)
    with hcLp
  have hcft : ((𝓕 cLp : Lp ℂ 2 (volume : Measure ℝᵈ)) : ℝᵈ → ℂ)
      =ᵐ[volume] (fun ξ => winP f ηm ξ * winW φ ξ) := by
    have h := Commons.Analysis.Fourier.fourier_convFun_ae d (f := (g : ℝᵈ → ℂ)) (φ := φ)
      (A := 1) (Lp.memLp g) (integrable_of_memLp_one hφ1) hφ2 (fun ξ => by
        exact show ‖𝓕 φ ξ‖ ≤ (1 : ℝ) from hW1 ξ)
    rw [hcLp]
    refine h.trans ?_
    have h2 : ((Lp.memLp g).toLp (g : ℝᵈ → ℂ)) = g := Lp.toLp_coeFn g (Lp.memLp g)
    filter_upwards [hPae] with ξ hξ
    rw [h2, hξ]
    rfl
  have hcLp_eq : (𝓕 cLp : Lp ℂ 2 (volume : Measure ℝᵈ))
      = hPW.toLp (fun ξ => winP f ηm ξ * winW φ ξ) := by
    refine Lp.ext ?_
    filter_upwards [hcft, MemLp.coeFn_toLp hPW] with ξ h1 h2
    rw [h1, h2]
  have hsum : ELp + E2Lp = cLp := by
    have h12 : G1lp + G2lp = hPW.toLp (fun ξ => winP f ηm ξ * winW φ ξ) := by
      rw [hG1lp, hG2lp, ← MemLp.toLp_add hG1 hG2]
      refine MemLp.toLp_congr _ _ ?_
      exact Filter.Eventually.of_forall (fun ξ => winG_split f φ ηm R ξ)
    have hkey : (𝓕 (ELp + E2Lp) : Lp ℂ 2 (volume : Measure ℝᵈ)) = (𝓕 cLp : Lp ℂ 2 (volume : Measure ℝᵈ)) := by
      rw [FourierAdd.fourier_add, hELp_ft, hE2Lp_ft, h12, hcLp_eq]
    calc ELp + E2Lp = 𝓕⁻ (𝓕 (ELp + E2Lp)) := (fourierInv_fourier_eq _).symm
      _ = 𝓕⁻ (𝓕 cLp) := by rw [hkey]
      _ = cLp := fourierInv_fourier_eq _
  have hELp_sub : (ELp : ℝᵈ → ℂ) =ᵐ[volume] (cLp : ℝᵈ → ℂ) - (E2Lp : ℝᵈ → ℂ) := by
    have h1 : ELp = cLp - E2Lp := by
      rw [← hsum]; abel
    rw [h1]
    exact Lp.coeFn_sub cLp E2Lp
  -- ### the local bound
  have hloc_pt : ∀ᵐ x ∂(volume : Measure ℝᵈ),
      ENNReal.ofReal (‖(ELp : ℝᵈ → ℂ) x‖ ^ 2)
        ≤ ENNReal.ofReal (2 * ‖(cLp : ℝᵈ → ℂ) x‖ ^ 2)
          + ENNReal.ofReal (2 * ‖(E2Lp : ℝᵈ → ℂ) x‖ ^ 2) := by
    filter_upwards [hELp_sub] with x hx
    rw [hx]
    have h1 : ‖(cLp : ℝᵈ → ℂ) x - (E2Lp : ℝᵈ → ℂ) x‖
        ≤ ‖(cLp : ℝᵈ → ℂ) x‖ + ‖(E2Lp : ℝᵈ → ℂ) x‖ := by
      exact norm_sub_le ((cLp : ℝᵈ → ℂ) x) ((E2Lp : ℝᵈ → ℂ) x)
    have h2 : ‖(cLp : ℝᵈ → ℂ) x - (E2Lp : ℝᵈ → ℂ) x‖ ^ 2
        ≤ (‖(cLp : ℝᵈ → ℂ) x‖ + ‖(E2Lp : ℝᵈ → ℂ) x‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h1 2
    have h3 : (‖(cLp : ℝᵈ → ℂ) x‖ + ‖(E2Lp : ℝᵈ → ℂ) x‖) ^ 2
        ≤ 2 * ‖(cLp : ℝᵈ → ℂ) x‖ ^ 2 + 2 * ‖(E2Lp : ℝᵈ → ℂ) x‖ ^ 2 := by
      nlinarith [sq_nonneg (‖(cLp : ℝᵈ → ℂ) x‖ - ‖(E2Lp : ℝᵈ → ℂ) x‖)]
    calc ENNReal.ofReal (‖(cLp : ℝᵈ → ℂ) x - (E2Lp : ℝᵈ → ℂ) x‖ ^ 2)
        ≤ ENNReal.ofReal (2 * ‖(cLp : ℝᵈ → ℂ) x‖ ^ 2 + 2 * ‖(E2Lp : ℝᵈ → ℂ) x‖ ^ 2) :=
          ENNReal.ofReal_le_ofReal (h2.trans h3)
      _ = ENNReal.ofReal (2 * ‖(cLp : ℝᵈ → ℂ) x‖ ^ 2)
            + ENNReal.ofReal (2 * ‖(E2Lp : ℝᵈ → ℂ) x‖ ^ 2) :=
          ENNReal.ofReal_add (by positivity) (by positivity)
  have hloc1 : ∫⁻ x in locCubesSmall c₁ a,
      ENNReal.ofReal (‖Commons.Analysis.Fourier.convFun (g : ℝᵈ → ℂ) φ x‖ ^ 2)
      ≤ ENNReal.ofReal (hsq (subLp (locCubes c₁ a) g hSmeas)) :=
    localisation_bound (d := d) hc₁ hφ1 hφ2 hφsupp hW1 hφw a g
  have hcLp_ae : (cLp : ℝᵈ → ℂ)
      =ᵐ[volume] Commons.Analysis.Fourier.convFun (g : ℝᵈ → ℂ) φ := by
    rw [hcLp]; exact MemLp.coeFn_toLp _
  have hE2int : Integrable (fun x : ℝᵈ => ‖(E2Lp : ℝᵈ → ℂ) x‖ ^ 2) volume :=
    (memLp_two_iff_integrable_sq_norm (Lp.memLp E2Lp).aestronglyMeasurable).mp (Lp.memLp E2Lp)
  have hE2sq : ∫ x, ‖(E2Lp : ℝᵈ → ℂ) x‖ ^ 2 ≤ (truncBeta d c₃ α R) ^ 2 * hsq g := by
    rw [← norm_sq_eq_integral E2Lp, ← MeasureTheory.Lp.norm_fourier_eq E2Lp, hE2Lp_ft, hG2lp,
      norm_sq_eq_integral (hG2.toLp (winG2 f φ ηm R)), hg]
    have h := window_high_le (d := d) hc₃ hα0 hα1 hRc hφ1 hφ2 hφw (η := ηm) hdec
    refine le_trans (le_of_eq ?_) h
    refine integral_congr_ae ?_
    filter_upwards [MemLp.coeFn_toLp hG2] with ξ hξ
    rw [hξ]
  have hloc : ∫⁻ x in locCubesSmall c₁ a, ENNReal.ofReal (‖(ELp : ℝᵈ → ℂ) x‖ ^ 2)
      ≤ ENNReal.ofReal (2 * windowCW d
            * hsq (subLp (locCubes c₁ a) g hSmeas)
          + 2 * ((truncBeta d c₃ α R) ^ 2 * hsq g)) := by
    have hstep1 : ∫⁻ x in locCubesSmall c₁ a, ENNReal.ofReal (‖(ELp : ℝᵈ → ℂ) x‖ ^ 2)
        ≤ ∫⁻ x in locCubesSmall c₁ a,
            (ENNReal.ofReal (2 * ‖(cLp : ℝᵈ → ℂ) x‖ ^ 2)
              + ENNReal.ofReal (2 * ‖(E2Lp : ℝᵈ → ℂ) x‖ ^ 2)) := by
      refine lintegral_mono_ae ?_
      rw [ae_restrict_iff' (measurableSet_locCubesSmall c₁ a)]
      filter_upwards [hloc_pt] with x hx _
      exact hx
    have hmeas1 : AEMeasurable
        (fun x : ℝᵈ => ENNReal.ofReal (2 * ‖(cLp : ℝᵈ → ℂ) x‖ ^ 2))
        (volume.restrict (locCubesSmall c₁ a)) := by
      have h1 : AEMeasurable (fun x : ℝᵈ => ‖(cLp : ℝᵈ → ℂ) x‖ ^ 2)
          (volume : Measure ℝᵈ) :=
        (Lp.memLp cLp).aestronglyMeasurable.aemeasurable.norm.pow_const 2
      exact ((h1.const_mul 2).ennreal_ofReal).mono_measure Measure.restrict_le_self
    have hsplit : ∫⁻ x in locCubesSmall c₁ a,
          (ENNReal.ofReal (2 * ‖(cLp : ℝᵈ → ℂ) x‖ ^ 2)
            + ENNReal.ofReal (2 * ‖(E2Lp : ℝᵈ → ℂ) x‖ ^ 2))
        = (∫⁻ x in locCubesSmall c₁ a, ENNReal.ofReal (2 * ‖(cLp : ℝᵈ → ℂ) x‖ ^ 2))
          + ∫⁻ x in locCubesSmall c₁ a,
              ENNReal.ofReal (2 * ‖(E2Lp : ℝᵈ → ℂ) x‖ ^ 2) :=
      lintegral_add_left' hmeas1 _
    have hmul1 : (fun x : ℝᵈ => ENNReal.ofReal (2 * ‖(cLp : ℝᵈ → ℂ) x‖ ^ 2))
        = fun x => (2 : ℝ≥0∞) * ENNReal.ofReal (‖(cLp : ℝᵈ → ℂ) x‖ ^ 2) := by
      funext x
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num
    have hmul2 : (fun x : ℝᵈ => ENNReal.ofReal (2 * ‖(E2Lp : ℝᵈ → ℂ) x‖ ^ 2))
        = fun x => (2 : ℝ≥0∞) * ENNReal.ofReal (‖(E2Lp : ℝᵈ → ℂ) x‖ ^ 2) := by
      funext x
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num
    have hA2 : (∫⁻ x in locCubesSmall c₁ a,
          ENNReal.ofReal (2 * ‖(cLp : ℝᵈ → ℂ) x‖ ^ 2))
        ≤ ENNReal.ofReal (2 * windowCW d * hsq (subLp (locCubes c₁ a) g hSmeas)) := by
      have hbase : ∫⁻ x in locCubesSmall c₁ a, ENNReal.ofReal (‖(cLp : ℝᵈ → ℂ) x‖ ^ 2)
          ≤ ENNReal.ofReal (hsq (subLp (locCubes c₁ a) g hSmeas)) := by
        refine le_trans (le_of_eq ?_) hloc1
        refine lintegral_congr_ae ?_
        filter_upwards [MeasureTheory.ae_restrict_of_ae hcLp_ae] with x hx
        rw [hx]
      rw [hmul1, lintegral_const_mul' 2 _ (by simp)]
      have hCW1' : (1 : ℝ) ≤ windowCW d := by
        rw [windowCW]
        calc (1 : ℝ) = 1 ^ d := (one_pow d).symm
          _ ≤ (40 * ((d : ℝ) + 1)) ^ d :=
              pow_le_pow_left₀ (by norm_num) (by linarith [Nat.cast_nonneg (α := ℝ) d]) d
      calc (2 : ℝ≥0∞) * ∫⁻ x in locCubesSmall c₁ a,
              ENNReal.ofReal (‖(cLp : ℝᵈ → ℂ) x‖ ^ 2)
          ≤ (2 : ℝ≥0∞) * ENNReal.ofReal (hsq (subLp (locCubes c₁ a) g hSmeas)) :=
            mul_le_mul' le_rfl hbase
        _ = ENNReal.ofReal (2 * hsq (subLp (locCubes c₁ a) g hSmeas)) := by
            rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 from by norm_num,
              ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
        _ ≤ ENNReal.ofReal (2 * windowCW d * hsq (subLp (locCubes c₁ a) g hSmeas)) := by
            refine ENNReal.ofReal_le_ofReal ?_
            nlinarith [hsq_nonneg (subLp (locCubes c₁ a) g hSmeas), hCW1']
    have hB2 : (∫⁻ x in locCubesSmall c₁ a,
          ENNReal.ofReal (2 * ‖(E2Lp : ℝᵈ → ℂ) x‖ ^ 2))
        ≤ ENNReal.ofReal (2 * ((truncBeta d c₃ α R) ^ 2 * hsq g)) := by
      rw [hmul2, lintegral_const_mul' 2 _ (by simp)]
      calc (2 : ℝ≥0∞) * ∫⁻ x in locCubesSmall c₁ a,
              ENNReal.ofReal (‖(E2Lp : ℝᵈ → ℂ) x‖ ^ 2)
          ≤ (2 : ℝ≥0∞) * ENNReal.ofReal ((truncBeta d c₃ α R) ^ 2 * hsq g) := by
            refine mul_le_mul' le_rfl ?_
            refine le_trans (lintegral_mono_set (subset_univ _)) ?_
            rw [Measure.restrict_univ, ← ofReal_integral_eq_lintegral_ofReal hE2int
              (Filter.Eventually.of_forall (fun x => by positivity))]
            exact ENNReal.ofReal_le_ofReal hE2sq
        _ = ENNReal.ofReal (2 * ((truncBeta d c₃ α R) ^ 2 * hsq g)) := by
            rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 from by norm_num,
              ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    have hn1 : (0 : ℝ) ≤ 2 * windowCW d * hsq (subLp (locCubes c₁ a) g hSmeas) := by
      have := hsq_nonneg (subLp (locCubes c₁ a) g hSmeas)
      have := windowCW_nonneg d
      positivity
    have hn2 : (0 : ℝ) ≤ 2 * ((truncBeta d c₃ α R) ^ 2 * hsq g) := by
      have := hsq_nonneg g
      have := sq_nonneg (truncBeta d c₃ α R)
      positivity
    refine hstep1.trans ?_
    rw [hsplit]
    refine (add_le_add hA2 hB2).trans (le_of_eq ?_)
    exact (ENNReal.ofReal_add hn1 hn2).symm
  have hCW1 : (1 : ℝ) ≤ windowCW d := by
    rw [windowCW]
    calc (1 : ℝ) = 1 ^ d := (one_pow d).symm
      _ ≤ (40 * ((d : ℝ) + 1)) ^ d := by
          exact pow_le_pow_left₀ (by norm_num) (by linarith [Nat.cast_nonneg (α := ℝ) d]) d
  have hlocR : 2 * windowCW d * hsq (subLp (locCubes c₁ a) g hSmeas)
      + 2 * ((truncBeta d c₃ α R) ^ 2 * hsq g)
      ≤ 2 * (windowCW d) ^ 2 * hsq (subLp (locCubes c₁ a) f hSmeas)
        + 2 * (truncBeta d c₃ α R) ^ 2 * (windowCW d) ^ 2 * hsq f := by
    have hsub : hsq (subLp (locCubes c₁ a) g hSmeas)
        ≤ windowCW d * hsq (subLp (locCubes c₁ a) f hSmeas) := by
      have h1 : subLp (locCubes c₁ a) g hSmeas
          = subLp (locCubes c₁ a)
              ((memLp_modEta (η := ηm) (Lp.memLp f)).toLp (modEta ηm (f : ℝᵈ → ℂ))) hSmeas := by
        rw [hg]
      have h2 : (memLp_modEta (η := ηm) ((Lp.memLp f).indicator hSmeas)).toLp
              (modEta ηm ((locCubes c₁ a).indicator (f : ℝᵈ → ℂ)))
          = (memLp_modEta (η := ηm)
              (Lp.memLp (subLp (locCubes c₁ a) f hSmeas))).toLp
              (modEta ηm ((subLp (locCubes c₁ a) f hSmeas : ℝᵈ → ℂ))) := by
        refine MemLp.toLp_congr _ _ ?_
        filter_upwards [subLp_coe (locCubes c₁ a) f hSmeas] with x hx
        rw [modEta, modEta, hx]
      rw [h1, subLp_modEta, h2]
      simpa only [windowCW] using hsq_modEta_le (η := ηm) hηm (subLp (locCubes c₁ a) f hSmeas)
    have hterm1 : 2 * windowCW d * hsq (subLp (locCubes c₁ a) g hSmeas)
        ≤ 2 * (windowCW d) ^ 2 * hsq (subLp (locCubes c₁ a) f hSmeas) := by
      have h := mul_le_mul_of_nonneg_left hsub (by positivity : (0 : ℝ) ≤ 2 * windowCW d)
      calc 2 * windowCW d * hsq (subLp (locCubes c₁ a) g hSmeas)
          ≤ 2 * windowCW d * (windowCW d * hsq (subLp (locCubes c₁ a) f hSmeas)) := h
        _ = 2 * (windowCW d) ^ 2 * hsq (subLp (locCubes c₁ a) f hSmeas) := by ring
    have hterm2 : 2 * (truncBeta d c₃ α R) ^ 2 * hsq g
        ≤ 2 * (truncBeta d c₃ α R) ^ 2 * (windowCW d) ^ 2 * hsq f := by
      have h := mul_le_mul_of_nonneg_left hgsq (by positivity : (0 : ℝ) ≤ 2 * (truncBeta d c₃ α R) ^ 2)
      have hCWs : windowCW d * hsq f ≤ (windowCW d) ^ 2 * hsq f := by
        refine mul_le_mul_of_nonneg_right ?_ (hsq_nonneg f)
        nlinarith
      calc 2 * (truncBeta d c₃ α R) ^ 2 * hsq g
          ≤ 2 * (truncBeta d c₃ α R) ^ 2 * (windowCW d * hsq f) := h
        _ = 2 * (truncBeta d c₃ α R) ^ 2 * (windowCW d * hsq f) := by ring
        _ ≤ 2 * (truncBeta d c₃ α R) ^ 2 * ((windowCW d) ^ 2 * hsq f) :=
            mul_le_mul_of_nonneg_left hCWs
              (by positivity : (0 : ℝ) ≤ 2 * (truncBeta d c₃ α R) ^ 2)
        _ = 2 * (truncBeta d c₃ α R) ^ 2 * (windowCW d) ^ 2 * hsq f := by ring
    linarith
  -- ### the entire extension and the strip bound
  have hH1supp : ∀ᵐ ξ ∂(volume : Measure ℝᵈ),
      ξ ∉ Commons.Analysis.Fourier.LogvinenkoSereda.bandCube d R → winG1 f φ ηm R ξ = 0 := by
    filter_upwards with ξ hnot
    refine winG1_eq_zero ?_
    rw [Commons.Analysis.Fourier.LogvinenkoSereda.bandCube, Set.mem_setOf_eq] at hnot
    simp only [not_forall, not_le] at hnot
    obtain ⟨i, hi⟩ := hnot
    exact lt_of_lt_of_le hi (Finset.single_le_sum (fun j _ => abs_nonneg (ξ j)) (Finset.mem_univ i))
  have hH1_1 : MemLp (winG1 f φ ηm R) 1 (volume : Measure ℝᵈ) :=
    Commons.Analysis.Fourier.LogvinenkoSereda.memLp_one_of_memLp_two_of_ae_support_cube d R
      hG1 hH1supp
  have hH1int : Integrable (winG1 f φ ηm R) := memLp_one_iff_integrable.mp hH1_1
  set FEnt : (Fin d → ℂ) → ℂ :=
    Commons.Analysis.Fourier.LogvinenkoSereda.FT d (winG1 f φ ηm R) with hFEntdef
  have hFdiff : Differentiable ℂ FEnt :=
    Commons.Analysis.Fourier.LogvinenkoSereda.differentiable_FT (winG1 f φ ηm R)
      (le_of_lt hR0) hH1int hH1supp
  have hFana : AnalyticOnNhd ℂ FEnt Set.univ := fun c _ =>
    Commons.Analysis.Fourier.LogvinenkoSereda.analyticAt_FT (winG1 f φ ηm R)
      (le_of_lt hR0) hH1int hH1supp c
  have hFae : (fun x : ℝᵈ => FEnt (fun i => (x i : ℂ))) =ᵐ[volume] (ELp : ℝᵈ → ℂ) := by
    have hpt : ∀ x : ℝᵈ, FEnt (fun i => (x i : ℂ)) = 𝓕⁻ (winG1 f φ ηm R) x := by
      intro x
      rw [hFEntdef, Commons.Analysis.Fourier.LogvinenkoSereda.FT, Real.fourierInv_eq']
      apply integral_congr_ae
      filter_upwards with a
      rw [Commons.Analysis.Fourier.LogvinenkoSereda.phase_iota_eq, mul_comm]
      rfl
    have h2 : (ELp : ℝᵈ → ℂ) =ᵐ[volume] (fun x => 𝓕⁻ (winG1 f φ ηm R) x) := by
      rw [hELp, hG1lp]
      exact Commons.Analysis.Fourier.fourierInv_toLp_ae_eq_fourierInv hH1_1 hG1
    have h1 : (fun x : ℝᵈ => FEnt (fun i => (x i : ℂ))) =ᵐ[volume]
        (fun x => 𝓕⁻ (winG1 f φ ηm R) x) := Filter.Eventually.of_forall hpt
    exact h1.trans h2.symm
  have hband : ∀ᵐ ξ ∂(volume : Measure ℝᵈ),
      ξ ∉ Metric.closedBall (0 : ℝᵈ) R →
      ((𝓕 ((Lp.memLp ELp).toLp (ELp : ℝᵈ → ℂ)) :
        Lp ℂ 2 (volume : Measure ℝᵈ)) : ℝᵈ → ℂ) ξ = 0 := by
    have hcoe1 : ((Lp.memLp ELp).toLp (ELp : ℝᵈ → ℂ)) = ELp := Lp.toLp_coeFn ELp (Lp.memLp ELp)
    filter_upwards [hELp_coe] with ξ hξ hnot
    rw [hcoe1, hξ]
    refine winG1_eq_zero ?_
    have hgt : R < ‖ξ‖ := by
      have h := hnot
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at h
      exact not_le.mp h
    exact lt_of_lt_of_le hgt (Commons.Analysis.Norm.norm_le_sum_abs_coord ξ)
  have hstrip0 := Commons.Analysis.Fourier.strip_lintegral_entire_le (d := d) (σ := R) (q := Q)
    (le_of_lt hR0) hQpos (Lp.memLp ELp) hband hFdiff hFae
  have hPdec : ∀ᵐ ξ ∂(volume : Measure ℝᵈ), winP f ηm ξ ≠ 0 →
      ‖winW φ ξ‖ ≤ Real.exp (-(c₃ * (∑ i : Fin d, |ξ i|) /
        (Real.log (2 + (∑ i : Fin d, |ξ i|))) ^ α)) := by
    filter_upwards [hdec] with ξ hξ hne
    exact hξ hne
  have hExpDiff : ∀ ξ : ℝᵈ, ‖((Real.exp (2 * Real.pi * Q * ∑ i : Fin d, |ξ i|) : ℝ) : ℂ)
        * winG1 f φ ηm R ξ‖ ^ 2
      = ‖winG1 f φ ηm R ξ‖ ^ 2 * Real.exp (4 * Real.pi * Q * ∑ i : Fin d, |ξ i|) := by
    intro ξ
    rw [normSq_ofReal_mul (Real.exp_nonneg _), mul_comm]
    congr 1
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  have hTFbound : ∀ ξ : ℝᵈ, ‖(if l1norm ξ ≤ R then
        ((Real.exp (c₃ * (Real.log (2 + R)) ^ (-α) * l1norm ξ) : ℝ) : ℂ)
          * (winP f ηm ξ * winW φ ξ) else 0)‖ ^ 2
      ≤ Real.exp (2 * (c₃ * (Real.log (2 + R)) ^ (-α) * R)) * ‖winP f ηm ξ‖ ^ 2 := by
    intro ξ
    by_cases hξ : l1norm ξ ≤ R
    · rw [if_pos hξ, normSq_ofReal_mul (Real.exp_nonneg _)]
      have h1 : (Real.exp (c₃ * (Real.log (2 + R)) ^ (-α) * l1norm ξ)) ^ 2
          ≤ Real.exp (2 * (c₃ * (Real.log (2 + R)) ^ (-α) * R)) := by
        rw [← Real.exp_nat_mul (c₃ * (Real.log (2 + R)) ^ (-α) * l1norm ξ) 2]
        refine Real.exp_le_exp.mpr ?_
        have hΘ : 0 ≤ (Real.log (2 + R)) ^ (-α) :=
          Real.rpow_nonneg (le_of_lt (Real.log_pos (by linarith))) _
        have h2c : (0 : ℝ) ≤ 2 * (c₃ * (Real.log (2 + R)) ^ (-α)) := by nlinarith
        have h3 : 2 * (c₃ * (Real.log (2 + R)) ^ (-α)) * l1norm ξ
            ≤ 2 * (c₃ * (Real.log (2 + R)) ^ (-α)) * R := mul_le_mul_of_nonneg_left hξ h2c
        calc 2 * (c₃ * (Real.log (2 + R)) ^ (-α) * l1norm ξ)
            = 2 * (c₃ * (Real.log (2 + R)) ^ (-α)) * l1norm ξ := by ring
          _ ≤ 2 * (c₃ * (Real.log (2 + R)) ^ (-α)) * R := h3
          _ = 2 * (c₃ * (Real.log (2 + R)) ^ (-α) * R) := by ring
      have h2 : ‖winP f ηm ξ * winW φ ξ‖ ^ 2 ≤ ‖winP f ηm ξ‖ ^ 2 := by
        refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
        rw [norm_mul]
        exact mul_le_of_le_one_right (norm_nonneg _) (hW1 ξ)
      exact mul_le_mul h1 h2 (sq_nonneg _) (Real.exp_nonneg _)
    · rw [if_neg hξ, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
      positivity
  have hupper_int : Integrable (fun ξ : ℝᵈ =>
      ‖(if l1norm ξ ≤ R then
          ((Real.exp (c₃ * (Real.log (2 + R)) ^ (-α) * l1norm ξ) : ℝ) : ℂ)
            * (winP f ηm ξ * winW φ ξ) else 0)‖ ^ 2) := by
    have hX : AEStronglyMeasurable (fun ξ : ℝᵈ =>
        ((Real.exp (c₃ * (Real.log (2 + R)) ^ (-α) * l1norm ξ) : ℝ) : ℂ)
          * (winP f ηm ξ * winW φ ξ)) volume :=
      (Complex.continuous_ofReal.comp (Real.continuous_exp.comp (continuous_const.mul
        (by rw [show (l1norm : ℝᵈ → ℝ) = fun ξ => ∑ i : Fin d, ‖ξ i‖ from rfl]; fun_prop)))).aestronglyMeasurable.mul
        hPW.aestronglyMeasurable
    have hfun : (fun ξ : ℝᵈ => ‖(if l1norm ξ ≤ R then
          ((Real.exp (c₃ * (Real.log (2 + R)) ^ (-α) * l1norm ξ) : ℝ) : ℂ)
            * (winP f ηm ξ * winW φ ξ) else 0)‖ ^ 2)
        = fun ξ : ℝᵈ => ({ξ : ℝᵈ | l1norm ξ ≤ R}.indicator (fun ξ => ‖
            ((Real.exp (c₃ * (Real.log (2 + R)) ^ (-α) * l1norm ξ) : ℝ) : ℂ)
              * (winP f ηm ξ * winW φ ξ)‖ ^ 2)) ξ := by
      funext ξ
      rw [Set.indicator_apply]
      by_cases h : ξ ∈ {ξ : ℝᵈ | l1norm ξ ≤ R}
      · rw [if_pos h, if_pos (show l1norm ξ ≤ R from h)]
      · rw [if_neg h, if_neg (show ¬(l1norm ξ ≤ R) from h), norm_zero,
          zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
    rw [hfun]
    exact Integrable.mono'
      (((memLp_two_iff_integrable_sq_norm hP.aestronglyMeasurable).mp hP).const_mul
        (Real.exp (2 * (c₃ * (Real.log (2 + R)) ^ (-α) * R))))
      ((hX.norm.pow 2).indicator (measurableSet_le_l1norm R))
      (Filter.Eventually.of_forall (fun ξ => by
        rw [Set.indicator_apply]
        by_cases h : ξ ∈ {ξ : ℝᵈ | l1norm ξ ≤ R}
        · rw [if_pos h]
          rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
          simpa only [if_pos (show l1norm ξ ≤ R from h)] using hTFbound ξ
        · rw [if_neg h, norm_zero]
          positivity))
  have hlow_int : Integrable (fun ξ : ℝᵈ =>
      ‖((Real.exp (2 * Real.pi * Q * ∑ i : Fin d, |ξ i|) : ℝ) : ℂ)
        * winG1 f φ ηm R ξ‖ ^ 2) := by
    refine Integrable.mono'
      (((memLp_two_iff_integrable_sq_norm hP.aestronglyMeasurable).mp hP).const_mul
        (Real.exp (4 * Real.pi * Q * R))) ?_ ?_
    · have hcont : Continuous (fun ξ : ℝᵈ =>
          ((Real.exp (2 * Real.pi * Q * ∑ i : Fin d, |ξ i|) : ℝ) : ℂ)) := by
        apply Complex.continuous_ofReal.comp
        apply Real.continuous_exp.comp
        apply continuous_const.mul
        fun_prop
      exact (hcont.aestronglyMeasurable.mul hG1.aestronglyMeasurable).norm.pow 2
    · filter_upwards with ξ
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), normSq_ofReal_mul (Real.exp_nonneg _)]
      by_cases hξ : l1norm ξ ≤ R
      · rw [show winG1 f φ ηm R ξ = winP f ηm ξ * winW φ ξ from by rw [winG1]; exact if_pos hξ]
        have h1 : (Real.exp (2 * Real.pi * Q * ∑ i : Fin d, |ξ i|)) ^ 2
            ≤ Real.exp (4 * Real.pi * Q * R) := by
          rw [← Real.exp_nat_mul (2 * Real.pi * Q * ∑ i : Fin d, |ξ i|) 2]
          refine Real.exp_le_exp.mpr ?_
          have hQnn : 0 ≤ Q := le_of_lt hQpos
          have h2 : (0 : ℝ) ≤ 2 * (2 * Real.pi * Q) := by positivity
          have h3 : 2 * (2 * Real.pi * Q) * (∑ i : Fin d, |ξ i|) ≤ 2 * (2 * Real.pi * Q) * R :=
            mul_le_mul_of_nonneg_left hξ h2
          calc 2 * (2 * Real.pi * Q * ∑ i : Fin d, |ξ i|)
              = 2 * (2 * Real.pi * Q) * (∑ i : Fin d, |ξ i|) := by ring
            _ ≤ 2 * (2 * Real.pi * Q) * R := h3
            _ = 4 * Real.pi * Q * R := by ring
        have h2 : ‖winP f ηm ξ * winW φ ξ‖ ^ 2 ≤ ‖winP f ηm ξ‖ ^ 2 := by
          refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
          rw [norm_mul]
          exact mul_le_of_le_one_right (norm_nonneg _) (hW1 ξ)
        exact mul_le_mul h1 h2 (sq_nonneg _) (Real.exp_nonneg _)
      · rw [show winG1 f φ ηm R ξ = 0 from by rw [winG1]; exact if_neg hξ, norm_zero,
          zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero]
        positivity
  have hmono_pt : ∀ ξ : ℝᵈ, ‖((Real.exp (2 * Real.pi * Q * ∑ i : Fin d, |ξ i|) : ℝ) : ℂ)
        * winG1 f φ ηm R ξ‖ ^ 2
      ≤ ‖(if l1norm ξ ≤ R then
          ((Real.exp (c₃ * (Real.log (2 + R)) ^ (-α) * l1norm ξ) : ℝ) : ℂ)
            * (winP f ηm ξ * winW φ ξ) else 0)‖ ^ 2 := by
    intro ξ
    by_cases hξ : l1norm ξ ≤ R
    · rw [if_pos hξ,
        show winG1 f φ ηm R ξ = winP f ηm ξ * winW φ ξ from by rw [winG1]; exact if_pos hξ,
        normSq_ofReal_mul (Real.exp_nonneg _), normSq_ofReal_mul (Real.exp_nonneg _)]
      refine mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (Real.exp_nonneg _) (Real.exp_le_exp.mpr ?_) 2) (sq_nonneg _)
      have h5 : 2 * Real.pi * Q ≤ c₃ * (Real.log (2 + R)) ^ (-α) := by
        nlinarith [hQ4, Real.pi_pos, le_of_lt hQpos]
      exact mul_le_mul_of_nonneg_right h5 (l1norm_nonneg ξ)
    · rw [if_neg hξ, show winG1 f φ ηm R ξ = 0 from by rw [winG1]; exact if_neg hξ, norm_zero,
        zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
      simp
  have hwint : ∫ ξ, ‖((𝓕 ((Lp.memLp ELp).toLp (ELp : ℝᵈ → ℂ)) :
        Lp ℂ 2 (volume : Measure ℝᵈ)) : ℝᵈ → ℂ) ξ‖ ^ 2
        * Real.exp (4 * Real.pi * Q * ∑ i : Fin d, |ξ i|)
      ≤ (1 + R ^ 2) ^ d * (windowCW d * hsq f) := by
    have hcoe1 : ((Lp.memLp ELp).toLp (ELp : ℝᵈ → ℂ)) = ELp := Lp.toLp_coeFn ELp (Lp.memLp ELp)
    rw [hcoe1, hELp_ft, hG1lp]
    have hstepA : ∫ ξ, ‖(hG1.toLp (winG1 f φ ηm R) : ℝᵈ → ℂ) ξ‖ ^ 2
          * Real.exp (4 * Real.pi * Q * ∑ i : Fin d, |ξ i|)
        = ∫ ξ, ‖winG1 f φ ηm R ξ‖ ^ 2
          * Real.exp (4 * Real.pi * Q * ∑ i : Fin d, |ξ i|) := by
      refine integral_congr_ae ?_
      filter_upwards [MemLp.coeFn_toLp hG1] with ξ hξ
      rw [hξ]
    rw [hstepA, show (∫ ξ, ‖winG1 f φ ηm R ξ‖ ^ 2
          * Real.exp (4 * Real.pi * Q * ∑ i : Fin d, |ξ i|))
        = ∫ ξ, ‖((Real.exp (2 * Real.pi * Q * ∑ i : Fin d, |ξ i|) : ℝ) : ℂ)
            * winG1 f φ ηm R ξ‖ ^ 2 from
      integral_congr_ae (Filter.Eventually.of_forall (fun ξ => (hExpDiff ξ).symm))]
    have hmono : ∫ ξ, ‖((Real.exp (2 * Real.pi * Q * ∑ i : Fin d, |ξ i|) : ℝ) : ℂ)
            * winG1 f φ ηm R ξ‖ ^ 2
        ≤ ∫ ξ, ‖(if l1norm ξ ≤ R then
            ((Real.exp (c₃ * (Real.log (2 + R)) ^ (-α) * l1norm ξ) : ℝ) : ℂ)
              * (winP f ηm ξ * winW φ ξ) else 0)‖ ^ 2 :=
      integral_mono_ae hlow_int hupper_int (Filter.Eventually.of_forall hmono_pt)
    refine hmono.trans ?_
    have hlow := Commons.Analysis.Fourier.truncation_low_le (d := d) (c₃ := c₃) (α := α) (R := R)
      (le_of_lt hc₃) (le_of_lt hα0) (le_of_lt hR0) (winP f ηm) (winW φ) hP hPW hPdec
    rw [hPq] at hlow
    refine hlow.trans ?_
    rw [Real.rpow_natCast]
    exact mul_le_mul_of_nonneg_left hgsq (by positivity)
  have hstrip : ∫⁻ z in {z : Fin d → ℂ | ∀ i : Fin d, |(z i).im| ≤ Q},
      ENNReal.ofReal (‖FEnt z‖ ^ 2)
      ≤ ENNReal.ofReal ((2 * Q) ^ d * ((1 + R ^ 2) ^ d * (windowCW d * hsq f))) := by
    refine hstrip0.trans ?_
    refine ENNReal.ofReal_le_ofReal ?_
    exact mul_le_mul_of_nonneg_left hwint (by positivity)
  -- ### the lens estimate
  have hQ4' : 4 * Real.pi * (ηL * q + r) ≤ c₃ * (Real.log (2 + R)) ^ (-α) := by
    simpa only [hQdef, windowQ] using hQ4
  have ha' : ∀ n : Fin d → ℤ, ∀ i : Fin d,
      2 * (n i : ℝ) + γ i ≤ (fun n i => a n i + 3 * c₁ / 4) n i ∧
        (fun n i => a n i + 3 * c₁ / 4) n i + 2 * (c₁ / 4) ≤ 2 * (n i : ℝ) + γ i + 2 := by
    intro n i
    obtain ⟨h1, h2⟩ := ha n i
    refine ⟨by linarith, by linarith⟩
  have hIbig' : ENNReal.ofReal ((ηL * zpLamMax q ε) ^ d * (2 * (20 ^ d * H)))
      ≤ ENNReal.ofReal ((2 * (c₁ / 4)) ^ d) := by
    convert hIbig using 2
    ring
  have hmain := localization_entire_euclidean (d := d) hd hq hε0 hε1 hδ0 hδ3 hH0 hH1 hηL0
    (by linarith : (0 : ℝ) < c₁ / 4) hr0 hητ hIbig' hFana
    (a := fun n i => a n i + 3 * c₁ / 4) ha'
  have hstrip' : ∫⁻ z in {z : Fin d → ℂ | ∀ i : Fin d, |(z i).im| ≤ ηL * q + r},
      ENNReal.ofReal (‖FEnt z‖ ^ 2)
      ≤ ENNReal.ofReal ((2 * Q) ^ d * ((1 + R ^ 2) ^ d * (windowCW d * hsq f))) := hstrip
  have hDnn : 0 ≤ windowD d q ε ηL r := le_of_lt (windowD_pos hηL0 hr0 hq hε0 (by linarith))
  have hJnn : 0 ≤ (2 * Q) ^ d * ((1 + R ^ 2) ^ d * (windowCW d * hsq f)) := by
    have h1 : (0:ℝ) ≤ (2 * Q) ^ d := by positivity
    have h2 : (0:ℝ) ≤ (1 + R ^ 2) ^ d := by positivity
    have h3 : (0:ℝ) ≤ windowCW d * hsq f := by
      have := hsq_nonneg f; have := windowCW_nonneg d; positivity
    positivity
  have hLnn : 0 ≤ 2 * (windowCW d) ^ 2 * hsq (subLp (locCubes c₁ a) f hSmeas)
      + 2 * (truncBeta d c₃ α R) ^ 2 * (windowCW d) ^ 2 * hsq f := by
    have h5 : 0 ≤ 2 * (windowCW d) ^ 2 * hsq (subLp (locCubes c₁ a) f hSmeas) := by
      have := hsq_nonneg (subLp (locCubes c₁ a) f hSmeas)
      have := windowCW_nonneg d
      positivity
    have h6 : 0 ≤ 2 * (truncBeta d c₃ α R) ^ 2 * (windowCW d) ^ 2 * hsq f := by
      have := hsq_nonneg f
      have := windowCW_nonneg d
      have := sq_nonneg (truncBeta d c₃ α R)
      positivity
    linarith
  have hAloc : ENNReal.ofReal (2 * windowCW d * hsq (subLp (locCubes c₁ a) g hSmeas)
      + 2 * ((truncBeta d c₃ α R) ^ 2 * hsq g))
      ≤ ENNReal.ofReal (2 * (windowCW d) ^ 2 * hsq (subLp (locCubes c₁ a) f hSmeas)
        + 2 * (truncBeta d c₃ α R) ^ 2 * (windowCW d) ^ 2 * hsq f) :=
    ENNReal.ofReal_le_ofReal hlocR
  have hLmono : ∫⁻ x in locCubesSmall c₁ a, ENNReal.ofReal (‖(ELp : ℝᵈ → ℂ) x‖ ^ 2)
      ≤ ENNReal.ofReal (2 * (windowCW d) ^ 2 * hsq (subLp (locCubes c₁ a) f hSmeas)
        + 2 * (truncBeta d c₃ α R) ^ 2 * (windowCW d) ^ 2 * hsq f) := hloc.trans hAloc
  have hS'id : locCubes (c₁ / 4) (fun n i => a n i + 3 * c₁ / 4) = locCubesSmall c₁ a := by
    rw [locCubesSmall, locCubes]
    congr 1
    funext n
    congr 1
    funext i
    ring
  rw [← hS'id] at hLmono
  have hA : ∫⁻ x : ℝᵈ, ENNReal.ofReal (‖FEnt (fun i => (x i : ℂ))‖ ^ 2)
      = ∫⁻ x : ℝᵈ, ENNReal.ofReal (‖(ELp : ℝᵈ → ℂ) x‖ ^ 2) := by
    refine lintegral_congr_ae ?_
    filter_upwards [hFae] with x hx
    rw [hx]
  rw [hA] at hmain
  have hlocF : ∫⁻ x in locCubes (c₁ / 4) (fun n i => a n i + 3 * c₁ / 4),
        ENNReal.ofReal (‖FEnt (fun i => (x i : ℂ))‖ ^ 2)
      = ∫⁻ x in locCubes (c₁ / 4) (fun n i => a n i + 3 * c₁ / 4),
        ENNReal.ofReal (‖(ELp : ℝᵈ → ℂ) x‖ ^ 2) := by
    refine lintegral_congr_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_of_ae hFae] with x hx
    rw [hx]
  rw [hlocF] at hmain
  have hmiddle : ENNReal.ofReal (windowD d q ε ηL r)
        * ∫⁻ z in {z : Fin d → ℂ | ∀ i : Fin d, |(z i).im| ≤ ηL * q + r},
            ENNReal.ofReal (‖FEnt z‖ ^ 2)
      ≤ ENNReal.ofReal (windowD d q ε ηL r)
        * ENNReal.ofReal ((2 * Q) ^ d * ((1 + R ^ 2) ^ d * (windowCW d * hsq f))) :=
    mul_le_mul' le_rfl hstrip'
  have hcnn : 0 ≤ cellZConst q ε δ H ηL (c₁ / 4) d :=
    le_of_lt (cellZConst_pos q ε δ H ηL (c₁ / 4) d hδ0 hδ3 hq hε0 hε1 hηL0 (by linarith))
  have hDnn : 0 ≤ windowD d q ε ηL r := le_of_lt (windowD_pos hηL0 hr0 hq hε0 (by linarith))
  have hJnn : 0 ≤ (2 * Q) ^ d * ((1 + R ^ 2) ^ d * (windowCW d * hsq f)) := by
    have h3 : (0 : ℝ) ≤ windowCW d * hsq f := by
      have := hsq_nonneg f; have := windowCW_nonneg d; positivity
    positivity
  have hLnn : 0 ≤ 2 * (windowCW d) ^ 2 * hsq (subLp (locCubes c₁ a) f hSmeas)
      + 2 * (truncBeta d c₃ α R) ^ 2 * (windowCW d) ^ 2 * hsq f := by
    have h5 : 0 ≤ 2 * (windowCW d) ^ 2 * hsq (subLp (locCubes c₁ a) f hSmeas) := by
      have := hsq_nonneg (subLp (locCubes c₁ a) f hSmeas)
      have := windowCW_nonneg d
      positivity
    have h6 : 0 ≤ 2 * (truncBeta d c₃ α R) ^ 2 * (windowCW d) ^ 2 * hsq f := by
      have := hsq_nonneg f
      have := windowCW_nonneg d
      have := sq_nonneg (truncBeta d c₃ α R)
      positivity
    linarith
  have hpow1 : (ENNReal.ofReal (windowD d q ε ηL r)
        * ∫⁻ z in {z : Fin d → ℂ | ∀ i : Fin d, |(z i).im| ≤ ηL * q + r},
            ENNReal.ofReal (‖FEnt z‖ ^ 2)) ^ (1 - zpKappa δ H d)
      ≤ ENNReal.ofReal ((windowD d q ε ηL r
          * ((2 * Q) ^ d * ((1 + R ^ 2) ^ d * (windowCW d * hsq f))))
            ^ (1 - zpKappa δ H d)) := by
    have h1 := ENNReal.rpow_le_rpow
      (hmiddle.trans (le_of_eq (ENNReal.ofReal_mul hDnn).symm))
      (show (0 : ℝ) ≤ 1 - zpKappa δ H d by linarith [hκ0, hκ1'])
    refine h1.trans (le_of_eq ?_)
    exact ENNReal.ofReal_rpow_of_nonneg (mul_nonneg hDnn hJnn) (by linarith [hκ0, hκ1'])
  have hpow2 : (∫⁻ x in locCubes (c₁ / 4) (fun n i => a n i + 3 * c₁ / 4),
        ENNReal.ofReal (‖(ELp : ℝᵈ → ℂ) x‖ ^ 2)) ^ (zpKappa δ H d)
      ≤ ENNReal.ofReal ((2 * (windowCW d) ^ 2 * hsq (subLp (locCubes c₁ a) f hSmeas)
        + 2 * (truncBeta d c₃ α R) ^ 2 * (windowCW d) ^ 2 * hsq f) ^ (zpKappa δ H d)) :=
    (ENNReal.rpow_le_rpow hLmono (le_of_lt hκ0)).trans
      (le_of_eq (ENNReal.ofReal_rpow_of_nonneg hLnn (le_of_lt hκ0)))
  have hELpint : Integrable (fun x : ℝᵈ => ‖(ELp : ℝᵈ → ℂ) x‖ ^ 2) volume :=
    (memLp_two_iff_integrable_sq_norm (Lp.memLp ELp).aestronglyMeasurable).mp (Lp.memLp ELp)
  have hstep2 : ∫⁻ x : ℝᵈ, ENNReal.ofReal (‖(ELp : ℝᵈ → ℂ) x‖ ^ 2)
      ≤ ENNReal.ofReal (cellZConst q ε δ H ηL (c₁ / 4) d)
        * ENNReal.ofReal ((windowD d q ε ηL r
            * ((2 * Q) ^ d * ((1 + R ^ 2) ^ d * (windowCW d * hsq f))))
              ^ (1 - zpKappa δ H d))
        * ENNReal.ofReal ((2 * (windowCW d) ^ 2 * hsq (subLp (locCubes c₁ a) f hSmeas)
            + 2 * (truncBeta d c₃ α R) ^ 2 * (windowCW d) ^ 2 * hsq f) ^ (zpKappa δ H d)) := by
    refine hmain.trans ?_
    exact mul_le_mul (mul_le_mul le_rfl hpow1 (by positivity) (by positivity)) hpow2
      (by positivity) (by positivity)
  have htoreal : (∫⁻ x : ℝᵈ, ENNReal.ofReal (‖(ELp : ℝᵈ → ℂ) x‖ ^ 2)).toReal
      = ∫ x : ℝᵈ, ‖(ELp : ℝᵈ → ℂ) x‖ ^ 2 := by
    rw [← ofReal_integral_eq_lintegral_ofReal hELpint
      (Filter.Eventually.of_forall (fun x => by positivity))]
    rw [ENNReal.toReal_ofReal (integral_nonneg (fun x => by positivity))]
  have hLHS : ∫ x : ℝᵈ, ‖(ELp : ℝᵈ → ℂ) x‖ ^ 2 = ∫ ξ, ‖winG1 f φ ηm R ξ‖ ^ 2 := by
    rw [← norm_sq_eq_integral ELp, ← MeasureTheory.Lp.norm_fourier_eq ELp, hELp_ft, hG1lp]
    rw [norm_sq_eq_integral (hG1.toLp (winG1 f φ ηm R))]
    refine integral_congr_ae ?_
    filter_upwards [MemLp.coeFn_toLp hG1] with ξ hξ
    rw [hξ]
  rw [← hLHS, ← htoreal]
  have hb : (ENNReal.ofReal (cellZConst q ε δ H ηL (c₁ / 4) d)
        * ENNReal.ofReal ((windowD d q ε ηL r
            * ((2 * Q) ^ d * ((1 + R ^ 2) ^ d * (windowCW d * hsq f))))
              ^ (1 - zpKappa δ H d))
        * ENNReal.ofReal ((2 * (windowCW d) ^ 2 * hsq (subLp (locCubes c₁ a) f hSmeas)
            + 2 * (truncBeta d c₃ α R) ^ 2 * (windowCW d) ^ 2 * hsq f)
              ^ (zpKappa δ H d))).toReal
      = cellZConst q ε δ H ηL (c₁ / 4) d
        * (windowD d q ε ηL r * ((2 * Q) ^ d * ((1 + R ^ 2) ^ d * (windowCW d * hsq f))))
            ^ (1 - zpKappa δ H d)
        * (2 * (windowCW d) ^ 2 * hsq (subLp (locCubes c₁ a) f hSmeas)
            + 2 * (truncBeta d c₃ α R) ^ 2 * (windowCW d) ^ 2 * hsq f) ^ (zpKappa δ H d) := by
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hcnn,
      ENNReal.toReal_ofReal (Real.rpow_nonneg (mul_nonneg hDnn hJnn) _),
      ENNReal.toReal_ofReal (Real.rpow_nonneg hLnn _)]
  rw [← hb]
  exact ENNReal.toReal_mono
    (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
      ENNReal.ofReal_ne_top) hstep2

/-! ## P4: the single-window estimate -/

/-- **P4, the single-window estimate.**  For a kernel `φ` whose Fourier transform is a damping
multiplier with decay on the frequency support of `f`, and for `ηm ∈ [-2,2]^d`, the window integral
`∫ ‖𝓕φ · 𝓕f(·-ηm)‖²` satisfies the `κ`-interpolated bound of Han–Schlag's Lemma 4.3. -/
theorem window_bound {q ε δ H ηL r c₁ c₃ α R : ℝ} (hd : 1 ≤ d)
    (hq : 0 < q) (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 2) (hδ0 : 0 < δ) (hδ3 : δ < 1 / 3)
    (hH0 : 0 < H) (hH1 : H ≤ 1) (hηL0 : 0 < ηL) (hc₁ : 0 < c₁) (hr0 : 0 < r)
    (hητ : 1 ≤ ηL * phiLens q ε (1 - 3 * δ))
    (hIbig : ENNReal.ofReal ((ηL * zpLamMax q ε) ^ d * (2 * (20 ^ d * H)))
      ≤ ENNReal.ofReal ((c₁ / 2) ^ d))
    (hc₃ : 0 < c₃) (hα0 : 0 < α) (hα1 : α ≤ 1) (hR0 : 0 < R) (hR1 : 1 ≤ R)
    (hRc : (2 * (d : ℝ) / c₃) ^ 2 ≤ R)
    (hQ4 : 4 * Real.pi * windowQ ηL q r ≤ c₃ * (Real.log (2 + R)) ^ (-α))
    {φ : ℝᵈ → ℂ} (hφ1 : MemLp φ 1 (volume : Measure ℝᵈ)) (hφ2 : MemLp φ 2 (volume : Measure ℝᵈ))
    (hφsupp : ∀ᵐ z ∂(volume : Measure ℝᵈ), (∃ i : Fin d, c₁ / 2 < |z i|) → φ z = 0)
    (hφw : ∀ᵐ ξ ∂(volume : Measure ℝᵈ), ‖winW φ ξ‖ ≤ (1 + ‖ξ‖ ^ 2) ^ (-(d : ℝ) / 2))
    {f : Lp ℂ 2 (volume : Measure ℝᵈ)} {ηm : ℝᵈ} (hηm : ∀ i : Fin d, |ηm i| ≤ 2)
    (hdec : ∀ᵐ ξ ∂(volume : Measure ℝᵈ), winP f ηm ξ ≠ 0 →
        ‖winW φ ξ‖ ≤ Real.exp (-(c₃ * l1norm ξ / (Real.log (2 + l1norm ξ)) ^ α)))
    {γ : ℝᵈ} {a : (Fin d → ℤ) → Fin d → ℝ}
    (ha : ∀ n : Fin d → ℤ, ∀ i : Fin d,
      2 * (n i : ℝ) + γ i ≤ a n i ∧ a n i + 2 * c₁ ≤ 2 * (n i : ℝ) + γ i + 2) :
    ∫ ξ, ‖winP f ηm ξ * winW φ ξ‖ ^ 2
      ≤ cellZConst q ε δ H ηL (c₁ / 4) d
        * (windowD d q ε ηL r * ((2 * windowQ ηL q r) ^ d * ((1 + R ^ 2) ^ d
            * (windowCW d * hsq f)))) ^ (1 - zpKappa δ H d)
        * (2 * (windowCW d) ^ 2 * hsq (subLp (locCubes c₁ a) f (measurableSet_locCubes c₁ a))
            + 2 * (truncBeta d c₃ α R) ^ 2 * (windowCW d) ^ 2 * hsq f) ^ (zpKappa δ H d)
        + (truncBeta d c₃ α R) ^ 2 * windowCW d * hsq f := by
  classical
  set g : Lp ℂ 2 (volume : Measure ℝᵈ) :=
    (memLp_modEta (η := ηm) (Lp.memLp f)).toLp (modEta ηm (f : ℝᵈ → ℂ)) with hg
  have hgsq : hsq g ≤ windowCW d * hsq f := by
    have h := hsq_modEta_le (η := ηm) hηm f
    rw [hg]
    simpa only [windowCW] using h
  have hlow := window_low_le (d := d) hd hq hε0 hε1 hδ0 hδ3 hH0 hH1 hηL0 hc₁ hr0 hητ hIbig
    hc₃ hα0 hα1 hR0 hR1 hRc hQ4 hφ1 hφ2 hφsupp hφw hηm hdec ha
  have hhigh := window_high_le (d := d) hc₃ hα0 hα1 hRc hφ1 hφ2 hφw (η := ηm) hdec
  rw [← hg] at hhigh
  have hhigh' : ∫ ξ, ‖winG2 f φ ηm R ξ‖ ^ 2 ≤ (truncBeta d c₃ α R) ^ 2 * (windowCW d * hsq f) :=
    hhigh.trans (mul_le_mul_of_nonneg_left hgsq (sq_nonneg _))
  have hP : MemLp (winP f ηm) 2 (volume : Measure ℝᵈ) := winP_memLp f ηm
  have hW1 : ∀ ξ : ℝᵈ, ‖winW φ ξ‖ ≤ 1 := winW_le_one hφ1 hφw
  have hG1 : MemLp (winG1 f φ ηm R) 2 (volume : Measure ℝᵈ) := by
    rw [winG1_eq_indicator]
    exact (winPW_memLp hP (winW_memLp hφ1 hφ2) (winW_bound (d := d) hφw)).indicator
      (measurableSet_le_l1norm R)
  have hG2 : MemLp (winG2 f φ ηm R) 2 (volume : Measure ℝᵈ) := by
    rw [winG2_eq_indicator]
    exact (winPW_memLp hP (winW_memLp hφ1 hφ2) (winW_bound (d := d) hφw)).indicator
      (measurableSet_lt_l1norm R)
  have hG1b : ∀ᵐ ξ ∂(volume : Measure ℝᵈ), ‖winG1 f φ ηm R ξ‖ ≤ ‖winP f ηm ξ‖ := by
    filter_upwards with ξ
    by_cases hξ : l1norm ξ ≤ R
    · rw [show winG1 f φ ηm R ξ = winP f ηm ξ * winW φ ξ from by rw [winG1]; exact if_pos hξ,
        norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) (hW1 ξ)
    · rw [show winG1 f φ ηm R ξ = 0 from by rw [winG1]; exact if_neg hξ, norm_zero]
      positivity
  have hG2b : ∀ᵐ ξ ∂(volume : Measure ℝᵈ), ‖winG2 f φ ηm R ξ‖ ≤ ‖winP f ηm ξ‖ := by
    filter_upwards with ξ
    by_cases hξ : R < l1norm ξ
    · rw [show winG2 f φ ηm R ξ = winP f ηm ξ * winW φ ξ from by rw [winG2]; exact if_pos hξ,
        norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) (hW1 ξ)
    · rw [show winG2 f φ ηm R ξ = 0 from by rw [winG2]; exact if_neg hξ, norm_zero]
      positivity
  have hPint : Integrable (fun ξ : ℝᵈ => ‖winP f ηm ξ‖ ^ 2) :=
    (memLp_two_iff_integrable_sq_norm hP.aestronglyMeasurable).mp hP
  have hG1int : Integrable (fun ξ : ℝᵈ => ‖winG1 f φ ηm R ξ‖ ^ 2) := by
    refine Integrable.mono' hPint (hG1.aestronglyMeasurable.norm.pow 2) ?_
    filter_upwards [hG1b] with ξ hξ
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (norm_nonneg _) hξ 2
  have hG2int : Integrable (fun ξ : ℝᵈ => ‖winG2 f φ ηm R ξ‖ ^ 2) := by
    refine Integrable.mono' hPint (hG2.aestronglyMeasurable.norm.pow 2) ?_
    filter_upwards [hG2b] with ξ hξ
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (norm_nonneg _) hξ 2
  have hPt : ∀ ξ : ℝᵈ, ‖winP f ηm ξ * winW φ ξ‖ ^ 2
      = ‖winG1 f φ ηm R ξ‖ ^ 2 + ‖winG2 f φ ηm R ξ‖ ^ 2 := by
    intro ξ
    rw [← winG_split f φ ηm R ξ, winG_normSq_split f φ ηm R ξ]
  calc ∫ ξ, ‖winP f ηm ξ * winW φ ξ‖ ^ 2
      = ∫ ξ, (‖winG1 f φ ηm R ξ‖ ^ 2 + ‖winG2 f φ ηm R ξ‖ ^ 2) :=
        integral_congr_ae (Filter.Eventually.of_forall hPt)
    _ = (∫ ξ, ‖winG1 f φ ηm R ξ‖ ^ 2) + ∫ ξ, ‖winG2 f φ ηm R ξ‖ ^ 2 :=
        integral_add hG1int hG2int
    _ ≤ (cellZConst q ε δ H ηL (c₁ / 4) d
        * (windowD d q ε ηL r * ((2 * windowQ ηL q r) ^ d * ((1 + R ^ 2) ^ d
            * (windowCW d * hsq f)))) ^ (1 - zpKappa δ H d)
        * (2 * (windowCW d) ^ 2 * hsq (subLp (locCubes c₁ a) f (measurableSet_locCubes c₁ a))
            + 2 * (truncBeta d c₃ α R) ^ 2 * (windowCW d) ^ 2 * hsq f) ^ (zpKappa δ H d))
        + (truncBeta d c₃ α R) ^ 2 * (windowCW d * hsq f) :=
        add_le_add hlow hhigh'
    _ = cellZConst q ε δ H ηL (c₁ / 4) d
        * (windowD d q ε ηL r * ((2 * windowQ ηL q r) ^ d * ((1 + R ^ 2) ^ d
            * (windowCW d * hsq f)))) ^ (1 - zpKappa δ H d)
        * (2 * (windowCW d) ^ 2 * hsq (subLp (locCubes c₁ a) f (measurableSet_locCubes c₁ a))
            + 2 * (truncBeta d c₃ α R) ^ 2 * (windowCW d) ^ 2 * hsq f) ^ (zpKappa δ H d)
        + (truncBeta d c₃ α R) ^ 2 * windowCW d * hsq f := by ring

end Submission.FUP
