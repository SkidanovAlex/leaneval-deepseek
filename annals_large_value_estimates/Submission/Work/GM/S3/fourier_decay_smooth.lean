import Mathlib
import Submission.Work.GM.S3.Base

/-!
# Fourier decay of a smooth function with all derivatives bounded on `[1,2]`

GM (Lemma 4.3 / "smooth" Fourier decay): if `f : ℝ → ℂ` is `C^∞`, supported in `[1,2]`, and
the `j`-th derivative of `f` is bounded by `B` everywhere, then
`‖𝓕 f ξ‖ ≤ C * B / |ξ|^j` for all `ξ ≠ 0`, with `C` depending only on `j`.

`Commons.Analysis.Fourier.fourierTransform_iteratedDeriv_decay` gives the same decay with the
constant `∫ ‖f^{(j)}‖`, which is not controlled by `B`; here the support hypothesis `⊆ [1,2]`
turns that `L¹`-norm into `B`, which is what the `S₃` argument needs.
-/

namespace Work.GM.S3

open MeasureTheory

/-! ### `L¹`-norm bounds for functions vanishing off `[1,2]` -/

/-- The norm of `2 * π * I * x` as a complex number is `2 * π * |x|`. -/
private lemma norm_two_pi_I_mul (x : ℝ) :
    ‖(2 * Real.pi * Complex.I * (x : ℂ))‖ = 2 * Real.pi * |x| := by
  rw [norm_mul, norm_mul, norm_mul]
  simp only [Complex.norm_ofNat, Complex.norm_I, mul_one]
  rw [show ‖(Real.pi : ℂ)‖ = Real.pi by simp [abs_of_nonneg Real.pi_pos.le]]
  simp

/-- A function that vanishes off the closed interval `[1,2]` has compact support. -/
private lemma hasCompactSupport_of_eq_zero_off_Icc {g : ℝ → ℂ}
    (h : ∀ x, x ∉ Set.Icc (1 : ℝ) 2 → g x = 0) : HasCompactSupport g := by
  rw [HasCompactSupport]
  exact (isCompact_Icc (a := (1 : ℝ)) (b := 2)).of_isClosed_subset isClosed_closure
    (closure_minimal (fun x hx => by
      by_contra hxc
      exact hx (h x hxc)) isClosed_Icc)

/-- If `g` vanishes off `[1,2]` and `‖g‖ ≤ B` pointwise, then `∫ ‖g‖ ≤ B`. -/
private lemma integral_norm_le_of_eq_zero_off_Icc {g : ℝ → ℂ}
    (hvan : ∀ x, x ∉ Set.Icc (1 : ℝ) 2 → g x = 0) (hgt : Integrable g) {B : ℝ}
    (hB : ∀ x, ‖g x‖ ≤ B) : ∫ x, ‖g x‖ ≤ B := by
  have hvol : volume (Set.Icc (1 : ℝ) 2) ≠ ⊤ := by
    rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
  have hle : (fun x : ℝ => ‖g x‖) ≤
      ((Set.Icc (1 : ℝ) 2).indicator (fun _ : ℝ => B) : ℝ → ℝ) := by
    intro x
    by_cases hx : x ∈ Set.Icc (1 : ℝ) 2
    · rw [Set.indicator_of_mem hx]; exact hB x
    · rw [Set.indicator_of_notMem hx]
      simp [hvan x hx]
  have hind : Integrable (((Set.Icc (1 : ℝ) 2).indicator (fun _ : ℝ => B)) : ℝ → ℝ) := by
    rw [integrable_indicator_iff measurableSet_Icc]
    exact integrableOn_const hvol (by simp)
  have hmono : ∫ x, ‖g x‖ ≤ volume.real (Set.Icc (1 : ℝ) 2) • B := by
    have h := integral_mono hgt.norm hind hle
    rwa [integral_indicator_const B measurableSet_Icc] at h
  have hvol' : volume.real (Set.Icc (1 : ℝ) 2) = 1 := by
    rw [Real.volume_real_Icc]; norm_num
  rw [hvol'] at hmono
  simpa using hmono

/-- `fourier_decay_smooth`: `‖𝓕 f ξ‖ ≤ C * B / |ξ|^j`, with `C` depending only on `j`, for
a `C^∞` function `f` supported in `[1,2]` whose `j`-th derivative is bounded by `B`. -/
theorem fourier_decay_smooth (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (B : ℝ) (f : ℝ → ℂ), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f →
      (∀ x, x ∉ Set.Icc (1 : ℝ) 2 → f x = 0) →
      (∀ x, ‖iteratedDeriv j f x‖ ≤ B) →
      ∀ ξ : ℝ, ξ ≠ 0 → ‖FourierTransform.fourier f ξ‖ ≤ C * B / |ξ| ^ j := by
  refine ⟨1 / (2 * Real.pi) ^ j, by positivity, ?_⟩
  intro B f hf hsupp hB ξ hξ
  -- All iterated derivatives vanish off `[1,2]` (the complement is open).
  have hderiv0 : ∀ n : ℕ, ∀ x, x ∉ Set.Icc (1 : ℝ) 2 → iteratedDeriv n f x = 0 := by
    intro n x hx
    have h := Set.EqOn.iteratedDeriv_of_isOpen (s := (Set.Icc (1 : ℝ) 2)ᶜ) (f := f)
        (g := fun _ => (0 : ℂ)) (fun y hy => hsupp y hy) isClosed_Icc.isOpen_compl n hx
    simpa using h
  have hcs : ∀ n : ℕ, HasCompactSupport (iteratedDeriv n f) := fun n =>
    hasCompactSupport_of_eq_zero_off_Icc (hderiv0 n)
  have hint : ∀ n : ℕ, Integrable (iteratedDeriv n f) := fun n =>
    (hf.continuous_iteratedDeriv n (WithTop.coe_le_coe.mpr le_top)).integrable_of_hasCompactSupport
      (hcs n)
  -- `∫ ‖f^{(j)}‖ ≤ B`, since `‖f^{(j)}‖` is supported in `[1,2]` and bounded by `B`.
  set A : ℝ := ∫ y, ‖iteratedDeriv j f y‖ with hAdef
  have hAle : A ≤ B := by
    rw [hAdef]
    exact integral_norm_le_of_eq_zero_off_Icc (hderiv0 j) (hint j) hB
  -- The Fourier transform of the `j`-th derivative is `(2πiξ)^j 𝓕 f ξ`.
  have hfj : ContDiff ℝ (j : ℕ∞) f := hf.of_le (WithTop.coe_le_coe.mpr le_top)
  have hfour := Real.fourier_iteratedDeriv (f := f) (N := (j : ℕ∞)) (n := j) hfj
      (fun n _ => hint n) (by simp)
  have hfour' : ∀ x : ℝ, FourierTransform.fourier (iteratedDeriv j f) x
      = (2 * Real.pi * Complex.I * (x : ℂ)) ^ j • (FourierTransform.fourier f x) :=
    fun x => congrFun hfour x
  -- and that transform is bounded by `A`.
  have hAbound (η : ℝ) : ‖FourierTransform.fourier (iteratedDeriv j f) η‖ ≤ A := by
    rw [Real.fourier_eq]
    refine (norm_integral_le_integral_norm _).trans ?_
    simp only [Circle.norm_smul]
    exact le_of_eq hAdef.symm
  have h2pi (η : ℝ) :
      ‖(2 * Real.pi * Complex.I * (η : ℂ)) ^ j‖ = (2 * Real.pi * |η|) ^ j := by
    rw [norm_pow, norm_two_pi_I_mul]
  have hkey (η : ℝ) : ‖FourierTransform.fourier f η‖ * (2 * Real.pi * |η|) ^ j ≤ B := by
    have hb : (2 * Real.pi * |η|) ^ j * ‖FourierTransform.fourier f η‖ ≤ B := by
      have h := hAbound η
      rw [hfour' η, norm_smul, h2pi η] at h
      exact le_trans h hAle
    calc ‖FourierTransform.fourier f η‖ * (2 * Real.pi * |η|) ^ j
        = (2 * Real.pi * |η|) ^ j * ‖FourierTransform.fourier f η‖ := by ring
      _ ≤ B := hb
  have hξpos : 0 < |ξ| := abs_pos.mpr hξ
  have hDpos : 0 < (2 * Real.pi * |ξ|) ^ j := pow_pos (by positivity) j
  have h1 : ‖FourierTransform.fourier f ξ‖ ≤ B / (2 * Real.pi * |ξ|) ^ j :=
    (le_div_iff₀ hDpos).mpr (hkey ξ)
  rw [mul_pow] at h1
  have hp : (2 * Real.pi) ^ j ≠ 0 := by positivity
  have hq : |ξ| ^ j ≠ 0 := ne_of_gt (pow_pos hξpos j)
  have h2 : B / ((2 * Real.pi) ^ j * |ξ| ^ j) = 1 / (2 * Real.pi) ^ j * B / |ξ| ^ j := by
    field_simp
  linarith [h1, h2.le, h2.ge]

end Work.GM.S3
