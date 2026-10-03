import Mathlib
import Submission.Work.FIArea4.Vflip.sep_defs
import Submission.Work.FIArea4.Vflip.sepG_decay
import Submission.Work.FIArea4.Vflip.sepG_mellin

/-!
# `separation_ineq`

The Fourier–Mellin separation inequality of Friedlander–Iwaniec: for a smooth `ψ` supported in
`(1/2, 5/2)` there is a constant `C` (depending on `ψ`, `a`, `b`) such that whenever
`a ≤ |x i| ≤ b`, `y i > 0`, and the exponential sums `∑ c_i e(u x_i) (y_i)^{it}` are bounded by
`M` uniformly in `u, t`, one has `‖∑ c_i ψ(|x i| * y i)‖ ≤ C (log(2 + b/a) + 1)^4 M`.

Ingredients: `sepG_mellin` (Mellin inversion on the critical line), `sepA_inversion` (additive
character expansion of `|x|^{2πit}` through the chirped cutoff `sepA`), `sepG_decay` (Schwartz
decay of `sepG ψ`) and `sepA_fourier_l1` (`∫ ‖𝓕 (sepA a b α)‖ ≤ K (1+|α|)^2`).
-/

open MeasureTheory
open scoped FourierTransform

namespace Work.FIArea4.Vflip

noncomputable section

lemma integrable_fourier_sepA (a b α : ℝ) (ha : 0 < a) : Integrable (𝓕 (sepA a b α)) := by
  let S : SchwartzMap ℝ ℂ :=
    (hasCompactSupport_sepA a b α ha).toSchwartzMap (contDiff_sepA a b α ha)
  have h : Integrable (⇑(𝓕 S : SchwartzMap ℝ ℂ)) := (𝓕 S : SchwartzMap ℝ ℂ).integrable (μ := volume)
  rw [SchwartzMap.fourier_coe] at h
  exact h

lemma integrable_sepG (ψ : ℝ → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hsupp : ∀ y : ℝ, (y ≤ 1 / 2 ∨ 5 / 2 ≤ y) → ψ y = 0) : Integrable (sepG ψ) := by
  have hcs : HasCompactSupport (fun u : ℝ => (ψ (Real.exp u) : ℂ)) := by
    refine HasCompactSupport.of_support_subset_isCompact
      (K := Set.Icc (Real.log (1 / 2)) (Real.log (5 / 2))) isCompact_Icc ?_
    rw [Function.support_subset_iff]
    intro u hu
    rw [Set.mem_Icc]
    constructor
    · by_contra hc
      have hlt : u < Real.log (1 / 2) := lt_of_not_ge hc
      have h2 : Real.exp u < 1 / 2 := by
        have h := Real.exp_lt_exp.mpr hlt
        rwa [Real.exp_log (by norm_num : (0 : ℝ) < 1 / 2)] at h
      exact hu (by rw [hsupp _ (Or.inl (le_of_lt h2))]; simp)
    · by_contra hc
      have hlt : Real.log (5 / 2) < u := lt_of_not_ge hc
      have h2 : 5 / 2 < Real.exp u := by
        have h := Real.exp_lt_exp.mpr hlt
        rwa [Real.exp_log (by norm_num : (0 : ℝ) < 5 / 2)] at h
      exact hu (by rw [hsupp _ (Or.inr (le_of_lt h2))]; simp)
  have hcd : ContDiff ℝ (⊤ : ℕ∞) (fun u : ℝ => (ψ (Real.exp u) : ℂ)) := by
    have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun u : ℝ => ψ (Real.exp u)) := hψ.comp Real.contDiff_exp
    exact Complex.ofRealCLM.contDiff.comp h1
  let S : SchwartzMap ℝ ℂ := hcs.toSchwartzMap hcd
  have hfun : (S : ℝ → ℂ) = fun u : ℝ => (ψ (Real.exp u) : ℂ) := by
    funext u; rfl
  have h : Integrable (𝓕 fun u : ℝ => (ψ (Real.exp u) : ℂ)) := by
    have h2 := (𝓕 S : SchwartzMap ℝ ℂ).integrable (μ := volume)
    rw [SchwartzMap.fourier_coe, hfun] at h2
    exact h2
  simpa [sepG] using h

/-- Complex powers of positive reals with imaginary exponents have norm one. -/
lemma norm_cpow_imag (r : ℝ) (hr : 0 < r) (s : ℝ) :
    ‖((r : ℂ)) ^ (Complex.I * (s : ℂ))‖ = 1 := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hr]
  simp

lemma cpow_ofReal_eq_exp (r : ℝ) (hr : 0 < r) (s : ℝ) :
    ((r : ℂ)) ^ (Complex.I * (s : ℂ)) = Complex.exp (s * (Real.log r) * Complex.I) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hr.ne'), Complex.ofReal_log hr.le]
  congr 1
  ring

lemma continuous_cpow_ofReal (r : ℝ) (hr : 0 < r) :
    Continuous (fun t : ℝ => ((r : ℂ)) ^ (Complex.I * ((2 * Real.pi * t : ℝ) : ℂ))) := by
  have h : (fun t : ℝ => ((r : ℂ)) ^ (Complex.I * ((2 * Real.pi * t : ℝ) : ℂ))) =
      fun t : ℝ => Complex.exp (((2 * Real.pi * t : ℝ) : ℂ) * ((Real.log r : ℂ) * Complex.I)) := by
    funext t
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hr.ne'), Complex.ofReal_log hr.le]
    congr 1
    ring
  rw [h]
  fun_prop

/-- If `f` is integrable and `‖g‖ ≤ C` (with `g` a.e. strongly measurable), then `f * g` is
integrable. -/
lemma Integrable.mul_of_norm_le {f g : ℝ → ℂ} (hf : Integrable f) (C : ℝ)
    (hg : ∀ x, ‖g x‖ ≤ C) (hm : AEStronglyMeasurable g) : Integrable (fun x => f x * g x) := by
  refine Integrable.mono' (hf.norm.const_mul C) (hf.aestronglyMeasurable.mul hm) ?_
  filter_upwards with x
  rw [norm_mul]
  calc ‖f x‖ * ‖g x‖ ≤ ‖f x‖ * C := mul_le_mul_of_nonneg_left (hg x) (norm_nonneg _)
    _ = C * ‖f x‖ := by ring

end

end Work.FIArea4.Vflip
