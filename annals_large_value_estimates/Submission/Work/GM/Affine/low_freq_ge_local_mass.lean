import Mathlib
import Submission.Work.GM.Affine.setup
import Submission.Work.GM.Affine.low_freq_defs
import Submission.Work.GM.Affine.integral_tri_div_fourierChar
import Submission.Work.GM.Affine.sinc_third_lower_bound
import Submission.Work.GM.Affine.weighted_plancherel_of_char
import Submission.Work.GM.Affine.low_freq_weight_le_upper
import Submission.Work.GM.Affine.local_mass_le_kernel_integral

/-!
# A positive-kernel lower bound for the low-frequency mass of `Fhat f`

GM §9 needs, for `f ≥ 0` supported in `[1/C₀, C₀]` and `T ≥ 1`, a lower bound for
`∫_{|ξ| ≤ T/2} ‖Fhat f ξ‖²` in terms of the *local mass* of `f` at scale `1/T`:

  `(1/5) * T * ∫ u, f u * (∫ v in Set.Icc (u - 1/T) (u + 1/T), f v) ≤ ∫ ξ in Set.Ioc (-(T/2)) (T/2), ‖Fhat f ξ‖²`.

## The argument

Put `A = T/3`, let `θ(ξ) = tri (ξ/A) = max (1 - |ξ|/A) 0` be the frequency weight and
`K(s) = A * sinc (π A s)²` the physical kernel; these are a Fourier pair
(`Work.GM.Affine.integral_tri_div_fourierChar`).  Then

* `0 ≤ θ ≤ 1` and `θ` vanishes for `|ξ| ≥ A = T/3 < T/2`, so (with `‖Fhat f‖² ≥ 0`)
  `∫ ξ, θ ξ * ‖Fhat f ξ‖² ≤ ∫_{|ξ|≤T/2} ‖Fhat f ξ‖²`
  (`Work.GM.Affine.low_freq_weight_le_upper`);
* the weighted Plancherel identity (`Work.GM.Affine.weighted_plancherel_of_char`, the
  triangle-kernel analogue of the Gaussian-weighted Plancherel already in this directory)
  turns the weighted frequency integral into the physical double integral
  `∫ z, f z * ∫ u, K (z - u) * f u`;
* `K(z-u) ≥ T/5` whenever `|z-u| ≤ 1/T` (because `|A (z-u)| ≤ 1/3` and
  `sinc (π y)² ≥ 3/5` for `|y| ≤ 1/3`, `Work.GM.Affine.sinc_third_lower_bound`), so with
  `f ≥ 0` the double integral dominates `(T/5) * ∫ z, f z * ∫_{z ± 1/T} f`
  (`Work.GM.Affine.local_mass_le_kernel_integral`).

Chaining the three gives exactly the claim, since `(1/5) * T = T/5`.
-/

open Complex MeasureTheory Finset
open scoped BigOperators FourierTransform

set_option autoImplicit false

namespace Work.GM.Affine

noncomputable section

/-! ### Elementary facts about the triangle kernel -/

/-- The triangle (tent) kernel is nonnegative. -/
lemma lf_tri_nonneg (x : ℝ) : 0 ≤ Commons.Analysis.Fourier.tri x := by
  unfold Commons.Analysis.Fourier.tri
  exact le_max_right _ _

/-- The triangle (tent) kernel is at most `1`. -/
lemma lf_tri_le_one (x : ℝ) : Commons.Analysis.Fourier.tri x ≤ 1 := by
  by_cases h : 1 ≤ |x|
  · rw [Commons.Analysis.Fourier.tri_eq_zero_of_one_le_abs h]; norm_num
  · rw [Commons.Analysis.Fourier.tri_eq_one_sub (le_of_lt (not_le.mp h))]
    linarith [abs_nonneg x]

/-- The Fourier transform of an integrable `f` is bounded by `∫ ‖f‖`. -/
lemma lf_norm_Fhat_le_integral (f : ℝ → ℝ) (ξ : ℝ) : ‖Fhat f ξ‖ ≤ ∫ u, ‖f u‖ := by
  rw [Fhat, Real.fourier_real_eq_integral_exp_smul]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  show ‖cexp (↑(-2 * Real.pi * u * ξ) * I) • (f u : ℂ)‖ = ‖f u‖
  rw [norm_smul, Complex.norm_exp_ofReal_mul_I, one_mul,
    show ‖((f u : ℝ) : ℂ)‖ = |f u| from RCLike.norm_ofReal (f u), Real.norm_eq_abs]

/-- `SuppHyp C₀ f` (together with `C₀ ≥ 1`) gives compact support: `f` is supported in the
compact interval `[1/C₀, C₀]`. -/
lemma lf_hasCompactSupport_of_suppHyp {C₀ : ℝ} {f : ℝ → ℝ} (hs : SuppHyp C₀ f) :
    HasCompactSupport f :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc (fun x hx => hs x hx)

/-! ### The real weighted-Plancherel identity for the triangle kernel -/

/-- **Weighted Plancherel for the triangle kernel.**  For `T ≥ 1` and `f` continuous with
compact support,

  `∫ ξ, tri (ξ/(T/3)) · ‖Fhat f ξ‖² = ∫ z, f z · ∫ u, (T/3) sinc (π (T/3) (z-u))² · f u`.

This is `Work.GM.Affine.weighted_plancherel_of_char` applied to the Fourier pair
`(θ, K) = (tri (·/(T/3)), (T/3) sinc (π (T/3) ·)²)` of
`Work.GM.Affine.integral_tri_div_fourierChar`, with the complex identity converted to a real
one by `Complex.ofReal_inj` (`f` is real-valued). -/
lemma lf_wp_real {T : ℝ} (hT : 1 ≤ T) {f : ℝ → ℝ} (hf : Continuous f)
    (hcs : HasCompactSupport f) :
    ∫ ξ : ℝ, Commons.Analysis.Fourier.tri (ξ / (T / 3)) * ‖Fhat f ξ‖ ^ 2
      = ∫ z : ℝ, f z * ∫ u : ℝ, (T / 3) * Real.sinc (Real.pi * ((T / 3) * (z - u))) ^ 2 * f u := by
  have hA : (0 : ℝ) < T / 3 := by linarith
  have hinv : ((T / 3)⁻¹) ≠ 0 := by positivity
  set θ : ℝ → ℝ := fun ξ => Commons.Analysis.Fourier.tri (ξ / (T / 3)) with hθ
  set K : ℝ → ℝ := fun s => (T / 3) * Real.sinc (Real.pi * ((T / 3) * s)) ^ 2 with hK
  have hθint : Integrable θ := by
    rw [hθ]
    have h := Commons.Analysis.Fourier.tri_integrable.comp_mul_left' (R := (T / 3)⁻¹) hinv
    simpa [div_eq_mul_inv, mul_comm] using h
  have hθbdd : ∃ M : ℝ, ∀ ξ, ‖θ ξ‖ ≤ M := by
    refine ⟨1, fun ξ => ?_⟩
    rw [Real.norm_eq_abs, abs_of_nonneg (lf_tri_nonneg _)]
    exact lf_tri_le_one _
  have hchar : ∀ s : ℝ,
      ∫ ξ : ℝ, ((θ ξ : ℝ) : ℂ) * (Real.fourierChar (s * ξ) : ℂ) = ((K s : ℝ) : ℂ) := by
    intro s
    rw [hθ, hK]
    exact integral_tri_div_fourierChar hA s
  have hgc : Continuous (fun u : ℝ => (f u : ℂ)) := Complex.continuous_ofReal.comp hf
  have hgcs : HasCompactSupport (fun u : ℝ => (f u : ℂ)) :=
    hcs.comp_left (g := fun x : ℝ => (x : ℂ)) (by simp)
  have hkey := weighted_plancherel_of_char hgc hgcs hθint hθbdd hchar
  have hL : (∫ ξ : ℝ, ((θ ξ * ‖Fhat f ξ‖ ^ 2 : ℝ) : ℂ))
      = ((∫ ξ : ℝ, θ ξ * ‖Fhat f ξ‖ ^ 2 : ℝ) : ℂ) := integral_ofReal
  have hR : (∫ z : ℝ, star ((f z : ℂ)) * ∫ u : ℝ, ((K (z - u) : ℝ) : ℂ) * (f u : ℂ))
      = ((∫ z : ℝ, f z * ∫ u : ℝ, K (z - u) * f u : ℝ) : ℂ) := by
    have h1 : ∀ z : ℝ, star ((f z : ℂ)) * ∫ u : ℝ, ((K (z - u) : ℝ) : ℂ) * (f u : ℂ)
        = ((f z * ∫ u : ℝ, K (z - u) * f u : ℝ) : ℂ) := by
      intro z
      have hin : (∫ u : ℝ, ((K (z - u) : ℝ) : ℂ) * (f u : ℂ))
          = ((∫ u : ℝ, K (z - u) * f u : ℝ) : ℂ) := by
        trans ∫ u : ℝ, ((K (z - u) * f u : ℝ) : ℂ)
        · refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
          exact (Complex.ofReal_mul (K (z - u)) (f u)).symm
        · exact integral_ofReal
      rw [show star ((f z : ℂ)) = ((f z : ℝ) : ℂ) from by simp, hin, ← Complex.ofReal_mul]
    calc (∫ z : ℝ, star ((f z : ℂ)) * ∫ u : ℝ, ((K (z - u) : ℝ) : ℂ) * (f u : ℂ))
        = ∫ z : ℝ, ((f z * ∫ u : ℝ, K (z - u) * f u : ℝ) : ℂ) := by
          refine integral_congr_ae (Filter.Eventually.of_forall h1)
      _ = ((∫ z : ℝ, f z * ∫ u : ℝ, K (z - u) * f u : ℝ) : ℂ) := integral_ofReal
  have hcomplex : ((∫ ξ : ℝ, θ ξ * ‖Fhat f ξ‖ ^ 2 : ℝ) : ℂ)
      = ((∫ z : ℝ, f z * ∫ u : ℝ, K (z - u) * f u : ℝ) : ℂ) := by
    rw [← hL, ← hR]
    exact hkey
  have hreal : (∫ ξ : ℝ, θ ξ * ‖Fhat f ξ‖ ^ 2)
      = ∫ z : ℝ, f z * ∫ u : ℝ, K (z - u) * f u := Complex.ofReal_inj.mp hcomplex
  rw [hreal]

/-! ### The main theorem -/

theorem low_freq_ge_local_mass {C₀ T₀ : ℝ} (hC₀ : 1 ≤ C₀) (hT₀ : 1 ≤ T₀) :
    ∀ T : ℝ, T₀ ≤ T → ∀ f : ℝ → ℝ, Continuous f → (∀ u, 0 ≤ f u) → Work.GM.Affine.SuppHyp C₀ f →
      (1 / 5) * T * ∫ u, (f u) * (∫ v in Set.Icc (u - 1 / T) (u + 1 / T), f v)
        ≤ ∫ ξ in Set.Ioc (-(T / 2)) (T / 2), ‖Work.GM.Affine.Fhat f ξ‖ ^ 2 := by
  intro T hT f hf hnn hs
  have hT1 : 1 ≤ T := le_trans hT₀ hT
  have hcs : HasCompactSupport f := lf_hasCompactSupport_of_suppHyp hs
  have hkey := lf_wp_real (T := T) hT1 hf hcs
  have hlow := local_mass_le_kernel_integral T hT1 f hf hcs hnn
    (fun y hy => sinc_third_lower_bound (y := y) hy)
  have hup := low_freq_weight_le_upper (T := T) hT1 hf hcs
  have hconst : (1 / 5) * T = T / 5 := by ring
  rw [hconst]
  calc (T / 5) * ∫ z : ℝ, f z * (∫ u in Set.Icc (z - 1 / T) (z + 1 / T), f u)
      ≤ ∫ z : ℝ, f z * ∫ u : ℝ, (T / 3) * Real.sinc (Real.pi * ((T / 3) * (z - u))) ^ 2 * f u :=
        hlow
    _ = ∫ ξ : ℝ, Commons.Analysis.Fourier.tri (ξ / (T / 3)) * ‖Fhat f ξ‖ ^ 2 := hkey.symm
    _ ≤ ∫ ξ in Set.Ioc (-(T / 2)) (T / 2), ‖Fhat f ξ‖ ^ 2 := hup

end

end Work.GM.Affine
