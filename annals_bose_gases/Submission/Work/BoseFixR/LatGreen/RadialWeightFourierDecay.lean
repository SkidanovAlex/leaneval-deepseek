import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Submission.Work.BoseFixR.Rb5Lin.radial_fourier_sinc
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Fourier decay of a radial weight `ψ ‖·‖`

This module contains the pieces of the Fourier-decay bound for a radial weight `x ↦ ψ ‖x‖`
on `ℝ³`, together with a fully proved version of the requested statement *with the a.e.
measurability of `ψ` made explicit*.

## Why the measurability hypothesis is needed

The requested statement `Work.BoseFixR.LatGreen.RadialWeightFourierDecay` assumes only
`IntegrableOn (fun r => r * |ψ r|) (Ioi 0)` and concludes, among other things,
`Integrable (fun x => ψ ‖x‖)`.  In this library `Integrable f μ` is
`AEStronglyMeasurable f μ ∧ HasFiniteIntegral f μ`, so the conclusion needs `ψ` to be
a.e. strongly measurable on `(0,∞)` — and domination alone cannot supply that.

The hypothesis `IntegrableOn (fun r => r * |ψ r|) (Ioi 0)` constrains only `|ψ|` (it says
that `r ↦ r * |ψ r|` is a.e. strongly measurable with finite integral); the *sign* of `ψ`
is invisible to it.  Concretely, if `A ⊆ (1/4,1/2)` is a non-Lebesgue-measurable set and
`ψ := 1_A - 1_{(0,1)∖A}` (with `ψ = 0` for `r ≤ 0` or `r ≥ 1`, so that `R := 1`), then
`|ψ r| = 1_{(0,1)}(r)` pointwise, hence

`fun r ↦ r * |ψ r| = fun r ↦ r * 1_{(0,1)}(r)`  (equal as functions, by `funext`),

which is measurable and integrable on `(0,∞)`: the hypothesis `hInt` holds.  But
`fun x ↦ ψ ‖x‖` is *not* a.e. strongly measurable, hence not integrable: if it were a.e.
equal to a strongly measurable `g`, then (slicing `ℝ³ = ℝ × ℝ²` and then `ℝ² = ℝ × ℝ`,
using that a.e. sections of a null set are null and that `g` has measurable sections) the
function `u ↦ ψ (√(u² + c²))` would be a.e. equal to a measurable function for some small
`c > 0`; the Lipschitz map `u ↦ √(u² + c²)` transports this to *all* radii `r > c`, so `A`
would be measurable up to a null set — a contradiction.

So the requested statement is false as written.  Adding `AEStronglyMeasurable ψ` on `(0,∞)`
(which is what the proof route in the docstring implicitly uses when it dominates `r²|ψ r|`
by `max R 1 * (r|ψ r|)` — domination requires measurability of the dominated function) makes
it true; that corrected statement is `RadialWeightFourierDecay_of_aemeasurable` below, with
the same conclusion and the same proof.
-/

namespace Work.BoseFixR.LatGreen

open MeasureTheory
open scoped Real

/-! ## Elementary inputs -/

/-- `sincR` is measurable: it is a piecewise function whose piece is the measurable set `{0}`. -/
lemma measurable_sincR : Measurable Work.BoseFixR.sincR := by
  show Measurable fun x : ℝ => if x = 0 then (1 : ℝ) else Real.sin x / x
  exact Measurable.ite (measurableSet_singleton 0) measurable_const
    (Real.measurable_sin.div measurable_id)

/-- `|sincR u| ≤ 1/|u|` for `u ≠ 0` (the decay input for the `1/‖ν‖` regime). -/
lemma abs_sincR_le_inv_abs {u : ℝ} (hu : u ≠ 0) :
    |Work.BoseFixR.sincR u| ≤ 1 / |u| := by
  rw [Work.BoseFixR.sincR_of_ne hu, abs_div, div_le_div_iff_of_pos_right (abs_pos.mpr hu)]
  exact Real.abs_sin_le_one u

/-- For a real-valued function on `(0,∞)`, `|∫ f| ≤ ∫ |f|` (the `|·|`/`‖·‖` normalisation of
`MeasureTheory.norm_integral_le_integral_norm`). -/
lemma abs_integral_Ioi_le {f : ℝ → ℝ} :
    |∫ r in Set.Ioi (0 : ℝ), f r| ≤ ∫ r in Set.Ioi (0 : ℝ), |f r| := by
  have h := norm_integral_le_integral_norm (μ := volume.restrict (Set.Ioi (0 : ℝ))) f
  simpa only [Real.norm_eq_abs] using h

/-- `Integrable (fun r => |f r|)` on `(0,∞)` from `IntegrableOn f (Ioi 0)`. -/
lemma integrable_abs_restrict {f : ℝ → ℝ} (h : IntegrableOn f (Set.Ioi (0 : ℝ))) :
    Integrable (fun r : ℝ => |f r|) (volume.restrict (Set.Ioi (0 : ℝ))) := by
  simpa only [Real.norm_eq_abs] using h.integrable.norm

/-- The norm of the coercion `ℝ → ℂ`: `‖(x : ℂ)‖ = |x|`. -/
lemma norm_ofReal_complex (x : ℝ) : ‖((x : ℝ) : ℂ)‖ = |x| := by
  have h := Complex.isometry_ofReal.dist_eq (0 : ℝ) x
  rw [Complex.dist_eq, Real.dist_eq] at h
  simpa using h

/-! ## The Fourier transform of an even real function is its cosine transform -/

/-- The imaginary part of `e^{−it}·w` for real `t w`: `(e^{−it}w).im = −w sin t`. -/
private lemma im_exp_mul_ofReal (t w : ℝ) :
    (Complex.exp (-(Complex.I * (t : ℂ))) * ((w : ℝ) : ℂ)).im = -(Real.sin t * w) := by
  have hz : -(Complex.I * (t : ℂ)) = ((-t : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [hz, Complex.mul_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
    Complex.ofReal_re, Complex.ofReal_im, Real.cos_neg, Real.sin_neg]
  ring

/-- The integral of `x ↦ sin⟪p,x⟫ · W x` vanishes for an even `W` (the integrand is odd and
Lebesgue measure on `ℝ³` is invariant under `x ↦ -x`). -/
lemma sin_integral_eq_zero_of_even {W : EuclideanSpace ℝ (Fin 3) → ℝ}
    (heven : ∀ x : EuclideanSpace ℝ (Fin 3), W (-x) = W x) (p : EuclideanSpace ℝ (Fin 3)) :
    (∫ x : EuclideanSpace ℝ (Fin 3), Real.sin (inner ℝ p x) * W x) = 0 := by
  set f : EuclideanSpace ℝ (Fin 3) → ℝ :=
    fun x => Real.sin (inner ℝ p x) * W x with hf
  have hodd : ∀ x : EuclideanSpace ℝ (Fin 3), f (-x) = - f x := by
    intro x
    rw [hf]
    show Real.sin (inner ℝ p (-x)) * W (-x) = -(Real.sin (inner ℝ p x) * W x)
    rw [inner_neg_right, Real.sin_neg, heven x]
    ring
  have h1 : (∫ x : EuclideanSpace ℝ (Fin 3), f (-x)) = ∫ x : EuclideanSpace ℝ (Fin 3), f x :=
    integral_neg_eq_self f (volume : Measure (EuclideanSpace ℝ (Fin 3)))
  have h2 : (∫ x : EuclideanSpace ℝ (Fin 3), f (-x)) =
      - ∫ x : EuclideanSpace ℝ (Fin 3), f x := by
    rw [show (fun x : EuclideanSpace ℝ (Fin 3) => f (-x)) =
        (fun x : EuclideanSpace ℝ (Fin 3) => - f x) from funext hodd, integral_neg]
  have h3 : (∫ x : EuclideanSpace ℝ (Fin 3), f x) =
      - ∫ x : EuclideanSpace ℝ (Fin 3), f x := h1.symm.trans h2
  linarith

/-- For an even integrable real `W` on `ℝ³`, the `p`-convention Fourier transform of its
complexification is real: its imaginary part vanishes. -/
lemma kinFT_im_eq_zero_of_even {W : EuclideanSpace ℝ (Fin 3) → ℝ} (hW : Integrable W)
    (heven : ∀ x : EuclideanSpace ℝ (Fin 3), W (-x) = W x)
    (p : EuclideanSpace ℝ (Fin 3)) :
    (Submission.BoseGases.kinFT (fun x : EuclideanSpace ℝ (Fin 3) => ((W x : ℝ) : ℂ)) p).im
      = 0 := by
  have hnorm : ∀ y : EuclideanSpace ℝ (Fin 3),
      ‖Complex.exp (-(Complex.I * (inner ℝ p y : ℂ)))‖ ≤ 1 := by
    intro y
    simp [Complex.norm_exp]
  have hInt : Integrable (fun y : EuclideanSpace ℝ (Fin 3) =>
      Complex.exp (-(Complex.I * (inner ℝ p y : ℂ))) * ((W y : ℝ) : ℂ)) :=
    hW.ofReal.bdd_mul (c := 1) (by fun_prop) (Filter.Eventually.of_forall hnorm)
  have hpt : ∀ y : EuclideanSpace ℝ (Fin 3),
      (Complex.exp (-(Complex.I * (inner ℝ p y : ℂ))) * ((W y : ℝ) : ℂ)).im
        = -(Real.sin (inner ℝ p y) * W y) :=
    fun y => im_exp_mul_ofReal (inner ℝ p y) (W y)
  rw [Submission.BoseGases.kinFT, ← Complex.imCLM_apply,
    ← ContinuousLinearMap.integral_comp_comm Complex.imCLM hInt]
  simp only [Complex.imCLM_apply]
  rw [show (∫ y : EuclideanSpace ℝ (Fin 3),
      (Complex.exp (-(Complex.I * (inner ℝ p y : ℂ))) * ((W y : ℝ) : ℂ)).im)
        = ∫ y : EuclideanSpace ℝ (Fin 3), -(Real.sin (inner ℝ p y) * W y) from
    integral_congr_ae (Filter.Eventually.of_forall hpt), integral_neg,
    sin_integral_eq_zero_of_even heven p, neg_zero]

/-- `𝓕 g ν = kinFT g ((2π) • ν)`: the two Fourier conventions. -/
lemma fourier_eq_kinFT (g : EuclideanSpace ℝ (Fin 3) → ℂ)
    (ν : EuclideanSpace ℝ (Fin 3)) :
    FourierTransform.fourier g ν = Submission.BoseGases.kinFT g ((2 * Real.pi) • ν) := by
  rw [Work.SmallBoxBridge.Resolve.kinFT_eq_fourier g ((2 * Real.pi) • ν), smul_smul,
    inv_mul_cancel₀ (by positivity : (2 * Real.pi) ≠ 0), one_smul]

/-- **The Fourier transform of an even real function is its cosine transform.**  For integrable
even `W`, `𝓕 (W : ℂ) ν = (chat W ((2π)•ν) : ℂ)`. -/
theorem fourier_ofReal_eq_chat {W : EuclideanSpace ℝ (Fin 3) → ℝ} (hW : Integrable W)
    (heven : ∀ x : EuclideanSpace ℝ (Fin 3), W (-x) = W x)
    (ν : EuclideanSpace ℝ (Fin 3)) :
    FourierTransform.fourier (fun x : EuclideanSpace ℝ (Fin 3) => ((W x : ℝ) : ℂ)) ν
      = ((Work.BoseFixR.chat W ((2 * Real.pi) • ν) : ℝ) : ℂ) := by
  have him : (Submission.BoseGases.kinFT (fun x : EuclideanSpace ℝ (Fin 3) => ((W x : ℝ) : ℂ))
      ((2 * Real.pi) • ν)).im = 0 := kinFT_im_eq_zero_of_even hW heven _
  have hre : Work.BoseFixR.chat W ((2 * Real.pi) • ν)
      = (Submission.BoseGases.kinFT (fun x : EuclideanSpace ℝ (Fin 3) => ((W x : ℝ) : ℂ))
          ((2 * Real.pi) • ν)).re := rfl
  rw [fourier_eq_kinFT]
  apply Complex.ext
  · simp [hre]
  · simpa [hre] using him

/-! ## The two dominated moments of `ψ` -/

/-- **`r ↦ r² ψ r` and `r ↦ r² |ψ r|` are integrable on `(0,∞)`.**  This is the domination
`r²|ψ r| ≤ max R 1 · r|ψ r|` (for `r ≥ R` both sides vanish), which needs the a.e. strong
measurability of `ψ` — that is *not* implied by the integrability of `r|ψ r|`. -/
lemma integrableOn_sq_mul_of_aemeasurable {ψ : ℝ → ℝ} {R : ℝ} (hR : 0 < R)
    (hψ : ∀ r : ℝ, R ≤ r → ψ r = 0)
    (hψm : AEStronglyMeasurable ψ (volume.restrict (Set.Ioi (0 : ℝ))))
    (hInt : IntegrableOn (fun r : ℝ => r * |ψ r|) (Set.Ioi (0 : ℝ))) :
    IntegrableOn (fun r : ℝ => r ^ 2 * ψ r) (Set.Ioi (0 : ℝ)) ∧
      IntegrableOn (fun r : ℝ => r ^ 2 * |ψ r|) (Set.Ioi (0 : ℝ)) := by
  have hMnn : (0 : ℝ) ≤ max R 1 := le_max_of_le_right zero_le_one
  have hmeas1 : AEStronglyMeasurable (fun r : ℝ => r ^ 2 * ψ r)
      (volume.restrict (Set.Ioi (0 : ℝ))) :=
    ((continuous_id.pow 2).aestronglyMeasurable).mul hψm
  have hmeas2 : AEStronglyMeasurable (fun r : ℝ => r ^ 2 * |ψ r|)
      (volume.restrict (Set.Ioi (0 : ℝ))) := by
    have h : AEStronglyMeasurable (fun r : ℝ => r ^ 2 * ‖ψ r‖)
        (volume.restrict (Set.Ioi (0 : ℝ))) :=
      ((continuous_id.pow 2).aestronglyMeasurable).mul hψm.norm
    simpa only [Real.norm_eq_abs] using h
  have hdom : Integrable (fun r : ℝ => max R 1 * (r * |ψ r|))
      (volume.restrict (Set.Ioi (0 : ℝ))) := hInt.const_mul (max R 1)
  constructor
  · refine hdom.mono' hmeas1 ?_
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with r hr
    have hrp : 0 < r := hr
    by_cases hRr : R ≤ r
    · simp [hψ r hRr]
    · have h1 : ‖r ^ 2 * ψ r‖ = r ^ 2 * |ψ r| := by
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg r)]
      rw [h1, show r ^ 2 * |ψ r| = r * (r * |ψ r|) from by ring]
      exact mul_le_mul_of_nonneg_right
        (le_trans (le_of_lt (lt_of_not_ge hRr)) (le_max_left R 1))
        (mul_nonneg hrp.le (abs_nonneg _))
  · refine hdom.mono' hmeas2 ?_
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with r hr
    have hrp : 0 < r := hr
    by_cases hRr : R ≤ r
    · simp [hψ r hRr]
    · have h1 : ‖r ^ 2 * |ψ r|‖ = r ^ 2 * |ψ r| := by
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg r) (abs_nonneg _))]
      rw [h1, show r ^ 2 * |ψ r| = r * (r * |ψ r|) from by ring]
      exact mul_le_mul_of_nonneg_right
        (le_trans (le_of_lt (lt_of_not_ge hRr)) (le_max_left R 1))
        (mul_nonneg hrp.le (abs_nonneg _))

/-! ## The Fourier decay of `ψ ‖·‖` -/

/-- **Fourier decay of a radial weight, with a.e. measurability made explicit.**  For `0 < R`,
`ψ` vanishing on `[R,∞)`, `ψ` a.e. strongly measurable on `(0,∞)` and `r ↦ r|ψ r|` integrable
on `(0,∞)`:

* `x ↦ ψ ‖x‖` is integrable on `ℝ³`, and
* `‖𝓕 (fun x ↦ ψ ‖x‖ : ℂ) ν‖ ≤ C/(1 + ‖ν‖)` for all `ν`, for some `C ≥ 0`.

`C := max (8π·max R 1·∫₀^∞ r|ψ r|) (4·∫₀^∞ r|ψ r|)` works. -/
theorem RadialWeightFourierDecay_of_aemeasurable {ψ : ℝ → ℝ} {R : ℝ} (hR : 0 < R)
    (hψ : ∀ r : ℝ, R ≤ r → ψ r = 0)
    (hψm : AEStronglyMeasurable ψ (volume.restrict (Set.Ioi (0 : ℝ))))
    (hInt : IntegrableOn (fun r : ℝ => r * |ψ r|) (Set.Ioi (0 : ℝ))) :
    Integrable (fun x : EuclideanSpace ℝ (Fin 3) => ψ ‖x‖) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ ν : EuclideanSpace ℝ (Fin 3),
        ‖FourierTransform.fourier
            (fun x : EuclideanSpace ℝ (Fin 3) => ((ψ ‖x‖ : ℝ) : ℂ)) ν‖ ≤ C / (1 + ‖ν‖) := by
  obtain ⟨hIntψ2, hIntabs2⟩ := integrableOn_sq_mul_of_aemeasurable hR hψ hψm hInt
  have hWint : Integrable (fun x : EuclideanSpace ℝ (Fin 3) => ψ ‖x‖) :=
    (Submission.BoseGases.integrable_radial_r3 (f := ψ)).mpr hIntψ2
  -- the two integrals `L = ∫₀^∞ r|ψ r|` and `D = ∫₀^∞ r²|ψ r|`
  set L : ℝ := ∫ r in Set.Ioi (0 : ℝ), r * |ψ r| with hL
  set D : ℝ := ∫ r in Set.Ioi (0 : ℝ), r ^ 2 * |ψ r| with hD
  have hLnn : 0 ≤ L := by
    rw [hL]
    exact setIntegral_nonneg measurableSet_Ioi (fun r hr => mul_nonneg hr.le (abs_nonneg _))
  have hDle : D ≤ max R 1 * L := by
    rw [hD, hL]
    have hdom : Integrable (fun r : ℝ => max R 1 * (r * |ψ r|))
        (volume.restrict (Set.Ioi (0 : ℝ))) := hInt.const_mul (max R 1)
    have hpt : (fun r : ℝ => r ^ 2 * |ψ r|)
        ≤ᵐ[volume.restrict (Set.Ioi (0 : ℝ))] (fun r : ℝ => max R 1 * (r * |ψ r|)) := by
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with r hr
      have hrp : 0 < r := hr
      by_cases hRr : R ≤ r
      · simp [hψ r hRr]
      · rw [show r ^ 2 * |ψ r| = r * (r * |ψ r|) from by ring]
        exact mul_le_mul_of_nonneg_right (le_trans (le_of_lt (lt_of_not_ge hRr)) (le_max_left R 1))
          (mul_nonneg hrp.le (abs_nonneg _))
    calc (∫ r in Set.Ioi (0 : ℝ), r ^ 2 * |ψ r|)
        ≤ ∫ r in Set.Ioi (0 : ℝ), max R 1 * (r * |ψ r|) :=
          integral_mono_ae hIntabs2 hdom hpt
      _ = max R 1 * ∫ r in Set.Ioi (0 : ℝ), r * |ψ r| := integral_const_mul _ _
  -- measurability and integrability of the oscillatory integrand against `sincR`
  have hsinc_meas : ∀ q : EuclideanSpace ℝ (Fin 3), AEStronglyMeasurable
      (fun r : ℝ => Work.BoseFixR.sincR (‖q‖ * r))
      (volume.restrict (Set.Ioi (0 : ℝ))) :=
    fun q => (measurable_sincR.comp (measurable_const.mul measurable_id)).aestronglyMeasurable
  have hgq_int : ∀ q : EuclideanSpace ℝ (Fin 3), IntegrableOn
      (fun r : ℝ => r ^ 2 * ψ r * Work.BoseFixR.sincR (‖q‖ * r)) (Set.Ioi (0 : ℝ)) := by
    intro q
    refine hIntabs2.mono'
      (((continuous_id.pow 2).aestronglyMeasurable).mul hψm |>.mul (hsinc_meas q)) ?_
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with r _
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (sq_nonneg r)]
    calc r ^ 2 * |ψ r| * |Work.BoseFixR.sincR (‖q‖ * r)| ≤ r ^ 2 * |ψ r| * 1 :=
          mul_le_mul_of_nonneg_left (Work.BoseFixR.abs_sincR_le_one _)
            (mul_nonneg (sq_nonneg r) (abs_nonneg _))
      _ = r ^ 2 * |ψ r| := mul_one _
  -- the two regimes
  have hbnd1 : ∀ q : EuclideanSpace ℝ (Fin 3),
      |Work.BoseFixR.chat (fun x : EuclideanSpace ℝ (Fin 3) => ψ ‖x‖) q|
        ≤ 4 * Real.pi * ∫ r in Set.Ioi (0 : ℝ), r ^ 2 * |ψ r| := by
    intro q
    rw [Work.BoseFixR.Rb5Lin.radial_fourier_sinc hWint (fun x => rfl) q]
    have h1 : |∫ r in Set.Ioi (0 : ℝ), r ^ 2 * ψ r * Work.BoseFixR.sincR (‖q‖ * r)|
        ≤ ∫ r in Set.Ioi (0 : ℝ), r ^ 2 * |ψ r| := by
      refine le_trans (abs_integral_Ioi_le (f := fun r : ℝ =>
          r ^ 2 * ψ r * Work.BoseFixR.sincR (‖q‖ * r)))
        (integral_mono_ae (integrable_abs_restrict (hgq_int q)) hIntabs2 ?_)
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with r _
      rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg r)]
      calc r ^ 2 * |ψ r| * |Work.BoseFixR.sincR (‖q‖ * r)| ≤ r ^ 2 * |ψ r| * 1 :=
            mul_le_mul_of_nonneg_left (Work.BoseFixR.abs_sincR_le_one _)
              (mul_nonneg (sq_nonneg r) (abs_nonneg _))
        _ = r ^ 2 * |ψ r| := mul_one _
    calc |4 * Real.pi * ∫ r in Set.Ioi (0 : ℝ),
            r ^ 2 * ψ r * Work.BoseFixR.sincR (‖q‖ * r)|
        = 4 * Real.pi * |∫ r in Set.Ioi (0 : ℝ),
            r ^ 2 * ψ r * Work.BoseFixR.sincR (‖q‖ * r)| := by
          rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 4 * Real.pi)]
      _ ≤ 4 * Real.pi * ∫ r in Set.Ioi (0 : ℝ), r ^ 2 * |ψ r| :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
  have hbnd2 : ∀ q : EuclideanSpace ℝ (Fin 3), 1 ≤ ‖q‖ →
      |Work.BoseFixR.chat (fun x : EuclideanSpace ℝ (Fin 3) => ψ ‖x‖) q|
        ≤ 4 * Real.pi * (∫ r in Set.Ioi (0 : ℝ), r * |ψ r|) / ‖q‖ := by
    intro q hq
    rw [Work.BoseFixR.Rb5Lin.radial_fourier_sinc hWint (fun x => rfl) q]
    have hqpos : 0 < ‖q‖ := lt_of_lt_of_le one_pos hq
    have hqne : ‖q‖ ≠ 0 := ne_of_gt hqpos
    have h1 : |∫ r in Set.Ioi (0 : ℝ), r ^ 2 * ψ r * Work.BoseFixR.sincR (‖q‖ * r)|
        ≤ (∫ r in Set.Ioi (0 : ℝ), r * |ψ r|) / ‖q‖ := by
      rw [← integral_div ‖q‖ (fun r : ℝ => r * |ψ r|)]
      refine le_trans (abs_integral_Ioi_le (f := fun r : ℝ =>
          r ^ 2 * ψ r * Work.BoseFixR.sincR (‖q‖ * r)))
        (integral_mono_ae (integrable_abs_restrict (hgq_int q)) (hInt.integrable.div_const ‖q‖) ?_)
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with r hr
      have hrp : 0 < r := hr
      have hqr : ‖q‖ * r ≠ 0 := by positivity
      rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg r)]
      calc r ^ 2 * |ψ r| * |Work.BoseFixR.sincR (‖q‖ * r)|
          ≤ r ^ 2 * |ψ r| * (1 / (‖q‖ * r)) := by
            refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (sq_nonneg r) (abs_nonneg _))
            have h := abs_sincR_le_inv_abs hqr
            rwa [abs_of_pos (by positivity : (0 : ℝ) < ‖q‖ * r)] at h
        _ = (r * |ψ r|) / ‖q‖ := by
            field_simp
            try ring
    calc |4 * Real.pi * ∫ r in Set.Ioi (0 : ℝ),
            r ^ 2 * ψ r * Work.BoseFixR.sincR (‖q‖ * r)|
        = 4 * Real.pi * |∫ r in Set.Ioi (0 : ℝ),
            r ^ 2 * ψ r * Work.BoseFixR.sincR (‖q‖ * r)| := by
          rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 4 * Real.pi)]
      _ ≤ 4 * Real.pi * ((∫ r in Set.Ioi (0 : ℝ), r * |ψ r|) / ‖q‖) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = 4 * Real.pi * (∫ r in Set.Ioi (0 : ℝ), r * |ψ r|) / ‖q‖ := by ring
  refine ⟨hWint, max (8 * Real.pi * max R 1 * L) (4 * L), ?_, ?_⟩
  · have h1 : (0 : ℝ) ≤ 8 * Real.pi * max R 1 * L := by
      have hpos : (0 : ℝ) < max R 1 := lt_of_lt_of_le one_pos (le_max_right R 1)
      positivity
    exact le_trans h1 (le_max_left _ _)
  · intro ν
    rw [fourier_ofReal_eq_chat hWint (fun x : EuclideanSpace ℝ (Fin 3) => by simp) ν,
      norm_ofReal_complex, le_div_iff₀ (by positivity : (0 : ℝ) < 1 + ‖ν‖)]
    have h1 : |Work.BoseFixR.chat (fun x : EuclideanSpace ℝ (Fin 3) => ψ ‖x‖)
        ((2 * Real.pi) • ν)| ≤ 4 * Real.pi * D := by
      have := hbnd1 ((2 * Real.pi) • ν)
      rwa [← hD] at this
    by_cases hν : ‖ν‖ ≤ 1
    · have h1' : |Work.BoseFixR.chat (fun x : EuclideanSpace ℝ (Fin 3) => ψ ‖x‖)
          ((2 * Real.pi) • ν)| ≤ 4 * Real.pi * max R 1 * L := by
        have h3 : 4 * Real.pi * D ≤ 4 * Real.pi * (max R 1 * L) :=
          mul_le_mul_of_nonneg_left hDle (by positivity)
        linarith
      have h4 : 1 + ‖ν‖ ≤ 2 := by linarith
      have h6 : |Work.BoseFixR.chat (fun x : EuclideanSpace ℝ (Fin 3) => ψ ‖x‖)
            ((2 * Real.pi) • ν)| * (1 + ‖ν‖) ≤ (4 * Real.pi * max R 1 * L) * 2 :=
        mul_le_mul h1' h4 (by positivity) (by positivity)
      have h7 : (4 * Real.pi * max R 1 * L) * 2
          ≤ max (8 * Real.pi * max R 1 * L) (4 * L) := by
        have he : (4 * Real.pi * max R 1 * L) * 2 = 8 * Real.pi * max R 1 * L := by ring
        rw [he]
        exact le_max_left _ _
      linarith
    · push_neg at hν
      have hpn : ‖(2 * Real.pi) • ν‖ = 2 * Real.pi * ‖ν‖ := by
        rw [norm_smul, Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
      have hq1 : 1 ≤ ‖(2 * Real.pi) • ν‖ := by
        rw [hpn]
        nlinarith [hν, Real.pi_gt_three]
      have h2 : |Work.BoseFixR.chat (fun x : EuclideanSpace ℝ (Fin 3) => ψ ‖x‖)
          ((2 * Real.pi) • ν)| ≤ 2 * L / ‖ν‖ := by
        have h0 := hbnd2 ((2 * Real.pi) • ν) hq1
        rw [← hL, hpn] at h0
        have hπ : (2 * Real.pi) ≠ 0 := by positivity
        have hνne : ‖ν‖ ≠ 0 := by positivity
        calc |Work.BoseFixR.chat (fun x : EuclideanSpace ℝ (Fin 3) => ψ ‖x‖)
              ((2 * Real.pi) • ν)|
            ≤ 4 * Real.pi * L / (2 * Real.pi * ‖ν‖) := h0
          _ = 2 * L / ‖ν‖ := by
              field_simp
              ring
      have h7 : (2 * L / ‖ν‖) * (1 + ‖ν‖) ≤ 4 * L := by
        have hνpos : 0 < ‖ν‖ := by linarith
        have h5 : 1 + ‖ν‖ ≤ 2 * ‖ν‖ := by linarith
        rw [div_mul_eq_mul_div, div_le_iff₀ hνpos]
        have h6 : 2 * L * (1 + ‖ν‖) ≤ 2 * L * (2 * ‖ν‖) :=
          mul_le_mul_of_nonneg_left h5 (by linarith)
        linarith
      have h8 : |Work.BoseFixR.chat (fun x : EuclideanSpace ℝ (Fin 3) => ψ ‖x‖)
            ((2 * Real.pi) • ν)| * (1 + ‖ν‖) ≤ 4 * L :=
        le_trans (mul_le_mul_of_nonneg_right h2 (by positivity)) h7
      have h9 : 4 * L ≤ max (8 * Real.pi * max R 1 * L) (4 * L) := le_max_right _ _
      linarith

/-- **The Fourier transform of a radial weight `ψ‖·‖` decays like `1/(1+‖ν‖)`, and the weight
is integrable** (namespace `Work.BoseFixR.LatGreen`).

Hypotheses: `0 < R`, `ψ` vanishes on `[R,∞)`, and `r ↦ r·|ψ r|` is integrable on `(0,∞)`.
(No regularity of `ψ` is assumed.)

Conclusion: `x ↦ ψ ‖x‖` is integrable on `ℝ³`, and there is `C ≥ 0` with
`‖𝓕 (fun x => (ψ ‖x‖ : ℂ)) ν‖ ≤ C/(1+‖ν‖)` for every `ν`.

Proof route (constants free, `L := ∫₀^∞ r|ψ r|`, `D := ∫₀^∞ r²|ψ r|`):

* `Integrable (fun x => ψ ‖x‖)`: `Submission.BoseGases.integrable_radial_r3` reduces this to
  `IntegrableOn (fun r => r² ψ r) (Ioi 0)`, which follows from
  `r²|ψ r| ≤ max R 1 · r|ψ r|` on `(0,∞)` (for `r ≥ R` both sides vanish since `ψ r = 0`).
* The second conjunct: by `Work.BoseFixR.Rb5Lin.radial_fourier_sinc` (with `W := fun x => ψ ‖x‖`)
  together with `Work.BoseFixR.Rb5Lin.chat_eq_cos` and the evenness `ψ ‖-x‖ = ψ ‖x‖` (which kills
  the imaginary part of the Fourier transform), one has
  `𝓕 (fun x => (ψ ‖x‖ : ℂ)) ν = (chat (fun x => ψ ‖x‖) ((2*π) • ν) : ℂ)`, and
  `chat (fun x => ψ ‖x‖) p = 4π ∫₀^∞ r² ψ r sincR (‖p‖ r) dr`.  Then
  `|sincR u| ≤ 1` gives the bound `4πD` for all `p`, while `|sincR u| ≤ 1/|u|` gives
  the bound `(4π/‖p‖)L = 2L/‖ν‖` for `p = (2π)•ν`, `ν ≠ 0`.  Combining the two regimes
  (`‖ν‖ ≤ 1` and `‖ν‖ ≥ 1`) with `D ≤ max R 1 · L` yields the stated form.
  Constants are free; e.g. `C := 8π·max R 1·L + 8L` works. -/
theorem RadialWeightFourierDecay {ψ : ℝ → ℝ} {R : ℝ} (hR : 0 < R)
    (hψ : ∀ r : ℝ, R ≤ r → ψ r = 0)
    (hInt : MeasureTheory.IntegrableOn (fun r : ℝ => r * |ψ r|) (Set.Ioi (0 : ℝ))) :
    MeasureTheory.Integrable (fun x : EuclideanSpace ℝ (Fin 3) => ψ ‖x‖) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ ν : EuclideanSpace ℝ (Fin 3),
        ‖FourierTransform.fourier
            (fun x : EuclideanSpace ℝ (Fin 3) => ((ψ ‖x‖ : ℝ) : ℂ)) ν‖ ≤ C / (1 + ‖ν‖) := by
  sorry

end Work.BoseFixR.LatGreen

