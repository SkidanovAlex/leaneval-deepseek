import Mathlib
import Submission.Work.BourgainPlan.Maximal.annulusPartitionDefs
import Submission.Work.BourgainPlan.Maximal.annulusSqfunDefs
import Submission.Commons.Analysis.Fourier.fourierInv_mul_fourier_eq_convolution

/-!
# Self-adjointness of the annulus projection in the `L²` pairing

The annulus projection `f ↦ K_n * f` (`K_n = 𝓕⁻ (annAtomC n)`) is the multiplier operator with
symbol `annAtomC n`.  Since that symbol is real-valued (`annAtomC n` is the complex lift of the
real-valued `annAtomZ n`), the operator is self-adjoint for the Hermitian pairing
`(f, g) ↦ ∫ x, f x * star (g x)`.

The proof avoids any double integral: it uses only the elementary Fourier pairing
`∫ x, 𝓕⁻ h x * star (k x) = ∫ x, h x * star (𝓕 k x)` (`star_pairing_fourierInv`, a rewriting of
`VectorFourier.integral_sesq_fourierIntegral_eq_neg_flip` from Mathlib's `inner` to `a * star b`)
and the convolution/multiplier identity `annulusConv (annAtomC n) f = 𝓕⁻ (annAtomC n · 𝓕 f)`
(`Commons.Analysis.Fourier.fourierInv_mul_fourier_eq_convolution`), which needs only the
integrability of `f` and of `annAtomC n`.  The pairing lemma needs the symbol times the Fourier
transform of the test function to be integrable: `annAtomC n` is bounded, supported in the bounded
interval `|ξ| < (3/2)·2^{-n}`, and `𝓕 f` is bounded by `∫ ‖f‖`, which gives that integrability
without any `L²` input.
-/

open MeasureTheory Filter
open scoped FourierTransform ENNReal

namespace Work.BourgainPlan.Maximal

/-! ## Elementary `star` calculus for the Bochner integral -/

/-- Conjugation commutes with the Bochner integral for `ℂ`-valued functions. -/
private lemma integral_star_eq (f : ℝ → ℂ) : ∫ x : ℝ, star (f x) = star (∫ x : ℝ, f x) := by
  rw [Complex.star_def]
  exact integral_conj

/-- **The Hermitian pairing is conjugated by swapping its arguments**:
`∫ x, f x * star (h x) = star (∫ x, h x * star (f x))`.  This is a purely pointwise identity
(no integrability is required) followed by `integral_star_eq`. -/
private lemma integral_mul_star_eq (f h : ℝ → ℂ) :
    ∫ x : ℝ, f x * star (h x) = star (∫ x : ℝ, h x * star (f x)) := by
  calc ∫ x : ℝ, f x * star (h x)
      = ∫ x : ℝ, star (h x * star (f x)) := by
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        simp only []
        rw [star_mul, star_star]
    _ = star (∫ x : ℝ, h x * star (f x)) := integral_star_eq _

/-- The Fourier integral with the sign-twisted kernel `-L.flip` is the inverse Fourier transform. -/
private lemma fourierIntegral_neg_flip_eq_fourierInv (k : ℝ → ℂ) :
    VectorFourier.fourierIntegral Real.fourierChar volume (-(innerₗ ℝ).flip) k = 𝓕⁻ k := by
  funext x
  rw [Real.fourierInv_eq, VectorFourier.fourierIntegral]
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  simp

/-- **The `L¹` Plancherel pairing in its `inner` form.**  For integrable `h` and `k`, the inverse
Fourier transform is adjoint to the Fourier transform for the pairing `inner ℂ`.  This is
Mathlib's `VectorFourier.integral_sesq_fourierIntegral_eq_neg_flip` specialised to `ℝ`; only
integrability of `h`, `k` is needed (no `L²`, no density argument). -/
private lemma pairing_fourierInv_inner (h k : ℝ → ℂ) (hh : Integrable h) (hk : Integrable k) :
    ∫ x : ℝ, inner ℂ (𝓕⁻ h x) (k x) = ∫ x : ℝ, inner ℂ (h x) (𝓕 k x) := by
  have hcomp : Integrable (fun x : ℝ => h (-x)) := hh.comp_neg
  have key := VectorFourier.integral_sesq_fourierIntegral_eq_neg_flip
      (𝕜 := ℝ) (V := ℝ) (W := ℝ) (E := ℂ) (F := ℂ) (G := ℂ)
      (e := Real.fourierChar) (μ := volume) (ν := volume) (L := innerₗ ℝ)
      (f := fun x : ℝ => h (-x)) (g := k) (innerSL ℂ) Real.continuous_fourierChar
      (by fun_prop) hcomp hk
  have key' : ∫ ξ, inner ℂ (VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ ℝ)
        (fun x => h (-x)) ξ) (k ξ)
      = ∫ x, inner ℂ (h (-x)) (𝓕⁻ k x) := by
    simpa only [innerSL_apply_apply, fourierIntegral_neg_flip_eq_fourierInv] using key
  rw [Real.fourierInv_eq_fourier_comp_neg h,
      show (∫ x, inner ℂ (𝓕 (fun x => h (-x)) x) (k x)) = ∫ x, inner ℂ (h (-x)) (𝓕⁻ k x)
        from key']
  simp_rw [Real.fourierInv_eq_fourier_neg]
  exact integral_neg_eq_self (fun y : ℝ => inner ℂ (h y) (𝓕 k y)) volume

/-- Uniform bound on the Fourier transform of an integrable function (its `L¹` norm). -/
private lemma norm_fourier_le (f : ℝ → ℂ) (ξ : ℝ) : ‖𝓕 f ξ‖ ≤ ∫ x : ℝ, ‖f x‖ :=
  VectorFourier.norm_fourierIntegral_le_integral_norm Real.fourierChar volume (innerₗ ℝ) f ξ

/-- **The Fourier pairing is Hermitian.**  For integrable `h` and `k`,
`∫ x, 𝓕⁻h x * star (k x) = ∫ x, h x * star (𝓕 k x)`.

This is `pairing_fourierInv_inner` rewritten from Mathlib's `inner ℂ a b = b * star a` to the
pairing `a * star b` with the help of `integral_mul_star_eq`. -/
lemma star_pairing_fourierInv (h k : ℝ → ℂ) (hh : Integrable h) (hk : Integrable k) :
    ∫ x : ℝ, 𝓕⁻ h x * star (k x) = ∫ x : ℝ, h x * star (𝓕 k x) := by
  have hpair := pairing_fourierInv_inner h k hh hk
  simp only [RCLike.inner_apply] at hpair
  rw [← Complex.star_def] at hpair
  rw [integral_mul_star_eq (𝓕⁻ h) k, hpair, ← integral_mul_star_eq h (𝓕 k)]

/-! ## The symbol `annAtomC n`: real-valued, bounded, compactly supported -/

/-- `annAtomC n` is real-valued. -/
lemma star_annAtomC (n : ℤ) (ξ : ℝ) : star (annAtomC n ξ) = annAtomC n ξ := by
  simp [annAtomC]

/-- `annAtomC n` vanishes where `|2^n ξ| ≥ 3/2`. -/
lemma annAtomC_eq_zero_of_three_halves_le {n : ℤ} {ξ : ℝ}
    (h : (3 : ℝ) / 2 ≤ |(2 : ℝ) ^ n * ξ|) : annAtomC n ξ = 0 := by
  rw [annAtomC_apply, annAtomZ, annAtom_eq_zero_of_three_halves_le_abs h, Complex.ofReal_zero]

/-- `annAtomC n` is bounded by one. -/
lemma norm_annAtomC_le_one (n : ℤ) (ξ : ℝ) : ‖annAtomC n ξ‖ ≤ 1 := by
  rw [annAtomC_apply]
  have h : ‖((annAtomZ n ξ : ℝ) : ℂ)‖ = |annAtomZ n ξ| := by simp
  rw [h]
  exact abs_le.mpr ⟨by linarith [annAtomZ_nonneg n ξ], annAtomZ_le_one n ξ⟩

/-- An interval endpoint comparison: outside `[-R,R]` (with `R > 0`) the absolute value exceeds
`R`. -/
private lemma lt_abs_of_notMem_Icc {R ξ : ℝ} (hR : 0 < R) (h : ξ ∉ Set.Icc (-R) R) : R < |ξ| := by
  simp only [Set.mem_Icc, not_and_or, not_le] at h
  rcases h with h | h
  · rw [abs_of_neg (by linarith)]
    linarith
  · rw [abs_of_pos (by linarith)]
    linarith

/-- `annAtomC n` vanishes where `|ξ| ≥ (3/2)·2^{-n}`. -/
lemma annAtomC_eq_zero_of_le {n : ℤ} {ξ : ℝ} (h : 3 / 2 / (2 : ℝ) ^ n ≤ |ξ|) :
    annAtomC n ξ = 0 := by
  refine annAtomC_eq_zero_of_three_halves_le ?_
  rw [abs_mul, abs_of_pos (show (0 : ℝ) < (2 : ℝ) ^ n by positivity)]
  calc (3 : ℝ) / 2 = (2 : ℝ) ^ n * (3 / 2 / (2 : ℝ) ^ n) := by field_simp
    _ ≤ (2 : ℝ) ^ n * |ξ| :=
        mul_le_mul_of_nonneg_left h (by positivity)

/-- The symbol `annAtomC n` is integrable (it is bounded and supported in a bounded interval). -/
lemma integrable_annAtomC (n : ℤ) : Integrable (annAtomC n) (volume : Measure ℝ) := by
  set R : ℝ := 3 / 2 / (2 : ℝ) ^ n with hR
  have hRpos : 0 < R := by rw [hR]; positivity
  have hmaj : Integrable (Set.indicator (Set.Icc (-R) R) (fun _ : ℝ => (1 : ℝ))) volume :=
    (integrable_indicator_iff measurableSet_Icc).mpr
      (integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top) (by simp))
  refine hmaj.mono' (contDiff_annAtomC n).continuous.aestronglyMeasurable ?_
  filter_upwards with ξ
  rw [Set.indicator_apply]
  by_cases hξ : ξ ∈ Set.Icc (-R) R
  · rw [if_pos hξ]
    exact norm_annAtomC_le_one n ξ
  · rw [if_neg hξ]
    have hlt : R < |ξ| := lt_abs_of_notMem_Icc hRpos hξ
    rw [hR] at hlt
    have hz : annAtomC n ξ = 0 := annAtomC_eq_zero_of_le hlt.le
    rw [hz, norm_zero]

/-- **The symbol times the Fourier transform of an integrable function is integrable.**  The
product is bounded by `∫ ‖f‖` on the support of `annAtomC n` and vanishes outside it. -/
lemma integrable_annAtomC_mul_fourier (n : ℤ) {f : ℝ → ℂ} (hf : Integrable f) :
    Integrable (fun ξ : ℝ => annAtomC n ξ * 𝓕 f ξ) (volume : Measure ℝ) := by
  set R : ℝ := 3 / 2 / (2 : ℝ) ^ n with hR
  have hRpos : 0 < R := by rw [hR]; positivity
  set C : ℝ := ∫ x : ℝ, ‖f x‖ with hC
  have hmaj : Integrable (Set.indicator (Set.Icc (-R) R) (fun _ : ℝ => C)) volume :=
    (integrable_indicator_iff measurableSet_Icc).mpr
      (integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top) (by simp))
  have hcont : Continuous (𝓕 f) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (by fun_prop) hf
  refine hmaj.mono' (((contDiff_annAtomC n).continuous.mul hcont).aestronglyMeasurable) ?_
  filter_upwards with ξ
  rw [Set.indicator_apply]
  by_cases hξ : ξ ∈ Set.Icc (-R) R
  · rw [if_pos hξ, norm_mul]
    calc ‖annAtomC n ξ‖ * ‖𝓕 f ξ‖ ≤ 1 * C :=
          mul_le_mul (norm_annAtomC_le_one n ξ)
            (norm_fourier_le f ξ) (norm_nonneg _)
            (by norm_num)
      _ = C := one_mul C
  · rw [if_neg hξ]
    have hlt : R < |ξ| := lt_abs_of_notMem_Icc hRpos hξ
    rw [hR] at hlt
    have hz : annAtomC n ξ = 0 := annAtomC_eq_zero_of_le hlt.le
    rw [hz, zero_mul, norm_zero]

/-! ## The main statement -/

/-- **The annulus projection is self-adjoint in the `L²` pairing.**  For `u, g ∈ L¹ ∩ L²(ℝ)`, the
convolution with the annulus kernel of the (real-valued, even) symbol
`Work.BourgainPlan.Maximal.annAtomC n` satisfies
`∫ x, (K_n * u) x * star (g x) = ∫ x, u x * star ((K_n * g) x)`.

Route.  `annulusConv (annAtomC n) f` is the multiplier operator with symbol `annAtomC n`, i.e.
`𝓕⁻ (annAtomC n · 𝓕 f)`.  The Fourier pairing `star_pairing_fourierInv` then identifies both
sides of the identity with `∫ ξ, annAtomC n ξ · 𝓕 u ξ · star (𝓕 g ξ)`: the left-hand side
directly, and the right-hand side after conjugating twice (which turns `star (annAtomC n ξ)` into
`annAtomC n ξ`, i.e. uses exactly the reality of the symbol). -/
theorem annulusConv_star_pairing (n : ℤ) (u g : ℝ → ℂ)
    (hu : MeasureTheory.MemLp u 2 (MeasureTheory.volume : MeasureTheory.Measure ℝ))
    (hu1 : MeasureTheory.MemLp u 1 (MeasureTheory.volume : MeasureTheory.Measure ℝ))
    (hg : MeasureTheory.MemLp g 2 (MeasureTheory.volume : MeasureTheory.Measure ℝ))
    (hg1 : MeasureTheory.MemLp g 1 (MeasureTheory.volume : MeasureTheory.Measure ℝ)) :
    ∫ x : ℝ, Work.BourgainPlan.Maximal.annulusConv Work.BourgainPlan.Maximal.annAtomC n u x * star (g x)
      = ∫ x : ℝ, u x * star (Work.BourgainPlan.Maximal.annulusConv Work.BourgainPlan.Maximal.annAtomC n g x) := by
  have huI : Integrable u := memLp_one_iff_integrable.mp hu1
  have hgI : Integrable g := memLp_one_iff_integrable.mp hg1
  have hHu : Integrable (fun ξ : ℝ => annAtomC n ξ * 𝓕 u ξ) :=
    integrable_annAtomC_mul_fourier n huI
  have hHg : Integrable (fun ξ : ℝ => annAtomC n ξ * 𝓕 g ξ) :=
    integrable_annAtomC_mul_fourier n hgI
  -- the convolution is the multiplier operator with symbol `annAtomC n`
  have hconv : ∀ (f : ℝ → ℂ), Integrable f →
      ∀ x : ℝ, annulusConv annAtomC n f x = 𝓕⁻ (fun ξ : ℝ => annAtomC n ξ * 𝓕 f ξ) x := by
    intro f hf x
    rw [annulusConv, annulusK,
      Commons.Analysis.Fourier.fourierInv_mul_fourier_eq_convolution (m := annAtomC n) (f := f)
        (integrable_annAtomC n) hf x]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only []
    ring
  have hpairu := star_pairing_fourierInv (fun ξ : ℝ => annAtomC n ξ * 𝓕 u ξ) g hHu hgI
  have hpairg := star_pairing_fourierInv (fun ξ : ℝ => annAtomC n ξ * 𝓕 g ξ) u hHg huI
  calc ∫ x : ℝ, annulusConv annAtomC n u x * star (g x)
      = ∫ x : ℝ, 𝓕⁻ (fun ξ : ℝ => annAtomC n ξ * 𝓕 u ξ) x * star (g x) := by
        refine integral_congr_ae (Eventually.of_forall fun y => ?_)
        simp only []
        rw [hconv u huI y]
    _ = ∫ ξ : ℝ, (annAtomC n ξ * 𝓕 u ξ) * star (𝓕 g ξ) := hpairu
    _ = ∫ ξ : ℝ, star ((annAtomC n ξ * 𝓕 g ξ) * star (𝓕 u ξ)) := by
        refine integral_congr_ae (Eventually.of_forall fun y => ?_)
        simp only []
        rw [star_mul, star_mul, star_star, star_annAtomC]
        ring
    _ = star (∫ ξ : ℝ, (annAtomC n ξ * 𝓕 g ξ) * star (𝓕 u ξ)) := integral_star_eq _
    _ = star (∫ ξ : ℝ, 𝓕⁻ (fun ξ : ℝ => annAtomC n ξ * 𝓕 g ξ) ξ * star (u ξ)) := by
        rw [hpairg]
    _ = ∫ x : ℝ, u x * star (𝓕⁻ (fun ξ : ℝ => annAtomC n ξ * 𝓕 g ξ) x) :=
        (integral_mul_star_eq u (𝓕⁻ (fun ξ : ℝ => annAtomC n ξ * 𝓕 g ξ))).symm
    _ = ∫ x : ℝ, u x * star (annulusConv annAtomC n g x) := by
        refine integral_congr_ae (Eventually.of_forall fun y => ?_)
        simp only []
        rw [hconv g hgI y]

end Work.BourgainPlan.Maximal
