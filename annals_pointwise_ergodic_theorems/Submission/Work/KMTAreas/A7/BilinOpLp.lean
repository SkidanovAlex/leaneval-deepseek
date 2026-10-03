/-
# The `ℓ^p` bound for the bilinear convolution operator (Young's inequality)

`bilinOp K u v x = ∑'_a ∑'_b K a b * u (x - a) * v (x - b)` is the bilinear operator whose
symbol is the Fourier transform of the kernel `K`; the paper's §6/§7 model operators are of this
form with `K = khalf m P` (`BilinOpKhalf`).  This module proves the fundamental `ℓ¹`-kernel bound

  `‖bilinOp K u v‖_{ℓ^p} ≤ ‖K‖_{ℓ¹(ℤ²)} ‖u‖_{ℓ^{p₁}} ‖v‖_{ℓ^{p₂}}`,   `1/p₁ + 1/p₂ = 1/p`,
  `1 ≤ p`,

i.e. Young's (convolution) inequality for a bilinear kernel.  It is the quantitative content of
"the operator norm of `bilinOp K` is at most the `ℓ¹(ℤ²)` mass of `K`" advertised in `ModelOps`.

The proof is the classical one:

* the pointwise bound `‖bilinOp K u v x‖ₑ ≤ ∑'_q ‖K q‖ₑ ‖u (x - q.1)‖ₑ ‖v (x - q.2)‖ₑ`
  (`enorm_tsum_le_tsum_enorm`, `enorm_mul`, `ENNReal.tsum_prod`);
* Minkowski's inequality for a countable sum of `ℝ≥0∞`-valued functions
  (`Submission.PointwiseErgodicTheorems.eLpNorm_tsum_le_tsum_eLpNorm`);
* the single-term bound, which is Hölder's inequality (`eLpNorm_le_eLpNorm_mul_eLpNorm'_of_norm`
  for real-valued functions) plus the translation invariance of the counting measure
  (`measurePreserving_sub_right`), transported across the identification
  `‖y‖ₑ = ENNReal.ofReal ‖y‖` of an `enorm` with a real norm.

Everything is expressed in `ℝ≥0∞`, so no summability of the operator's defining series is needed.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.ModelOps
import Submission.Port.Aesm

namespace Work.KMTAreas.A7

open MeasureTheory
open scoped ENNReal

noncomputable section

/-- The `enorm` of an element of a normed group is the `ofReal` of its norm. -/
lemma bilin_enorm_eq_ofReal_norm {E : Type*} [SeminormedAddCommGroup E] (x : E) :
    ‖x‖ₑ = ENNReal.ofReal ‖x‖ := by
  rw [← enorm_norm x, Real.enorm_eq_ofReal (norm_nonneg x)]

/-- `eLpNorm` of the `ℝ≥0∞`-valued function `x ↦ ofReal (H x)` is the `eLpNorm` of `H`,
for a nonnegative `H`. -/
lemma bilin_eLpNorm_ofReal_eq {α : Type*} [MeasurableSpace α] {μ : Measure α} {H : α → ℝ}
    (hH : ∀ x, 0 ≤ H x) (p : ENNReal) (hHm : AEStronglyMeasurable H μ := by pw_aesm) :
    eLpNorm (fun x => ENNReal.ofReal (H x)) p μ = eLpNorm H p μ := by
  rw [← eLpNorm_enorm (hf := hHm) H]
  congr 1
  funext x
  exact (Real.enorm_eq_ofReal (hH x)).symm

/-- Translation invariance of `eLpNorm` on `ℤ` with the counting measure, for the real-valued
function `x ↦ ‖u x‖`. -/
lemma bilin_eLpNorm_norm_sub (u : ℤ → ℂ) (a : ℤ) (p : ENNReal) :
    eLpNorm (fun x : ℤ => ‖u (x - a)‖) p Measure.count = eLpNorm u p Measure.count := by
  have h1 : eLpNorm (fun x : ℤ => ‖u (x - a)‖) p Measure.count
      = eLpNorm (fun x : ℤ => ‖u (x - a)‖ₑ) p Measure.count := by
    rw [← eLpNorm_enorm (hf := by pw_aesm) (fun x : ℤ => ‖u (x - a)‖)]
    congr 1
    funext x
    exact enorm_norm (u (x - a))
  rw [h1, eLpNorm_enorm (hf := by pw_aesm) (fun x : ℤ => u (x - a))]
  exact eLpNorm_comp_measurePreserving (measurable_of_countable _).aestronglyMeasurable
    (measurePreserving_sub_right Measure.count a)

/-- Hölder's inequality for the two translated norm functions: the single-term estimate of the
Young inequality for `bilinOp`. -/
lemma bilin_eLpNorm_mul_shift_le (u v : ℤ → ℂ) (a b : ℤ) {p p₁ p₂ : ENNReal}
    (hp : p₁⁻¹ + p₂⁻¹ = p⁻¹) :
    eLpNorm (fun x : ℤ => ‖u (x - a)‖ₑ * ‖v (x - b)‖ₑ) p Measure.count
      ≤ eLpNorm u p₁ Measure.count * eLpNorm v p₂ Measure.count := by
  have htri : p₁.HolderTriple p₂ p := ⟨hp⟩
  have hEq : eLpNorm (fun x : ℤ => ‖u (x - a)‖ₑ * ‖v (x - b)‖ₑ) p Measure.count
      = eLpNorm (fun x : ℤ => ‖u (x - a)‖ * ‖v (x - b)‖) p Measure.count := by
    have hfun : (fun x : ℤ => ‖u (x - a)‖ₑ * ‖v (x - b)‖ₑ)
        = fun x : ℤ => ENNReal.ofReal (‖u (x - a)‖ * ‖v (x - b)‖) := by
      funext x
      rw [bilin_enorm_eq_ofReal_norm, bilin_enorm_eq_ofReal_norm,
        ← ENNReal.ofReal_mul (norm_nonneg _)]
    rw [hfun]
    exact bilin_eLpNorm_ofReal_eq (fun x => mul_nonneg (norm_nonneg _) (norm_nonneg _)) p
  have hHolder : eLpNorm (fun x : ℤ => ‖u (x - a)‖ * ‖v (x - b)‖) p Measure.count
      ≤ 1 * eLpNorm (fun x : ℤ => ‖u (x - a)‖) p₁ Measure.count
          * eLpNorm (fun x : ℤ => ‖v (x - b)‖) p₂ Measure.count := by
    have h := eLpNorm_le_eLpNorm_mul_eLpNorm_of_norm
      (μ := Measure.count) (f := fun x : ℤ => ‖u (x - a)‖) (g := fun x : ℤ => ‖v (x - b)‖)
      (p := p₁) (q := p₂) (r := p)
      (fun s t : ℝ => s * t) 1 (continuous_fst.mul continuous_snd)
      (measurable_of_countable _).aestronglyMeasurable
      (measurable_of_countable _).aestronglyMeasurable
      (by filter_upwards with x
          simp [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))])
      (hpqr := htri)
    simpa using h
  rw [hEq]
  refine hHolder.trans ?_
  rw [one_mul, bilin_eLpNorm_norm_sub u a p₁, bilin_eLpNorm_norm_sub v b p₂]

theorem BilinOpLp {K : ℤ → ℤ → ℂ} {p p₁ p₂ : ENNReal}
    (hp : p₁⁻¹ + p₂⁻¹ = p⁻¹) (hp1 : 1 ≤ p)
    (hK : Summable fun q : ℤ × ℤ => ‖K q.1 q.2‖) (u v : ℤ → ℂ) :
    MeasureTheory.eLpNorm (fun x : ℤ => Work.KMTAreas.A7.bilinOp K u v x) p
        (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ)
      ≤ ENNReal.ofReal (∑' q : ℤ × ℤ, ‖K q.1 q.2‖)
          * MeasureTheory.eLpNorm u p₁ (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ)
          * MeasureTheory.eLpNorm v p₂ (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ) := by
  -- the weight of the kernel as an `ℝ≥0∞`-valued `tsum`
  have hw : (∑' q : ℤ × ℤ, ‖K q.1 q.2‖ₑ) = ENNReal.ofReal (∑' q : ℤ × ℤ, ‖K q.1 q.2‖) := by
    rw [ENNReal.ofReal_tsum_of_nonneg (fun q => norm_nonneg _) hK]
    exact tsum_congr fun q => bilin_enorm_eq_ofReal_norm (K q.1 q.2)
  -- the pointwise bound by the weighted sum of the shifted norms
  have hpt : ∀ x : ℤ, ‖bilinOp K u v x‖ₑ
      ≤ ∑' q : ℤ × ℤ, ‖K q.1 q.2‖ₑ * ‖u (x - q.1)‖ₑ * ‖v (x - q.2)‖ₑ := by
    intro x
    rw [bilinOp]
    calc ‖∑' a : ℤ, ∑' b : ℤ, K a b * u (x - a) * v (x - b)‖ₑ
        ≤ ∑' a : ℤ, ‖∑' b : ℤ, K a b * u (x - a) * v (x - b)‖ₑ := enorm_tsum_le_tsum_enorm
      _ ≤ ∑' a : ℤ, ∑' b : ℤ, ‖K a b * u (x - a) * v (x - b)‖ₑ := by
          gcongr with a
          exact enorm_tsum_le_tsum_enorm
      _ = ∑' a : ℤ, ∑' b : ℤ, ‖K a b‖ₑ * ‖u (x - a)‖ₑ * ‖v (x - b)‖ₑ := by
          simp_rw [enorm_mul]
      _ = ∑' q : ℤ × ℤ, ‖K q.1 q.2‖ₑ * ‖u (x - q.1)‖ₑ * ‖v (x - q.2)‖ₑ :=
          (ENNReal.tsum_prod (f := fun a b : ℤ =>
            ‖K a b‖ₑ * ‖u (x - a)‖ₑ * ‖v (x - b)‖ₑ)).symm
  -- the `eLpNorm` of the dominating series
  have hstep2 : eLpNorm (fun x : ℤ => ‖bilinOp K u v x‖ₑ) p Measure.count
      ≤ eLpNorm (fun x : ℤ => ∑' q : ℤ × ℤ,
          ‖K q.1 q.2‖ₑ * ‖u (x - q.1)‖ₑ * ‖v (x - q.2)‖ₑ) p Measure.count := by
    have h := eLpNorm_le_mul_eLpNorm_of_ae_le_mul'' (μ := Measure.count) (p := p) (c := 1)
      (f := fun x : ℤ => ‖bilinOp K u v x‖ₑ)
      (g := fun x : ℤ => ∑' q : ℤ × ℤ, ‖K q.1 q.2‖ₑ * ‖u (x - q.1)‖ₑ * ‖v (x - q.2)‖ₑ)
      (measurable_of_countable _).aestronglyMeasurable
      (by filter_upwards with x
          simp only [enorm_eq_self, one_mul]
          exact hpt x)
    simpa using h
  -- Minkowski's inequality for the countable sum
  have hstep3 : eLpNorm (fun x : ℤ => ∑' q : ℤ × ℤ,
        ‖K q.1 q.2‖ₑ * ‖u (x - q.1)‖ₑ * ‖v (x - q.2)‖ₑ) p Measure.count
      ≤ ∑' q : ℤ × ℤ, eLpNorm (fun x : ℤ =>
          ‖K q.1 q.2‖ₑ * ‖u (x - q.1)‖ₑ * ‖v (x - q.2)‖ₑ) p Measure.count :=
    Submission.PointwiseErgodicTheorems.eLpNorm_tsum_le_tsum_eLpNorm (μ := Measure.count) hp1
      (f := fun q : ℤ × ℤ => fun x : ℤ => ‖K q.1 q.2‖ₑ * ‖u (x - q.1)‖ₑ * ‖v (x - q.2)‖ₑ)
      (fun q => (measurable_of_countable _).aemeasurable)
  -- the single-term estimate: Hölder plus the kernel weight
  have hstep4 : (∑' q : ℤ × ℤ, eLpNorm (fun x : ℤ =>
        ‖K q.1 q.2‖ₑ * ‖u (x - q.1)‖ₑ * ‖v (x - q.2)‖ₑ) p Measure.count)
      ≤ ∑' q : ℤ × ℤ, ‖K q.1 q.2‖ₑ * (eLpNorm u p₁ Measure.count * eLpNorm v p₂ Measure.count) := by
    refine ENNReal.tsum_le_tsum (fun q => ?_)
    have h1 := eLpNorm_le_mul_eLpNorm_of_ae_le_mul'' (μ := Measure.count) (p := p)
      (c := ‖K q.1 q.2‖ₑ)
      (f := fun x : ℤ => ‖K q.1 q.2‖ₑ * ‖u (x - q.1)‖ₑ * ‖v (x - q.2)‖ₑ)
      (g := fun x : ℤ => ‖u (x - q.1)‖ₑ * ‖v (x - q.2)‖ₑ)
      (measurable_of_countable _).aestronglyMeasurable
      (by filter_upwards with x; simp only [enorm_eq_self]; rw [mul_assoc])
    exact h1.trans (mul_le_mul' le_rfl (bilin_eLpNorm_mul_shift_le u v q.1 q.2 hp))
  -- factor the constant out of the `tsum`
  have hstep5 : (∑' q : ℤ × ℤ,
        ‖K q.1 q.2‖ₑ * (eLpNorm u p₁ Measure.count * eLpNorm v p₂ Measure.count))
      = (∑' q : ℤ × ℤ, ‖K q.1 q.2‖ₑ) * eLpNorm u p₁ Measure.count
          * eLpNorm v p₂ Measure.count := by
    rw [ENNReal.tsum_mul_right, mul_assoc]
  calc eLpNorm (fun x : ℤ => bilinOp K u v x) p (Measure.count : Measure ℤ)
      = eLpNorm (fun x : ℤ => ‖bilinOp K u v x‖ₑ) p Measure.count :=
        (eLpNorm_enorm (hf := by pw_aesm) (fun x : ℤ => bilinOp K u v x)).symm
    _ ≤ eLpNorm (fun x : ℤ => ∑' q : ℤ × ℤ,
          ‖K q.1 q.2‖ₑ * ‖u (x - q.1)‖ₑ * ‖v (x - q.2)‖ₑ) p Measure.count := hstep2
    _ ≤ ∑' q : ℤ × ℤ, eLpNorm (fun x : ℤ =>
          ‖K q.1 q.2‖ₑ * ‖u (x - q.1)‖ₑ * ‖v (x - q.2)‖ₑ) p Measure.count := hstep3
    _ ≤ ∑' q : ℤ × ℤ, ‖K q.1 q.2‖ₑ
          * (eLpNorm u p₁ Measure.count * eLpNorm v p₂ Measure.count) := hstep4
    _ = (∑' q : ℤ × ℤ, ‖K q.1 q.2‖ₑ) * eLpNorm u p₁ Measure.count
          * eLpNorm v p₂ Measure.count := hstep5
    _ = ENNReal.ofReal (∑' q : ℤ × ℤ, ‖K q.1 q.2‖) * eLpNorm u p₁ Measure.count
          * eLpNorm v p₂ Measure.count := by rw [hw]

end

end Work.KMTAreas.A7
