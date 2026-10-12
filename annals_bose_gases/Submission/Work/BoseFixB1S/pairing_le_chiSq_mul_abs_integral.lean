import Mathlib.Tactic.Have
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Submission.Work.BoseFixB1.WB.Lead
import Submission.Work.BoseFixB1.abs_wSmallPair_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The `χ ⊗ χ` pairing bound

For `χ ≥ 0` continuous with compact support and `f` integrable,

  `∬ χ(x)·|f(x−y)|·χ(y) dx dy ≤ (∫χ²)·(∫|f|)`,

and the double integral is itself integrable on the product.

The proof is the AM–GM (Young) bound `2χ(x)χ(y) ≤ χ(x)² + χ(y)²` together with Tonelli and
the translation invariance of Lebesgue measure.  The left half of the bound is computed by
`∬ χ(x)² |f(x−y)| = (∫χ²)(∫|f|)` and the right half symmetrically.
-/

namespace Work.BoseFixB1S

open MeasureTheory
open scoped ENNReal

set_option autoImplicit false

/-- The function `p ↦ f (p.1 - p.2)` on the product space is a.e. measurable as soon as `f` is
(with respect to the product of Lebesgue measure with itself).  This is the statement that the
difference map is quasi-measure-preserving, which follows from the measure-preserving shear
`(x,y) ↦ (y, x − y)` and the quasi-measure-preserving second projection. -/
lemma subPair_aemeasurable {f : ℝ³ → ℝ}
    (hf : AEMeasurable f (volume : Measure ℝ³)) :
    AEMeasurable (fun p : ℝ³ × ℝ³ => f (p.1 - p.2)) (volume : Measure (ℝ³ × ℝ³)) := by
  have hqmp : Measure.QuasiMeasurePreserving
      (fun p : ℝ³ × ℝ³ => p.1 - p.2) (volume : Measure (ℝ³ × ℝ³)) (volume : Measure ℝ³) :=
    (Measure.quasiMeasurePreserving_snd (μ := (volume : Measure ℝ³))
        (ν := (volume : Measure ℝ³))).comp
      ((measurePreserving_prod_sub_swap (volume : Measure ℝ³)
        (volume : Measure ℝ³)).quasiMeasurePreserving)
  exact hf.comp_quasiMeasurePreserving hqmp

/-- `p ↦ |f (p.1 - p.2)|` is a.e. strongly measurable on the product. -/
lemma abs_subPair_aestronglyMeasurable {f : ℝ³ → ℝ}
    (hf : AEStronglyMeasurable f (volume : Measure ℝ³)) :
    AEStronglyMeasurable (fun p : ℝ³ × ℝ³ => |f (p.1 - p.2)|)
      (volume : Measure (ℝ³ × ℝ³)) := by
  have h1 : AEStronglyMeasurable (fun p : ℝ³ × ℝ³ => f (p.1 - p.2))
      (volume : Measure (ℝ³ × ℝ³)) :=
    (subPair_aemeasurable hf.aemeasurable).aestronglyMeasurable
  simpa [Real.norm_eq_abs] using h1.norm

/-- The three `ℝ≥0∞`-valued integrands appearing in the pairing bound are a.e. measurable on the
product. -/
lemma aemeasurable_pair_integrands {χ f : ℝ³ → ℝ}
    (hχc : Continuous χ) (hf : AEStronglyMeasurable f (volume : Measure ℝ³)) :
    AEMeasurable (fun p : ℝ³ × ℝ³ => ENNReal.ofReal (χ p.1 ^ 2 * |f (p.1 - p.2)|))
        (volume : Measure (ℝ³ × ℝ³))
      ∧ AEMeasurable (fun p : ℝ³ × ℝ³ => ENNReal.ofReal (χ p.2 ^ 2 * |f (p.1 - p.2)|))
        (volume : Measure (ℝ³ × ℝ³))
      ∧ AEMeasurable (fun p : ℝ³ × ℝ³ => ENNReal.ofReal (χ p.1 * |f (p.1 - p.2)| * χ p.2))
        (volume : Measure (ℝ³ × ℝ³)) := by
  have habs := abs_subPair_aestronglyMeasurable hf
  have h1 : AEStronglyMeasurable (fun p : ℝ³ × ℝ³ => χ p.1 ^ 2 * |f (p.1 - p.2)|)
      (volume : Measure (ℝ³ × ℝ³)) :=
    ((hχc.comp continuous_fst).pow 2).aestronglyMeasurable.mul habs
  have h2 : AEStronglyMeasurable (fun p : ℝ³ × ℝ³ => χ p.2 ^ 2 * |f (p.1 - p.2)|)
      (volume : Measure (ℝ³ × ℝ³)) :=
    ((hχc.comp continuous_snd).pow 2).aestronglyMeasurable.mul habs
  have h3 : AEStronglyMeasurable (fun p : ℝ³ × ℝ³ => χ p.1 * |f (p.1 - p.2)| * χ p.2)
      (volume : Measure (ℝ³ × ℝ³)) :=
    (((hχc.comp continuous_fst).aestronglyMeasurable.mul habs).mul
      (hχc.comp continuous_snd).aestronglyMeasurable)
  exact ⟨h1.aemeasurable.ennreal_ofReal, h2.aemeasurable.ennreal_ofReal,
    h3.aemeasurable.ennreal_ofReal⟩

/-- Left half of the pairing computation: `∬⁻ χ(x)²|f(x−y)| = (∫χ²)(∫|f|)`. -/
lemma lintegral_pair_chiSq_fst_mul_abs {χ f : ℝ³ → ℝ}
    (hχc : Continuous χ) (hχs : HasCompactSupport χ) (hf : Integrable f) :
    ∫⁻ p : ℝ³ × ℝ³, ENNReal.ofReal (χ p.1 ^ 2 * |f (p.1 - p.2)|)
      = ENNReal.ofReal ((∫ x : ℝ³, χ x ^ 2) * (∫ z : ℝ³, |f z|)) := by
  have hχ2int : Integrable (fun x : ℝ³ => χ x ^ 2) := by
    have h : Integrable (χ * χ) (volume : Measure ℝ³) :=
      (hχc.mul hχc).integrable_of_hasCompactSupport (hχs.mul_right (f' := χ))
        (μ := (volume : Measure ℝ³))
    have h2 : (fun x : ℝ³ => χ x ^ 2) = (χ * χ) := by
      funext x; simp [pow_two]
    rw [h2]; exact h
  have hfabs : Integrable (fun z : ℝ³ => |f z|) := hf.abs
  have hc2 : 0 ≤ ∫ x : ℝ³, χ x ^ 2 := integral_nonneg fun x => sq_nonneg (χ x)
  obtain ⟨hUmeas, -, -⟩ := aemeasurable_pair_integrands hχc hf.aestronglyMeasurable
  have hinner : ∀ x : ℝ³,
      ∫⁻ y : ℝ³, ENNReal.ofReal (χ x ^ 2 * |f (x - y)|)
        = ENNReal.ofReal (χ x ^ 2) * ENNReal.ofReal (∫ z : ℝ³, |f z|) := by
    intro x
    have hsplit : ∫⁻ y : ℝ³, ENNReal.ofReal (χ x ^ 2 * |f (x - y)|)
        = ∫⁻ y : ℝ³, ENNReal.ofReal (χ x ^ 2) * ENNReal.ofReal (|f (x - y)|) :=
      lintegral_congr fun y => ENNReal.ofReal_mul (sq_nonneg (χ x))
    have hshift : ∫⁻ y : ℝ³, ENNReal.ofReal (|f (x - y)|)
        = ∫⁻ y : ℝ³, ENNReal.ofReal (|f y|) :=
      lintegral_sub_left_eq_self (μ := (volume : Measure ℝ³))
        (fun z => ENNReal.ofReal (|f z|)) x
    rw [hsplit, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hshift]
    congr 1
    exact (ofReal_integral_eq_lintegral_ofReal hfabs
      (ae_of_all (volume : Measure ℝ³) fun z => abs_nonneg (f z))).symm
  rw [Measure.volume_eq_prod ℝ³ ℝ³, lintegral_prod _ hUmeas]
  rw [show (∫⁻ x : ℝ³, ∫⁻ y : ℝ³, ENNReal.ofReal (χ x ^ 2 * |f (x - y)|))
      = ∫⁻ x : ℝ³, ENNReal.ofReal (χ x ^ 2) * ENNReal.ofReal (∫ z : ℝ³, |f z|) from
      lintegral_congr hinner]
  rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
  rw [(ofReal_integral_eq_lintegral_ofReal hχ2int
      (ae_of_all (volume : Measure ℝ³) fun x => sq_nonneg (χ x))).symm]
  exact (ENNReal.ofReal_mul hc2).symm

/-- Right half of the pairing computation: `∬⁻ χ(y)²|f(x−y)| = (∫χ²)(∫|f|)`. -/
lemma lintegral_pair_abs_chiSq_snd_mul_abs {χ f : ℝ³ → ℝ}
    (hχc : Continuous χ) (hχs : HasCompactSupport χ) (hf : Integrable f) :
    ∫⁻ p : ℝ³ × ℝ³, ENNReal.ofReal (χ p.2 ^ 2 * |f (p.1 - p.2)|)
      = ENNReal.ofReal ((∫ x : ℝ³, χ x ^ 2) * (∫ z : ℝ³, |f z|)) := by
  have hχ2int : Integrable (fun x : ℝ³ => χ x ^ 2) := by
    have h : Integrable (χ * χ) (volume : Measure ℝ³) :=
      (hχc.mul hχc).integrable_of_hasCompactSupport (hχs.mul_right (f' := χ))
        (μ := (volume : Measure ℝ³))
    have h2 : (fun x : ℝ³ => χ x ^ 2) = (χ * χ) := by
      funext x; simp [pow_two]
    rw [h2]; exact h
  have hfabs : Integrable (fun z : ℝ³ => |f z|) := hf.abs
  have hc2 : 0 ≤ ∫ x : ℝ³, χ x ^ 2 := integral_nonneg fun x => sq_nonneg (χ x)
  obtain ⟨-, hVmeas, -⟩ := aemeasurable_pair_integrands hχc hf.aestronglyMeasurable
  have hinner : ∀ y : ℝ³,
      ∫⁻ x : ℝ³, ENNReal.ofReal (χ y ^ 2 * |f (x - y)|)
        = ENNReal.ofReal (χ y ^ 2) * ENNReal.ofReal (∫ z : ℝ³, |f z|) := by
    intro y
    have hsplit : ∫⁻ x : ℝ³, ENNReal.ofReal (χ y ^ 2 * |f (x - y)|)
        = ∫⁻ x : ℝ³, ENNReal.ofReal (χ y ^ 2) * ENNReal.ofReal (|f (x - y)|) :=
      lintegral_congr fun x => ENNReal.ofReal_mul (sq_nonneg (χ y))
    have hshift : ∫⁻ x : ℝ³, ENNReal.ofReal (|f (x - y)|)
        = ∫⁻ x : ℝ³, ENNReal.ofReal (|f x|) :=
      lintegral_sub_right_eq_self (μ := (volume : Measure ℝ³))
        (fun z => ENNReal.ofReal (|f z|)) y
    rw [hsplit, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hshift]
    congr 1
    exact (ofReal_integral_eq_lintegral_ofReal hfabs
      (ae_of_all (volume : Measure ℝ³) fun z => abs_nonneg (f z))).symm
  rw [Measure.volume_eq_prod ℝ³ ℝ³, lintegral_prod_symm _ hVmeas]
  rw [show (∫⁻ y : ℝ³, ∫⁻ x : ℝ³, ENNReal.ofReal (χ y ^ 2 * |f (x - y)|))
      = ∫⁻ y : ℝ³, ENNReal.ofReal (χ y ^ 2) * ENNReal.ofReal (∫ z : ℝ³, |f z|) from
      lintegral_congr hinner]
  rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
  rw [(ofReal_integral_eq_lintegral_ofReal hχ2int
      (ae_of_all (volume : Measure ℝ³) fun x => sq_nonneg (χ x))).symm]
  exact (ENNReal.ofReal_mul hc2).symm

theorem pairing_le_chiSq_mul_abs_integral {χ f : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hχ0 : ∀ x, 0 ≤ χ x) (hχc : Continuous χ) (hχs : HasCompactSupport χ)
    (hf : MeasureTheory.Integrable f) :
    MeasureTheory.Integrable
        (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
          χ p.1 * |f (p.1 - p.2)| * χ p.2)
      ∧ (∫ p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3),
            χ p.1 * |f (p.1 - p.2)| * χ p.2)
          ≤ (∫ x : EuclideanSpace ℝ (Fin 3), χ x ^ 2) * (∫ z : EuclideanSpace ℝ (Fin 3), |f z|) := by
  obtain ⟨hUmeas, -, hWmeas⟩ := aemeasurable_pair_integrands hχc hf.aestronglyMeasurable
  -- pointwise AM–GM bound in `ℝ≥0∞`
  have hpt : ∀ p : ℝ³ × ℝ³,
      ENNReal.ofReal (χ p.1 * |f (p.1 - p.2)| * χ p.2)
        + ENNReal.ofReal (χ p.1 * |f (p.1 - p.2)| * χ p.2)
        ≤ ENNReal.ofReal (χ p.1 ^ 2 * |f (p.1 - p.2)|)
          + ENNReal.ofReal (χ p.2 ^ 2 * |f (p.1 - p.2)|) := by
    intro p
    have hz0 : 0 ≤ χ p.1 * |f (p.1 - p.2)| * χ p.2 :=
      mul_nonneg (mul_nonneg (hχ0 _) (abs_nonneg _)) (hχ0 _)
    have hreal : 2 * (χ p.1 * |f (p.1 - p.2)| * χ p.2)
        ≤ χ p.1 ^ 2 * |f (p.1 - p.2)| + χ p.2 ^ 2 * |f (p.1 - p.2)| := by
      have h1 : 2 * χ p.1 * χ p.2 ≤ χ p.1 ^ 2 + χ p.2 ^ 2 := two_mul_le_add_sq _ _
      have ht0 : 0 ≤ |f (p.1 - p.2)| := abs_nonneg _
      nlinarith [mul_le_mul_of_nonneg_right h1 ht0]
    calc ENNReal.ofReal (χ p.1 * |f (p.1 - p.2)| * χ p.2)
            + ENNReal.ofReal (χ p.1 * |f (p.1 - p.2)| * χ p.2)
        = ENNReal.ofReal (χ p.1 * |f (p.1 - p.2)| * χ p.2
            + χ p.1 * |f (p.1 - p.2)| * χ p.2) := (ENNReal.ofReal_add hz0 hz0).symm
      _ ≤ ENNReal.ofReal (χ p.1 ^ 2 * |f (p.1 - p.2)| + χ p.2 ^ 2 * |f (p.1 - p.2)|) :=
          ENNReal.ofReal_le_ofReal (by linarith)
      _ = ENNReal.ofReal (χ p.1 ^ 2 * |f (p.1 - p.2)|)
            + ENNReal.ofReal (χ p.2 ^ 2 * |f (p.1 - p.2)|) :=
          ENNReal.ofReal_add (mul_nonneg (sq_nonneg _) (abs_nonneg _))
            (mul_nonneg (sq_nonneg _) (abs_nonneg _))
  -- the lintegral bound
  have hWle : ∫⁻ p : ℝ³ × ℝ³, ENNReal.ofReal (χ p.1 * |f (p.1 - p.2)| * χ p.2)
      ≤ ENNReal.ofReal ((∫ x : ℝ³, χ x ^ 2) * (∫ z : ℝ³, |f z|)) := by
    have h1 : ∫⁻ p : ℝ³ × ℝ³, (ENNReal.ofReal (χ p.1 * |f (p.1 - p.2)| * χ p.2)
          + ENNReal.ofReal (χ p.1 * |f (p.1 - p.2)| * χ p.2))
        ≤ ∫⁻ p : ℝ³ × ℝ³, (ENNReal.ofReal (χ p.1 ^ 2 * |f (p.1 - p.2)|)
          + ENNReal.ofReal (χ p.2 ^ 2 * |f (p.1 - p.2)|)) := lintegral_mono hpt
    rw [lintegral_add_left' hWmeas
      (fun p : ℝ³ × ℝ³ => ENNReal.ofReal (χ p.1 * |f (p.1 - p.2)| * χ p.2)),
      lintegral_add_left' hUmeas
        (fun p : ℝ³ × ℝ³ => ENNReal.ofReal (χ p.2 ^ 2 * |f (p.1 - p.2)|))] at h1
    rw [lintegral_pair_chiSq_fst_mul_abs hχc hχs hf,
      lintegral_pair_abs_chiSq_snd_mul_abs hχc hχs hf] at h1
    have h2 : (2 : ℝ≥0∞) * (∫⁻ p : ℝ³ × ℝ³,
          ENNReal.ofReal (χ p.1 * |f (p.1 - p.2)| * χ p.2))
        ≤ (2 : ℝ≥0∞) * ENNReal.ofReal ((∫ x : ℝ³, χ x ^ 2) * (∫ z : ℝ³, |f z|)) :=
      calc (2 : ℝ≥0∞) * (∫⁻ p : ℝ³ × ℝ³,
              ENNReal.ofReal (χ p.1 * |f (p.1 - p.2)| * χ p.2))
          = (∫⁻ p : ℝ³ × ℝ³, ENNReal.ofReal (χ p.1 * |f (p.1 - p.2)| * χ p.2))
              + ∫⁻ p : ℝ³ × ℝ³, ENNReal.ofReal (χ p.1 * |f (p.1 - p.2)| * χ p.2) :=
            two_mul _
        _ ≤ ENNReal.ofReal ((∫ x : ℝ³, χ x ^ 2) * (∫ z : ℝ³, |f z|))
              + ENNReal.ofReal ((∫ x : ℝ³, χ x ^ 2) * (∫ z : ℝ³, |f z|)) := h1
        _ = (2 : ℝ≥0∞) * ENNReal.ofReal ((∫ x : ℝ³, χ x ^ 2) * (∫ z : ℝ³, |f z|)) :=
            (two_mul _).symm
    exact (ENNReal.mul_le_mul_iff_right (a := (2 : ℝ≥0∞)) (by norm_num) (by norm_num)).mp h2
  -- integrability of the pairing integrand
  have hFmeas : AEStronglyMeasurable
      (fun p : ℝ³ × ℝ³ => χ p.1 * |f (p.1 - p.2)| * χ p.2)
      (volume : Measure (ℝ³ × ℝ³)) :=
    (((hχc.comp continuous_fst).aestronglyMeasurable.mul
      (abs_subPair_aestronglyMeasurable hf.aestronglyMeasurable)).mul
      (hχc.comp continuous_snd).aestronglyMeasurable)
  have hFnn : 0 ≤ᵐ[(volume : Measure (ℝ³ × ℝ³))]
      (fun p : ℝ³ × ℝ³ => χ p.1 * |f (p.1 - p.2)| * χ p.2) :=
    ae_of_all (volume : Measure (ℝ³ × ℝ³)) fun p =>
      mul_nonneg (mul_nonneg (hχ0 _) (abs_nonneg _)) (hχ0 _)
  have hFfin : HasFiniteIntegral
      (fun p : ℝ³ × ℝ³ => χ p.1 * |f (p.1 - p.2)| * χ p.2)
      (volume : Measure (ℝ³ × ℝ³)) :=
    (hasFiniteIntegral_iff_ofReal hFnn).mpr (lt_of_le_of_lt hWle ENNReal.ofReal_lt_top)
  have hc2 : 0 ≤ ∫ x : ℝ³, χ x ^ 2 := integral_nonneg fun x => sq_nonneg (χ x)
  have hc1 : 0 ≤ ∫ z : ℝ³, |f z| := integral_nonneg fun z => abs_nonneg (f z)
  refine ⟨⟨hFmeas, hFfin⟩, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae hFnn hFmeas]
  calc (∫⁻ p : ℝ³ × ℝ³, ENNReal.ofReal (χ p.1 * |f (p.1 - p.2)| * χ p.2)).toReal
      ≤ (ENNReal.ofReal ((∫ x : ℝ³, χ x ^ 2) * (∫ z : ℝ³, |f z|))).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hWle
    _ = (∫ x : ℝ³, χ x ^ 2) * (∫ z : ℝ³, |f z|) := ENNReal.toReal_ofReal (mul_nonneg hc2 hc1)

end Work.BoseFixB1S
