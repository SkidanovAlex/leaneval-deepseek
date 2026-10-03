import Mathlib
import Submission.Commons.Analysis.Complex.hadamard_three_lines
import Submission.Commons.Analysis.Integral.exists_dual_witness
import Submission.Commons.Analysis.Integral.holder_complex_finset

open MeasureTheory
open scoped ENNReal BigOperators

namespace Work.BourgainPlan.Maximal

noncomputable section

/-! ## Extending a function on a finite subset of `ℤ` by zero -/

/-- Extend a function on a finset `S : Finset ℤ` by zero to a finitely supported function
on `ℤ`. -/
noncomputable def extendZeroLM (S : Finset ℤ) : (↥S → ℂ) →ₗ[ℂ] (ℤ →₀ ℂ) where
  toFun g := Finsupp.embDomain (Function.Embedding.subtype (fun n : ℤ => n ∈ S))
    ((Finsupp.linearEquivFunOnFinite ℂ ℂ ↥S).symm g)
  map_add' g h := by
    simp only [map_add, Finsupp.embDomain_add]
  map_smul' c g := by
    simp only [map_smul, Finsupp.embDomain_eq_mapDomain, Finsupp.mapDomain_smul,
      RingHom.id_apply]

lemma extendZeroLM_apply (S : Finset ℤ) (g : ↥S → ℂ) (n : ℤ) :
    extendZeroLM S g n = if h : n ∈ S then g ⟨n, h⟩ else 0 := by
  change Finsupp.embDomain (Function.Embedding.subtype (fun m : ℤ => m ∈ S))
    ((Finsupp.linearEquivFunOnFinite ℂ ℂ ↥S).symm g) n
      = if h : n ∈ S then g ⟨n, h⟩ else 0
  rw [Finsupp.embDomain_apply]
  by_cases hn : n ∈ S
  · have hcho : (⟨⟨n, hn⟩, rfl⟩ : ∃ a : ↥S,
        (Function.Embedding.subtype (fun m : ℤ => m ∈ S)) a = n).choose = ⟨n, hn⟩ :=
      Subtype.ext (Exists.choose_spec (⟨⟨n, hn⟩, rfl⟩ : ∃ a : ↥S,
        (Function.Embedding.subtype (fun m : ℤ => m ∈ S)) a = n))
    rw [dif_pos ⟨⟨n, hn⟩, rfl⟩, dif_pos hn, hcho]
    exact congrFun (Finsupp.linearEquivFunOnFinite_symm_apply ℂ ℂ ↥S g) ⟨n, hn⟩
  · have hno : ¬ ∃ a : ↥S, (Function.Embedding.subtype (fun m : ℤ => m ∈ S)) a = n := by
      rintro ⟨a, ha⟩
      exact hn (ha ▸ a.2)
    rw [dif_neg hno, dif_neg hn]

lemma extendZeroLM_self (f : ℤ →₀ ℂ) : extendZeroLM f.support (fun a => f a) = f := by
  ext n
  simp only [extendZeroLM_apply]
  by_cases hn : n ∈ f.support
  · rw [dif_pos hn]
  · rw [dif_neg hn]; exact (Finsupp.notMem_support_iff.mp hn).symm

lemma tsum_norm_extendZeroLM (S : Finset ℤ) (g : ↥S → ℂ) {q : ℝ} (hq : 0 < q) :
    (∑' n : ℤ, ‖extendZeroLM S g n‖ ^ q) = ∑ a : ↥S, ‖g a‖ ^ q := by
  rw [tsum_eq_sum (s := S) (f := fun n : ℤ => ‖extendZeroLM S g n‖ ^ q)]
  · rw [Finset.sum_subtype S (fun x => Iff.rfl) (fun n => ‖extendZeroLM S g n‖ ^ q)]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [extendZeroLM_apply, dif_pos a.2]
  · intro n hn
    rw [extendZeroLM_apply, dif_neg hn, norm_zero, Real.zero_rpow (ne_of_gt hq)]

/-! ## `eLpNorm` on `ℤ` with counting measure -/

/-- `eLpNorm` against the counting measure on `ℤ` as a (possibly infinite) `ℓ^q` sum. -/
lemma eLpNorm_count_eq_tsum (f : ℤ → ℂ) {q : ℝ} (hq : 0 < q) :
    eLpNorm f (ENNReal.ofReal q) Measure.count
      = (∑' n : ℤ, ENNReal.ofReal (‖f n‖ ^ q)) ^ (1 / q) := by
  rw [eLpNorm_eq_eLpNorm' (ENNReal.ofReal_ne_zero_iff.mpr hq) ENNReal.ofReal_ne_top
    (measurable_of_countable f).aestronglyMeasurable,
    MeasureTheory.eLpNorm', ENNReal.toReal_ofReal hq.le, MeasureTheory.lintegral_count]
  congr 1
  apply tsum_congr
  intro n
  rw [show ‖f n‖ₑ = ENNReal.ofReal ‖f n‖ by simp [enorm_eq_nnnorm],
    ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hq.le]

/-- For a function supported in a finite window, the `eLpNorm` against the counting measure is the
`ofReal` of the finite `ℓ^q` sum. -/
lemma eLpNorm_count_eq_ofReal_sum {f : ℤ → ℂ} {W : Finset ℤ} (hf : ∀ n, n ∉ W → f n = 0)
    {q : ℝ} (hq : 0 < q) :
    eLpNorm f (ENNReal.ofReal q) Measure.count
      = ENNReal.ofReal ((∑ n ∈ W, ‖f n‖ ^ q) ^ (1 / q)) := by
  rw [eLpNorm_count_eq_tsum f hq]
  have h : (∑' n : ℤ, ENNReal.ofReal (‖f n‖ ^ q)) = ∑ n ∈ W, ENNReal.ofReal (‖f n‖ ^ q) :=
    tsum_eq_sum (fun n hn => by
      rw [hf n hn, norm_zero, Real.zero_rpow (ne_of_gt hq), ENNReal.ofReal_zero])
  rw [h, ← ENNReal.ofReal_sum_of_nonneg (fun n _ => Real.rpow_nonneg (norm_nonneg _) q)]
  exact ENNReal.ofReal_rpow_of_nonneg
    (Finset.sum_nonneg fun n _ => Real.rpow_nonneg (norm_nonneg _) q) (by positivity)

/-- The reverse comparison: a finite `ℓ^q` sum over a window is dominated by the `eLpNorm`. -/
lemma ofReal_sum_le_eLpNorm_count (f : ℤ → ℂ) {q : ℝ} (hq : 0 < q) (F : Finset ℤ) :
    ENNReal.ofReal ((∑ n ∈ F, ‖f n‖ ^ q) ^ (1 / q))
      ≤ eLpNorm f (ENNReal.ofReal q) Measure.count := by
  rw [eLpNorm_count_eq_tsum f hq, ← ENNReal.ofReal_rpow_of_nonneg
    (Finset.sum_nonneg fun n _ => Real.rpow_nonneg (norm_nonneg _) q) (by positivity : (0:ℝ) ≤ 1/q)]
  apply ENNReal.rpow_le_rpow _ (by positivity)
  rw [ENNReal.ofReal_sum_of_nonneg (fun n _ => Real.rpow_nonneg (norm_nonneg _) q)]
  exact ENNReal.sum_le_tsum F

/-! ## The finite-`F` reduction -/

/-- The finite-`F` restriction of the operator: `g ↦ (b ↦ T (extendZeroLM S g) b)`. -/
noncomputable def restrictLM (T : (ℤ →₀ ℂ) →ₗ[ℂ] (ℤ → ℂ)) (S : Finset ℤ) (F : Finset ℤ) :
    (↥S → ℂ) →ₗ[ℂ] (↥F → ℂ) where
  toFun g b := T (extendZeroLM S g) b
  map_add' g h := by funext b; simp
  map_smul' c g := by funext b; simp

@[simp] lemma restrictLM_apply (T : (ℤ →₀ ℂ) →ₗ[ℂ] (ℤ → ℂ)) (S F : Finset ℤ)
    (g : ↥S → ℂ) (b : ↥F) : restrictLM T S F g b = T (extendZeroLM S g) b := rfl

/-- Transfer of a single `eLpNorm` endpoint bound to the finite type `↥S`: a finite `ℓ^q`-sum over
a window `F` of `T (extendZeroLM S g)` is bounded by `M` times the finite `ℓ^q`-sum of `g`. -/
private lemma endpoint_bound {q M : ℝ} (hq : 0 < q) (hM : 0 ≤ M)
    (T : (ℤ →₀ ℂ) →ₗ[ℂ] (ℤ → ℂ))
    (hT : ∀ f : ℤ →₀ ℂ, eLpNorm (T f) (ENNReal.ofReal q) Measure.count
      ≤ ENNReal.ofReal M * eLpNorm f (ENNReal.ofReal q) Measure.count)
    (S : Finset ℤ) (g : ↥S → ℂ) (F : Finset ℤ) :
    (∑ b ∈ F, ‖T (extendZeroLM S g) b‖ ^ q) ^ (1 / q)
      ≤ M * (∑ a : ↥S, ‖g a‖ ^ q) ^ (1 / q) := by
  have he := hT (extendZeroLM S g)
  have hlow := ofReal_sum_le_eLpNorm_count (T (extendZeroLM S g)) hq F
  have hup : eLpNorm (extendZeroLM S g) (ENNReal.ofReal q) Measure.count
      = ENNReal.ofReal ((∑ a : ↥S, ‖g a‖ ^ q) ^ (1 / q)) := by
    rw [eLpNorm_count_eq_ofReal_sum (f := extendZeroLM S g) (W := S)
      (fun n hn => by rw [extendZeroLM_apply, dif_neg hn]) hq]
    have hs : (∑ n ∈ S, ‖extendZeroLM S g n‖ ^ q) = ∑ a : ↥S, ‖g a‖ ^ q := by
      rw [Finset.sum_subtype S (fun x => Iff.rfl) (fun n => ‖extendZeroLM S g n‖ ^ q)]
      exact Finset.sum_congr rfl (fun a _ => by rw [extendZeroLM_apply, dif_pos a.2])
    rw [hs]
  have h1 : ENNReal.ofReal ((∑ b ∈ F, ‖T (extendZeroLM S g) b‖ ^ q) ^ (1 / q))
      ≤ ENNReal.ofReal M * ENNReal.ofReal ((∑ a : ↥S, ‖g a‖ ^ q) ^ (1 / q)) :=
    calc ENNReal.ofReal ((∑ b ∈ F, ‖T (extendZeroLM S g) b‖ ^ q) ^ (1 / q))
        ≤ eLpNorm (T (extendZeroLM S g)) (ENNReal.ofReal q) Measure.count := hlow
      _ ≤ ENNReal.ofReal M * eLpNorm (extendZeroLM S g) (ENNReal.ofReal q) Measure.count := he
      _ = ENNReal.ofReal M * ENNReal.ofReal ((∑ a : ↥S, ‖g a‖ ^ q) ^ (1 / q)) := by rw [hup]
  rw [← ENNReal.ofReal_mul hM] at h1
  exact (ENNReal.ofReal_le_ofReal_iff
    (mul_nonneg hM (Real.rpow_nonneg
      (Finset.sum_nonneg (fun a _ => Real.rpow_nonneg (norm_nonneg _) q)) _))).mp h1

end

end Work.BourgainPlan.Maximal
