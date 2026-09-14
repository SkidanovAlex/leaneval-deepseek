import Mathlib
import Submission.Commons.NumberTheory.NumberField.nrComplexPlaces_eq_one_of_finrank_three_of_discr_neg

open scoped ENNReal NNReal
open NumberField

namespace Commons.NumberTheory.NumberField

theorem exists_nonzero_integer_lt_of_finrank_three_of_discr_neg_no_lt_one {K : Type*} [Field K] [NumberField K]
    (hfin : Module.finrank ℚ K = 3) (hneg : NumberField.discr K < 0)
    {A B : ℝ} (hA0 : 0 < A) (hB0 : 0 < B)
    (hAB : A * B ^ 2 = 3)
    (hvol : 4 * Real.sqrt |(NumberField.discr K : ℝ)| < 2 * Real.pi * A * B ^ 2) :
    ∃ a : NumberField.RingOfIntegers K, a ≠ 0 ∧
      (∀ w : NumberField.InfinitePlace K, w.IsReal → (w a : ℝ) < A) ∧
      (∀ w : NumberField.InfinitePlace K, ¬ w.IsReal → (w a : ℝ) < B) := by
  classical
  let f : NumberField.InfinitePlace K → NNReal :=
    fun w => if w.IsReal then Real.toNNReal A else Real.toNNReal B
  have hnr : NumberField.InfinitePlace.nrComplexPlaces K = 1 :=
    Commons.NumberTheory.NumberField.nrComplexPlaces_eq_one_of_finrank_three_of_discr_neg hfin hneg
  have hnrreal : NumberField.InfinitePlace.nrRealPlaces K = 1 := by
    have h := NumberField.InfinitePlace.card_add_two_mul_card_eq_rank K
    rw [hfin, hnr] at h
    omega
  have hcard_real : Fintype.card {w : NumberField.InfinitePlace K // w.IsReal} = 1 := by
    simpa [NumberField.InfinitePlace.nrRealPlaces] using hnrreal
  have hcard_complex : Fintype.card {w : NumberField.InfinitePlace K // w.IsComplex} = 1 := by
    simpa [NumberField.InfinitePlace.nrComplexPlaces] using hnr
  have hprod_real : (∏ w : {w : NumberField.InfinitePlace K // w.IsReal},
      f w.1 ^ w.1.mult) = Real.toNNReal A := by
    rcases (Fintype.card_eq_one_iff.mp hcard_real) with ⟨w0, hw0⟩
    rw [Fintype.prod_eq_single w0]
    · have hw0real : (w0 : NumberField.InfinitePlace K).IsReal := w0.2
      simp [f, hw0real, NumberField.InfinitePlace.mult_isReal w0]
    · intro x hx
      exfalso
      exact hx (hw0 x)
  have hprod_complex : (∏ w : {w : NumberField.InfinitePlace K // w.IsComplex},
      f w.1 ^ w.1.mult) = (Real.toNNReal B) ^ 2 := by
    rcases (Fintype.card_eq_one_iff.mp hcard_complex) with ⟨w0, hw0⟩
    rw [Fintype.prod_eq_single w0]
    · have hw0complex : (w0 : NumberField.InfinitePlace K).IsComplex := w0.2
      have hnot : ¬ (w0 : NumberField.InfinitePlace K).IsReal := by
        simpa [NumberField.InfinitePlace.not_isReal_iff_isComplex] using hw0complex
      simp [f, hnot, NumberField.InfinitePlace.mult_isComplex w0]
    · intro x hx
      exfalso
      exact hx (hw0 x)
  have hprod_nn : (∏ w : NumberField.InfinitePlace K, f w ^ w.mult) =
      Real.toNNReal A * (Real.toNNReal B) ^ 2 := by
    rw [NumberField.InfinitePlace.prod_eq_prod_mul_prod]
    rw [hprod_real, hprod_complex]
  have hfactor_nn : NumberField.mixedEmbedding.convexBodyLTFactor K =
      (2 : NNReal) * NNReal.pi := by
    simp [NumberField.mixedEmbedding.convexBodyLTFactor, hnrreal, hnr]
  have hvol_conv : MeasureTheory.volume (NumberField.mixedEmbedding.convexBodyLT K f) =
      ENNReal.ofReal (2 * Real.pi * A * B ^ 2) := by
    rw [NumberField.mixedEmbedding.convexBodyLT_volume, hfactor_nn, hprod_nn]
    rw [← ENNReal.coe_mul]
    rw [← ENNReal.ofReal_coe_nnreal]
    congr 1
    simp [NNReal.coe_mul, NNReal.coe_pow, Real.coe_toNNReal A (le_of_lt hA0),
      Real.coe_toNNReal B (le_of_lt hB0), NNReal.coe_real_pi]
    ring
  have h2inv_enn : (2 : ENNReal)⁻¹ = ENNReal.ofReal (1 / 2) := by
    rw [← ENNReal.ofReal_ofNat]
    rw [← ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 2)]
    norm_num
  have hmink_eq : NumberField.mixedEmbedding.minkowskiBound K 1 =
      ENNReal.ofReal (4 * Real.sqrt |(NumberField.discr K : ℝ)|) := by
    have hfinmix : Module.finrank ℝ (NumberField.mixedEmbedding.mixedSpace K) = 3 := by
      rw [NumberField.mixedEmbedding.finrank, hfin]
    rw [NumberField.mixedEmbedding.minkowskiBound, hfinmix]
    rw [NumberField.mixedEmbedding.volume_fundamentalDomain_fractionalIdealLatticeBasis]
    rw [NumberField.mixedEmbedding.volume_fundamentalDomain_latticeBasis]
    simp [FractionalIdeal.absNorm_one, hnr]
    have hsqrt_enn : ((NNReal.sqrt ‖NumberField.discr K‖₊ : NNReal) : ENNReal) =
        ENNReal.ofReal (Real.sqrt |(NumberField.discr K : ℝ)|) := by
      rw [← ENNReal.ofReal_coe_nnreal]
      congr 1
      rw [Real.coe_sqrt, coe_nnnorm, Int.norm_eq_abs]
    rw [hsqrt_enn]
    rw [h2inv_enn]
    norm_num
    have h8 : (8 : ENNReal) = ENNReal.ofReal 8 := by norm_num
    have h4 : (4 : ENNReal) = ENNReal.ofReal 4 := by norm_num
    rw [h8, h4]
    rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    rw [← ENNReal.ofReal_mul
      (by positivity : (0 : ℝ) ≤ (1 / 2) * Real.sqrt |(NumberField.discr K : ℝ)|)]
    rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
    congr 1
    ring
  have hmink_lt : NumberField.mixedEmbedding.minkowskiBound K 1 <
      MeasureTheory.volume (NumberField.mixedEmbedding.convexBodyLT K f) := by
    rw [hmink_eq, hvol_conv]
    rw [ENNReal.ofReal_lt_ofReal_iff]
    · exact hvol
    · positivity
  obtain ⟨a, ha0, ha⟩ :=
    NumberField.mixedEmbedding.exists_ne_zero_mem_ringOfIntegers_lt K hmink_lt
  refine ⟨a, ha0, ?_, ?_⟩
  · intro w hw
    have hfa : (f w : ℝ) = A := by
      have hif : f w = Real.toNNReal A := by simp [f, hw]
      rw [hif, Real.coe_toNNReal A (le_of_lt hA0)]
    rw [← hfa]
    exact ha w
  · intro w hw
    have hfb : (f w : ℝ) = B := by
      have hif : f w = Real.toNNReal B := by simp [f, hw]
      rw [hif, Real.coe_toNNReal B (le_of_lt hB0)]
    rw [← hfb]
    exact ha w

end Commons.NumberTheory.NumberField
