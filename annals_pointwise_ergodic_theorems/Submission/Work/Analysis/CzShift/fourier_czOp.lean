import Mathlib
import Submission.Work.Analysis.CzShift.Defs

/-!
# The Fourier transform of the shifted Calderón–Zygmund operator `czOp`

For a finite family of scalar kernels `K i : ℝ → ℂ` and scalars `ε i : ℂ`, the operator

  `czOp D K ε f x = ∑_{i ∈ D} ε i • ∫ y, K i (x − y) • f y`

is a finite sum of the convolution operators with kernels `K i`, i.e. of the multipliers
`ξ ↦ 𝓕(K i) ξ`.  Hence its Fourier transform is the multiplier with symbol
`ξ ↦ (∑_{i ∈ D} ε i · 𝓕(K i) ξ)`:

  `𝓕 (czOp D K ε f) ξ = (∑_{i ∈ D} ε i * 𝓕 (K i) ξ) • 𝓕 f ξ`.

This is the identity used in the `L²` bound for `czOp` via Plancherel
(`Work.Analysis.CzShift.l2_bound_of_fourier_symbol`), and in the proof of the shifted
Calderón–Zygmund multiplier theorem of Appendix B of Krause–Mirek–Tao.

The three ingredients of the proof are:

* `czOpOne K f` is the convolution `K ⋆ f` in Mathlib's convention
  (`MeasureTheory.convolution_lsmul_swap`);
* Mathlib's convolution theorem for the scalar-multiplication convolution,
  `Real.fourier_smul_convolution_eq`, valid for integrable functions;
* linearity of the Fourier integral over finite sums of *integrable* functions,
  proved here by induction (`fourier_sum_smul`), holding pointwise for the
  `L¹` Fourier transform since `𝓕` on `ℝ → H` is not registered as a linear map in Mathlib.
-/

namespace Work.Analysis.CzShift

open MeasureTheory Finset
open scoped Convolution

section FourierCZOp

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

set_option linter.unusedSectionVars false

/-- The single-kernel operator `czOpOne K f` is the convolution `K ⋆ f` in the sense of
scalar multiplication.  Mathlib's convolution is `(K ⋆ f) x = ∫ t, K t • f (x − t)`, so this is
just the change of variables `t ↦ x − t` (`MeasureTheory.convolution_lsmul_swap`). -/
lemma czOpOne_eq_convolution (K : ℝ → ℂ) (f : ℝ → H) :
    czOpOne K f = K ⋆[ContinuousLinearMap.lsmul ℂ ℂ] f := by
  funext x
  rw [convolution_lsmul_swap]
  rfl

/-- The convolution of an integrable scalar kernel with an integrable vector-valued function is
integrable. -/
lemma integrable_czOpOne (K : ℝ → ℂ) (f : ℝ → H) (hK : MeasureTheory.Integrable K)
    (hf : MeasureTheory.Integrable f) : MeasureTheory.Integrable (czOpOne K f) := by
  rw [czOpOne_eq_convolution]
  exact Integrable.integrable_convolution (ContinuousLinearMap.lsmul ℂ ℂ) hK hf

/-- The Fourier transform of the single-kernel operator `czOpOne K f` is the product of the
Fourier transforms: `𝓕 (K ⋆ f) ξ = 𝓕 K ξ • 𝓕 f ξ`.  This is Mathlib's convolution theorem
`Real.fourier_smul_convolution_eq`. -/
lemma fourier_czOpOne (K : ℝ → ℂ) (f : ℝ → H) (hK : MeasureTheory.Integrable K)
    (hf : MeasureTheory.Integrable f) (ξ : ℝ) :
    FourierTransform.fourier (czOpOne K f) ξ
      = FourierTransform.fourier K ξ • FourierTransform.fourier f ξ := by
  rw [czOpOne_eq_convolution, Real.fourier_smul_convolution_eq hK hf ξ]

/-- A finite sum `∑ i ∈ s, c i • g i` of integrable functions is integrable. -/
lemma integrable_sum_smul {ι : Type*} (s : Finset ι) (c : ι → ℂ) (g : ι → ℝ → H)
    (hg : ∀ i ∈ s, MeasureTheory.Integrable (g i)) :
    MeasureTheory.Integrable (∑ i ∈ s, c i • g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact ((hg i (Finset.mem_insert_self i s)).smul (c i)).add
      (ih fun j hj => hg j (Finset.mem_insert_of_mem hj))

/-- The Fourier transform of a finite sum of integrable functions is the sum of the Fourier
transforms: `𝓕 (∑ i ∈ s, c i • g i) = ∑ i ∈ s, c i • 𝓕 (g i)`. -/
lemma fourier_sum_smul {ι : Type*} (s : Finset ι) (c : ι → ℂ) (g : ι → ℝ → H)
    (hg : ∀ i ∈ s, MeasureTheory.Integrable (g i)) :
    FourierTransform.fourier (∑ i ∈ s, c i • g i)
      = ∑ i ∈ s, c i • FourierTransform.fourier (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty]
    ext ξ
    rw [Real.fourier_real_eq]
    simp
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    have hgi : MeasureTheory.Integrable (g i) := hg i (Finset.mem_insert_self i s)
    have hgs : MeasureTheory.Integrable (∑ j ∈ s, c j • g j) :=
      integrable_sum_smul s c g fun j hj => hg j (Finset.mem_insert_of_mem hj)
    have h₁ : FourierTransform.fourier (c i • g i + ∑ j ∈ s, c j • g j)
        = FourierTransform.fourier (c i • g i)
          + FourierTransform.fourier (∑ j ∈ s, c j • g j) :=
      VectorFourier.fourierIntegral_add Real.continuous_fourierChar continuous_inner
        (hgi.smul (c i)) hgs
    have h₂ : FourierTransform.fourier (c i • g i) = c i • FourierTransform.fourier (g i) :=
      VectorFourier.fourierIntegral_const_smul Real.fourierChar volume (innerₗ ℝ) (g i) (c i)
    rw [h₁, h₂, ih (fun j hj => hg j (Finset.mem_insert_of_mem hj))]

end FourierCZOp

theorem fourier_czOp {ι : Type*} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (D : Finset ι) (K : ι → ℝ → ℂ) (ε : ι → ℂ) (f : ℝ → H)
    (hK : ∀ i ∈ D, MeasureTheory.Integrable (K i)) (hf : MeasureTheory.Integrable f) :
    FourierTransform.fourier (Work.Analysis.CzShift.czOp D K ε f) =
      fun ξ => (∑ i ∈ D, ε i * FourierTransform.fourier (K i) ξ) •
        FourierTransform.fourier f ξ := by
  -- `czOp` is the finite sum of the single-kernel operators `ε i • czOpOne (K i) f`.
  have hsplit : czOp D K ε f = ∑ i ∈ D, ε i • czOpOne (K i) f := by
    funext x
    simp only [czOp, czOpOne, Finset.sum_apply, Pi.smul_apply]
  rw [hsplit]
  ext ξ
  -- Linearity of `𝓕` over the finite sum of integrable functions.
  rw [fourier_sum_smul D ε (fun i => czOpOne (K i) f)
    (fun i hi => integrable_czOpOne (K i) f (hK i hi) hf)]
  simp only [Finset.sum_apply, Pi.smul_apply]
  -- Each term is the product of the two Fourier transforms; then collect the scalar factors.
  rw [Finset.sum_congr rfl (fun i hi => by
        rw [fourier_czOpOne (K i) f (hK i hi) hf ξ, smul_smul]),
      ← Finset.sum_smul]

end Work.Analysis.CzShift
