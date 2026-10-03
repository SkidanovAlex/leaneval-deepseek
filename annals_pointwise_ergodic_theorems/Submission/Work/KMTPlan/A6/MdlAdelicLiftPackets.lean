/-
# Band-limited functions are closed under products

`Work.KMTPlan.A6.hasRealFreqSupport_mul`: if `ψ` (resp. `χ`) is the inverse Fourier transform of an
integrable amplitude supported in `S` (resp. `T`), then `ψ · χ` is the inverse Fourier transform of
an integrable amplitude supported in any set `U` containing `S + T`.

This is the elementary step of the §8 adelic construction
(`Work.KMTPlan.A6.AdelicFormPropPlus`, clauses (1)–(3)): the lift of the good part of the frozen
slice is `F n X ρ = zmodAvg P Q (u n X) (v n X) ρ`, a finite combination of *products* of the two
band-limited packet families, and the band `1/(8Q)` of `F` is exactly the sum of the bands of the
two packets.
-/
import Mathlib
import Submission.Work.KMTPlan.A6.MdlAdelicDefs
import Submission.Work.KMTPlan.A6.fourierInv_mul_eq_fourierInv_conv

-- v4.35 port: restore the v4.34 instance-unification behaviour (respectTransparency) in this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Work.KMTPlan.A6

noncomputable section

open MeasureTheory Polynomial
open scoped FourierTransform Convolution BigOperators
open Work.KMTAreas.A7Rep

/-- **The product of two band-limited functions is band-limited**, with the bands adding: if `ψ`
has amplitude supported in `S` and `χ` has amplitude supported in `T`, then `ψ · χ` has amplitude
(the convolution of the two amplitudes) supported in any `U ⊇ S + T`. -/
theorem hasRealFreqSupport_mul {S T U : Set ℝ} {ψ χ : ℝ → ℂ}
    (hψ : HasRealFreqSupport ψ S) (hχ : HasRealFreqSupport χ T)
    (hSTU : ∀ η ∈ S, ∀ ζ ∈ T, η + ζ ∈ U) :
    HasRealFreqSupport (fun t : ℝ => ψ t * χ t) U := by
  obtain ⟨A, hAint, hAsupp, hAeq⟩ := hψ
  obtain ⟨B, hBint, hBsupp, hBeq⟩ := hχ
  refine ⟨fun ζ : ℝ => ∫ η : ℝ, A η * B (ζ - η), ?_, ?_, ?_⟩
  · -- the convolution of two integrable amplitudes is integrable
    have h2 : (fun ζ : ℝ => ∫ η : ℝ, A η * B (ζ - η))
        = (A ⋆[ContinuousLinearMap.lsmul ℂ ℂ, volume] B) := by
      funext ζ
      rw [convolution_def]
      simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
    rw [h2]
    exact hAint.integrable_convolution (L := ContinuousLinearMap.lsmul ℂ ℂ) hBint
  · -- and it vanishes outside `U` (it vanishes outside `S + T ⊆ U`)
    intro ζ hζ
    have hzero : (fun η : ℝ => A η * B (ζ - η)) = fun _ : ℝ => (0 : ℂ) := by
      funext η
      by_cases hη : η ∈ S
      · have hζη : ζ - η ∉ T := fun hc => hζ (by
          have hmem := hSTU η hη (ζ - η) hc
          rwa [show η + (ζ - η) = ζ by ring] at hmem)
        rw [hBsupp (ζ - η) hζη, mul_zero]
      · rw [hAsupp η hη, zero_mul]
    simp [hzero]
  · -- and its inverse Fourier transform is the product
    intro t
    show ψ t * χ t = FourierTransformInv.fourierInv
      (fun ζ : ℝ => ∫ η : ℝ, A η * B (ζ - η)) t
    rw [hAeq t, hBeq t]
    exact fourierInv_mul_eq_fourierInv_conv A B hAint hBint t


/-- Additivity of the inverse Fourier transform on integrable amplitudes. -/
theorem fourierInv_add (f g : ℝ → ℂ) (hf : MeasureTheory.Integrable f)
    (hg : MeasureTheory.Integrable g) (x : ℝ) :
    FourierTransformInv.fourierInv (fun ξ : ℝ => f ξ + g ξ) x
      = FourierTransformInv.fourierInv f x + FourierTransformInv.fourierInv g x := by
  have h1 : MeasureTheory.Integrable (fun ξ : ℝ =>
      Complex.exp (↑(2 * Real.pi * inner ℝ ξ x) * Complex.I) • f ξ) :=
    hf.bdd_mul (by fun_prop) (Filter.Eventually.of_forall fun ξ => by
      rw [Complex.norm_exp_ofReal_mul_I])
  have h2 : MeasureTheory.Integrable (fun ξ : ℝ =>
      Complex.exp (↑(2 * Real.pi * inner ℝ ξ x) * Complex.I) • g ξ) :=
    hg.bdd_mul (by fun_prop) (Filter.Eventually.of_forall fun ξ => by
      rw [Complex.norm_exp_ofReal_mul_I])
  rw [Real.fourierInv_eq', Real.fourierInv_eq', Real.fourierInv_eq']
  rw [show (fun ξ : ℝ => Complex.exp (↑(2 * Real.pi * inner ℝ ξ x) * Complex.I) • (f ξ + g ξ))
        = (fun ξ : ℝ => Complex.exp (↑(2 * Real.pi * inner ℝ ξ x) * Complex.I) • f ξ)
            + (fun ξ : ℝ => Complex.exp (↑(2 * Real.pi * inner ℝ ξ x) * Complex.I) • g ξ) from by
      funext ξ; simp only [Pi.add_apply, smul_add]]
  exact integral_add h1 h2

/-- Homogeneity of the inverse Fourier transform for a scalar multiple. -/
theorem fourierInv_const_mul (a : ℂ) (f : ℝ → ℂ) (x : ℝ) :
    FourierTransformInv.fourierInv (fun ξ : ℝ => a * f ξ) x
      = a * FourierTransformInv.fourierInv f x := by
  rw [Real.fourierInv_eq', Real.fourierInv_eq']
  rw [show (fun ξ : ℝ => Complex.exp (↑(2 * Real.pi * inner ℝ ξ x) * Complex.I) • (a * f ξ))
        = fun ξ : ℝ => a * (Complex.exp (↑(2 * Real.pi * inner ℝ ξ x) * Complex.I) • f ξ) from by
      funext ξ; rw [smul_eq_mul, smul_eq_mul]; ring]
  exact integral_const_mul a _

/-- The inverse Fourier transform of a finite linear combination of integrable amplitudes. -/
theorem fourierInv_finset_sum {ι : Type*} (s : Finset ι) (c : ι → ℂ) (g : ι → ℝ → ℂ)
    (hg : ∀ i ∈ s, MeasureTheory.Integrable (g i)) (x : ℝ) :
    FourierTransformInv.fourierInv (fun ξ : ℝ => ∑ i ∈ s, c i * g i ξ) x
      = ∑ i ∈ s, c i * FourierTransformInv.fourierInv (g i) x := by
  have hInt : ∀ i ∈ s, MeasureTheory.Integrable (fun ξ : ℝ =>
      Complex.exp (↑(2 * Real.pi * inner ℝ ξ x) * Complex.I) • (c i * g i ξ)) := by
    intro i hi
    exact ((hg i hi).const_mul (c i)).bdd_mul (by fun_prop)
      (Filter.Eventually.of_forall fun ξ => by rw [Complex.norm_exp_ofReal_mul_I])
  rw [Real.fourierInv_eq']
  rw [show (fun ξ : ℝ => Complex.exp (↑(2 * Real.pi * inner ℝ ξ x) * Complex.I) •
        (∑ i ∈ s, c i * g i ξ))
      = fun ξ : ℝ => ∑ i ∈ s, Complex.exp (↑(2 * Real.pi * inner ℝ ξ x) * Complex.I) •
          (c i * g i ξ) from by
        funext ξ; rw [Finset.smul_sum]]
  rw [integral_finsetSum s hInt]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [← Real.fourierInv_eq']
  rw [fourierInv_const_mul (c i) (g i) x]

/-- **`HasRealFreqSupport` is closed under finite sums with constant coefficients.** -/
theorem hasRealFreqSupport_finset_sum {ι : Type*} (s : Finset ι) (c : ι → ℂ)
    {S : Set ℝ} {ψ : ι → ℝ → ℂ} (h : ∀ i ∈ s, HasRealFreqSupport (ψ i) S) :
    HasRealFreqSupport (fun t : ℝ => ∑ i ∈ s, c i * ψ i t) S := by
  classical
  let g : ι → ℝ → ℂ := fun i => if hi : i ∈ s then Classical.choose (h i hi) else 0
  have hgint : ∀ i ∈ s, MeasureTheory.Integrable (g i) := by
    intro i hi
    simp only [g, dif_pos hi]
    exact (Classical.choose_spec (h i hi)).1
  have hgsupp : ∀ i ∈ s, ∀ ξ : ℝ, ξ ∉ S → g i ξ = 0 := by
    intro i hi ξ hξ
    simp only [g, dif_pos hi]
    exact (Classical.choose_spec (h i hi)).2.1 ξ hξ
  have hgeq : ∀ i ∈ s, ∀ t : ℝ, ψ i t = FourierTransformInv.fourierInv (g i) t := by
    intro i hi t
    simp only [g, dif_pos hi]
    exact (Classical.choose_spec (h i hi)).2.2 t
  refine ⟨fun ξ : ℝ => ∑ i ∈ s, c i * g i ξ, ?_, ?_, ?_⟩
  · exact MeasureTheory.integrable_finsetSum s (fun i hi => (hgint i hi).const_mul (c i))
  · intro ξ hξ
    refine Finset.sum_eq_zero fun i hi => ?_
    rw [hgsupp i hi ξ hξ, mul_zero]
  · intro t
    rw [fourierInv_finset_sum s c g hgint t]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [hgeq i hi t]

/-- `HasRealFreqSupport` is closed under multiplication by a constant. -/
theorem hasRealFreqSupport_const_mul (c : ℂ) {S : Set ℝ} {ψ : ℝ → ℂ}
    (h : HasRealFreqSupport ψ S) : HasRealFreqSupport (fun t : ℝ => c * ψ t) S := by
  obtain ⟨g, hgint, hgsupp, hgeq⟩ := h
  refine ⟨fun ξ : ℝ => c * g ξ, hgint.const_mul c, ?_, ?_⟩
  · intro ξ hξ
    show c * g ξ = 0
    rw [hgsupp ξ hξ, mul_zero]
  · intro t
    show c * ψ t = FourierTransformInv.fourierInv (fun ξ : ℝ => c * g ξ) t
    rw [hgeq t, fourierInv_const_mul c g t]

/-- **The adelic lift of a slice that is the diagonal of a `zmodAvg` of two band-limited packet
families** — clauses (1)–(3) of `Work.KMTPlan.A6.AdelicFormPropPlus`, in the form in which the
construction of the packets is separated from the construction of the lift.  If the good part `c`
of a slice family is the diagonal of the `ZMod Q` averaging form of two band-limited families
`u`, `v`, then the lift `F n X ρ := zmodAvg P Q (u n X) (v n X) (ρ : ZMod Q)` realises both the
diagonal identity and the band `Icc (-β) β`. -/
theorem exists_adelicLift_of_zmodAvg {Q : ℕ} (P : ℤ[X]) {β β₁ β₂ : ℝ}
    (hβ : β₁ + β₂ ≤ β) (u v : ℕ → ℝ → ZMod Q → ℂ) (c : ℕ → ℤ → ℂ)
    (hu : ∀ (n : ℕ) (θ : ZMod Q),
      HasRealFreqSupport (fun X : ℝ => u n X θ) (Set.Icc (-β₁) β₁))
    (hv : ∀ (n : ℕ) (θ : ZMod Q),
      HasRealFreqSupport (fun X : ℝ => v n X θ) (Set.Icc (-β₂) β₂))
    (hc : ∀ (n : ℕ) (x : ℤ), c n x = zmodAvg P Q (u n x) (v n x) (x % ((Q : ℕ) : ℤ))) :
    ∃ F : ℕ → ℝ → ℤ → ℂ,
      (∀ (n : ℕ) (x : ℤ), F n (x : ℝ) (x % ((Q : ℕ) : ℤ)) = c n x) ∧
      (∀ (n : ℕ) (ρ : ℤ),
        HasRealFreqSupport (fun X : ℝ => F n X ρ) (Set.Icc (-β) β)) := by
  classical
  refine ⟨fun n X ρ => zmodAvg P Q (u n X) (v n X) ((ρ : ℤ) : ZMod Q), ?_, ?_⟩
  · intro n x
    show zmodAvg P Q (u n (x : ℝ)) (v n (x : ℝ))
        (((x % ((Q : ℕ) : ℤ) : ℤ)) : ZMod Q) = c n x
    exact (hc n x).symm
  · intro n ρ
    have hprod : ∀ y ∈ Finset.range Q,
        HasRealFreqSupport (fun X : ℝ =>
          u n X (((ρ : ℤ) : ZMod Q) + (y : ZMod Q))
            * v n X (((ρ : ℤ) : ZMod Q) + ((P.eval (y : ℤ) : ℤ) : ZMod Q)))
          (Set.Icc (-β) β) := by
      intro y _
      refine hasRealFreqSupport_mul (hu n _) (hv n _) ?_
      intro η hη ζ hζ
      simp only [Set.mem_Icc] at hη hζ ⊢
      constructor <;> linarith [hη.1, hη.2, hζ.1, hζ.2, hβ]
    have hsum := hasRealFreqSupport_finset_sum (Finset.range Q) (fun _ => (1 : ℂ)) hprod
    have hfinal : HasRealFreqSupport (fun X : ℝ => (Q : ℂ)⁻¹ * ∑ y ∈ Finset.range Q,
        u n X (((ρ : ℤ) : ZMod Q) + (y : ZMod Q))
          * v n X (((ρ : ℤ) : ZMod Q) + ((P.eval (y : ℤ) : ℤ) : ZMod Q)))
        (Set.Icc (-β) β) :=
      hasRealFreqSupport_const_mul _ (by simpa using hsum)
    have hform : (fun X : ℝ => zmodAvg P Q (u n X) (v n X) ((ρ : ℤ) : ZMod Q))
        = (fun X : ℝ => (Q : ℂ)⁻¹ * ∑ y ∈ Finset.range Q,
            u n X (((ρ : ℤ) : ZMod Q) + (y : ZMod Q))
              * v n X (((ρ : ℤ) : ZMod Q) + ((P.eval (y : ℤ) : ℤ) : ZMod Q))) := rfl
    rw [hform]
    exact hfinal

end

end Work.KMTPlan.A6
