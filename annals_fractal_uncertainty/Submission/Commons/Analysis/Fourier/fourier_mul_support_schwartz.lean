import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

/-!
# The Fourier transform of a product of Schwartz functions with separated support

If `g` and `φ` are Schwartz functions whose Fourier transforms vanish outside the sets
`K` and `K'` respectively, then the Fourier transform of the pointwise product `g * φ`
vanishes outside the Minkowski sum `K + K'`.

The crucial identity is that the Fourier transform of a product is the convolution of the
Fourier transforms:
`𝓕 (g * φ) ξ = ∫ y, (𝓕⁻ φ) y • (𝓕 g) (y + ξ)`.
For `ξ ∉ K + K'` and every `y`, either `-y ∉ K'`, in which case `(𝓕⁻ φ) y = 𝓕 φ (-y) = 0`,
or `-y ∈ K'`, in which case `y + ξ ∉ K` (since otherwise `ξ = (y + ξ) + (-y) ∈ K + K'`),
so that `(𝓕 g) (y + ξ) = 0`. Hence the integrand vanishes identically.
-/

set_option autoImplicit false

namespace Commons.Analysis.Fourier

open MeasureTheory FourierTransform
open scoped Real RealInnerProductSpace

section General

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V]
    [BorelSpace V] [FiniteDimensional ℝ V]

/-- The Fourier integral with respect to the flipped inner product agrees with the Fourier
transform, since the inner product is symmetric. -/
theorem vectorFourier_flip_inner_eq_fourier (h : V → ℂ) :
    VectorFourier.fourierIntegral 𝐞 volume (innerₗ V).flip h = 𝓕 h := by
  ext x
  rw [Real.fourier_eq]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro y
  simp only [LinearMap.flip_apply, innerₗ_apply_apply]
  rw [real_inner_comm]

/-- The Fourier transform is self-adjoint: `∫ 𝓕 f · h = ∫ f · 𝓕 h` for integrable functions
`f` and `h`. -/
theorem fourier_integral_mul_selfadjoint (f h : V → ℂ) (hf : Integrable f) (hh : Integrable h) :
    ∫ x, 𝓕 f x • h x = ∫ x, f x • 𝓕 h x := by
  have hL : Continuous fun p : V × V => (innerₗ V) p.1 p.2 := by
    change Continuous fun p : V × V => ⟪p.1, p.2⟫
    exact continuous_inner
  have hthis := VectorFourier.integral_fourierIntegral_smul_eq_flip (𝕜 := ℝ) (V := V) (W := V)
    (e := (𝐞 : AddChar ℝ Circle)) (μ := volume) (ν := volume) (L := innerₗ V)
    (f := f) (g := h) Real.continuous_fourierChar hL hf hh
  rw [vectorFourier_flip_inner_eq_fourier] at hthis
  exact hthis

/-- The Fourier transform of a pointwise product is the integral of the product of the
inverse Fourier and Fourier transforms, shifted by `ξ`. -/
theorem fourier_mul_eq_integral_inner (g φ : SchwartzMap V ℂ) (ξ : V) :
    𝓕 (fun x : V => (g : V → ℂ) x * (φ : V → ℂ) x) ξ
      = ∫ x : V, (𝓕⁻ ((φ : V → ℂ))) x • 𝓕 ((g : V → ℂ)) (x + ξ) := by
  set h : V → ℂ := fun x => 𝐞 (-inner ℝ x ξ) • (g : V → ℂ) x with hh
  have hfinv : Integrable (𝓕⁻ ((φ : V → ℂ))) volume := by
    rw [← SchwartzMap.fourierInv_coe φ]
    exact (𝓕⁻ φ).integrable
  have hhint : Integrable h volume := by
    rw [hh]
    exact (Real.fourierIntegral_convergent_iff (f := (g : V → ℂ)) (μ := volume) ξ).2 g.integrable
  have hinv : 𝓕 (𝓕⁻ ((φ : V → ℂ))) = (φ : V → ℂ) := by
    refine Continuous.fourier_fourierInv_eq φ.continuous φ.integrable ?_
    rw [← SchwartzMap.fourier_coe φ]
    exact (𝓕 φ).integrable
  have key1 : 𝓕 (fun x : V => (g : V → ℂ) x * (φ : V → ℂ) x) ξ
      = ∫ x, (φ : V → ℂ) x • h x := by
    rw [Real.fourier_eq]
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro x
    rw [hh]
    simp only [Circle.smul_def]
    ring
  have key2 : ∫ x, (φ : V → ℂ) x • h x = ∫ x, (𝓕⁻ ((φ : V → ℂ))) x • 𝓕 h x := by
    have := fourier_integral_mul_selfadjoint (𝓕⁻ ((φ : V → ℂ))) h hfinv hhint
    rwa [hinv] at this
  have hFh : 𝓕 h = fun x => 𝓕 ((g : V → ℂ)) (x + ξ) := by
    funext x
    rw [Real.fourier_eq, Real.fourier_eq]
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro y
    simp only [hh]
    rw [smul_smul, ← AddChar.map_add_eq_mul, ← neg_add, ← inner_add_right]
  have key3 : ∫ x, (𝓕⁻ ((φ : V → ℂ))) x • 𝓕 h x
      = ∫ x, (𝓕⁻ ((φ : V → ℂ))) x • 𝓕 ((g : V → ℂ)) (x + ξ) := by
    rw [hFh]
  exact key1.trans (key2.trans key3)

/-- General version of `fourier_mul_support_schwartz` over an arbitrary finite-dimensional
real inner product space. -/
theorem fourier_mul_support_schwartz_gen (g φ : SchwartzMap V ℂ) {K K' : Set V}
    (hK : ∀ ξ, ξ ∉ K → FourierTransform.fourier g ξ = 0)
    (hK' : ∀ ξ, ξ ∉ K' → FourierTransform.fourier φ ξ = 0) :
    ∀ ξ, (∀ a ∈ K, ∀ b ∈ K', ξ ≠ a + b) →
      FourierTransform.fourier
        (fun x : V => (g : V → ℂ) x * (φ : V → ℂ) x) ξ = 0 := by
  intro ξ hξ
  rw [fourier_mul_eq_integral_inner g φ ξ]
  have hzero : (fun x : V => (𝓕⁻ ((φ : V → ℂ))) x • 𝓕 ((g : V → ℂ)) (x + ξ)) = 0 := by
    funext x
    by_cases hx : -x ∈ K'
    · have hgz : 𝓕 ((g : V → ℂ)) (x + ξ) = 0 := by
        by_contra hne
        have hmem : x + ξ ∈ K := by
          by_contra hc
          exact hne (by
            rw [← congrFun (SchwartzMap.fourier_coe g) (x + ξ)]
            exact hK (x + ξ) hc)
        exact hξ (x + ξ) hmem (-x) hx (by abel)
      simp [hgz]
    · have hφz : (𝓕⁻ ((φ : V → ℂ))) x = 0 := by
        rw [Real.fourierInv_eq_fourier_neg]
        rw [← congrFun (SchwartzMap.fourier_coe φ) (-x)]
        exact hK' (-x) hx
      simp [hφz]
  rw [hzero]
  simp

end General

/-- If the Fourier transforms of the Schwartz functions `g` and `φ` are supported in `K` and
`K'`, then the Fourier transform of the product `g * φ` is supported in the Minkowski sum
`K + K'`. -/
theorem fourier_mul_support_schwartz {d : ℕ} (g φ : SchwartzMap (EuclideanSpace ℝ (Fin d)) ℂ)
    {K K' : Set (EuclideanSpace ℝ (Fin d))}
    (hK : ∀ ξ, ξ ∉ K → FourierTransform.fourier g ξ = 0)
    (hK' : ∀ ξ, ξ ∉ K' → FourierTransform.fourier φ ξ = 0) :
    ∀ ξ, (∀ a ∈ K, ∀ b ∈ K', ξ ≠ a + b) →
      FourierTransform.fourier
        (fun x : EuclideanSpace ℝ (Fin d) => (g : EuclideanSpace ℝ (Fin d) → ℂ) x *
          (φ : EuclideanSpace ℝ (Fin d) → ℂ) x) ξ = 0 := by
  exact fourier_mul_support_schwartz_gen g φ hK hK'

end Commons.Analysis.Fourier