import Mathlib.Analysis.Fourier.LpSpace

/-!
# The `L²` inverse Fourier transform of an `L¹ ∩ L²` function is the inverse Fourier integral

If `h : V → ℂ` is both integrable and square-integrable, then the pointwise inverse Fourier
integral `ξ ↦ ∫ v, 𝐞 ⟪v, ξ⟫ • h v` represents the Plancherel (`L²`) inverse Fourier transform
of the `L²` class `h2.toLp h` of `h`. This is the classical statement that the `L²` (Plancherel)
inverse Fourier transform agrees with the `L¹` inverse Fourier transform on the intersection
`L¹ ∩ L²`.

This mirrors `Commons.Analysis.Fourier.fourier_toLp_ae_eq_fourier_of_memLp` for the *forward*
transform. The proof goes through the embedding of `Lᵖ` functions into tempered distributions:
the `L¹` and the `L²` class of `h` define the same tempered distribution, hence their
(distributional) inverse Fourier transforms agree; the distributional inverse Fourier transform
of an `L¹` function is integration against the inverse Fourier integral, and finally a tempered
distribution which is (a.e.) an `L¹ₗₒ𝒸` function determines that function up to a.e. equality.
-/

open MeasureTheory FourierTransform
open scoped FourierTransform SchwartzMap ContDiff

namespace Commons.Analysis.Fourier

set_option maxHeartbeats 1000000

/-- The bilinear form `-⟪·,·⟫` (the phase of the inverse Fourier transform) is continuous. -/
lemma continuous_neg_innerₗ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] :
    Continuous fun p : V × V ↦ (-innerₗ V : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) p.1 p.2 := by
  simp only [LinearMap.neg_apply]
  exact continuous_inner.neg

/-- The bilinear form `-⟪·,·⟫` is symmetric, i.e. equal to its flip. -/
lemma flip_neg_innerₗ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] :
    (-innerₗ V : V →ₗ[ℝ] V →ₗ[ℝ] ℝ).flip = -innerₗ V := by
  ext x y
  simp [LinearMap.flip_apply, real_inner_comm]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V]

/-- `(r : ℂ) • z = r • z`: the complex scalar action of a real number is the real scalar action. -/
lemma ofReal_smul_eq_smul' (r : ℝ) (z : ℂ) : (r : ℂ) • z = r • z := by
  rw [smul_eq_mul, Complex.real_smul]

/-- Self-adjointness of the inverse Fourier transform, with one of the two functions only
assumed integrable (so that its inverse Fourier transform is the inverse Fourier integral). -/
theorem integral_fourierInv_smul_eq_of_integrable
    {f : V → ℂ} (hf : Integrable f) (g : SchwartzMap V ℂ) :
    ∫ x, (𝓕⁻ g : SchwartzMap V ℂ) x • f x = ∫ x, (g : V → ℂ) x • (𝓕⁻ f) x := by
  have h1 : ((𝓕⁻ g : SchwartzMap V ℂ) : V → ℂ) =
      VectorFourier.fourierIntegral Real.fourierChar volume (-innerₗ V) (g : V → ℂ) := by
    rw [SchwartzMap.fourierInv_coe]; rfl
  have h2 : (𝓕⁻ f) = VectorFourier.fourierIntegral Real.fourierChar volume (-innerₗ V) f := rfl
  rw [h1, h2]
  have := VectorFourier.integral_fourierIntegral_smul_eq_flip (𝕜 := ℝ) (V := V) (W := V)
    (e := Real.fourierChar) (μ := volume) (ν := volume) (L := -innerₗ V)
    Real.continuous_fourierChar continuous_neg_innerₗ g.integrable hf
  rwa [flip_neg_innerₗ] at this

/-- The `L²` inverse Fourier transform of an `L¹ ∩ L²` function `h` is, almost everywhere, the
pointwise inverse Fourier integral `ξ ↦ ∫ v, 𝐞 ⟪v, ξ⟫ • h v`. -/
theorem fourierInv_toLp_ae_eq_fourierInv
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V]
    {h : V → ℂ} (h1 : MeasureTheory.MemLp h 1 (MeasureTheory.volume : MeasureTheory.Measure V))
    (h2 : MeasureTheory.MemLp h 2 (MeasureTheory.volume : MeasureTheory.Measure V)) :
    ((FourierTransform.fourierInv (h2.toLp h) :
        MeasureTheory.Lp ℂ 2 (MeasureTheory.volume : MeasureTheory.Measure V)) : V → ℂ) =ᵐ[MeasureTheory.volume]
      (fun ξ => FourierTransform.fourierInv h ξ) := by
  -- The `L¹` class and the `L²` class of `h` define the same tempered distribution.
  have hA : ((h2.toLp h : Lp ℂ 2 (volume : Measure V)) : 𝓢'(V, ℂ))
      = ((h1.toLp h : Lp ℂ 1 (volume : Measure V)) : 𝓢'(V, ℂ)) := by
    ext G
    rw [Lp.toTemperedDistribution_apply, Lp.toTemperedDistribution_apply]
    refine integral_congr_ae ?_
    filter_upwards [h2.coeFn_toLp, h1.coeFn_toLp] with x hx2 hx1
    rw [hx2, hx1]
  -- The distributional inverse Fourier transform of the `L²` class is the `L²` inverse transform.
  have hB : 𝓕⁻ ((h2.toLp h : Lp ℂ 2 (volume : Measure V)) : 𝓢'(V, ℂ))
      = (((𝓕⁻ (h2.toLp h) : Lp ℂ 2 (volume : Measure V))) : 𝓢'(V, ℂ)) :=
    Lp.fourierInv_toTemperedDistribution_eq (h2.toLp h)
  have hC : (((𝓕⁻ (h2.toLp h) : Lp ℂ 2 (volume : Measure V))) : 𝓢'(V, ℂ))
      = 𝓕⁻ ((h1.toLp h : Lp ℂ 1 (volume : Measure V)) : 𝓢'(V, ℂ)) :=
    hB.symm.trans (congrArg (fun T : 𝓢'(V, ℂ) => 𝓕⁻ T) hA)
  -- The distributional inverse Fourier transform of an `L¹` class is integration against the
  -- inverse Fourier integral.
  have hR : ∀ G : SchwartzMap V ℂ,
      (𝓕⁻ ((h1.toLp h : Lp ℂ 1 (volume : Measure V)) : 𝓢'(V, ℂ))) G
        = ∫ x, (G : V → ℂ) x • (𝓕⁻ h) x := by
    intro G
    rw [TemperedDistribution.fourierInv_apply]
    rw [Lp.toTemperedDistribution_apply]
    rw [show (∫ x, (𝓕⁻ G : SchwartzMap V ℂ) x • ((h1.toLp h) : V → ℂ) x
        = ∫ x, (𝓕⁻ G : SchwartzMap V ℂ) x • h x) from ?_]
    · exact integral_fourierInv_smul_eq_of_integrable (memLp_one_iff_integrable.mp h1) G
    · refine integral_congr_ae ?_
      filter_upwards [h1.coeFn_toLp] with x hx
      rw [hx]
  -- Consequently the two functions agree when integrated against any Schwartz function.
  have hkey : ∀ G : SchwartzMap V ℂ,
      ∫ x, (G : V → ℂ) x • (((𝓕⁻ (h2.toLp h) : Lp ℂ 2 (volume : Measure V))) : V → ℂ) x
        = ∫ x, (G : V → ℂ) x • (𝓕⁻ h) x := by
    intro G
    have hG : (((𝓕⁻ (h2.toLp h) : Lp ℂ 2 (volume : Measure V))) : 𝓢'(V, ℂ)) G
        = ∫ x, (G : V → ℂ) x
            • (((𝓕⁻ (h2.toLp h) : Lp ℂ 2 (volume : Measure V))) : V → ℂ) x := by
      rw [Lp.toTemperedDistribution_apply]
    rw [← hG, hC, hR G]
  -- Local integrability of the two sides, to apply the fundamental lemma of the calculus of
  -- variations for smooth compactly supported test functions.
  have hlocu : LocallyIntegrable
      (fun x => ((𝓕⁻ (h2.toLp h) : Lp ℂ 2 (volume : Measure V)) : V → ℂ) x)
      (volume : Measure V) :=
    (Lp.memLp (𝓕⁻ (h2.toLp h))).locallyIntegrable (by norm_num)
  have hlocw : LocallyIntegrable (fun x => (𝓕⁻ h) x) (volume : Measure V) :=
    (VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar continuous_neg_innerₗ
      (memLp_one_iff_integrable.mp h1)).locallyIntegrable
  refine ae_eq_of_integral_contDiff_smul_eq hlocu hlocw ?_
  intro φ hφd hφs
  have hΦsupp : HasCompactSupport (fun x : V => (φ x : ℂ)) :=
    hφs.comp_left (g := Complex.ofRealCLM) rfl
  have hΦdiff : ContDiff ℝ ∞ (fun x : V => (φ x : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hφd
  let Φ : SchwartzMap V ℂ := hΦsupp.toSchwartzMap hΦdiff
  have hΦcoe : (Φ : V → ℂ) = fun x => (φ x : ℂ) := rfl
  have hmain := hkey Φ
  rw [hΦcoe] at hmain
  simpa only [ofReal_smul_eq_smul'] using hmain

end Commons.Analysis.Fourier
