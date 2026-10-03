import Mathlib.Analysis.Fourier.LpSpace

/-!
# Plancherel's theorem for an integrable `L²` function with values in a complex Hilbert space

If `h : ℝ → H` is both integrable and square-integrable, then the pointwise inverse Fourier
integral `𝓕⁻ h` has the same `L²` norm as `h`:

`‖𝓕⁻ h‖_{L²} = ‖h‖_{L²}`.

This is Plancherel's theorem in the form used for `L¹ ∩ L²` functions.  The pointwise inverse
Fourier integral is the `L¹` inverse Fourier transform, and the key input is that on `L¹ ∩ L²` it
agrees almost everywhere with the Plancherel (`L²`) inverse Fourier transform
(`fourierInv_toLp_ae_eq_fourierInv_vec`), which is an isometry of `L²`.

The main auxiliary results proved here are vector-valued refinements of the classical scalar
statements `Commons.Analysis.Fourier.fourierInv_toLp_ae_eq_fourierInv`: the target space is an
arbitrary complex Hilbert space `H`.

* `integral_fourierInv_smul_eq_of_integrable_vec`: self-adjointness of the inverse Fourier
  transform, with the `H`-valued function only assumed integrable.
* `fourierInv_toLp_ae_eq_fourierInv_vec`: the `L²` inverse Fourier transform of the `L²` class of
  `h` agrees a.e. with the pointwise inverse Fourier integral `𝓕⁻ h`.
* `enorm_fourierInv_Lp`: the inverse Fourier transform is an isometry of `L²`.
-/

open MeasureTheory FourierTransform
open scoped FourierTransform SchwartzMap ContDiff ENNReal

namespace Commons.Analysis.Fourier

set_option maxHeartbeats 1000000

/-- The bilinear form `-⟪·,·⟫` (the phase of the inverse Fourier transform) is continuous. -/
lemma continuous_neg_innerₗ_vec {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] :
    Continuous fun p : V × V ↦ (-innerₗ V : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) p.1 p.2 := by
  simp only [LinearMap.neg_apply]
  exact continuous_inner.neg

/-- The bilinear form `-⟪·,·⟫` is symmetric, i.e. equal to its flip. -/
lemma flip_neg_innerₗ_vec {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] :
    (-innerₗ V : V →ₗ[ℝ] V →ₗ[ℝ] ℝ).flip = -innerₗ V := by
  ext x y
  simp [LinearMap.flip_apply, real_inner_comm]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V]

/-- Self-adjointness of the inverse Fourier transform, with the `E`-valued function only
assumed integrable (so that its inverse Fourier transform is the inverse Fourier integral). -/
theorem integral_fourierInv_smul_eq_of_integrable_vec
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {f : V → E} (hf : Integrable f) (g : SchwartzMap V ℂ) :
    ∫ x, (𝓕⁻ g : SchwartzMap V ℂ) x • f x = ∫ x, (g : V → ℂ) x • (𝓕⁻ f) x := by
  have h1 : ((𝓕⁻ g : SchwartzMap V ℂ) : V → ℂ) =
      VectorFourier.fourierIntegral Real.fourierChar volume (-innerₗ V) (g : V → ℂ) := by
    rw [SchwartzMap.fourierInv_coe]; rfl
  have h2 : (𝓕⁻ f) = VectorFourier.fourierIntegral Real.fourierChar volume (-innerₗ V) f := rfl
  rw [h1, h2]
  have := VectorFourier.integral_fourierIntegral_smul_eq_flip (𝕜 := ℝ) (V := V) (W := V)
    (e := Real.fourierChar) (μ := volume) (ν := volume) (L := -innerₗ V)
    Real.continuous_fourierChar continuous_neg_innerₗ_vec g.integrable hf
  rwa [flip_neg_innerₗ_vec] at this

/-- The complex scalar action of a real number is the real scalar action. -/
lemma ofReal_smul_eq_smul_vec {E : Type*} [AddCommMonoid E] [Module ℝ E] [Module ℂ E]
    [IsScalarTower ℝ ℂ E] (r : ℝ) (z : E) : (r : ℂ) • z = r • z :=
  algebraMap_smul ℂ r z

/-- The `L²` inverse Fourier transform of an `L¹ ∩ L²` function `h : V → H` is, almost
everywhere, the pointwise inverse Fourier integral of `h`.

This is the vector-valued generalisation of
`Commons.Analysis.Fourier.fourierInv_toLp_ae_eq_fourierInv`. -/
theorem fourierInv_toLp_ae_eq_fourierInv_vec
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {h : V → H} (h1 : MemLp h 1 (volume : Measure V)) (h2 : MemLp h 2 (volume : Measure V)) :
    ((𝓕⁻ (h2.toLp h) : Lp H 2 (volume : Measure V)) : V → H) =ᵐ[volume]
      (fun ξ => 𝓕⁻ h ξ) := by
  -- The `L¹` class and the `L²` class of `h` define the same tempered distribution.
  have hA : ((h2.toLp h : Lp H 2 (volume : Measure V)) : 𝓢'(V, H))
      = ((h1.toLp h : Lp H 1 (volume : Measure V)) : 𝓢'(V, H)) := by
    ext G
    rw [Lp.toTemperedDistribution_apply, Lp.toTemperedDistribution_apply]
    refine integral_congr_ae ?_
    filter_upwards [h2.coeFn_toLp, h1.coeFn_toLp] with x hx2 hx1
    rw [hx2, hx1]
  -- The distributional inverse Fourier transform of the `L²` class is the `L²` inverse transform.
  have hB : 𝓕⁻ ((h2.toLp h : Lp H 2 (volume : Measure V)) : 𝓢'(V, H))
      = (((𝓕⁻ (h2.toLp h) : Lp H 2 (volume : Measure V))) : 𝓢'(V, H)) :=
    Lp.fourierInv_toTemperedDistribution_eq (h2.toLp h)
  have hC : (((𝓕⁻ (h2.toLp h) : Lp H 2 (volume : Measure V))) : 𝓢'(V, H))
      = 𝓕⁻ ((h1.toLp h : Lp H 1 (volume : Measure V)) : 𝓢'(V, H)) :=
    hB.symm.trans (congrArg (fun T : 𝓢'(V, H) => 𝓕⁻ T) hA)
  -- The distributional inverse Fourier transform of an `L¹` class is integration against the
  -- inverse Fourier integral.
  have hR : ∀ G : SchwartzMap V ℂ,
      (𝓕⁻ ((h1.toLp h : Lp H 1 (volume : Measure V)) : 𝓢'(V, H))) G
        = ∫ x, (G : V → ℂ) x • (𝓕⁻ h) x := by
    intro G
    rw [TemperedDistribution.fourierInv_apply]
    rw [Lp.toTemperedDistribution_apply]
    rw [show (∫ x, (𝓕⁻ G : SchwartzMap V ℂ) x • ((h1.toLp h) : V → H) x
        = ∫ x, (𝓕⁻ G : SchwartzMap V ℂ) x • h x) from ?_]
    · exact integral_fourierInv_smul_eq_of_integrable_vec (memLp_one_iff_integrable.mp h1) G
    · refine integral_congr_ae ?_
      filter_upwards [h1.coeFn_toLp] with x hx
      rw [hx]
  -- Consequently the two functions agree when integrated against any Schwartz function.
  have hkey : ∀ G : SchwartzMap V ℂ,
      ∫ x, (G : V → ℂ) x • (((𝓕⁻ (h2.toLp h) : Lp H 2 (volume : Measure V))) : V → H) x
        = ∫ x, (G : V → ℂ) x • (𝓕⁻ h) x := by
    intro G
    have hG : (((𝓕⁻ (h2.toLp h) : Lp H 2 (volume : Measure V))) : 𝓢'(V, H)) G
        = ∫ x, (G : V → ℂ) x
            • (((𝓕⁻ (h2.toLp h) : Lp H 2 (volume : Measure V))) : V → H) x := by
      rw [Lp.toTemperedDistribution_apply]
    rw [← hG, hC, hR G]
  -- Local integrability of the two sides, to apply the fundamental lemma of the calculus of
  -- variations for smooth compactly supported test functions.
  have hlocu : LocallyIntegrable
      (fun x => ((𝓕⁻ (h2.toLp h) : Lp H 2 (volume : Measure V)) : V → H) x)
      (volume : Measure V) :=
    (Lp.memLp (𝓕⁻ (h2.toLp h))).locallyIntegrable (by norm_num)
  have hlocw : LocallyIntegrable (fun x => (𝓕⁻ h) x) (volume : Measure V) :=
    (VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar continuous_neg_innerₗ_vec
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
  simpa only [ofReal_smul_eq_smul_vec] using hmain

/-- The inverse Fourier transform is an isometry of `L²` for functions on the real line with
values in a complex Hilbert space. -/
lemma enorm_fourierInv_Lp {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (Y : Lp H 2 (volume : Measure ℝ)) : ‖𝓕⁻ Y‖ₑ = ‖Y‖ₑ := by
  have h : ‖𝓕⁻ Y‖ = ‖Y‖ := by
    have := MeasureTheory.Lp.norm_fourier_eq (𝓕⁻ Y)
    rw [FourierInvPair.fourier_fourierInv_eq] at this
    exact this.symm
  rw [MeasureTheory.Lp.enorm_def, MeasureTheory.Lp.enorm_def]
  rw [MeasureTheory.Lp.norm_def, MeasureTheory.Lp.norm_def] at h
  rcases (ENNReal.toReal_eq_toReal_iff _ _).mp h with h' | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact h'
  · exact absurd h2 (MeasureTheory.Lp.eLpNorm_ne_top Y)
  · exact absurd h1 (MeasureTheory.Lp.eLpNorm_ne_top _)

/-- **Plancherel's theorem** for an integrable `L²` function with values in a complex Hilbert
space: the inverse Fourier transform preserves the `L²` norm. -/
theorem plancherel_integrable_memLp_two {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (h : ℝ → H) (h1 : MeasureTheory.Integrable h) (h2 : MeasureTheory.MemLp h 2 MeasureTheory.volume) : MeasureTheory.eLpNorm (FourierTransform.fourierInv h) (ENNReal.ofReal 2) MeasureTheory.volume = MeasureTheory.eLpNorm h (ENNReal.ofReal 2) MeasureTheory.volume := by
  have htwo : ENNReal.ofReal 2 = (2 : ℝ≥0∞) := by norm_num
  rw [htwo]
  have hf1 : MemLp h 1 (volume : Measure ℝ) := memLp_one_iff_integrable.mpr h1
  have hae := fourierInv_toLp_ae_eq_fourierInv_vec (V := ℝ) (h1 := hf1) (h2 := h2)
  have hnorm : ‖𝓕⁻ (h2.toLp h)‖ₑ = ‖h2.toLp h‖ₑ := enorm_fourierInv_Lp _
  calc eLpNorm (𝓕⁻ h) 2 volume
      = eLpNorm ((𝓕⁻ (h2.toLp h) : Lp H 2 (volume : Measure ℝ)) : ℝ → H) 2 volume :=
        eLpNorm_congr_ae hae.symm
    _ = ‖𝓕⁻ (h2.toLp h)‖ₑ := (MeasureTheory.Lp.enorm_def _).symm
    _ = ‖h2.toLp h‖ₑ := hnorm
    _ = eLpNorm h 2 volume := MeasureTheory.Lp.enorm_toLp h2

end Commons.Analysis.Fourier
