import Mathlib.Tactic.Have
import Mathlib.Analysis.Fourier.LpSpace
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The `L²` Fourier transform of an `L¹ ∩ L²` function is the Fourier integral

If `h : ℝᵈ → ℂ` is both integrable and square-integrable, then the pointwise Fourier integral
`ξ ↦ ∫ v, 𝐞 (-⟪v, ξ⟫) • h v` represents the `L²` Fourier transform of the `L²` class `h2.toLp h`
of `h`. This is the classical statement that the `L²` (Plancherel) Fourier transform agrees with
the `L¹` Fourier transform on the intersection `L¹ ∩ L²`.

The proof goes through the embedding of `Lᵖ` functions into tempered distributions: since the `L¹`
and the `L²` class of `h` define the same tempered distribution, their (distributional) Fourier
transforms agree; the distributional Fourier transform of an `L¹` function is integration against
the Fourier integral, and finally a tempered distribution which is (a.e.) an `L¹ₗₒ𝒸` function
determines that function up to a.e. equality.
-/

open MeasureTheory FourierTransform
open scoped FourierTransform SchwartzMap ContDiff

namespace Commons.Analysis.Fourier

set_option maxHeartbeats 1000000

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V]

/-- `(r : ℂ) • z = r • z`: the complex scalar action of a real number is the real scalar action. -/
lemma ofReal_smul_eq_smul (r : ℝ) (z : ℂ) : (r : ℂ) • z = r • z := by
  rw [smul_eq_mul, Complex.real_smul]

/-- Self-adjointness of the Fourier transform, with one of the two functions only assumed
integrable (so that its Fourier transform is the Fourier integral). -/
theorem integral_fourier_smul_eq_of_integrable
    {f : V → ℂ} (hf : Integrable f) (g : SchwartzMap V ℂ) :
    ∫ x, (𝓕 g : SchwartzMap V ℂ) x • f x = ∫ x, (g : V → ℂ) x • (𝓕 f) x := by
  have h1 : ((𝓕 g : SchwartzMap V ℂ) : V → ℂ) =
      VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ V) (g : V → ℂ) := by
    rw [SchwartzMap.fourier_coe]; rfl
  have h2 : (𝓕 f) = VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ V) f := rfl
  rw [h1, h2]
  have := VectorFourier.integral_fourierIntegral_smul_eq_flip (𝕜 := ℝ) (V := V) (W := V)
    (e := Real.fourierChar) (μ := volume) (ν := volume) (L := innerₗ V)
    Real.continuous_fourierChar continuous_inner g.integrable hf
  rw [flip_innerₗ] at this
  exact this

/-- The `L²` Fourier transform of an `L¹ ∩ L²` function `h` is, almost everywhere, the pointwise
Fourier integral `ξ ↦ ∫ v, 𝐞 (-⟪v, ξ⟫) • h v`. -/
theorem fourier_toLp_ae_eq_fourier_of_memLp {h : V → ℂ}
    (h1 : MemLp h 1 (volume : Measure V)) (h2 : MemLp h 2 (volume : Measure V)) :
    ((𝓕 (h2.toLp h) : Lp ℂ 2 (volume : Measure V)) : V → ℂ)
      =ᵐ[volume] (fun ξ => 𝓕 h ξ) := by
  -- The `L¹` class and the `L²` class of `h` define the same tempered distribution.
  have hA : ((h2.toLp h : Lp ℂ 2 (volume : Measure V)) : 𝓢'(V, ℂ))
      = ((h1.toLp h : Lp ℂ 1 (volume : Measure V)) : 𝓢'(V, ℂ)) := by
    ext G
    rw [Lp.toTemperedDistribution_apply, Lp.toTemperedDistribution_apply]
    refine integral_congr_ae ?_
    filter_upwards [h2.coeFn_toLp, h1.coeFn_toLp] with x hx2 hx1
    rw [hx2, hx1]
  -- The distributional Fourier transform of the `L²` class is the `L²` Fourier transform.
  have hB : 𝓕 ((h2.toLp h : Lp ℂ 2 (volume : Measure V)) : 𝓢'(V, ℂ))
      = (((𝓕 (h2.toLp h) : Lp ℂ 2 (volume : Measure V))) : 𝓢'(V, ℂ)) :=
    Lp.fourier_toTemperedDistribution_eq (h2.toLp h)
  have hC : (((𝓕 (h2.toLp h) : Lp ℂ 2 (volume : Measure V))) : 𝓢'(V, ℂ))
      = 𝓕 ((h1.toLp h : Lp ℂ 1 (volume : Measure V)) : 𝓢'(V, ℂ)) :=
    hB.symm.trans (congrArg (fun T : 𝓢'(V, ℂ) => 𝓕 T) hA)
  -- The distributional Fourier transform of an `L¹` class is integration against the integral.
  have hR : ∀ G : SchwartzMap V ℂ,
      (𝓕 ((h1.toLp h : Lp ℂ 1 (volume : Measure V)) : 𝓢'(V, ℂ))) G
        = ∫ x, (G : V → ℂ) x • (𝓕 h) x := by
    intro G
    rw [TemperedDistribution.fourier_apply]
    rw [Lp.toTemperedDistribution_apply]
    rw [show (∫ x, (𝓕 G : SchwartzMap V ℂ) x • ((h1.toLp h) : V → ℂ) x
        = ∫ x, (𝓕 G : SchwartzMap V ℂ) x • h x) from ?_]
    · exact integral_fourier_smul_eq_of_integrable (memLp_one_iff_integrable.mp h1) G
    · refine integral_congr_ae ?_
      filter_upwards [h1.coeFn_toLp] with x hx
      rw [hx]
  -- Consequently the two functions agree when integrated against any Schwartz function.
  have hkey : ∀ G : SchwartzMap V ℂ,
      ∫ x, (G : V → ℂ) x • (((𝓕 (h2.toLp h) : Lp ℂ 2 (volume : Measure V))) : V → ℂ) x
        = ∫ x, (G : V → ℂ) x • (𝓕 h) x := by
    intro G
    have hG : (((𝓕 (h2.toLp h) : Lp ℂ 2 (volume : Measure V))) : 𝓢'(V,ℂ)) G
        = ∫ x, (G : V → ℂ) x
            • (((𝓕 (h2.toLp h) : Lp ℂ 2 (volume : Measure V))) : V → ℂ) x := by
      rw [Lp.toTemperedDistribution_apply]
    rw [← hG, hC, hR G]
  -- Local integrability of the two sides, to apply the fundamental lemma of the calculus of
  -- variations for smooth compactly supported test functions.
  have hlocu : LocallyIntegrable
      (fun x => ((𝓕 (h2.toLp h) : Lp ℂ 2 (volume : Measure V)) : V → ℂ) x)
      (volume : Measure V) :=
    (Lp.memLp (𝓕 (h2.toLp h))).locallyIntegrable (by norm_num)
  have hlocw : LocallyIntegrable (fun x => (𝓕 h) x) (volume : Measure V) :=
    (VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar continuous_inner
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
  simpa only [ofReal_smul_eq_smul] using hmain

/-- The `L²` Fourier transform of an `L¹ ∩ L²` function `h : ℝᵈ → ℂ` is, almost everywhere, the
pointwise Fourier integral of `h`. -/
theorem fourier_toLp_eq_fourier_integral {d : ℕ} {h : EuclideanSpace ℝ (Fin d) → ℂ}
    (h1 : MeasureTheory.MemLp h 1 (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))))
    (h2 : MeasureTheory.MemLp h 2 (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d)))) :
    ((FourierTransform.fourier (h2.toLp h) : MeasureTheory.Lp ℂ 2 (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d)))) :
        EuclideanSpace ℝ (Fin d) → ℂ)
      =ᵐ[MeasureTheory.volume] (fun ξ => FourierTransform.fourier h ξ) :=
  fourier_toLp_ae_eq_fourier_of_memLp h1 h2

end Commons.Analysis.Fourier