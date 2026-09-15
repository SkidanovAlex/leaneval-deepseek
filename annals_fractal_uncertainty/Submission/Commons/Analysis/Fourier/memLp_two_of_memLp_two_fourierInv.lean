import Mathlib.Analysis.Fourier.LpSpace

namespace Commons.Analysis.Fourier

open MeasureTheory FourierTransform
open scoped FourierTransform SchwartzMap ENNReal

section Aux

variable {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V]

/-- Parseval-type pairing identity underlying the `L¹`-Fourier inversion: for an integrable
function `G` and a Schwartz function `ψ`,
`∫ G · ψ = ∫ (𝓕⁻G) · (𝓕ψ)`.

This is the "self-adjointness of the Fourier transform on `L¹ ∩ 𝓢`" statement
(`VectorFourier.integral_fourierIntegral_smul_eq_flip`), combined with the reflection identities
`𝓕⁻ f = 𝓕 (f ∘ neg)` and `𝓕 (𝓕⁻ ψ) = ψ`. -/
lemma integral_mul_eq_integral_fourierInv_mul_fourier {G : V → ℂ} (hG : Integrable G)
    (ψ : 𝓢(V, ℂ)) :
    ∫ x, G x * ψ x = ∫ ξ, (𝓕⁻ G) ξ * (𝓕 ψ : 𝓢(V,ℂ)) ξ := by
  have hflip : (innerₗ V).flip = innerₗ V := by
    ext v w
    simp only [LinearMap.flip_apply, innerₗ_apply_apply]
    rw [real_inner_comm]
  have hgint : Integrable (fun x : V => (𝓕⁻ ψ : 𝓢(V,ℂ)) x) := (𝓕⁻ ψ).integrable
  have key := VectorFourier.integral_fourierIntegral_smul_eq_flip (𝕜 := ℝ) (V := V) (W := V)
    (F := ℂ) (e := Real.fourierChar) (μ := volume) (ν := volume) (L := innerₗ V)
    (f := G) (g := fun x : V => (𝓕⁻ ψ : 𝓢(V,ℂ)) x)
    Real.continuous_fourierChar continuous_inner hG hgint
  rw [hflip] at key
  have hfinv : (𝓕 (fun x : V => (𝓕⁻ ψ : 𝓢(V,ℂ)) x) : V → ℂ) = ⇑ψ := by
    have hcoeeq : (fun x : V => (𝓕⁻ ψ : 𝓢(V,ℂ)) x) = (𝓕⁻ (⇑ψ) : V → ℂ) := by
      funext x; rw [SchwartzMap.fourierInv_coe]
    rw [hcoeeq]
    exact ψ.continuous.fourier_fourierInv_eq ψ.integrable
      (by rw [← SchwartzMap.fourier_coe]; exact (𝓕 ψ).integrable)
  have hkey : ∫ ξ, (𝓕 G) ξ * (𝓕⁻ ψ : 𝓢(V,ℂ)) ξ = ∫ x, G x * ψ x := by
    have k2 := key
    rw [show VectorFourier.fourierIntegral 𝐞 volume (innerₗ V) G = (𝓕 G : V → ℂ) from rfl] at k2
    rw [show VectorFourier.fourierIntegral 𝐞 volume (innerₗ V)
        (fun x : V => (𝓕⁻ ψ : 𝓢(V,ℂ)) x) = (⇑ψ : V → ℂ) from hfinv] at k2
    simpa using k2
  have hreflect : ∫ ξ, (𝓕⁻ G) ξ * (𝓕 ψ : 𝓢(V,ℂ)) ξ
      = ∫ ξ, (𝓕 G) ξ * (𝓕⁻ ψ : 𝓢(V,ℂ)) ξ := by
    have h1 : ∀ ξ, (𝓕⁻ G) ξ = (𝓕 G) (-ξ) := fun ξ => Real.fourierInv_eq_fourier_neg G ξ
    have h2 : ∀ ξ, (𝓕⁻ ψ : 𝓢(V,ℂ)) ξ = (𝓕 ψ : 𝓢(V,ℂ)) (-ξ) := by
      intro ξ
      rw [SchwartzMap.fourierInv_coe, SchwartzMap.fourier_coe]
      exact Real.fourierInv_eq_fourier_neg (⇑ψ) ξ
    simp_rw [h1, h2]
    simpa using MeasureTheory.integral_neg_eq_self
      (fun ξ => (𝓕 G) ξ * (𝓕 ψ : 𝓢(V,ℂ)) (-ξ)) volume
  rw [← hkey]
  exact hreflect.symm

end Aux

/-- An integrable function whose inverse Fourier transform is square-integrable is itself
square-integrable.  (Fourier inversion: the square-integrable function `𝓕⁻ G` is the
`L²`-Fourier transform of its own `L²`-transform, which is `G`.) -/
theorem memLp_two_of_memLp_two_fourierInv {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V]
    {G : V → ℂ} (hG : MeasureTheory.Integrable G)
    (h2 : MeasureTheory.MemLp (𝓕⁻ G) 2 (MeasureTheory.volume : MeasureTheory.Measure V)) :
    MeasureTheory.MemLp G 2 (MeasureTheory.volume : MeasureTheory.Measure V) := by
  have hG1 : MemLp G 1 (volume : Measure V) := memLp_one_iff_integrable.mpr hG
  let G1 : Lp ℂ 1 (volume : Measure V) := hG1.toLp G
  let u : Lp ℂ 2 (volume : Measure V) := h2.toLp (𝓕⁻ G)
  let k : Lp ℂ 2 (volume : Measure V) := 𝓕 u
  have hu : (u : V → ℂ) =ᵐ[volume] 𝓕⁻ G := h2.coeFn_toLp
  have hG1c : (G1 : V → ℂ) =ᵐ[volume] G := hG1.coeFn_toLp
  -- Pairing of `𝓕 u` against every Schwarz function agrees with that of `G`.
  have hpair : ∀ ψ : 𝓢(V, ℂ), ∫ x, ψ x * (k : V → ℂ) x = ∫ x, ψ x * G x := by
    intro ψ
    have key : (k : 𝓢'(V,ℂ)) ψ = (G1 : 𝓢'(V,ℂ)) ψ := by
      have hfourier : (k : 𝓢'(V,ℂ)) = 𝓕 (u : 𝓢'(V,ℂ)) := by
        simp only [k]
        exact (MeasureTheory.Lp.fourier_toTemperedDistribution_eq u).symm
      rw [hfourier, TemperedDistribution.fourier_apply,
        MeasureTheory.Lp.toTemperedDistribution_apply,
        MeasureTheory.Lp.toTemperedDistribution_apply]
      have step1 : ∫ x, (𝓕 ψ : 𝓢(V,ℂ)) x • (u : V → ℂ) x
          = ∫ x, (𝓕 ψ : 𝓢(V,ℂ)) x • (𝓕⁻ G) x := by
        apply integral_congr_ae
        filter_upwards [hu] with x hx
        rw [hx]
      have step2 : ∫ x, (𝓕 ψ : 𝓢(V,ℂ)) x • (𝓕⁻ G) x = ∫ x, ψ x • G x := by
        have hp := integral_mul_eq_integral_fourierInv_mul_fourier hG ψ
        simp only [smul_eq_mul]
        trans ∫ x, (𝓕⁻ G) x * (𝓕 ψ : 𝓢(V,ℂ)) x
        · apply integral_congr_ae
          filter_upwards with x
          exact mul_comm _ _
        · rw [← hp]
          apply integral_congr_ae
          filter_upwards with x
          exact mul_comm _ _
      have step3 : ∫ x, ψ x • (G1 : V → ℂ) x = ∫ x, ψ x • G x := by
        apply integral_congr_ae
        filter_upwards [hG1c] with x hx
        rw [hx]
      rw [step1, step2, ← step3]
    have hk : (k : 𝓢'(V,ℂ)) ψ = ∫ x, ψ x * (k : V → ℂ) x := by
      rw [MeasureTheory.Lp.toTemperedDistribution_apply]
      simp only [smul_eq_mul]
    have hG' : (G1 : 𝓢'(V,ℂ)) ψ = ∫ x, ψ x * G x := by
      rw [MeasureTheory.Lp.toTemperedDistribution_apply]
      simp only [smul_eq_mul]
      apply integral_congr_ae
      filter_upwards [hG1c] with x hx
      rw [hx]
    rw [← hk, key, hG']
  -- Test functions: `∫ g • (𝓕u - G) = 0` for all compactly supported smooth real `g`.
  have hzero : ∀ g : V → ℝ, ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g →
      ∫ x, g x • ((k : V → ℂ) x - G x) = 0 := by
    intro g hgs hgc
    have hg1 : HasCompactSupport (Complex.ofRealCLM ∘ g) := hgc.comp_left rfl
    have hg2 : ContDiff ℝ (⊤ : ℕ∞) (Complex.ofRealCLM ∘ g) := by fun_prop
    set ψ : 𝓢(V, ℂ) := hg1.toSchwartzMap hg2
    have hψcoe : ∀ x, (ψ : V → ℂ) x = (g x : ℂ) := fun x => rfl
    have hp := hpair ψ
    have hI1 : Integrable (fun x => ψ x * (k : V → ℂ) x) :=
      memLp_one_iff_integrable.mp (MemLp.mul (Lp.memLp k) (ψ.memLp 2 volume))
    have hI2 : Integrable (fun x => ψ x * G x) :=
      memLp_one_iff_integrable.mp (MemLp.mul hG1 (ψ.memLp ⊤ volume))
    have e1 : ∫ x, g x • ((k : V → ℂ) x - G x)
        = ∫ x, (ψ x * (k : V → ℂ) x - ψ x * G x) := by
      apply integral_congr_ae
      filter_upwards with x
      rw [hψcoe x, Complex.real_smul, mul_sub]
    rw [e1, integral_sub hI1 hI2, hp, sub_self]
  have hae : (fun x => (k : V → ℂ) x - G x) =ᵐ[volume] 0 :=
    ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (((Lp.memLp k).locallyIntegrable (by norm_num)).sub hG.locallyIntegrable) hzero
  have hkeq : (k : V → ℂ) =ᵐ[volume] G := by
    filter_upwards [hae] with x hx
    exact sub_eq_zero.mp hx
  exact MemLp.ae_eq hkeq (Lp.memLp k)

end Commons.Analysis.Fourier