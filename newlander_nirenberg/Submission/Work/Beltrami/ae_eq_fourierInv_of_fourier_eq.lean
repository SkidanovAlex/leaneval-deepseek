import Mathlib

namespace Work.Beltrami

open MeasureTheory
open scoped ContDiff FourierTransform SchwartzMap RealInnerProductSpace

set_option maxHeartbeats 800000

/-- Fourier inversion, `L¹`/`L²` compatibility form: if `u ∈ L²(ℂ)`, `V` is the `L²` Fourier
transform of (the `L²` class of) `u`, and `V` is integrable, then `u` agrees almost everywhere with
the absolutely convergent inverse Fourier integral `x ↦ ∫ ξ, e^{2πi⟪ξ,x⟫} V ξ`.

Suggested route: write `w := fun x => ∫ ξ, 𝐞 (inner ℝ ξ x) • V ξ` (which is `𝓕⁻ (fun ξ => V ξ)`,
hence continuous and bounded by `∫ ‖V‖`). Both `u` and `w` are locally integrable
(`MemLp.locallyIntegrable`; a continuous bounded function is locally integrable), so by
`ae_eq_of_integral_contDiff_smul_eq` (`Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff`) it
suffices to prove `∫ x, g x • u x = ∫ x, g x • w x` for every `g : ℂ → ℝ` that is `ContDiff ℝ ∞`
with compact support. For such `g` (complex-valued version `φ x = (g x : ℂ)`), show both sides equal
`∫ ξ, V ξ * 𝓕⁻φ ξ`:
* `∫ x, φ x * w x = ∫ ξ, V ξ * 𝓕⁻φ ξ` by `Real.fourierInv_eq` and `integral_integral_swap`
  (Fubini is justified by `V ∈ L¹` and `φ` compactly supported);
* `∫ x, φ x * u x = ∫ ξ, V ξ * 𝓕⁻φ ξ` from `hV`, i.e. the distributional identity
  `𝓕 ((hL2.toLp u : 𝓢'(ℂ,ℂ))) = (V : 𝓢'(ℂ,ℂ))`
  (`MeasureTheory.Lp.fourier_toTemperedDistribution_eq`), tested against `𝓕⁻φ` and using
  `TemperedDistribution.fourier_apply`, `Lp.toTemperedDistribution_apply`,
  `fourier_fourierInv_eq` (valid since `𝓕⁻φ` is Schwartz when `φ` has compact support, via
  `HasCompactSupport.toSchwartzMap`), and `coeFn_toLp` to replace `uL` by `u`. -/
theorem ae_eq_fourierInv_of_fourier_eq {u : ℂ → ℂ} (hL2 : MemLp u 2 volume)
    {V : Lp ℂ 2 volume} (hV : 𝓕 (hL2.toLp u) = V) (hint : Integrable (fun ξ : ℂ => V ξ)) :
    u =ᵐ[volume] fun x : ℂ => ∫ ξ : ℂ, 𝐞 (inner ℝ ξ x) • V ξ := by
  -- the bilinear form `L v w = -⟪v, w⟫` makes the (general) Fourier integral the inverse transform
  have hLcont : Continuous fun p : ℂ × ℂ => (-innerₗ ℂ) p.1 p.2 := by
    simp only [LinearMap.neg_apply]; exact continuous_inner.neg
  -- the candidate inverse transform is continuous, hence locally integrable
  have hWcont : Continuous (fun x : ℂ => ∫ ξ : ℂ, 𝐞 (inner ℝ ξ x) • V ξ) := by
    have hWa : (fun x : ℂ => ∫ ξ : ℂ, 𝐞 (inner ℝ ξ x) • V ξ)
        = VectorFourier.fourierIntegral 𝐞 volume (-innerₗ ℂ) (fun ξ : ℂ => V ξ) := by
      funext x
      simp [VectorFourier.fourierIntegral, LinearMap.neg_apply, neg_neg, real_inner_comm]
    rw [hWa]
    exact VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar hLcont hint
  have huloc : LocallyIntegrable u volume := hL2.locallyIntegrable (by norm_num)
  have hwloc : LocallyIntegrable (fun x : ℂ => ∫ ξ : ℂ, 𝐞 (inner ℝ ξ x) • V ξ) volume :=
    hWcont.locallyIntegrable
  -- it suffices to test against smooth compactly supported functions
  refine ae_eq_of_integral_contDiff_smul_eq huloc hwloc ?_
  intro g hgdiff hgsupp
  have hcomp : HasCompactSupport (fun x : ℂ => (g x : ℂ)) :=
    hgsupp.comp_left (g := Complex.ofReal) (by simp)
  have hcdiff : ContDiff ℝ ∞ (fun x : ℂ => (g x : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hgdiff
  let φ : 𝓢(ℂ, ℂ) := hcomp.toSchwartzMap hcdiff
  have hφeq : ∀ x : ℂ, φ x = (g x : ℂ) :=
    fun x => HasCompactSupport.toSchwartzMap_toFun hcomp hcdiff x
  -- self-adjointness of the Fourier transform identifies the two sides
  have hparseval : ∫ x : ℂ, (φ x) • (∫ ξ : ℂ, 𝐞 (inner ℝ ξ x) • V ξ)
      = ∫ ξ : ℂ, (𝓕⁻ φ) ξ • V ξ := by
    have hφint : Integrable (φ : ℂ → ℂ) := φ.integrable
    have h := VectorFourier.integral_fourierIntegral_smul_eq_flip
        (e := Real.fourierChar) (μ := volume) (ν := volume) (L := -innerₗ ℂ)
        Real.continuous_fourierChar hLcont hφint hint
    have hfun : VectorFourier.fourierIntegral 𝐞 volume (-innerₗ ℂ) (⇑φ)
        = fun ξ : ℂ => (𝓕⁻ φ) ξ := by
      funext ξ
      simp [SchwartzMap.fourierInv_coe, Real.fourierInv_eq, VectorFourier.fourierIntegral]
    have h' : ∫ ξ : ℂ, (𝓕⁻ φ) ξ • V ξ
        = ∫ x : ℂ, φ x • VectorFourier.fourierIntegral 𝐞 volume (-innerₗ ℂ).flip
            (fun ξ : ℂ => V ξ) x := by
      simpa [hfun] using h
    rw [h']
    apply integral_congr_ae
    filter_upwards with x
    simp [VectorFourier.fourierIntegral, LinearMap.flip_apply, LinearMap.neg_apply, neg_neg,
      real_inner_comm]
  -- the distributional identity from `hV`
  have hdist : ∫ x : ℂ, (φ x) • u x = ∫ ξ : ℂ, (𝓕⁻ φ) ξ • V ξ := by
    have hcoe : (hL2.toLp u : ℂ → ℂ) =ᵐ[volume] u := MemLp.coeFn_toLp hL2
    have h1 : ∫ x : ℂ, (φ x) • u x = ∫ x : ℂ, (φ x) • (hL2.toLp u : ℂ → ℂ) x := by
      apply integral_congr_ae
      filter_upwards [hcoe] with x hx
      rw [hx]
    rw [h1]
    have h2 : ∫ x : ℂ, (φ x) • (hL2.toLp u : ℂ → ℂ) x
        = Lp.toTemperedDistribution (hL2.toLp u) φ := by
      rw [Lp.toTemperedDistribution_apply]
    rw [h2]
    have h3 : Lp.toTemperedDistribution (hL2.toLp u) φ
        = (𝓕 (Lp.toTemperedDistribution (hL2.toLp u))) (𝓕⁻ φ) := by
      rw [TemperedDistribution.fourier_apply]
      simp
    rw [h3]
    have h4 : 𝓕 (Lp.toTemperedDistribution (hL2.toLp u)) = Lp.toTemperedDistribution V := by
      rw [Lp.fourier_toTemperedDistribution_eq, hV]
    rw [h4]
    rw [Lp.toTemperedDistribution_apply]
  -- rewrite the real scalar multiplications as complex ones and assemble
  have hgu : ∫ x : ℂ, g x • u x = ∫ x : ℂ, (φ x) • u x := by
    apply integral_congr_ae
    filter_upwards with x
    rw [hφeq, Complex.real_smul, smul_eq_mul]
  have hgw : ∫ x : ℂ, g x • (∫ ξ : ℂ, 𝐞 (inner ℝ ξ x) • V ξ)
      = ∫ x : ℂ, (φ x) • (∫ ξ : ℂ, 𝐞 (inner ℝ ξ x) • V ξ) := by
    apply integral_congr_ae
    filter_upwards with x
    rw [hφeq, Complex.real_smul, smul_eq_mul]
  rw [hgu, hgw, hdist, hparseval]

end Work.Beltrami
