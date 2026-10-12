import Mathlib.Analysis.Convolution
import Mathlib.Tactic.Have
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseBoxFock.uvKernel_L1_bound_of_decay
import Submission.Work.BoseBoxFock.uvKernel_tail_of_decay
import Submission.Work.BoseFixB1.tendsto_integral_norm_sub_translate
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.uvSmear_L1_tendsto`

The UV-smearing kernel `uvKernel fu Λ = 𝓕⁻(ζ_Λ)` (`ζ_Λ(p) = fu.f (‖p‖/Λ)`, `fu : LowCut`) has
unit mass and a uniformly bounded `L¹` norm, and its mass concentrates at the origin as `Λ → ∞`.
Hence the smoothed function `uvSmear fu Λ f = uvKernel fu Λ ⋆ f` converges to `f` in `L¹` for
every `f ∈ L¹(ℝ³)`:

    `∫ x, ‖(uvKernel fu Λ ⋆ f) x − f x‖ → 0`  as `Λ → ∞`
    (`uvSmear_L1_tendsto`).

This is the mechanism by which the UV cut-off of the cubic row is absorbed: the discrepancy
`uvSmear fu Λ (W₁) − W₁` is small in `L¹` once `Λ` is large
(see the header of `PotCubicSmoothWeight.lean`).

## Structure

* `uvKernel_decay` — the scaled Schwartz decay `‖uvKernel fu Λ z‖ ≤ C Λ³ (1 + Λ‖z‖)^{-N}`
  (from the already-proved `lowCut_invFT_scale`);
* `integral_uvKernel` — **the unit-mass identity** `∫ uvKernel fu Λ = 1` (Fourier inversion);
* `tendsto_integral_norm_sub_translate_real` — continuity of translation in `L¹(ℝ³)` (the
  `ℝ`-valued instance of the proved `ℂ`-valued lemma
  `Work.BoseFixB1.tendsto_integral_norm_sub_translate`);
* `convolution_sub_eq_integral`, `convolution_L1_le` — the generic approximate-identity
  estimate `‖K ⋆ f − f‖₁ ≤ ∫ ‖K z‖ ‖τ_z f − f‖₁ dz` for a unit-mass kernel `K` (Fubini);
* `uvSmear_L1_tendsto` — the assembly.
-/

noncomputable section

open MeasureTheory Filter
open scoped Real Topology BigOperators Convolution

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## 1. The scaled decay of the smoothing kernel -/

/-- The normalisation `(2π)⁻³` of the `p`-convention inverse Fourier transform. -/
def kinNorm : ℝ := ((2 * π) ^ 3)⁻¹

lemma kinNorm_nonneg : 0 ≤ kinNorm := by
  rw [kinNorm]; positivity

/-- **The scaled Schwartz decay of the UV kernel.**  For every order `N` there is `C ≥ 0` with
`‖uvKernel fu Λ z‖ ≤ C Λ³ (1 + Λ‖z‖)^{-N}` for all `Λ > 0` and all `z`. -/
lemma uvKernel_decay (fu : Work.BoseBoxFix.LowCut) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (Λ : ℝ), 0 < Λ → ∀ z : E3,
      ‖uvKernel fu Λ z‖ ≤ C * Λ ^ 3 * (1 + Λ * ‖z‖) ^ (-(N : ℤ)) := by
  obtain ⟨C₀, hC₀nn, hC₀⟩ := lowCut_invFT_scale fu N
  refine ⟨kinNorm * C₀, mul_nonneg kinNorm_nonneg hC₀nn, fun Λ hΛ z => ?_⟩
  have hint_eq :
      (∫ p : E3, (((fun r : ℝ => fu.f (r / Λ)) ‖p‖ : ℝ) : ℂ) *
          Complex.exp (Complex.I * (inner ℝ p z : ℂ)))
        = ∫ p : E3, Complex.exp (Complex.I * (inner ℝ p z : ℂ)) *
            ((fu.f (‖p‖ / Λ) : ℝ) : ℂ) := by
    apply integral_congr_ae
    filter_upwards with p
    rw [mul_comm]
  have hcast : (Submission.BoseGases.kinKernel (fun r : ℝ => fu.f (r / Λ)) z : ℂ)
      = Submission.BoseGases.kinKernelC (fun r : ℝ => fu.f (r / Λ)) z :=
    (Work.SmallBoxBridge.Kernel.kinKernelC_eq_ofReal (fun r : ℝ => fu.f (r / Λ)) z).symm
  have hc : ‖((((2 * π) ^ 3)⁻¹ : ℝ) : ℂ)‖ = ((2 * π) ^ 3)⁻¹ := by
    rw [Complex.norm_def, Complex.normSq_ofReal, ← sq, Real.sqrt_sq_eq_abs]
    exact abs_of_nonneg (by positivity)
  calc ‖uvKernel fu Λ z‖
      = ‖Submission.BoseGases.kinKernel (fun r : ℝ => fu.f (r / Λ)) z‖ := rfl
    _ = ‖Submission.BoseGases.kinKernelC (fun r : ℝ => fu.f (r / Λ)) z‖ := by
        rw [← hcast, Complex.norm_def, Complex.normSq_ofReal, ← sq, Real.sqrt_sq_eq_abs]
        rw [Real.norm_eq_abs]
    _ = kinNorm * ‖∫ p : E3, Complex.exp (Complex.I * (inner ℝ p z : ℂ)) *
            ((fu.f (‖p‖ / Λ) : ℝ) : ℂ)‖ := by
        rw [Submission.BoseGases.kinKernelC, hint_eq, norm_mul, hc, kinNorm]
    _ ≤ kinNorm * (C₀ * Λ ^ 3 * (1 + Λ * ‖z‖) ^ (-(N : ℤ))) :=
        mul_le_mul_of_nonneg_left (hC₀ Λ hΛ z) kinNorm_nonneg
    _ = kinNorm * C₀ * Λ ^ 3 * (1 + Λ * ‖z‖) ^ (-(N : ℤ)) := by ring

/-! ## 2. The unit mass of the kernel (Fourier inversion) -/

/-- **The unit-mass identity** `∫ uvKernel fu Λ = 1` for `Λ > 0`: the kernel is the inverse
Fourier transform of the symbol `ζ_Λ`, whose value at `0` is `fu.f 0 = 1`. -/
lemma integral_uvKernel (fu : Work.BoseBoxFix.LowCut) {Λ : ℝ} (hΛ : 0 < Λ) :
    ∫ z : E3, uvKernel fu Λ z = 1 := by
  have hinv := (uvSymbol_contDiff fu hΛ).continuous.fourier_fourierInv_eq
    (integrable_uvSymbol fu hΛ) (integrable_fourier_uvSymbol fu hΛ)
  have hA : (∫ z : E3, ((uvKernel fu Λ z : ℝ) : ℂ))
      = FourierTransform.fourier (FourierTransform.fourierInv (uvSymbol fu Λ)) 0 := by
    rw [uvKernel_cast_eq_fourierInv fu Λ]
    rw [Real.fourier_eq']
    simp
  rw [hinv] at hA
  have h0 : uvSymbol fu Λ 0 = 1 := by
    simp [uvSymbol, fu.one 0 (by norm_num : (0 : ℝ) ≤ 1)]
  have h1 : (∫ z : E3, ((uvKernel fu Λ z : ℝ) : ℂ)) = 1 := by rw [hA, h0]
  have hcast : ((∫ z : E3, uvKernel fu Λ z : ℝ) : ℂ) = 1 :=
    (integral_ofReal (μ := (volume : Measure E3)) (𝕜 := ℂ) (f := uvKernel fu Λ)).symm.trans h1
  exact Complex.ofReal_inj.mp hcast

/-! ## 3. Continuity of translation in `L¹(ℝ³)`, real-valued -/

/-- **Continuity of translation in `L¹`.**  For `f ∈ L¹(ℝ³)`, the `L¹` modulus of continuity
`z ↦ ∫ x, ‖f (x − z) − f x‖` tends to `0` at `z = 0`.  This is the `ℝ`-valued instance of the
proved `ℂ`-valued lemma `Work.BoseFixB1.tendsto_integral_norm_sub_translate`. -/
lemma tendsto_integral_norm_sub_translate_real {f : E3 → ℝ} (hf : Integrable f) :
    Tendsto (fun z : E3 => ∫ x : E3, ‖f (x - z) - f x‖) (𝓝 0) (𝓝 0) := by
  have hg : Integrable (fun x : E3 => ((f x : ℝ) : ℂ)) :=
    Complex.ofRealCLM.integrable_comp hf
  have h := Work.BoseFixB1.tendsto_integral_norm_sub_translate hg
  refine h.congr' (Eventually.of_forall fun z => ?_)
  apply integral_congr_ae
  filter_upwards with x
  calc ‖(fun y : E3 => ((f y : ℝ) : ℂ)) (x - z) - (fun y : E3 => ((f y : ℝ) : ℂ)) x‖
      = ‖(((f (x - z) - f x : ℝ)) : ℂ)‖ :=
        congrArg Norm.norm (Complex.ofReal_sub _ _).symm
    _ = ‖f (x - z) - f x‖ := by
        rw [Complex.norm_def, Complex.normSq_ofReal, ← sq, Real.sqrt_sq_eq_abs,
          Real.norm_eq_abs]

/-- The `L¹` modulus of continuity is bounded by `2‖f‖₁`. -/
lemma omega_le_two {f : E3 → ℝ} (hf : Integrable f) (z : E3) :
    ∫ x : E3, ‖f (x - z) - f x‖ ≤ 2 * ∫ x : E3, ‖f x‖ := by
  have h1 : Integrable (fun x : E3 => f (x - z)) := hf.comp_sub_right z
  have h2 : Integrable (fun x : E3 => ‖f (x - z) - f x‖) := (h1.sub hf).norm
  calc ∫ x : E3, ‖f (x - z) - f x‖
      ≤ ∫ x : E3, (‖f (x - z)‖ + ‖f x‖) :=
        integral_mono h2 (h1.norm.add hf.norm) (fun x => norm_sub_le _ _)
    _ = (∫ x : E3, ‖f (x - z)‖) + ∫ x : E3, ‖f x‖ := integral_add h1.norm hf.norm
    _ = (∫ x : E3, ‖f x‖) + ∫ x : E3, ‖f x‖ := by
        rw [integral_sub_right_eq_self (fun y : E3 => ‖f y‖) z]
    _ = 2 * ∫ x : E3, ‖f x‖ := by ring

/-- The set-integral form of `∫ x in s, f x * c = (∫ x in s, f x) * c`. -/
lemma setIntegral_mul_const' {s : Set E3} (hs : MeasurableSet s) (g : E3 → ℝ) (c : ℝ) :
    ∫ t in s, g t * c = (∫ t in s, g t) * c := by
  rw [← integral_indicator hs, ← integral_indicator hs, ← integral_mul_const]
  apply integral_congr_ae
  filter_upwards with t
  by_cases ht : t ∈ s
  · simp [Set.indicator_of_mem ht]
  · simp [Set.indicator_of_notMem ht]

/-! ## 4. Generic approximate-identity lemmas -/

/-- **The differenced form of the smearing.**  If `∫ K = 1` and `K` is bounded, then
`(K ⋆ f) x − f x = ∫ t, K t (f (x − t) − f x) dt`. -/
lemma convolution_sub_eq_integral {f K : E3 → ℝ} (hf : Integrable f) (hK : Integrable K)
    (hK1 : ∫ z : E3, K z = 1) {B : ℝ} (hKbdd : ∀ z : E3, ‖K z‖ ≤ B) (x : E3) :
    (K ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure E3)] f) x - f x
      = ∫ t : E3, K t * (f (x - t) - f x) := by
  have hbdd_meas : AEStronglyMeasurable K (volume : Measure E3) := hK.aestronglyMeasurable
  have hbdd : ∀ᵐ t ∂(volume : Measure E3), ‖K t‖ ≤ B := Eventually.of_forall hKbdd
  have hFx : Integrable (fun t : E3 => K t * f (x - t)) :=
    Integrable.bdd_mul (hf.comp_sub_left x) hbdd_meas hbdd
  have hFc : Integrable (fun t : E3 => K t * f x) := hK.mul_const _
  have hKint : ∫ t : E3, K t * f x = f x := by
    rw [integral_mul_const, hK1, one_mul]
  have hsub : (∫ t : E3, K t * (f (x - t) - f x))
      = (∫ t : E3, K t * f (x - t)) - ∫ t : E3, K t * f x := by
    rw [← integral_sub hFx hFc]
    apply integral_congr_ae
    filter_upwards with t
    ring
  rw [convolution_lsmul]
  simp only [smul_eq_mul]
  rw [hsub, hKint]

/-- **The approximate-identity estimate.**  For a unit-mass, bounded `K ∈ L¹`,
`∫ x, ‖(K ⋆ f) x − f x‖ ≤ ∫ z, ‖K z‖ (∫ x, ‖f (x − z) − f x‖)`. -/
lemma convolution_L1_le {f K : E3 → ℝ} (hf : Integrable f) (hK : Integrable K)
    (hK1 : ∫ z : E3, K z = 1) {B : ℝ} (hKbdd : ∀ z : E3, ‖K z‖ ≤ B) :
    ∫ x : E3, ‖(K ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure E3)] f) x - f x‖
      ≤ ∫ z : E3, ‖K z‖ * (∫ x : E3, ‖f (x - z) - f x‖) := by
  set Φ : E3 → E3 → ℝ := fun x t => ‖K t‖ * ‖f (x - t) - f x‖ with hΦ
  have hA : AEStronglyMeasurable (fun p : E3 × E3 => f (p.1 - p.2))
      ((volume : Measure E3).prod volume) := by
    have h := MeasureTheory.AEStronglyMeasurable.convolution_integrand
      (L := ContinuousLinearMap.lsmul ℝ ℝ) (f := fun _ : E3 => (1 : ℝ)) (g := f)
      (μ := (volume : Measure E3)) (ν := (volume : Measure E3))
      aestronglyMeasurable_const hf.aestronglyMeasurable
    simpa [ContinuousLinearMap.lsmul_apply] using h
  have hB : AEStronglyMeasurable (fun p : E3 × E3 => f p.1)
      ((volume : Measure E3).prod volume) := hf.aestronglyMeasurable.comp_fst
  have hC : AEStronglyMeasurable (fun p : E3 × E3 => K p.2)
      ((volume : Measure E3).prod volume) := hK.aestronglyMeasurable.comp_snd
  have hΦjoint : AEStronglyMeasurable (fun p : E3 × E3 => Φ p.1 p.2)
      ((volume : Measure E3).prod volume) := by
    rw [hΦ]
    exact hC.norm.mul (hA.sub hB).norm
  have hΦ₁ : Integrable (fun p : E3 × E3 => ‖K p.2‖ * ‖f (p.1 - p.2)‖)
      ((volume : Measure E3).prod volume) := by
    have h := MeasureTheory.Integrable.convolution_integrand
      (L := ContinuousLinearMap.lsmul ℝ ℝ) (f := fun z : E3 => ‖K z‖) (g := fun z : E3 => ‖f z‖)
      (μ := (volume : Measure E3)) (ν := (volume : Measure E3)) hK.norm hf.norm
    simpa [ContinuousLinearMap.lsmul_apply] using h
  have hΦ₂ : Integrable (fun p : E3 × E3 => ‖f p.1‖ * ‖K p.2‖)
      ((volume : Measure E3).prod volume) := Integrable.mul_prod hf.norm hK.norm
  have hFub : Integrable (fun p : E3 × E3 => Φ p.1 p.2)
      ((volume : Measure E3).prod volume) := by
    refine Integrable.mono' (hΦ₁.add hΦ₂) hΦjoint (Eventually.of_forall fun p => ?_)
    rw [hΦ]
    have h1 : (0 : ℝ) ≤ ‖K p.2‖ * ‖f (p.1 - p.2) - f p.1‖ := by positivity
    rw [Real.norm_of_nonneg h1]
    calc ‖K p.2‖ * ‖f (p.1 - p.2) - f p.1‖
        ≤ ‖K p.2‖ * (‖f (p.1 - p.2)‖ + ‖f p.1‖) :=
          mul_le_mul_of_nonneg_left (norm_sub_le _ _) (norm_nonneg _)
      _ = ‖K p.2‖ * ‖f (p.1 - p.2)‖ + ‖f p.1‖ * ‖K p.2‖ := by ring
  have hintx : Integrable (fun x : E3 => ∫ t : E3, Φ x t) (volume : Measure E3) :=
    hFub.integral_prod_left
  have hswap : (∫ x : E3, ∫ t : E3, Φ x t) = ∫ t : E3, ∫ x : E3, Φ x t :=
    integral_integral_swap hFub
  have hpt : ∀ x : E3, ‖(K ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure E3)] f) x - f x‖
      ≤ ∫ t : E3, Φ x t := by
    intro x
    rw [convolution_sub_eq_integral hf hK hK1 hKbdd x]
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    apply integral_congr_ae
    filter_upwards with t
    rw [norm_mul, hΦ]
  have hLHSmeas : AEStronglyMeasurable
      (fun x : E3 => (K ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure E3)] f) x - f x)
      (volume : Measure E3) := by
    have hJ2 : AEStronglyMeasurable (fun p : E3 × E3 => K p.2 * f (p.1 - p.2))
        ((volume : Measure E3).prod volume) := hC.mul hA
    have hcm : AEStronglyMeasurable
        (fun x : E3 => (K ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure E3)] f) x)
        (volume : Measure E3) := by
      have h := hJ2.integral_prod_right'
      simpa [convolution_lsmul, smul_eq_mul] using h
    exact hcm.sub hf.aestronglyMeasurable
  have hLHSint : Integrable
      (fun x : E3 => ‖(K ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure E3)] f) x - f x‖)
      (volume : Measure E3) :=
    (Integrable.mono' hintx hLHSmeas (Eventually.of_forall hpt)).norm
  calc ∫ x : E3, ‖(K ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure E3)] f) x - f x‖
      ≤ ∫ x : E3, ∫ t : E3, Φ x t := integral_mono hLHSint hintx (fun x => hpt x)
    _ = ∫ t : E3, ∫ x : E3, Φ x t := hswap
    _ = ∫ t : E3, ‖K t‖ * (∫ x : E3, ‖f (x - t) - f x‖) := by
        apply integral_congr_ae
        filter_upwards with t
        rw [hΦ]
        exact integral_const_mul _ _

/-- **Integrability of the `ω`-weighted kernel mass**, for `K ∈ L¹` and `f ∈ L¹`. -/
lemma integrable_norm_mul_omega {f K : E3 → ℝ} (hf : Integrable f) (hK : Integrable K) :
    Integrable (fun t : E3 => ‖K t‖ * (∫ x : E3, ‖f (x - t) - f x‖)) (volume : Measure E3) := by
  have hmaj : Integrable (fun t : E3 => ‖K t‖ * (2 * ∫ x : E3, ‖f x‖)) :=
    hK.norm.mul_const _
  have hωmeas : AEStronglyMeasurable (fun t : E3 => ∫ x : E3, ‖f (x - t) - f x‖)
      (volume : Measure E3) := by
    have hA : AEStronglyMeasurable (fun p : E3 × E3 => f (p.1 - p.2))
        ((volume : Measure E3).prod volume) := by
      have h := MeasureTheory.AEStronglyMeasurable.convolution_integrand
        (L := ContinuousLinearMap.lsmul ℝ ℝ) (f := fun _ : E3 => (1 : ℝ)) (g := f)
        (μ := (volume : Measure E3)) (ν := (volume : Measure E3))
        aestronglyMeasurable_const hf.aestronglyMeasurable
      simpa [ContinuousLinearMap.lsmul_apply] using h
    have hB : AEStronglyMeasurable (fun p : E3 × E3 => f p.1)
        ((volume : Measure E3).prod volume) := hf.aestronglyMeasurable.comp_fst
    have hjoint : AEStronglyMeasurable (fun p : E3 × E3 => ‖f (p.1 - p.2) - f p.1‖)
        ((volume : Measure E3).prod volume) := (hA.sub hB).norm
    have h := (hjoint.prod_swap).integral_prod_right'
    simpa using h
  refine Integrable.mono' hmaj (hK.norm.aestronglyMeasurable.mul hωmeas)
    (Eventually.of_forall fun t => ?_)
  rw [Real.norm_of_nonneg (by positivity)]
  exact mul_le_mul_of_nonneg_left (omega_le_two hf t) (norm_nonneg _)

/-! ## 5. The main theorem -/

theorem uvSmear_L1_tendsto (fu : Work.BoseBoxFix.LowCut)
    {f : EuclideanSpace ℝ (Fin 3) → ℝ} (hf : MeasureTheory.Integrable f) :
    Filter.Tendsto
      (fun Λ : ℝ => ∫ x : EuclideanSpace ℝ (Fin 3),
        ‖(∫ y : EuclideanSpace ℝ (Fin 3),
            Submission.BoseGases.kinKernel (fun r : ℝ => fu.f (r / Λ)) (x - y) * f y)
          - f x‖)
      Filter.atTop (nhds 0) := by
  obtain ⟨C, hCnn, hdec⟩ := uvKernel_decay fu 5
  obtain ⟨M, hMnn, hM⟩ := uvKernel_L1_bound_of_decay fu hCnn hdec
  -- mass concentration at the origin (the delegated lemma `uvKernel_tail_of_decay`)
  have htail : ∀ δ : ℝ, 0 < δ → Tendsto
      (fun Λ : ℝ => ∫ z in {z : E3 | δ ≤ ‖z‖}, ‖uvKernel fu Λ z‖) atTop (𝓝 0) :=
    fun δ hδ => uvKernel_tail_of_decay fu hCnn hdec hδ
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- the key bound at each `Λ > 0`
  have hkey : ∀ (Λ : ℝ), 0 < Λ →
      ∫ x : E3, ‖(∫ y : E3, Submission.BoseGases.kinKernel (fun r : ℝ => fu.f (r / Λ))
            (x - y) * f y) - f x‖
        ≤ ∫ t : E3, ‖uvKernel fu Λ t‖ * (∫ x : E3, ‖f (x - t) - f x‖) := by
    intro Λ hΛ
    have hsub : ∀ x : E3, (∫ y : E3, Submission.BoseGases.kinKernel (fun r : ℝ => fu.f (r / Λ))
          (x - y) * f y)
        = (uvKernel fu Λ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure E3)] f) x := by
      intro x
      rw [convolution_lsmul]
      simp only [smul_eq_mul]
      have h := integral_sub_left_eq_self (fun t : E3 => uvKernel fu Λ t * f (x - t)) volume x
      simpa only [uvKernel, sub_sub_cancel] using h
    have hbdd : ∀ z : E3, ‖uvKernel fu Λ z‖ ≤ C * Λ ^ 3 := by
      intro z
      have h1 : (1 + Λ * ‖z‖) ^ (-(5 : ℤ)) ≤ 1 := by
        rw [zpow_neg]
        exact inv_le_one_of_one_le₀ (one_le_pow₀ (by
          have : (0 : ℝ) ≤ Λ * ‖z‖ := mul_nonneg hΛ.le (norm_nonneg z)
          linarith))
      calc ‖uvKernel fu Λ z‖ ≤ C * Λ ^ 3 * (1 + Λ * ‖z‖) ^ (-(5 : ℤ)) := hdec Λ hΛ z
        _ ≤ C * Λ ^ 3 * 1 := mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = C * Λ ^ 3 := by ring
    calc ∫ x : E3, ‖(∫ y : E3, Submission.BoseGases.kinKernel (fun r : ℝ => fu.f (r / Λ))
            (x - y) * f y) - f x‖
        = ∫ x : E3, ‖(uvKernel fu Λ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure E3)] f) x
            - f x‖ := by
          apply integral_congr_ae
          filter_upwards with x
          rw [hsub x]
      _ ≤ ∫ t : E3, ‖uvKernel fu Λ t‖ * (∫ x : E3, ‖f (x - t) - f x‖) :=
          convolution_L1_le hf (integrable_uvKernel fu hΛ) (integral_uvKernel fu hΛ) hbdd
  -- translation continuity provides the small ball
  have htrans := tendsto_integral_norm_sub_translate_real hf
  have hsmall : ∀ᶠ z in 𝓝 (0 : E3), (∫ x : E3, ‖f (x - z) - f x‖) < ε / (8 * (M + 1)) := by
    have h := (Metric.tendsto_nhds.1 htrans) (ε / (8 * (M + 1))) (by positivity)
    filter_upwards [h] with z hz
    rw [Real.dist_eq, sub_zero,
      abs_of_nonneg (integral_nonneg fun x => norm_nonneg _)] at hz
    exact hz
  obtain ⟨δ, hδpos, hδ⟩ := Metric.mem_nhds_iff.1 hsmall
  have hδ' : ∀ z : E3, ‖z‖ < δ → (∫ x : E3, ‖f (x - z) - f x‖) < ε / (8 * (M + 1)) :=
    fun z hz => hδ (by rwa [Metric.mem_ball, dist_zero_right])
  have hs : MeasurableSet {t : E3 | ‖t‖ < δ} := measurableSet_lt measurable_norm measurable_const
  -- the mass concentration threshold
  have htailε : ∀ᶠ (Λ : ℝ) in atTop,
      2 * (∫ x : E3, ‖f x‖) * (∫ z in {z : E3 | δ ≤ ‖z‖}, ‖uvKernel fu Λ z‖) < ε / 8 := by
    have h1 : Tendsto
        (fun Λ : ℝ => 2 * (∫ x : E3, ‖f x‖) *
          (∫ z in {z : E3 | δ ≤ ‖z‖}, ‖uvKernel fu Λ z‖)) atTop
        (𝓝 (2 * (∫ x : E3, ‖f x‖) * 0)) :=
      tendsto_const_nhds.mul (htail δ hδpos)
    rw [mul_zero] at h1
    exact (tendsto_order.1 h1).2 (ε / 8) (by linarith)
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 htailε
  refine ⟨max N₀ 1, fun Λ hΛ => ?_⟩
  have hΛ1 : 0 < Λ := lt_of_lt_of_le zero_lt_one (le_trans (le_max_right _ _) hΛ)
  have hN₀' := hN₀ Λ (le_trans (le_max_left _ _) hΛ)
  have hωint : Integrable (fun t : E3 => ‖uvKernel fu Λ t‖ * (∫ x : E3, ‖f (x - t) - f x‖))
      (volume : Measure E3) := integrable_norm_mul_omega hf (integrable_uvKernel fu hΛ1)
  have hKnorm : Integrable (fun t : E3 => ‖uvKernel fu Λ t‖) (volume : Measure E3) :=
    (integrable_uvKernel fu hΛ1).norm
  have hsplit : (∫ t : E3, ‖uvKernel fu Λ t‖ * (∫ x : E3, ‖f (x - t) - f x‖))
      = (∫ t in {t : E3 | ‖t‖ < δ}, ‖uvKernel fu Λ t‖ * (∫ x : E3, ‖f (x - t) - f x‖))
        + ∫ t in ({t : E3 | ‖t‖ < δ})ᶜ,
            ‖uvKernel fu Λ t‖ * (∫ x : E3, ‖f (x - t) - f x‖) :=
    (integral_add_compl hs hωint).symm
  have hset2 : ({t : E3 | ‖t‖ < δ})ᶜ = {t : E3 | δ ≤ ‖t‖} := by
    ext t; simp [not_lt]
  have hfirst : (∫ t in {t : E3 | ‖t‖ < δ},
        ‖uvKernel fu Λ t‖ * (∫ x : E3, ‖f (x - t) - f x‖)) ≤ ε / 8 := by
    have hmono : (∫ t in {t : E3 | ‖t‖ < δ},
          ‖uvKernel fu Λ t‖ * (∫ x : E3, ‖f (x - t) - f x‖))
        ≤ ∫ t in {t : E3 | ‖t‖ < δ}, ‖uvKernel fu Λ t‖ * (ε / (8 * (M + 1))) := by
      refine setIntegral_mono_on hωint.integrableOn (hKnorm.mul_const _).integrableOn hs
        (fun t ht => ?_)
      have hωt : (∫ x : E3, ‖f (x - t) - f x‖) ≤ ε / (8 * (M + 1)) := le_of_lt (hδ' t ht)
      exact mul_le_mul_of_nonneg_left hωt (norm_nonneg _)
    have hglob : (∫ t in {t : E3 | ‖t‖ < δ}, ‖uvKernel fu Λ t‖ * (ε / (8 * (M + 1))))
        ≤ ∫ t : E3, ‖uvKernel fu Λ t‖ * (ε / (8 * (M + 1))) :=
      setIntegral_le_integral (hKnorm.mul_const _) (Eventually.of_forall fun t => by positivity)
    have hval : (∫ t : E3, ‖uvKernel fu Λ t‖ * (ε / (8 * (M + 1))))
        = (∫ t : E3, ‖uvKernel fu Λ t‖) * (ε / (8 * (M + 1))) := integral_mul_const _ _
    have hMb : (∫ t : E3, ‖uvKernel fu Λ t‖) * (ε / (8 * (M + 1))) ≤ ε / 8 := by
      have h2 : M * (ε / (8 * (M + 1))) ≤ ε / 8 := by
        have h3 : M * (ε / (8 * (M + 1))) ≤ (M + 1) * (ε / (8 * (M + 1))) :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
        have h4 : (M + 1) * (ε / (8 * (M + 1))) = ε / 8 := by
          rw [mul_comm, div_mul_eq_mul_div]
          rw [mul_div_mul_right _ _ (by linarith : (M + 1) ≠ 0)]
        linarith
      exact (mul_le_mul_of_nonneg_right (hM Λ hΛ1) (by positivity)).trans h2
    calc (∫ t in {t : E3 | ‖t‖ < δ}, ‖uvKernel fu Λ t‖ * (∫ x : E3, ‖f (x - t) - f x‖))
        ≤ ∫ t in {t : E3 | ‖t‖ < δ}, ‖uvKernel fu Λ t‖ * (ε / (8 * (M + 1))) := hmono
      _ ≤ ∫ t : E3, ‖uvKernel fu Λ t‖ * (ε / (8 * (M + 1))) := hglob
      _ = (∫ t : E3, ‖uvKernel fu Λ t‖) * (ε / (8 * (M + 1))) := hval
      _ ≤ ε / 8 := hMb
  have hsecond : (∫ t in ({t : E3 | ‖t‖ < δ})ᶜ,
        ‖uvKernel fu Λ t‖ * (∫ x : E3, ‖f (x - t) - f x‖)) ≤ ε / 8 := by
    rw [hset2]
    have hmono : (∫ t in {t : E3 | δ ≤ ‖t‖},
          ‖uvKernel fu Λ t‖ * (∫ x : E3, ‖f (x - t) - f x‖))
        ≤ ∫ t in {t : E3 | δ ≤ ‖t‖}, ‖uvKernel fu Λ t‖ * (2 * ∫ x : E3, ‖f x‖) := by
      refine setIntegral_mono_on hωint.integrableOn (hKnorm.mul_const _).integrableOn
        (measurableSet_le measurable_const measurable_norm) (fun t ht => ?_)
      exact mul_le_mul_of_nonneg_left (omega_le_two hf t) (norm_nonneg _)
    have hval : (∫ t in {t : E3 | δ ≤ ‖t‖}, ‖uvKernel fu Λ t‖ * (2 * ∫ x : E3, ‖f x‖))
        = (∫ t in {t : E3 | δ ≤ ‖t‖}, ‖uvKernel fu Λ t‖) * (2 * ∫ x : E3, ‖f x‖) :=
      setIntegral_mul_const' (measurableSet_le measurable_const measurable_norm) _ _
    rw [hval] at hmono
    calc (∫ t in {t : E3 | δ ≤ ‖t‖},
          ‖uvKernel fu Λ t‖ * (∫ x : E3, ‖f (x - t) - f x‖))
        ≤ (∫ t in {t : E3 | δ ≤ ‖t‖}, ‖uvKernel fu Λ t‖) * (2 * ∫ x : E3, ‖f x‖) := hmono
      _ = 2 * (∫ x : E3, ‖f x‖) * (∫ t in {t : E3 | δ ≤ ‖t‖}, ‖uvKernel fu Λ t‖) := by ring
      _ ≤ ε / 8 := le_of_lt hN₀'
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (integral_nonneg fun x => norm_nonneg _)]
  have hmain := hkey Λ hΛ1
  rw [hsplit] at hmain
  have hsum : (∫ t in {t : E3 | ‖t‖ < δ}, ‖uvKernel fu Λ t‖ * (∫ x : E3, ‖f (x - t) - f x‖))
      + (∫ t in ({t : E3 | ‖t‖ < δ})ᶜ,
          ‖uvKernel fu Λ t‖ * (∫ x : E3, ‖f (x - t) - f x‖)) ≤ ε / 8 + ε / 8 :=
    add_le_add hfirst hsecond
  linarith [hmain, hsum, hε]

end Work.BoseBoxFock
