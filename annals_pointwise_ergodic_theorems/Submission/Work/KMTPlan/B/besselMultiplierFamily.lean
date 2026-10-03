import Mathlib
import Submission.Work.Analysis.IWMultiplier.Gap

/-!
# The Bessel inequality for a family of Fourier multipliers

For a finite family `(m i)_{i ∈ ι}` of bounded measurable functions on the frequency circle
whose pointwise `ℓ²(ι)`-norms are bounded by `A`,

`∑_i ‖m i ξ‖² ≤ A²` for all `ξ`,

the associated Fourier multipliers `T_{m i}` on `ℓ²(ℤ)` satisfy the Bessel inequality

`∑_i ‖T_{m i} G‖² ≤ A² ‖G‖²`   for all `G ∈ ℓ²(ℤ)`.

This is the standard consequence of Plancherel's theorem: transporting along the isometry
`𝓕_ℤ : ℓ²(ℤ) ≃ L²(ℝ/ℤ)`, each multiplier becomes multiplication by the symbol, and the
two-sided estimate is the pointwise inequality integrated against `‖𝓕_ℤ G‖²`.

The auxiliary lemmas below (`bessel_normSq_eq_integral`, `bessel_integrable_normSq`,
`bessel_smul_family`) are the general `L²` facts behind this computation; they are stated for
an arbitrary measure space.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTPlan.B

open MeasureTheory
open scoped ENNReal NNReal BigOperators

/-- **The `L²` norm of an `Lp` element, squared, is the integral of the squared norm.**
For `f : L²(μ)` (with values in `ℂ`), `‖f‖² = ∫ ‖f x‖² ∂μ`. -/
lemma bessel_normSq_eq_integral {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (f : Lp ℂ 2 μ) : ‖f‖^2 = ∫ x, ‖f x‖^2 ∂μ := by
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ) f, MeasureTheory.L2.inner_def,
    ← integral_re (MeasureTheory.L2.integrable_inner f f)]
  exact integral_congr_ae
    (Filter.Eventually.of_forall fun x => inner_self_eq_norm_sq (𝕜 := ℂ) (f x))

/-- **The squared norm of an `L²` function is integrable.** -/
lemma bessel_integrable_normSq {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (f : Lp ℂ 2 μ) : Integrable (fun x => ‖f x‖^2) μ :=
  (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable f)).mp (Lp.memLp f)

/-- **Bessel's inequality for a family of multiplication operators on `L²`.**
If the multiplication symbols `M i ∈ L^∞(μ)` satisfy `∑_i ‖M i ξ‖² ≤ A²` for a.e. `ξ`, then
`∑_i ‖M i • F‖² ≤ A² ‖F‖²` for every `F ∈ L²(μ)`. -/
lemma bessel_smul_family {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {ι : Type*} [Fintype ι] (M : ι → Lp ℂ ⊤ μ) {A : ℝ}
    (hA : ∀ᵐ ξ ∂μ, ∑ i, ‖M i ξ‖^2 ≤ A^2) (F : Lp ℂ 2 μ) :
    ∑ i, ‖M i • F‖^2 ≤ A^2 * ‖F‖^2 := by
  -- the pointwise description of the product
  have hae : ∀ i, (fun ξ => ‖(M i • F) ξ‖^2) =ᵐ[μ]
      (fun ξ => ‖M i ξ‖^2 * ‖F ξ‖^2) := by
    intro i
    filter_upwards [Lp.coeFn_lpSMul (p := ⊤) (q := 2) (r := 2) (M i) F] with ξ hξ
    rw [hξ, Pi.smul_apply', norm_smul, mul_pow]
  have hint : ∀ i, Integrable (fun ξ => ‖M i ξ‖^2 * ‖F ξ‖^2) μ := fun i =>
    (bessel_integrable_normSq μ (M i • F)).congr (hae i)
  have hAsum : ∀ᵐ ξ ∂μ, (∑ i, ‖M i ξ‖^2) * ‖F ξ‖^2 ≤ A^2 * ‖F ξ‖^2 := by
    filter_upwards [hA] with ξ hξ
    exact mul_le_mul_of_nonneg_right hξ (by positivity)
  calc ∑ i, ‖M i • F‖^2
      = ∑ i, ∫ ξ, ‖M i ξ‖^2 * ‖F ξ‖^2 ∂μ := Finset.sum_congr rfl fun i _ => by
          rw [bessel_normSq_eq_integral μ (M i • F)]
          exact integral_congr_ae (hae i)
    _ = ∫ ξ, ∑ i, ‖M i ξ‖^2 * ‖F ξ‖^2 ∂μ :=
          (integral_finsetSum Finset.univ fun i _ => hint i).symm
    _ = ∫ ξ, (∑ i, ‖M i ξ‖^2) * ‖F ξ‖^2 ∂μ :=
          integral_congr_ae (Filter.Eventually.of_forall fun ξ => (Finset.sum_mul ..).symm)
    _ ≤ ∫ ξ, A^2 * ‖F ξ‖^2 ∂μ :=
          integral_mono_ae
            ((integrable_finsetSum Finset.univ fun i _ => hint i).congr
              (Filter.Eventually.of_forall fun ξ => (Finset.sum_mul ..).symm))
            ((bessel_integrable_normSq μ F).const_mul _) hAsum
    _ = A^2 * ∫ ξ, ‖F ξ‖^2 ∂μ := integral_const_mul _ _
    _ = A^2 * ‖F‖^2 := by rw [bessel_normSq_eq_integral μ F]

/-- **The Bessel inequality for a finite family of Fourier multipliers on `ℓ²(ℤ)`.**
If `m : ι → ℝ/ℤ → ℂ` is a finite family of bounded measurable symbols with
`∑_i ‖m i ξ‖² ≤ A²` for every frequency `ξ`, then the Fourier multipliers `T_{m i}` satisfy
`∑_i ‖T_{m i} G‖² ≤ A² ‖G‖²` for every `G ∈ ℓ²(ℤ)`. -/
theorem besselMultiplierFamily {ι : Type*} [Fintype ι]
    (m : ι → Work.Analysis.IonescuWainger.Circle → ℂ)
    (hm : ∀ i, MeasureTheory.MemLp (m i) ⊤ Work.Analysis.IonescuWainger.circleMeasure)
    {A : ℝ} (hA : ∀ ξ, ∑ i, ‖m i ξ‖ ^ 2 ≤ A ^ 2)
    (G : Work.Analysis.IonescuWainger.L2Z) :
    ∑ i, ‖(Work.Analysis.IonescuWainger.multiplierOf (m i) (hm i)) G‖ ^ 2 ≤ A ^ 2 * ‖G‖ ^ 2 := by
  -- the a.e. identification of the `L^∞` classes `(hm i).toLp (m i)` with the functions `m i`
  have haeM : ∀ i, ∀ᵐ ξ ∂Work.Analysis.IonescuWainger.circleMeasure,
      ‖(hm i).toLp (m i) ξ‖ = ‖m i ξ‖ := fun i =>
    (MemLp.coeFn_toLp (hm i)).mono fun ξ hξ => by rw [hξ]
  -- the hypothesis transfers to the `L^∞` classes
  have hA' : ∀ᵐ ξ ∂Work.Analysis.IonescuWainger.circleMeasure,
      ∑ i, ‖(hm i).toLp (m i) ξ‖^2 ≤ A^2 := by
    filter_upwards [Filter.eventually_all.2 haeM] with ξ hξ
    rw [Finset.sum_congr rfl fun i _ => by rw [hξ i]]
    exact hA ξ
  have key := bessel_smul_family Work.Analysis.IonescuWainger.circleMeasure
    (fun i => (hm i).toLp (m i)) hA' (Work.Analysis.IonescuWainger.fourierZ G)
  -- each multiplier is the conjugate of the multiplication operator by `𝓕_ℤ`
  have hnorm : ∀ i, ‖(Work.Analysis.IonescuWainger.multiplierOf (m i) (hm i)) G‖
      = ‖(hm i).toLp (m i) • Work.Analysis.IonescuWainger.fourierZ G‖ := fun i =>
    (Work.Analysis.IonescuWainger.fourierZ.norm_map _).symm.trans
      (congrArg norm (Work.Analysis.IonescuWainger.fourierZ_multiplierOf (m i) (hm i) G))
  calc ∑ i, ‖(Work.Analysis.IonescuWainger.multiplierOf (m i) (hm i)) G‖ ^ 2
      = ∑ i, ‖(hm i).toLp (m i) • Work.Analysis.IonescuWainger.fourierZ G‖^2 :=
          Finset.sum_congr rfl fun i _ => by rw [hnorm i]
    _ ≤ A^2 * ‖Work.Analysis.IonescuWainger.fourierZ G‖^2 := key
    _ = A^2 * ‖G‖^2 := by rw [Work.Analysis.IonescuWainger.fourierZ.norm_map]

end Work.KMTPlan.B
