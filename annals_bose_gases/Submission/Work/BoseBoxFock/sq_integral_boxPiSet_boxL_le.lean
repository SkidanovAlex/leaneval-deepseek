import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.imgFibreEnergyDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.sq_integral_boxPiSet_boxL_le`

Cauchy–Schwarz (in its squared form) for the iterated integral over the Fock box
`boxPiSet ι ℓ` (a product of `|ι|` copies of the one-particle box `boxL ℓ`) and the one-particle
box `boxL ℓ`:

    (∫_{x'} ∫_s f (x', s) g (x', s))² ≤ (∫_{x'} ∫_s f (x', s)²) (∫_{x'} ∫_s g (x', s)²) .

**Proof.**  The iterated set integral is the integral over the *product* measure
`(volume.restrict A).prod (volume.restrict B) = (volume : Measure ((ι → E3) × E3)).restrict
(A ×ˢ B)` (Fubini, the integrand being continuous on a compact set), so the assertion is the
Cauchy–Schwarz inequality for the Bochner integral of two `L²` functions.  The latter is proved
below as `sq_integral_mul_le_of_memLp` from Hölder's inequality
(`MeasureTheory.integral_mul_norm_le_Lp_mul_Lq` at `p = q = 2`).

`sorry`-free.
-/

namespace Work.BoseBoxFock

open MeasureTheory

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- Cauchy–Schwarz for the Bochner integral of two `L²` real functions:
`(∫ f g)² ≤ (∫ f²) (∫ g²)`.

Obtained from Hölder's inequality with conjugate exponents `p = q = 2`,
`∫ ‖f‖‖g‖ ≤ (∫‖f‖²)^{1/2} (∫‖g‖²)^{1/2}`, together with `‖∫ f g‖ ≤ ∫ ‖f g‖`. -/
theorem sq_integral_mul_le_of_memLp {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g : α → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (∫ x, f x * g x ∂μ) ^ 2 ≤ (∫ x, f x ^ 2 ∂μ) * (∫ x, g x ^ 2 ∂μ) := by
  have hf' : MemLp f (ENNReal.ofReal 2) μ := by simpa using hf
  have hg' : MemLp g (ENNReal.ofReal 2) μ := by simpa using hg
  have hH := MeasureTheory.integral_mul_norm_le_Lp_mul_Lq (μ := μ) (f := f) (g := g)
      (p := 2) (q := 2) Real.HolderConjugate.two_two hf' hg'
  have habs : |∫ x, f x * g x ∂μ| ≤ ∫ x, ‖f x‖ * ‖g x‖ ∂μ := by
    rw [← Real.norm_eq_abs]
    simpa [norm_mul] using MeasureTheory.norm_integral_le_integral_norm (fun x => f x * g x)
  have hsq1 : (∫ x, ‖f x‖ ^ (2 : ℝ) ∂μ) = ∫ x, (f x) ^ 2 ∂μ := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show ‖f x‖ ^ (2 : ℝ) = f x ^ 2
    rw [Real.norm_eq_abs, Real.rpow_two, sq_abs]
  have hsq2 : (∫ x, ‖g x‖ ^ (2 : ℝ) ∂μ) = ∫ x, (g x) ^ 2 ∂μ := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show ‖g x‖ ^ (2 : ℝ) = g x ^ 2
    rw [Real.norm_eq_abs, Real.rpow_two, sq_abs]
  have hA0 : 0 ≤ ∫ x, (f x) ^ 2 ∂μ :=
    integral_nonneg_of_ae (Filter.Eventually.of_forall fun x => sq_nonneg _)
  have hB0 : 0 ≤ ∫ x, (g x) ^ 2 ∂μ :=
    integral_nonneg_of_ae (Filter.Eventually.of_forall fun x => sq_nonneg _)
  have step : |∫ x, f x * g x ∂μ|
      ≤ Real.sqrt (∫ x, (f x) ^ 2 ∂μ) * Real.sqrt (∫ x, (g x) ^ 2 ∂μ) := by
    have h := habs.trans hH
    rwa [hsq1, hsq2, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at h
  calc (∫ x, f x * g x ∂μ) ^ 2
      = |∫ x, f x * g x ∂μ| ^ 2 := by rw [sq_abs]
    _ ≤ (Real.sqrt (∫ x, (f x) ^ 2 ∂μ) * Real.sqrt (∫ x, (g x) ^ 2 ∂μ)) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) step 2
    _ = (∫ x, (f x) ^ 2 ∂μ) * (∫ x, (g x) ^ 2 ∂μ) := by
        rw [mul_pow, Real.sq_sqrt hA0, Real.sq_sqrt hB0]

theorem sq_integral_boxPiSet_boxL_le {ι : Type*} [Fintype ι] {ℓ : ℝ} (hℓ : 0 < ℓ)
    {f g : (ι → EuclideanSpace ℝ (Fin 3)) × EuclideanSpace ℝ (Fin 3) → ℝ}
    (hf : Continuous f) (hg : Continuous g) :
    (∫ x' in Work.BoseBoxFock.boxPiSet ι ℓ, ∫ s in Work.BoseK15.corpusBox.boxL ℓ,
        f (x', s) * g (x', s)) ^ 2
      ≤ (∫ x' in Work.BoseBoxFock.boxPiSet ι ℓ, ∫ s in Work.BoseK15.corpusBox.boxL ℓ,
            f (x', s) ^ 2)
        * (∫ x' in Work.BoseBoxFock.boxPiSet ι ℓ, ∫ s in Work.BoseK15.corpusBox.boxL ℓ,
            g (x', s) ^ 2) := by
  -- The product `boxPiSet ι ℓ × boxL ℓ` is compact, hence the restricted measure is finite and
  -- continuous integrands are integrable / in `L²` for it.
  have hK : IsCompact (boxPiSet ι ℓ ×ˢ Work.BoseK15.corpusBox.boxL ℓ) :=
    (isCompact_boxPiSet hℓ).prod (Work.BoseK15.corpusBox.boxL_compact ℓ)
  -- the restricted product measure is the product of the restricted measures
  have hprod : (volume : Measure ((ι → E3) × E3)).restrict
        (boxPiSet ι ℓ ×ˢ Work.BoseK15.corpusBox.boxL ℓ)
      = ((volume : Measure (ι → E3)).restrict (boxPiSet ι ℓ)).prod
          ((volume : Measure E3).restrict (Work.BoseK15.corpusBox.boxL ℓ)) := by
    rw [Measure.prod_restrict, Measure.volume_eq_prod]
  have hintH : Integrable (fun z : (ι → E3) × E3 => f z * g z)
      ((volume : Measure ((ι → E3) × E3)).restrict
        (boxPiSet ι ℓ ×ˢ Work.BoseK15.corpusBox.boxL ℓ)) :=
    ((hf.mul hg).continuousOn).integrableOn_compact hK
  have hintF : Integrable (fun z : (ι → E3) × E3 => f z ^ 2)
      ((volume : Measure ((ι → E3) × E3)).restrict
        (boxPiSet ι ℓ ×ˢ Work.BoseK15.corpusBox.boxL ℓ)) :=
    ((hf.pow 2).continuousOn).integrableOn_compact hK
  have hintG : Integrable (fun z : (ι → E3) × E3 => g z ^ 2)
      ((volume : Measure ((ι → E3) × E3)).restrict
        (boxPiSet ι ℓ ×ˢ Work.BoseK15.corpusBox.boxL ℓ)) :=
    ((hg.pow 2).continuousOn).integrableOn_compact hK
  -- Fubini: the iterated set integrals are the integrals over the product restricted measure
  have h1 : (∫ x' in boxPiSet ι ℓ,
        ∫ s in Work.BoseK15.corpusBox.boxL ℓ, f (x', s) * g (x', s))
      = ∫ z, f z * g z ∂((volume : Measure ((ι → E3) × E3)).restrict
          (boxPiSet ι ℓ ×ˢ Work.BoseK15.corpusBox.boxL ℓ)) := by
    rw [hprod]
    rw [MeasureTheory.integral_prod (fun z : (ι → E3) × E3 => f z * g z) (hprod ▸ hintH)]
  have h2 : (∫ x' in boxPiSet ι ℓ,
        ∫ s in Work.BoseK15.corpusBox.boxL ℓ, f (x', s) ^ 2)
      = ∫ z, f z ^ 2 ∂((volume : Measure ((ι → E3) × E3)).restrict
          (boxPiSet ι ℓ ×ˢ Work.BoseK15.corpusBox.boxL ℓ)) := by
    rw [hprod]
    rw [MeasureTheory.integral_prod (fun z : (ι → E3) × E3 => f z ^ 2) (hprod ▸ hintF)]
  have h3 : (∫ x' in boxPiSet ι ℓ,
        ∫ s in Work.BoseK15.corpusBox.boxL ℓ, g (x', s) ^ 2)
      = ∫ z, g z ^ 2 ∂((volume : Measure ((ι → E3) × E3)).restrict
          (boxPiSet ι ℓ ×ˢ Work.BoseK15.corpusBox.boxL ℓ)) := by
    rw [hprod]
    rw [MeasureTheory.integral_prod (fun z : (ι → E3) × E3 => g z ^ 2) (hprod ▸ hintG)]
  have hmemf : MemLp (fun z : (ι → E3) × E3 => f z) 2
      ((volume : Measure ((ι → E3) × E3)).restrict
        (boxPiSet ι ℓ ×ˢ Work.BoseK15.corpusBox.boxL ℓ)) :=
    (memLp_two_iff_integrable_sq hf.aestronglyMeasurable).2 hintF
  have hmemg : MemLp (fun z : (ι → E3) × E3 => g z) 2
      ((volume : Measure ((ι → E3) × E3)).restrict
        (boxPiSet ι ℓ ×ˢ Work.BoseK15.corpusBox.boxL ℓ)) :=
    (memLp_two_iff_integrable_sq hg.aestronglyMeasurable).2 hintG
  have hcs := sq_integral_mul_le_of_memLp
    (μ := (volume : Measure ((ι → E3) × E3)).restrict
      (boxPiSet ι ℓ ×ˢ Work.BoseK15.corpusBox.boxL ℓ))
    (f := fun z : (ι → E3) × E3 => f z) (g := fun z : (ι → E3) × E3 => g z) hmemf hmemg
  rw [h1, h2, h3]
  exact hcs

end Work.BoseBoxFock
