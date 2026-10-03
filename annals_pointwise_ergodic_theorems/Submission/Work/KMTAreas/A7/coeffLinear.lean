/-
# Linearity of the double Fourier coefficient `coeff` on the torus (Area A7)

`Work.KMTAreas.A7.coeff F a b = ∫ θ₁, ∫ θ₂, F θ₁ θ₂ e(-a θ₁) e(-b θ₂)` is the `(a,b)`-th double
Fourier coefficient of a symbol `F` on `𝕋²` (`Work.KMTAreas.A7.symbolDefs`).  This module proves
that it is *linear* over finite sums (and differences) of symbols that are measurable and bounded:

* `coeff_eq_prod_integral` — `coeff` is the integral of the integrand against the product measure
  `circleMeasure.prod circleMeasure` (Fubini);
* `coeff_finset_sum` — `coeff (∑ i ∈ S, F i) = ∑ i ∈ S, coeff (F i)`;
* `coeff_sub` — `coeff (F - G) = coeff F - coeff G`.

The linearity is what turns the pointwise §6 collapse
`concSymb - modSymbC = ∑_β spikeSymb β` (`A7/spikeCollapse.lean`) into the corresponding identity
for the kernels (`smallKconc - smallKmod`), which is the form in which the `ℓ¹(ℤ²)`-mass bound of
the §6 model approximation is stated.

The integrability hypotheses are exactly `Integrable (F p.1 p.2 * e(-a p.1) * e(-b p.2))
(circleMeasure.prod circleMeasure)`; in the applications `F` is measurable and bounded and the
torus is a probability space, so this is automatic (`coeff_finset_sum_of_bound` below).
-/
import Mathlib
import Submission.Work.KMTAreas.A7.symbolDefs
import Submission.Work.KMTAreas.A7.liftCollapse

set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace Work.KMTAreas.A7

noncomputable section

open MeasureTheory
open scoped BigOperators
open Work.Analysis.IonescuWainger

/-- The finite sum of integrable functions is integrable. -/
private lemma integrable_finset_sum' {ι : Type*} (S : Finset ι)
    {g : ι → AddCircle 1 × AddCircle 1 → ℂ}
    (h : ∀ i ∈ S, Integrable (g i) (circleMeasure.prod circleMeasure)) :
    Integrable (fun p => ∑ i ∈ S, g i p) (circleMeasure.prod circleMeasure) := by
  classical
  induction S using Finset.induction with
  | empty => simp
  | insert i s hi ih =>
      have h1 : Integrable (g i) (circleMeasure.prod circleMeasure) :=
        h i (Finset.mem_insert_self i s)
      have h2 : Integrable (fun p => ∑ j ∈ s, g j p) (circleMeasure.prod circleMeasure) :=
        ih (fun j hj => h j (Finset.mem_insert_of_mem hj))
      simp only [Finset.sum_insert hi]
      exact h1.add h2

/-- **`coeff` as an integral against the product measure** (Fubini). -/
theorem coeff_eq_prod_integral (F : AddCircle 1 → AddCircle 1 → ℂ) (a b : ℤ)
    (hF : Integrable (fun p : AddCircle 1 × AddCircle 1 =>
        F p.1 p.2 * fourier (T := 1) (-a) p.1 * fourier (T := 1) (-b) p.2)
      (circleMeasure.prod circleMeasure)) :
    coeff F a b = ∫ p : AddCircle 1 × AddCircle 1,
        F p.1 p.2 * fourier (T := 1) (-a) p.1 * fourier (T := 1) (-b) p.2
      ∂(circleMeasure.prod circleMeasure) := by
  rw [coeff]
  exact (MeasureTheory.integral_prod _ hF).symm

/-- **Linearity of `coeff` over finite sums.** -/
theorem coeff_finset_sum {ι : Type*} (S : Finset ι) (F : ι → AddCircle 1 → AddCircle 1 → ℂ)
    (a b : ℤ)
    (hF : ∀ i ∈ S, Integrable (fun p : AddCircle 1 × AddCircle 1 =>
        F i p.1 p.2 * fourier (T := 1) (-a) p.1 * fourier (T := 1) (-b) p.2)
      (circleMeasure.prod circleMeasure)) :
    coeff (fun θ₁ θ₂ => ∑ i ∈ S, F i θ₁ θ₂) a b = ∑ i ∈ S, coeff (F i) a b := by
  classical
  have hsm : (fun p : AddCircle 1 × AddCircle 1 =>
        (∑ i ∈ S, F i p.1 p.2) * fourier (T := 1) (-a) p.1 * fourier (T := 1) (-b) p.2)
      = fun p : AddCircle 1 × AddCircle 1 => ∑ i ∈ S,
          (F i p.1 p.2 * fourier (T := 1) (-a) p.1 * fourier (T := 1) (-b) p.2) := by
    funext p
    rw [Finset.sum_mul, Finset.sum_mul]
  have hInt : Integrable (fun p : AddCircle 1 × AddCircle 1 =>
      (∑ i ∈ S, F i p.1 p.2) * fourier (T := 1) (-a) p.1 * fourier (T := 1) (-b) p.2)
      (circleMeasure.prod circleMeasure) := by
    rw [hsm]
    exact integrable_finset_sum' S (fun i hi => hF i hi)
  rw [coeff_eq_prod_integral _ a b hInt, hsm,
    MeasureTheory.integral_finsetSum S (fun i hi => hF i hi)]
  exact Finset.sum_congr rfl fun i hi => by rw [coeff_eq_prod_integral _ a b (hF i hi)]

/-- **Additivity of `coeff`.** -/
theorem coeff_add (F G : AddCircle 1 → AddCircle 1 → ℂ) (a b : ℤ)
    (hF : Integrable (fun p : AddCircle 1 × AddCircle 1 =>
        F p.1 p.2 * fourier (T := 1) (-a) p.1 * fourier (T := 1) (-b) p.2)
      (circleMeasure.prod circleMeasure))
    (hG : Integrable (fun p : AddCircle 1 × AddCircle 1 =>
        G p.1 p.2 * fourier (T := 1) (-a) p.1 * fourier (T := 1) (-b) p.2)
      (circleMeasure.prod circleMeasure)) :
    coeff (fun θ₁ θ₂ => F θ₁ θ₂ + G θ₁ θ₂) a b = coeff F a b + coeff G a b := by
  have hsm : (fun p : AddCircle 1 × AddCircle 1 =>
        (F p.1 p.2 + G p.1 p.2) * fourier (T := 1) (-a) p.1 * fourier (T := 1) (-b) p.2)
      = fun p : AddCircle 1 × AddCircle 1 =>
          (F p.1 p.2 * fourier (T := 1) (-a) p.1 * fourier (T := 1) (-b) p.2)
            + (G p.1 p.2 * fourier (T := 1) (-a) p.1 * fourier (T := 1) (-b) p.2) := by
    funext p; ring
  have hInt : Integrable (fun p : AddCircle 1 × AddCircle 1 =>
      (F p.1 p.2 + G p.1 p.2) * fourier (T := 1) (-a) p.1 * fourier (T := 1) (-b) p.2)
      (circleMeasure.prod circleMeasure) := by
    rw [hsm]; exact hF.add hG
  rw [coeff_eq_prod_integral _ a b hInt, hsm, MeasureTheory.integral_add hF hG,
    coeff_eq_prod_integral _ a b hF, coeff_eq_prod_integral _ a b hG]

/-- **Subtractivity of `coeff`.** -/
theorem coeff_sub (F G : AddCircle 1 → AddCircle 1 → ℂ) (a b : ℤ)
    (hF : Integrable (fun p : AddCircle 1 × AddCircle 1 =>
        F p.1 p.2 * fourier (T := 1) (-a) p.1 * fourier (T := 1) (-b) p.2)
      (circleMeasure.prod circleMeasure))
    (hG : Integrable (fun p : AddCircle 1 × AddCircle 1 =>
        G p.1 p.2 * fourier (T := 1) (-a) p.1 * fourier (T := 1) (-b) p.2)
      (circleMeasure.prod circleMeasure)) :
    coeff (fun θ₁ θ₂ => F θ₁ θ₂ - G θ₁ θ₂) a b = coeff F a b - coeff G a b := by
  have hsm : (fun p : AddCircle 1 × AddCircle 1 =>
        (F p.1 p.2 - G p.1 p.2) * fourier (T := 1) (-a) p.1 * fourier (T := 1) (-b) p.2)
      = fun p : AddCircle 1 × AddCircle 1 =>
          (F p.1 p.2 * fourier (T := 1) (-a) p.1 * fourier (T := 1) (-b) p.2)
            - (G p.1 p.2 * fourier (T := 1) (-a) p.1 * fourier (T := 1) (-b) p.2) := by
    funext p; ring
  have hInt : Integrable (fun p : AddCircle 1 × AddCircle 1 =>
      (F p.1 p.2 - G p.1 p.2) * fourier (T := 1) (-a) p.1 * fourier (T := 1) (-b) p.2)
      (circleMeasure.prod circleMeasure) := by
    rw [hsm]; exact hF.sub hG
  rw [coeff_eq_prod_integral _ a b hInt, hsm, MeasureTheory.integral_sub hF hG,
    coeff_eq_prod_integral _ a b hF, coeff_eq_prod_integral _ a b hG]

/-- **`coeff` of a bounded measurable symbol.**  On the probability space `𝕋²` a measurable and
bounded symbol is integrable against the characters, so `coeff` may be computed by linearity. -/
theorem integrable_coeff_integrand {F : AddCircle 1 → AddCircle 1 → ℂ} {C : ℝ}
    (hF : Measurable (fun p : AddCircle 1 × AddCircle 1 => F p.1 p.2))
    (hC : ∀ θ₁ θ₂, ‖F θ₁ θ₂‖ ≤ C) (a b : ℤ) :
    Integrable (fun p : AddCircle 1 × AddCircle 1 =>
        F p.1 p.2 * fourier (T := 1) (-a) p.1 * fourier (T := 1) (-b) p.2)
      (circleMeasure.prod circleMeasure) := by
  refine MeasureTheory.Integrable.of_bound ?_ (max C 0) (Filter.Eventually.of_forall fun p => ?_)
  · exact ((hF.mul (((fourier (T := 1) (-a)).continuous.measurable).comp measurable_fst)).mul
      (((fourier (T := 1) (-b)).continuous.measurable).comp measurable_snd)).aestronglyMeasurable
  · have h1 : ‖fourier (T := 1) (-a) p.1‖ ≤ 1 := by
      have := ContinuousMap.norm_coe_le_norm (fourier (T := 1) (-a)) p.1
      rwa [fourier_norm (T := 1) (-a)] at this
    have h2 : ‖fourier (T := 1) (-b) p.2‖ ≤ 1 := by
      have := ContinuousMap.norm_coe_le_norm (fourier (T := 1) (-b)) p.2
      rwa [fourier_norm (T := 1) (-b)] at this
    have h3 : (0 : ℝ) ≤ max C 0 := le_max_right _ _
    calc ‖F p.1 p.2 * fourier (T := 1) (-a) p.1 * fourier (T := 1) (-b) p.2‖
        = ‖F p.1 p.2‖ * ‖fourier (T := 1) (-a) p.1‖ * ‖fourier (T := 1) (-b) p.2‖ := by
          rw [norm_mul, norm_mul]
      _ ≤ max C 0 * 1 * 1 := by
          refine mul_le_mul (mul_le_mul (le_trans (hC p.1 p.2) (le_max_left C 0)) h1
            (norm_nonneg _) h3) h2 (norm_nonneg _) (by positivity)
      _ = max C 0 := by ring

end

end Work.KMTAreas.A7
