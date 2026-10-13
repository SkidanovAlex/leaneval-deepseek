/-
# `∫∫ A² ≤ 16` for the Cauchy–Schwarz weight `A` of `L₁₂(Transport f)(0)`

The function

`A(z,θ) = 3 K(θ)·z/(1+z)³·sin(2θ)^{η/2}`

is the first factor in the Cauchy–Schwarz decomposition `C0 f = ∫∫ A·B` of the
zero-mode of `L₁₂(Transport f)` (see `L12f_Transport_zero_sq_le`).  This file proves
that `A²` is integrable on the product measure `(volume|Iz) ⊗ (volume|Iθ)` and that its
integral is at most `16`, the constant needed by the Cauchy–Schwarz inequality.

`A²` is a product of a function of `z` alone and a function of `θ` alone:

`A(z,θ)² = (z/(1+z)³)² · (3 K(θ) sin(2θ)^{η/2})²`,

so the integral factorises.  The two one-dimensional facts are

* `∫_z (z/(1+z)³)² = ∫_z z²/(1+z)⁶ = 1/30 ≤ 1/16` (the integrand of
  `Work.Coercivity.C0D`, whose value is `Work.Coercivity.C0D_le`);
* `∫_θ 9 K(θ)² sin(2θ)^η ≤ ∫_θ 81 = 81 · |Iθ| ≤ 162`, because on `Iθ` one has
  `|3 K(θ)| ≤ 9` and `sin(2θ)^{η/2} ≤ 1`, so the angular integrand is bounded by `81`.

`1/16 · 162 = 10.125 ≤ 16` gives the claimed constant.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.integrable_prod_of_iterated
import Submission.Work.Coercivity.C0D_le
import Submission.Work.Coercivity.L2CoercivityTransport

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.CoercivityFix.Transfer.E2norm

noncomputable section

open MeasureTheory Set Filter
open scoped Real Topology

set_option autoImplicit false

/-! ## The two one-dimensional factors -/

/-- The radial factor `(z/(1+z)³)²` of `A²`. -/
private def cwAz (z : ℝ) : ℝ := (z / (1 + z) ^ 3) ^ 2

/-- The angular factor `(3 K(θ) sin(2θ)^{η/2})²` of `A²`. -/
private def cwAt (θ : ℝ) : ℝ :=
  (3 * Work.Spaces.K θ * (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2

private lemma cwAz_eq (z : ℝ) : cwAz z = z ^ 2 / (1 + z) ^ 6 := by
  simp only [cwAz]
  rw [div_pow, ← pow_mul]

/-- The radial factor is integrable on `Iz`, being the integrand of `C0D`. -/
private lemma cwAz_integrable : Integrable cwAz (volume.restrict Work.Spaces.Iz) :=
  Work.Coercivity.integrable_Iz_zsq_div_six.congr
    (Filter.Eventually.of_forall fun z => (cwAz_eq z).symm)

/-- `∫_z (z/(1+z)³)² = 1/30`. -/
private lemma cwAz_integral : ∫ z in Work.Spaces.Iz, cwAz z = 1 / 30 := by
  rw [← Work.Coercivity.integral_Iz_zsq_div_six]
  exact setIntegral_congr_fun measurableSet_Ici (fun z _ => cwAz_eq z)

/-- `∫_z (z/(1+z)³)² ≤ 1/16`. -/
private lemma cwAz_integral_le : ∫ z in Work.Spaces.Iz, cwAz z ≤ 1 / 16 := by
  rw [cwAz_integral]; norm_num

/-- Nonnegativity of the angular factor. -/
private lemma cwAt_nonneg (θ : ℝ) : 0 ≤ cwAt θ := by
  simpa only [cwAt] using
    sq_nonneg (3 * Work.Spaces.K θ * (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))

private lemma cwAt_continuous : Continuous cwAt := by
  have hrpow : Continuous fun θ : ℝ => (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) :=
    (Real.continuous_rpow_const (by norm_num [Work.Spaces.eta])).comp (by fun_prop)
  have hK : Continuous fun θ : ℝ => 3 * Work.Spaces.K θ := by
    rw [show (fun θ : ℝ => 3 * Work.Spaces.K θ)
        = fun θ : ℝ => 3 * (3 * Real.sin θ * Real.cos θ ^ 2) from rfl]
    fun_prop
  exact (hK.mul hrpow).pow 2

/-- The angular factor is integrable on the interval `Iθ`. -/
private lemma cwAt_integrable : Integrable cwAt (volume.restrict Work.Spaces.Iθ) :=
  cwAt_continuous.continuousOn.integrableOn_compact isCompact_Icc

/-- On `Iθ` the angular factor is bounded by `81`: indeed `|3 K(θ)| ≤ 9` and
`sin(2θ)^{η/2} ∈ [0,1]` there. -/
private lemma cwAt_le_eighty_one {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : cwAt θ ≤ 81 := by
  have hπ : (0 : ℝ) < π := Real.pi_pos
  have hsinθ0 : 0 ≤ Real.sin θ := Real.sin_nonneg_of_mem_Icc ⟨hθ.1, by linarith [hθ.2, hπ]⟩
  have hsinθ1 : Real.sin θ ≤ 1 := Real.sin_le_one θ
  have hcos2 : Real.cos θ ^ 2 ≤ 1 := Real.cos_sq_le_one θ
  have hcos0 : 0 ≤ Real.cos θ ^ 2 := sq_nonneg _
  have hs0 : 0 ≤ Real.sin (2 * θ) :=
    Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, hπ]⟩
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hη : 0 ≤ Work.Spaces.eta / 2 := by norm_num [Work.Spaces.eta]
  have hr0 : 0 ≤ (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) := Real.rpow_nonneg hs0 _
  have hr1 : (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) ≤ 1 := Real.rpow_le_one hs0 hs1 hη
  have hKabs : |3 * Work.Spaces.K θ| ≤ 9 := by
    have hKnn : 0 ≤ 3 * Work.Spaces.K θ := by
      rw [Work.Spaces.K]; nlinarith [hsinθ0, hcos0]
    rw [abs_of_nonneg hKnn, Work.Spaces.K]
    nlinarith [hsinθ0, hsinθ1, hcos0, hcos2]
  have hbound : |3 * Work.Spaces.K θ * (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)| ≤ 9 := by
    rw [abs_mul]
    calc |3 * Work.Spaces.K θ| * |(Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)|
        ≤ 9 * 1 := mul_le_mul hKabs (by rw [abs_of_nonneg hr0]; exact hr1)
          (abs_nonneg _) (by norm_num)
      _ = 9 := by norm_num
  have hx9 := abs_le.mp hbound
  have hsq : (3 * Work.Spaces.K θ * (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2
      ≤ (9 : ℝ) ^ 2 := sq_le_sq' hx9.1 hx9.2
  norm_num at hsq
  simpa only [cwAt] using hsq

/-- `∫_θ 9 K(θ)² sin(2θ)^η ≤ 162`. -/
private lemma cwAt_integral_le : ∫ θ in Work.Spaces.Iθ, cwAt θ ≤ 162 := by
  have hmono := setIntegral_mono_on (f := cwAt) (g := fun _ : ℝ => (81 : ℝ))
      cwAt_integrable (integrable_const 81) measurableSet_Icc
      (fun θ hθ => cwAt_le_eighty_one hθ)
  calc ∫ θ in Work.Spaces.Iθ, cwAt θ
      ≤ ∫ θ in Work.Spaces.Iθ, (81 : ℝ) := hmono
    _ = volume.real Work.Spaces.Iθ * 81 := by rw [setIntegral_const, smul_eq_mul]
    _ ≤ 2 * 81 := mul_le_mul_of_nonneg_right Work.Coercivity.volumeReal_Iθ_le_two (by norm_num)
    _ = 162 := by norm_num

/-! ## The product bound -/

theorem A_sq_prod_le :
    MeasureTheory.Integrable (fun p : ℝ × ℝ =>
        (3 * Work.Spaces.K p.2 * (p.1 / (1 + p.1) ^ 3)
          * (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2)) ^ 2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) ∧
    ∫ p, (3 * Work.Spaces.K p.2 * (p.1 / (1 + p.1) ^ 3)
          * (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2)) ^ 2
        ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) ≤ 16 := by
  -- `A²` factors into its radial and angular parts.
  have hfactor : ∀ z θ : ℝ,
      (3 * Work.Spaces.K θ * (z / (1 + z) ^ 3) * (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2
        = cwAz z * cwAt θ := by
    intro z θ
    simp only [cwAz, cwAt]
    ring
  have hInt : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      (3 * Work.Spaces.K p.2 * (p.1 / (1 + p.1) ^ 3)
        * (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2)) ^ 2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    (cwAz_integrable.mul_prod cwAt_integrable).congr
      (Filter.Eventually.of_forall fun p => (hfactor p.1 p.2).symm)
  refine ⟨hInt, ?_⟩
  calc ∫ p, (3 * Work.Spaces.K p.2 * (p.1 / (1 + p.1) ^ 3)
          * (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2)) ^ 2
        ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ))
      = ∫ p, cwAz p.1 * cwAt p.2
        ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
        integral_congr_ae (Filter.Eventually.of_forall fun p => hfactor p.1 p.2)
    _ = (∫ z in Work.Spaces.Iz, cwAz z) * (∫ θ in Work.Spaces.Iθ, cwAt θ) :=
        Work.Coercivity.integral_prod_sep cwAz cwAt cwAz_integrable cwAt_integrable
    _ ≤ (1 / 16) * 162 :=
        mul_le_mul cwAz_integral_le cwAt_integral_le
          (setIntegral_nonneg (s := Set.Icc 0 (π / 2)) (μ := volume) measurableSet_Icc
            (fun θ _ => cwAt_nonneg θ))
          (by norm_num)
    _ ≤ 16 := by norm_num

end

end Work.FTS.CoercivityFix.Transfer.E2norm
