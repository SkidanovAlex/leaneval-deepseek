import Submission.FUP.PSHToFourier
import Submission.Commons.Analysis.Complex.meanValue_polydisc
import Submission.Commons.Analysis.Complex.differentiable_complex_of_dbar_eq_zero

open FractalUncertainty MeasureTheory FourierTransform Metric Filter Set
open scoped ENNReal BigOperators Topology ContDiff

set_option autoImplicit false
variable {d : ℕ}
local notation "ℝᵈ" => EuclideanSpace ℝ (Fin d)
local notation "ℂᵈ" => (Fin d → ℂ)

/-!
# §5 of Cohen's paper, part 2: the estimates

This module continues `Submission/FUP/PSHToFourier.lean`.  It

* proves the integrability hypothesis of Hörmander's `∂̄` theorem for the test form
  `η = ∂̄h` and the weight `φ = section5Phi ρ u u₀` of §5 (step (A));
* applies `HormanderStatement` and produces the entire `F = h - g` (step (B)).
-/

namespace Submission.FUP

/-! ## Elementary lower bounds for the weight -/

lemma sum_sq_ge_norm_sq (z : ℂᵈ) : ‖z‖ ^ 2 ≤ ∑ j, ‖z j‖ ^ 2 := by
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    have : z = 0 := Subsingleton.elim _ _
    rw [this]; simp
  · obtain ⟨j₀, -, hj₀⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin d))
      (fun j => ‖z j‖) ⟨⟨0, hd⟩, Finset.mem_univ _⟩
    have h : ‖z‖ ≤ ‖z j₀‖ :=
      (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr (fun j => hj₀ j (Finset.mem_univ j))
    have h2 : ‖z‖ = ‖z j₀‖ := le_antisymm h (norm_le_pi_norm z j₀)
    rw [h2]
    exact Finset.single_le_sum (f := fun j => ‖z j‖ ^ 2) (fun i _ => sq_nonneg _)
      (Finset.mem_univ j₀)

lemma logWeight_ge_of_le_norm (z : ℂᵈ) {c : ℝ} (hc : 0 < c) (hz : c ≤ ‖z‖) :
    20 * (d : ℝ) * Real.log c ≤ logWeight z := by
  have hsum : c ^ 2 ≤ ∑ j, ‖z j‖ ^ 2 :=
    le_trans (pow_le_pow_left₀ hc.le hz 2) (sum_sq_ge_norm_sq z)
  have hlog : Real.log (c ^ 2) ≤ Real.log (∑ j, ‖z j‖ ^ 2) :=
    Real.log_le_log (by positivity) hsum
  rw [Real.log_pow] at hlog
  have key : (10:ℝ) * (d:ℝ) * (2 * Real.log c)
      ≤ (10:ℝ) * (d:ℝ) * Real.log (∑ j, ‖z j‖ ^ 2) :=
    mul_le_mul_of_nonneg_left hlog (by positivity)
  rw [logWeight]
  nlinarith [key]

/-- On the annulus `c ≤ ‖z‖ ≤ 1` (with `c > 0`), the §5 weight `φ` is bounded below. -/
lemma section5Phi_ge {CLip ρ c : ℝ} (hCLip : 0 ≤ CLip) (hρ : 0 < ρ) (hc : 0 < c)
    {u u0 : ℂᵈ → ℝ} (huzero : ∀ x : ℝᵈ, ‖x‖ ≤ 2 → u (toCpx x) = 0)
    (hulip : ∀ x₁ x₂ : ℝᵈ, |u (toCpx x₁) - u (toCpx x₂)| ≤ CLip * ‖x₁ - x₂‖)
    (hugrowth : ∀ z : ℂᵈ, u (toCpx (reVec z)) ≤ u z)
    (hu0zero : ∀ x : ℝᵈ, ‖x‖ ≤ 2 → u0 (toCpx x) = 0)
    (hu0lip : ∀ x₁ x₂ : ℝᵈ, |u0 (toCpx x₁) - u0 (toCpx x₂)| ≤ 1 * ‖x₁ - x₂‖)
    (hu0growth : ∀ z : ℂᵈ, u0 (toCpx (reVec z)) ≤ u0 z) :
    ∀ z : ℂᵈ, c ≤ ‖z‖ → ‖z‖ ≤ 1 →
      -(2 * CLip + ρ) * Real.sqrt d + 20 * (d : ℝ) * Real.log c
        ≤ section5Phi ρ u u0 z := by
  intro z hz1 hz2
  have hre : ‖reVec z‖ ≤ Real.sqrt d := by
    calc ‖reVec z‖ ≤ Real.sqrt (d : ℝ) * ‖z‖ := norm_reVec_le z
      _ ≤ Real.sqrt (d : ℝ) * 1 := mul_le_mul_of_nonneg_left hz2 (Real.sqrt_nonneg _)
      _ = Real.sqrt d := mul_one _
  have hu1 : -CLip * Real.sqrt d ≤ u z := by
    have h1 : |u (toCpx (reVec z))| ≤ CLip * ‖reVec z‖ := by
      have h := hulip (reVec z) 0
      have h0 : u (toCpx (0 : ℝᵈ)) = 0 := huzero 0 (by simp)
      simpa only [h0, sub_zero] using h
    have h2 : -CLip * ‖reVec z‖ ≤ u (toCpx (reVec z)) := by
      linarith [neg_abs_le (u (toCpx (reVec z)))]
    have h3 : CLip * ‖reVec z‖ ≤ CLip * Real.sqrt d := mul_le_mul_of_nonneg_left hre hCLip
    linarith [hugrowth z]
  have hu2 : -Real.sqrt d ≤ u0 z := by
    have h1 : |u0 (toCpx (reVec z))| ≤ 1 * ‖reVec z‖ := by
      have h := hu0lip (reVec z) 0
      have h0 : u0 (toCpx (0 : ℝᵈ)) = 0 := hu0zero 0 (by simp)
      simpa only [h0, sub_zero] using h
    have h2 : -1 * ‖reVec z‖ ≤ u0 (toCpx (reVec z)) := by
      linarith [neg_abs_le (u0 (toCpx (reVec z)))]
    linarith [hu0growth z, hre]
  have hlw : 20 * (d : ℝ) * Real.log c ≤ logWeight z :=
    logWeight_ge_of_le_norm z hc hz1
  have ht : 0 ≤ (ρ / 2) * (imNorm z - 1) :=
    mul_nonneg (by positivity) (by linarith [one_le_imNorm z])
  rw [section5Phi]
  nlinarith [hu1, hu2, hlw, ht, hρ.le, Real.sqrt_nonneg (d : ℝ)]

end Submission.FUP
namespace Submission.FUP

lemma formNormSq_eq_zero {η : ℂᵈ → (Fin d → ℂ)} {z : ℂᵈ} (h : η z = 0) :
    formNormSq η z = 0 := by
  simp only [formNormSq, h, Pi.zero_apply, norm_zero]
  simp

lemma one_div_section5Kappa_le {ρ : ℝ} (hρ : 0 < ρ) {z : ℂᵈ} (hz : ‖z‖ ≤ 1) :
    1 / section5Kappa ρ z ≤ 8 * (Real.sqrt (1 + (d : ℝ))) ^ 3 / ρ := by
  have hz2 : ‖z‖ ^ 2 ≤ (1 : ℝ) := by nlinarith [norm_nonneg z, hz]
  have him : ∑ j, (z j).im ^ 2 ≤ (d : ℝ) := by
    calc ∑ j, (z j).im ^ 2 ≤ ∑ _j : Fin d, ‖z‖ ^ 2 :=
          Finset.sum_le_sum fun j _ => by
            have h1 : |(z j).im| ≤ ‖z j‖ := Complex.abs_im_le_norm (z j)
            have h2 : ‖z j‖ ≤ ‖z‖ := norm_le_pi_norm z j
            calc (z j).im ^ 2 = |(z j).im| ^ 2 := by rw [sq_abs]
              _ ≤ ‖z‖ ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (le_trans h1 h2) 2
      _ = (d : ℝ) * ‖z‖ ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ ≤ (d : ℝ) * 1 := mul_le_mul_of_nonneg_left hz2 (Nat.cast_nonneg d)
      _ = (d : ℝ) := mul_one _
  have h1 : (imNorm z) ^ 2 ≤ 1 + (d : ℝ) := by rw [imNorm_sq]; linarith
  have h2 : imNorm z ≤ Real.sqrt (1 + (d : ℝ)) := by
    rw [← Real.sqrt_sq (by linarith [one_le_imNorm z] : (0:ℝ) ≤ imNorm z)]
    exact Real.sqrt_le_sqrt h1
  have h3 : (imNorm z) ^ 3 ≤ (Real.sqrt (1 + (d : ℝ))) ^ 3 :=
    pow_le_pow_left₀ (by linarith [one_le_imNorm z]) h2 3
  have h4 : section5Kappa ρ z = (ρ / 8) / (imNorm z) ^ 3 := rfl
  have hkey : (imNorm z) ^ 3 / (ρ / 8) = 8 * (imNorm z) ^ 3 / ρ := by
    field_simp
  rw [h4, one_div_div, hkey]
  exact div_le_div_of_nonneg_right (by linarith) hρ.le

/-- The explicit constant bounding the Hörmander test integral. -/
noncomputable def hormanderConst (d : ℕ) (CLip ρ B : ℝ) : ℝ :=
  (d : ℝ) * B ^ 2 * (8 * (Real.sqrt (1 + (d : ℝ))) ^ 3 / ρ)
    * Real.exp ((2 * CLip + ρ) * Real.sqrt d + 20 * (d : ℝ) * Real.log 2)

/-- **Step (A)**: the integrand of Hörmander's hypothesis is bounded and compactly supported. -/
theorem lintegral_hormanderTest_le (hd : 1 ≤ d) {CLip ρ : ℝ} (hCLip : 0 ≤ CLip) (hρ : 0 < ρ)
    {B : ℝ} (hB : ∀ z : ℂᵈ, ‖fderiv ℝ (bumpC (d := d)) z‖ ≤ B)
    {u u0 : ℂᵈ → ℝ} (huzero : ∀ x : ℝᵈ, ‖x‖ ≤ 2 → u (toCpx x) = 0)
    (hulip : ∀ x₁ x₂ : ℝᵈ, |u (toCpx x₁) - u (toCpx x₂)| ≤ CLip * ‖x₁ - x₂‖)
    (hugrowth : ∀ z : ℂᵈ, u (toCpx (reVec z)) ≤ u z)
    (hu0zero : ∀ x : ℝᵈ, ‖x‖ ≤ 2 → u0 (toCpx x) = 0)
    (hu0lip : ∀ x₁ x₂ : ℝᵈ, |u0 (toCpx x₁) - u0 (toCpx x₂)| ≤ 1 * ‖x₁ - x₂‖)
    (hu0growth : ∀ z : ℂᵈ, u0 (toCpx (reVec z)) ≤ u0 z) :
    ∫⁻ z, ENNReal.ofReal (formNormSq (dbarFun (bumpC (d := d))) z
      * Real.exp (-(section5Phi ρ u u0 z)) / section5Kappa ρ z)
      ≤ ENNReal.ofReal (hormanderConst d CLip ρ B) * volume (Metric.closedBall (0 : ℂᵈ) 1) := by
  have hBnn : (0:ℝ) ≤ B := le_trans (norm_nonneg _) (hB 0)
  set C0 : ℝ := hormanderConst d CLip ρ B with hC0
  have hC0nn : (0:ℝ) ≤ C0 := by
    rw [hC0, hormanderConst]
    have : (0:ℝ) ≤ 8 * (Real.sqrt (1 + (d : ℝ))) ^ 3 / ρ := by positivity
    positivity
  have hpoint : ∀ z : ℂᵈ, formNormSq (dbarFun (bumpC (d := d))) z
      * Real.exp (-(section5Phi ρ u u0 z)) / section5Kappa ρ z ≤ C0 := by
    intro z
    rcases lt_or_ge ‖z‖ (1 / 2) with hz | hz
    · rw [formNormSq_eq_zero (dbarFun_bumpC_eq_zero_of_lt_half hz), zero_mul, zero_div]
      exact hC0nn
    · rcases le_or_gt ‖z‖ 1 with hz1 | hz1
      · have hη : formNormSq (dbarFun (bumpC (d := d))) z ≤ (d : ℝ) * B ^ 2 :=
          formNormSq_dbarFun_bumpC_le hB z
        have hlog2 : Real.log (1 / 2) = -Real.log 2 := by
          rw [one_div, Real.log_inv]
        have hphi := section5Phi_ge (d := d) hCLip hρ (by norm_num : (0:ℝ) < 1 / 2)
          huzero hulip hugrowth hu0zero hu0lip hu0growth z hz hz1
        rw [hlog2] at hphi
        have hexp : Real.exp (-(section5Phi ρ u u0 z))
            ≤ Real.exp ((2 * CLip + ρ) * Real.sqrt d + 20 * (d : ℝ) * Real.log 2) :=
          Real.exp_le_exp.mpr (by linarith)
        have hκ := one_div_section5Kappa_le (d := d) hρ hz1
        have hκpos : 0 < section5Kappa ρ z := section5Kappa_pos hρ z
        have hEnn : (0:ℝ) ≤ Real.exp ((2 * CLip + ρ) * Real.sqrt d
            + 20 * (d : ℝ) * Real.log 2) := (Real.exp_pos _).le
        rw [div_eq_mul_one_div]
        calc formNormSq (dbarFun (bumpC (d := d))) z
              * Real.exp (-(section5Phi ρ u u0 z)) * (1 / section5Kappa ρ z)
            ≤ ((d : ℝ) * B ^ 2) * Real.exp ((2 * CLip + ρ) * Real.sqrt d
                + 20 * (d : ℝ) * Real.log 2) * (8 * (Real.sqrt (1 + (d : ℝ))) ^ 3 / ρ) := by
              refine mul_le_mul ?_ hκ (le_of_lt (div_pos one_pos hκpos)) ?_
              · exact mul_le_mul hη hexp (Real.exp_pos _).le (by positivity)
              · exact mul_nonneg (by positivity) hEnn
          _ = C0 := by rw [hC0, hormanderConst]; ring
      · rw [formNormSq_eq_zero (dbarFun_bumpC_eq_zero_of_one_lt hz1), zero_mul, zero_div]
        exact hC0nn
  have hle1 : ∀ z : ℂᵈ, ENNReal.ofReal (formNormSq (dbarFun (bumpC (d := d))) z
        * Real.exp (-(section5Phi ρ u u0 z)) / section5Kappa ρ z)
      ≤ (Metric.closedBall (0 : ℂᵈ) 1).indicator (fun _ => ENNReal.ofReal C0) z := by
    intro z
    by_cases hz : z ∈ Metric.closedBall (0 : ℂᵈ) 1
    · rw [Set.indicator_of_mem hz]
      exact ENNReal.ofReal_le_ofReal (hpoint z)
    · have hz1 : (1 : ℝ) < ‖z‖ := by
        rw [Metric.mem_closedBall, dist_zero_right] at hz
        exact not_le.mp hz
      rw [Set.indicator_of_notMem hz,
        formNormSq_eq_zero (dbarFun_bumpC_eq_zero_of_one_lt (d := d) hz1), zero_mul, zero_div,
        ENNReal.ofReal_zero]
  calc ∫⁻ z, ENNReal.ofReal (formNormSq (dbarFun (bumpC (d := d))) z
        * Real.exp (-(section5Phi ρ u u0 z)) / section5Kappa ρ z)
      ≤ ∫⁻ z, (Metric.closedBall (0 : ℂᵈ) 1).indicator
          (fun _ => ENNReal.ofReal C0) z := lintegral_mono hle1
    _ = ∫⁻ z in Metric.closedBall (0 : ℂᵈ) 1, ENNReal.ofReal C0 :=
        lintegral_indicator measurableSet_closedBall _
    _ = ENNReal.ofReal C0 * volume (Metric.closedBall (0 : ℂᵈ) 1) := setLIntegral_const _ _
    _ = ENNReal.ofReal (hormanderConst d CLip ρ B) * volume (Metric.closedBall (0 : ℂᵈ) 1) := by
        rw [hC0]

end Submission.FUP

namespace Submission.FUP

/-! ### Step (B): applying Hörmander's theorem -/

lemma partialZbar_sub (j : Fin d) {f g : ℂᵈ → ℂ} {z : ℂᵈ} (hf : DifferentiableAt ℝ f z)
    (hg : DifferentiableAt ℝ g z) :
    partialZbar j (fun z => f z - g z) z = partialZbar j f z - partialZbar j g z := by
  have h : fderiv ℝ (fun z => f z - g z) z = fderiv ℝ f z - fderiv ℝ g z := fderiv_sub hf hg
  simp only [partialZbar, h, sub_apply]
  ring

/-- **Step (B)**: applying Hörmander's `∂̄` theorem to `η = ∂̄h` produces `g` and the entire
function `F = h - g` of §5. -/
theorem exists_F_of_hormander (hH : HormanderStatement (d := d)) (hd : 1 ≤ d)
    {CLip ρ : ℝ} (hCLip : 0 ≤ CLip) (hρ : 0 < ρ)
    {u u0 : ℂᵈ → ℝ} (hupsh : IsPSH u) (hu0psh : IsPSH u0)
    (huzero : ∀ x : ℝᵈ, ‖x‖ ≤ 2 → u (toCpx x) = 0)
    (hulip : ∀ x₁ x₂ : ℝᵈ, |u (toCpx x₁) - u (toCpx x₂)| ≤ CLip * ‖x₁ - x₂‖)
    (hugrowth : ∀ z : ℂᵈ, u (toCpx (reVec z)) ≤ u z ∧
      u z ≤ u (toCpx (reVec z)) + ρ * ‖imVec z‖)
    (hu0zero : ∀ x : ℝᵈ, ‖x‖ ≤ 2 → u0 (toCpx x) = 0)
    (hu0lip : ∀ x₁ x₂ : ℝᵈ, |u0 (toCpx x₁) - u0 (toCpx x₂)| ≤ 1 * ‖x₁ - x₂‖)
    (hu0growth : ∀ z : ℂᵈ, u0 (toCpx (reVec z)) ≤ u0 z ∧
      u0 z ≤ u0 (toCpx (reVec z)) + (1 / 2) * ‖imVec z‖) :
    ∃ (F g : ℂᵈ → ℂ), Differentiable ℂ F ∧
      (∀ z, F z = bumpC z - g z) ∧ ContDiff ℝ ∞ g ∧
      (∀ j : Fin d, (fun z => partialZbar j g z) = fun z => dbarFun (bumpC (d := d)) z j) ∧
      (∫⁻ z, ENNReal.ofReal (‖g z‖ ^ 2 * Real.exp (-(section5Phi ρ u u0 z)))
        ≤ ∫⁻ z, ENNReal.ofReal (formNormSq (dbarFun (bumpC (d := d))) z
            * Real.exp (-(section5Phi ρ u u0 z)) / section5Kappa ρ z)) := by
  have hpos : DbarDbarPos (section5Phi ρ u u0) (section5Kappa ρ) :=
    dbarDbarPos_section5Phi hd hCLip hρ hupsh hu0psh huzero hulip hugrowth hu0zero hu0lip
      hu0growth
  have hκpos : ∀ z : ℂᵈ, 0 < section5Kappa ρ z := fun z => section5Kappa_pos hρ z
  obtain ⟨B, hB⟩ := exists_bound_fderiv_bumpC (d := d)
  have hint := lintegral_hormanderTest_le (d := d) hd hCLip hρ hB huzero hulip
    (fun z => (hugrowth z).1) hu0zero hu0lip (fun z => (hu0growth z).1)
  have hint_lt : ∫⁻ z, ENNReal.ofReal (formNormSq (dbarFun (bumpC (d := d))) z
      * Real.exp (-(section5Phi ρ u u0 z)) / section5Kappa ρ z) < ⊤ :=
    lt_of_le_of_lt hint (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (isCompact_closedBall (0 : ℂᵈ) 1).measure_lt_top)
  obtain ⟨g, hgsm, hgpart, hgL2⟩ := hH (section5Phi ρ u u0) (section5Kappa ρ) hpos hκpos
    (dbarFun (bumpC (d := d))) dbarClosed_bumpC contDiff_dbarFun_bumpC hint_lt
  have hbump : Differentiable ℝ (bumpC (d := d)) := contDiff_bumpC.differentiable (by norm_num)
  have hgd : Differentiable ℝ g := hgsm.differentiable (by simp)
  refine ⟨fun z => bumpC z - g z, g, ?_, fun z => rfl, hgsm, hgpart, hgL2⟩
  refine Commons.Analysis.Complex.differentiable_complex_of_dbar_eq_zero (hbump.sub hgd) ?_
  intro j z
  have h1 : partialZbar j (fun z => bumpC z - g z) z = 0 := by
    rw [partialZbar_sub j (hbump z) (hgd z)]
    have hz := congrFun (hgpart j) z
    simp only [dbarFun] at hz
    rw [hz, sub_self]
  have h2 : partialZbar j (fun z => bumpC z - g z) z
      = (fderiv ℝ (fun z => bumpC z - g z) z (Pi.single j 1)
        + Complex.I * fderiv ℝ (fun z => bumpC z - g z) z (Pi.single j Complex.I)) / 2 := rfl
  rw [h2] at h1
  rcases div_eq_zero_iff.mp h1 with h | h
  · exact h
  · norm_num at h

end Submission.FUP

namespace Submission.FUP

/-! ### Step (C): pointwise bounds from the weighted `L²` estimate -/

/-- **Pointwise bound from the mean value inequality.**  If `f` is analytic on a polydisc
`P(z,r)` on which the §5 weight satisfies `φ ≤ B`, then
`|f(z)|² ≤ (πr²)^{-d} e^B ∫_{P(z,r)} |f|² e^{-φ}`. -/
lemma ofReal_norm_sq_le_of_analyticOnNhd {ρ : ℝ} {u u0 : ℂᵈ → ℝ} {f : ℂᵈ → ℂ} {z : ℂᵈ}
    {r B : ℝ} (hr : 0 < r) (hf : AnalyticOnNhd ℂ f (Metric.closedBall z r))
    (hB : ∀ w ∈ Metric.closedBall z r, section5Phi ρ u u0 w ≤ B) :
    ENNReal.ofReal (‖f z‖ ^ 2) ≤
      ENNReal.ofReal (((Real.pi * r ^ 2) ^ d)⁻¹ * Real.exp B) *
        ∫⁻ w in Metric.closedBall z r,
          ENNReal.ofReal (‖f w‖ ^ 2 * Real.exp (-(section5Phi ρ u u0 w))) := by
  have hvol : (volume (Metric.closedBall z r)).toReal = (Real.pi * r ^ 2) ^ d :=
    Commons.Analysis.Complex.polydisc_volume z hr
  have hcont : ContinuousOn f (Metric.closedBall z r) := hf.continuousOn
  have hmeas : AEStronglyMeasurable (fun w : ℂᵈ => ‖f w‖ ^ 2)
      (volume.restrict (Metric.closedBall z r)) :=
    ((hcont.aestronglyMeasurable measurableSet_closedBall).norm).pow 2
  have hint : ∫ w in Metric.closedBall z r, ‖f w‖ ^ 2
      = (∫⁻ w in Metric.closedBall z r, ENNReal.ofReal (‖f w‖ ^ 2)).toReal :=
    MeasureTheory.integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall (fun w => sq_nonneg _)) hmeas
  have hmv := Commons.Analysis.Complex.meanValue_polydisc (d := d) hr hf
  rw [hvol] at hmv
  have hstep1 : ENNReal.ofReal (‖f z‖ ^ 2)
      ≤ ENNReal.ofReal (((Real.pi * r ^ 2) ^ d)⁻¹)
        * (∫⁻ w in Metric.closedBall z r, ENNReal.ofReal (‖f w‖ ^ 2)) := by
    calc ENNReal.ofReal (‖f z‖ ^ 2)
        ≤ ENNReal.ofReal (((Real.pi * r ^ 2) ^ d)⁻¹
            * ∫ w in Metric.closedBall z r, ‖f w‖ ^ 2) := ENNReal.ofReal_le_ofReal hmv
      _ = ENNReal.ofReal (((Real.pi * r ^ 2) ^ d)⁻¹)
            * ENNReal.ofReal (∫ w in Metric.closedBall z r, ‖f w‖ ^ 2) :=
          ENNReal.ofReal_mul (by positivity)
      _ = ENNReal.ofReal (((Real.pi * r ^ 2) ^ d)⁻¹)
            * ENNReal.ofReal ((∫⁻ w in Metric.closedBall z r,
                ENNReal.ofReal (‖f w‖ ^ 2)).toReal) := by rw [hint]
      _ ≤ ENNReal.ofReal (((Real.pi * r ^ 2) ^ d)⁻¹)
            * (∫⁻ w in Metric.closedBall z r, ENNReal.ofReal (‖f w‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left ENNReal.ofReal_toReal_le (bot_le)
  have hstep2 : (∫⁻ w in Metric.closedBall z r, ENNReal.ofReal (‖f w‖ ^ 2))
      ≤ ENNReal.ofReal (Real.exp B)
        * (∫⁻ w in Metric.closedBall z r,
            ENNReal.ofReal (‖f w‖ ^ 2 * Real.exp (-(section5Phi ρ u u0 w)))) := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_closedBall] with w hw
    have hφw : section5Phi ρ u u0 w ≤ B := hB w hw
    calc ENNReal.ofReal (‖f w‖ ^ 2)
        = ENNReal.ofReal (‖f w‖ ^ 2 * Real.exp (-(section5Phi ρ u u0 w)))
            * ENNReal.ofReal (Real.exp (section5Phi ρ u u0 w)) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          congr 1
          rw [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
      _ ≤ ENNReal.ofReal (‖f w‖ ^ 2 * Real.exp (-(section5Phi ρ u u0 w)))
            * ENNReal.ofReal (Real.exp B) :=
          mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr hφw))
            (bot_le)
      _ = ENNReal.ofReal (Real.exp B)
            * ENNReal.ofReal (‖f w‖ ^ 2 * Real.exp (-(section5Phi ρ u u0 w))) := by ring
  calc ENNReal.ofReal (‖f z‖ ^ 2)
      ≤ ENNReal.ofReal (((Real.pi * r ^ 2) ^ d)⁻¹)
          * (∫⁻ w in Metric.closedBall z r, ENNReal.ofReal (‖f w‖ ^ 2)) := hstep1
    _ ≤ ENNReal.ofReal (((Real.pi * r ^ 2) ^ d)⁻¹)
          * (ENNReal.ofReal (Real.exp B)
            * (∫⁻ w in Metric.closedBall z r,
                ENNReal.ofReal (‖f w‖ ^ 2 * Real.exp (-(section5Phi ρ u u0 w))))) :=
          mul_le_mul_of_nonneg_left hstep2 (bot_le)
    _ = ENNReal.ofReal (((Real.pi * r ^ 2) ^ d)⁻¹ * Real.exp B)
          * (∫⁻ w in Metric.closedBall z r,
              ENNReal.ofReal (‖f w‖ ^ 2 * Real.exp (-(section5Phi ρ u u0 w)))) := by
          rw [ENNReal.ofReal_mul (by positivity)]; ring

end Submission.FUP

namespace Submission.FUP

/-! ### The weight bounds used in the estimates -/

/-- The set `{|z| ≥ 1/8}` on which `|F|²e^{-φ}` is integrable. -/
def U5 : Set ℂᵈ := {z | 1 / 8 ≤ ‖z‖}

lemma isClosed_U5 : IsClosed (U5 (d := d)) := isClosed_Ici.preimage continuous_norm
lemma measurableSet_U5 : MeasurableSet (U5 (d := d)) := isClosed_U5.measurableSet
lemma mem_U5 {z : ℂᵈ} : z ∈ U5 ↔ 1 / 8 ≤ ‖z‖ := Iff.rfl

lemma norm_bumpC_le_one (z : ℂᵈ) : ‖bumpC (d := d) z‖ ≤ 1 := by
  have h0 : (0:ℝ) ≤ (unitBump (d := d) z : ℝ) :=
    ContDiffBump.nonneg (unitBump (d := d)) (x := z)
  have h1 : (unitBump (d := d) z : ℝ) ≤ 1 :=
    ContDiffBump.le_one (unitBump (d := d)) (x := z)
  have hn : ‖bumpC (d := d) z‖ ^ 2 = ((unitBump (d := d) z : ℝ)) ^ 2 := by
    rw [bumpC, ← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal, sq]
  nlinarith [norm_nonneg (bumpC (d := d) z)]

/-- On the annulus `1/8 ≤ ‖z‖ ≤ 1` the exponential of the §5 weight is bounded. -/
lemma exp_neg_section5Phi_le {CLip ρ : ℝ} (hCLip : 0 ≤ CLip) (hρ : 0 < ρ)
    {u u0 : ℂᵈ → ℝ} (huzero : ∀ x : ℝᵈ, ‖x‖ ≤ 2 → u (toCpx x) = 0)
    (hulip : ∀ x₁ x₂ : ℝᵈ, |u (toCpx x₁) - u (toCpx x₂)| ≤ CLip * ‖x₁ - x₂‖)
    (hugrowth : ∀ z : ℂᵈ, u (toCpx (reVec z)) ≤ u z)
    (hu0zero : ∀ x : ℝᵈ, ‖x‖ ≤ 2 → u0 (toCpx x) = 0)
    (hu0lip : ∀ x₁ x₂ : ℝᵈ, |u0 (toCpx x₁) - u0 (toCpx x₂)| ≤ 1 * ‖x₁ - x₂‖)
    (hu0growth : ∀ z : ℂᵈ, u0 (toCpx (reVec z)) ≤ u0 z) {z : ℂᵈ}
    (hz : 1 / 8 ≤ ‖z‖) (hz1 : ‖z‖ ≤ 1) :
    Real.exp (-(section5Phi ρ u u0 z))
      ≤ Real.exp ((2 * CLip + ρ) * Real.sqrt d + 20 * (d : ℝ) * Real.log 8) := by
  have hlog : Real.log (1 / 8 : ℝ) = -Real.log 8 := by rw [one_div, Real.log_inv]
  have h := section5Phi_ge (d := d) hCLip hρ (by norm_num : (0:ℝ) < 1 / 8)
    huzero hulip hugrowth hu0zero hu0lip hu0growth z hz hz1
  rw [hlog] at h
  rw [Real.exp_le_exp]
  linarith

/-- The exponent bounding `e^{-φ}` on the annulus `1/8 ≤ ‖z‖ ≤ 1`. -/
noncomputable def Bann (d : ℕ) (CLip ρ : ℝ) : ℝ :=
  (2 * CLip + ρ) * Real.sqrt d + 20 * (d : ℝ) * Real.log 8

/-- **Finiteness of `∫_{|z| ≥ 1/8} |F|² e^{-φ}`** where `F = h - g`. -/
lemma lintegral_F_U5_le {CLip ρ : ℝ} (hCLip : 0 ≤ CLip) (hρ : 0 < ρ)
    {L : ℝ≥0∞}
    {u u0 : ℂᵈ → ℝ} {F g : ℂᵈ → ℂ}
    (huzero : ∀ x : ℝᵈ, ‖x‖ ≤ 2 → u (toCpx x) = 0)
    (hulip : ∀ x₁ x₂ : ℝᵈ, |u (toCpx x₁) - u (toCpx x₂)| ≤ CLip * ‖x₁ - x₂‖)
    (hugrowth : ∀ z : ℂᵈ, u (toCpx (reVec z)) ≤ u z)
    (hu0zero : ∀ x : ℝᵈ, ‖x‖ ≤ 2 → u0 (toCpx x) = 0)
    (hu0lip : ∀ x₁ x₂ : ℝᵈ, |u0 (toCpx x₁) - u0 (toCpx x₂)| ≤ 1 * ‖x₁ - x₂‖)
    (hu0growth : ∀ z : ℂᵈ, u0 (toCpx (reVec z)) ≤ u0 z)
    (hFeq : ∀ z, F z = bumpC (d := d) z - g z)
    (hg : ∫⁻ z, ENNReal.ofReal (‖g z‖ ^ 2 * Real.exp (-(section5Phi ρ u u0 z))) ≤ L) :
    ∫⁻ z in U5, ENNReal.ofReal (‖F z‖ ^ 2 * Real.exp (-(section5Phi ρ u u0 z)))
      ≤ 2 * (ENNReal.ofReal (Real.exp (Bann d CLip ρ))
          * volume (U5 ∩ Metric.closedBall (0 : ℂᵈ) 1)) + 2 * L := by
  set B8 : ℝ := Bann d CLip ρ with hB8
  set cst : ℝ≥0∞ := ENNReal.ofReal (Real.exp B8) with hcst
  set cand : ℂᵈ → ℝ≥0∞ := (Metric.closedBall (0 : ℂᵈ) 1).indicator (fun _ => cst) with hcand
  have hbump : ∀ z ∈ U5, ENNReal.ofReal (‖bumpC (d := d) z‖ ^ 2
      * Real.exp (-(section5Phi ρ u u0 z))) ≤ cand z := by
    intro z hz
    by_cases hz2 : z ∈ Metric.closedBall (0 : ℂᵈ) 1
    · rw [hcand, Set.indicator_of_mem hz2]
      have hz1 : ‖z‖ ≤ 1 := by
        rw [Metric.mem_closedBall, dist_zero_right] at hz2; exact hz2
      have hb : ‖bumpC (d := d) z‖ ^ 2 ≤ 1 := by
        nlinarith [norm_bumpC_le_one (d := d) z, norm_nonneg (bumpC (d := d) z)]
      have hexp : Real.exp (-(section5Phi ρ u u0 z)) ≤ Real.exp B8 := by
        rw [hB8, Bann]
        exact exp_neg_section5Phi_le (d := d) hCLip hρ huzero hulip hugrowth hu0zero hu0lip
          hu0growth (mem_U5.mp hz) hz1
      calc ENNReal.ofReal (‖bumpC (d := d) z‖ ^ 2 * Real.exp (-(section5Phi ρ u u0 z)))
          ≤ ENNReal.ofReal (1 * Real.exp B8) :=
            ENNReal.ofReal_le_ofReal (mul_le_mul hb hexp (Real.exp_pos _).le (by norm_num))
        _ = cst := by rw [hcst, one_mul]
    · rw [hcand, Set.indicator_of_notMem hz2]
      have hz1 : (1 : ℝ) < ‖z‖ := by
        rw [Metric.mem_closedBall, dist_zero_right, not_le] at hz2; exact hz2
      rw [bumpC_eq_zero_of_one_lt (d := d) hz1]
      simp
  have hpt : ∀ᵐ z ∂(volume.restrict (U5 (d := d))),
      ENNReal.ofReal (‖F z‖ ^ 2 * Real.exp (-(section5Phi ρ u u0 z)))
        ≤ 2 * cand z + 2 * ENNReal.ofReal (‖g z‖ ^ 2 * Real.exp (-(section5Phi ρ u u0 z))) := by
    filter_upwards [ae_restrict_mem measurableSet_U5] with z hz
    have hb1 : ‖bumpC (d := d) z - g z‖ ≤ ‖bumpC (d := d) z‖ + ‖g z‖ := norm_sub_le _ _
    have hb2 : (‖bumpC (d := d) z‖ + ‖g z‖) ^ 2
        ≤ 2 * ‖bumpC (d := d) z‖ ^ 2 + 2 * ‖g z‖ ^ 2 := by
      nlinarith [sq_nonneg (‖bumpC (d := d) z‖ - ‖g z‖)]
    have hb3 : ‖bumpC (d := d) z - g z‖ ^ 2 ≤ (‖bumpC (d := d) z‖ + ‖g z‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hb1 2
    have hn : ‖F z‖ ^ 2 ≤ 2 * ‖bumpC (d := d) z‖ ^ 2 + 2 * ‖g z‖ ^ 2 := by
      rw [hFeq z]
      linarith [hb2, hb3]
    have h1 : ‖F z‖ ^ 2 * Real.exp (-(section5Phi ρ u u0 z))
        ≤ 2 * (‖bumpC (d := d) z‖ ^ 2 * Real.exp (-(section5Phi ρ u u0 z)))
          + 2 * (‖g z‖ ^ 2 * Real.exp (-(section5Phi ρ u u0 z))) := by
      nlinarith [Real.exp_pos (-(section5Phi ρ u u0 z))]
    calc ENNReal.ofReal (‖F z‖ ^ 2 * Real.exp (-(section5Phi ρ u u0 z)))
        ≤ ENNReal.ofReal (2 * (‖bumpC (d := d) z‖ ^ 2 * Real.exp (-(section5Phi ρ u u0 z)))
            + 2 * (‖g z‖ ^ 2 * Real.exp (-(section5Phi ρ u u0 z)))) :=
          ENNReal.ofReal_le_ofReal h1
      _ = 2 * ENNReal.ofReal (‖bumpC (d := d) z‖ ^ 2 * Real.exp (-(section5Phi ρ u u0 z)))
            + 2 * ENNReal.ofReal (‖g z‖ ^ 2 * Real.exp (-(section5Phi ρ u u0 z))) := by
          rw [ENNReal.ofReal_add (by positivity) (by positivity),
            ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2),
            ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2), ENNReal.ofReal_ofNat]
      _ ≤ 2 * cand z + 2 * ENNReal.ofReal (‖g z‖ ^ 2 * Real.exp (-(section5Phi ρ u u0 z))) :=
          add_le_add (mul_le_mul_of_nonneg_left (hbump z hz) (bot_le : (0:ℝ≥0∞) ≤ 2)) le_rfl
  have hcand_int : ∫⁻ z in U5, cand z
      = cst * volume (U5 ∩ Metric.closedBall (0 : ℂᵈ) 1) := by
    rw [hcand]
    rw [show ∫⁻ z in U5, (Metric.closedBall (0 : ℂᵈ) 1).indicator (fun _ => cst) z
        = ∫⁻ z in U5 ∩ Metric.closedBall (0 : ℂᵈ) 1, cst from by
      rw [← lintegral_indicator measurableSet_U5, Set.indicator_indicator]
      exact lintegral_indicator (measurableSet_U5.inter measurableSet_closedBall) _]
    rw [setLIntegral_const]
  have hmeas_cand : AEMeasurable (fun z => 2 * cand z) (volume.restrict (U5 (d := d))) := by
    rw [hcand]
    exact ((Measurable.const_mul (Measurable.indicator measurable_const measurableSet_closedBall) 2)).aemeasurable
  have hg' : ∫⁻ z in U5, ENNReal.ofReal (‖g z‖ ^ 2 * Real.exp (-(section5Phi ρ u u0 z))) ≤ L :=
    le_trans (setLIntegral_le_lintegral _ _) hg
  calc ∫⁻ z in U5, ENNReal.ofReal (‖F z‖ ^ 2 * Real.exp (-(section5Phi ρ u u0 z)))
      ≤ ∫⁻ z in U5, (2 * cand z
          + 2 * ENNReal.ofReal (‖g z‖ ^ 2 * Real.exp (-(section5Phi ρ u u0 z)))) :=
        lintegral_mono_ae hpt
    _ = 2 * (∫⁻ z in U5, cand z)
        + 2 * (∫⁻ z in U5, ENNReal.ofReal (‖g z‖ ^ 2 * Real.exp (-(section5Phi ρ u u0 z)))) := by
        rw [lintegral_add_left' hmeas_cand, lintegral_const_mul' 2 _ (by norm_num),
          lintegral_const_mul' 2 _ (by norm_num)]
    _ = 2 * (cst * volume (U5 ∩ Metric.closedBall (0 : ℂᵈ) 1))
        + 2 * (∫⁻ z in U5, ENNReal.ofReal (‖g z‖ ^ 2 * Real.exp (-(section5Phi ρ u u0 z)))) := by
        rw [hcand_int]
    _ ≤ 2 * (ENNReal.ofReal (Real.exp (Bann d CLip ρ))
          * volume (U5 ∩ Metric.closedBall (0 : ℂᵈ) 1)) + 2 * L := by
        rw [hcst, hB8]
        exact add_le_add_right (mul_le_mul_of_nonneg_left hg' (bot_le : (0:ℝ≥0∞) ≤ 2)) _

end Submission.FUP
