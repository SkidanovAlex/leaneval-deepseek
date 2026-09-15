import Submission.FUP.LogWeight
import Submission.FUP.AuxWeight2
import Submission.FUP.DbarBump
import Submission.FUP.Hormander
import Submission.FUP.PSHWeight
import Submission.Commons.Analysis.Complex.meanValue_polydisc


import Submission.Commons.Measure.Real.integrableOn_log_rpow_decay

open FractalUncertainty MeasureTheory FourierTransform Metric Filter Set
open scoped ENNReal BigOperators Topology

set_option autoImplicit false
variable {d : ℕ}
local notation "ℝᵈ" => EuclideanSpace ℝ (Fin d)
local notation "ℂᵈ" => (Fin d → ℂ)

/-!
# §5 of Cohen's paper: from plurisubharmonic weights to bounded Fourier transforms

This module formalises `prop:psh_to_bounded_fourier` (Cohen, §5, after Bourgain).  Given a
plurisubharmonic `u : ℂᵈ → ℝ` with

* `u ≤ 0` on `ℝᵈ`, `u = 0` on `B₂`,
* `u` Lipschitz with constant `CLip` on `ℝᵈ`,
* `u(x) ≤ u(x+iy) ≤ u(x) + ρ|y|`,

it constructs an entire function `F` with `|F(z)| ≤ A e^{2ρ|Im z|}`, `|F| ≥ 1/2` near the origin,
`|F(x)| ≤ C e^{u(x)}` on `ℝᵈ` and `F|_ℝᵈ ∈ L²`.

The construction is Cohen's: with the auxiliary weight `u₀` of §5 (`AuxWeight2`), the logarithmic
weight `Λ` (`LogWeight`), the strictly plurisubharmonic weight
`(ρ/2)(⟨Im z⟩-1)` (`PshWeights`) and the bump `h` of `DbarBump`, one sets

  `φ = 2u + Λ + ρu₀ + (ρ/2)(⟨Im z⟩-1)`,   `κ = (ρ/8)⟨Im z⟩^{-3}`,

applies Hörmander's `∂̄` theorem to `η = ∂̄h` and takes `F = h - g`.  All the estimates are
gathered in this file.
-/

namespace Submission.FUP

/-! ### Elementary norm estimates on `ℂᵈ` -/

lemma norm_reVec_le (z : ℂᵈ) : ‖reVec z‖ ≤ Real.sqrt (d : ℝ) * ‖z‖ := by
  have h1 : ‖reVec z‖ ^ 2 = ∑ j, (z j).re ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [reVec_apply, Real.norm_eq_abs, sq_abs]
  have h2 : ∑ j, (z j).re ^ 2 ≤ ∑ j, ‖z j‖ ^ 2 :=
    Finset.sum_le_sum fun j _ => by
      have h := Complex.sq_norm (z j)
      rw [Complex.normSq_apply] at h
      nlinarith [sq_nonneg (z j).im]
  have h3 : ∑ j, ‖z j‖ ^ 2 ≤ (d : ℝ) * ‖z‖ ^ 2 := by
    calc ∑ j : Fin d, ‖z j‖ ^ 2 ≤ ∑ _j : Fin d, ‖z‖ ^ 2 :=
          Finset.sum_le_sum fun j _ => by
            have h := norm_le_pi_norm z j
            nlinarith [norm_nonneg (z j), norm_nonneg z]
      _ = (d : ℝ) * ‖z‖ ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have h4 : ‖reVec z‖ ^ 2 ≤ (Real.sqrt (d : ℝ) * ‖z‖) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg d)]
    rw [h1]; linarith
  calc ‖reVec z‖ = Real.sqrt (‖reVec z‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt ((Real.sqrt (d : ℝ) * ‖z‖) ^ 2) := Real.sqrt_le_sqrt h4
    _ = Real.sqrt (d : ℝ) * ‖z‖ := Real.sqrt_sq (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))

lemma norm_imVec_le (z : ℂᵈ) : ‖imVec z‖ ≤ Real.sqrt (d : ℝ) * ‖z‖ := by
  have h1 : ‖imVec z‖ ^ 2 = ∑ j, (z j).im ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [imVec_apply, Real.norm_eq_abs, sq_abs]
  have h2 : ∑ j, (z j).im ^ 2 ≤ ∑ j, ‖z j‖ ^ 2 :=
    Finset.sum_le_sum fun j _ => by
      have h := Complex.sq_norm (z j)
      rw [Complex.normSq_apply] at h
      nlinarith [sq_nonneg (z j).re]
  have h3 : ∑ j, ‖z j‖ ^ 2 ≤ (d : ℝ) * ‖z‖ ^ 2 := by
    calc ∑ j : Fin d, ‖z j‖ ^ 2 ≤ ∑ _j : Fin d, ‖z‖ ^ 2 :=
          Finset.sum_le_sum fun j _ => by
            have h := norm_le_pi_norm z j
            nlinarith [norm_nonneg (z j), norm_nonneg z]
      _ = (d : ℝ) * ‖z‖ ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have h4 : ‖imVec z‖ ^ 2 ≤ (Real.sqrt (d : ℝ) * ‖z‖) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg d)]
    rw [h1]; linarith
  calc ‖imVec z‖ = Real.sqrt (‖imVec z‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt ((Real.sqrt (d : ℝ) * ‖z‖) ^ 2) := Real.sqrt_le_sqrt h4
    _ = Real.sqrt (d : ℝ) * ‖z‖ := Real.sqrt_sq (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))

/-! ### The §5 weight and its Hörmander curvature -/

/-- The weight `φ = 2u + Λ + ρu₀ + (ρ/2)(⟨Im z⟩-1)` of §5. -/
noncomputable def section5Phi (ρ : ℝ) (u u0 : ℂᵈ → ℝ) (z : ℂᵈ) : ℝ :=
  2 * u z + logWeight z + ρ * u0 z + (ρ / 2) * (imNorm z - 1)

/-- The curvature `κ = (ρ/8)⟨Im z⟩^{-3}` of §5. -/
noncomputable def section5Kappa (ρ : ℝ) (z : ℂᵈ) : ℝ :=
  (ρ / 8) / (imNorm z) ^ 3

lemma section5Kappa_pos {ρ : ℝ} (hρ : 0 < ρ) (z : ℂᵈ) : 0 < section5Kappa ρ z := by
  rw [section5Kappa]
  exact div_pos (by linarith : (0:ℝ) < ρ / 8) (pow_pos (imNorm_pos z) 3)

lemma imNorm_sq (z : ℂᵈ) : (imNorm z) ^ 2 = 1 + ∑ j, (z j).im ^ 2 := by
  rw [imNorm, Real.sq_sqrt (by positivity)]

lemma one_le_imNorm_sq (z : ℂᵈ) : 1 ≤ (imNorm z) ^ 2 := by
  rw [imNorm_sq]
  have h : 0 ≤ ∑ j : Fin d, (z j).im ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
  linarith

/-- Boundedness on balls from the §5 hypotheses on a weight. -/
lemma boundedOnCompact_of_hyp {v : ℂᵈ → ℝ} {C ρv : ℝ} (hC : 0 ≤ C) (hρv : 0 ≤ ρv)
    (h0 : ∀ x : ℝᵈ, ‖x‖ ≤ 2 → v (toCpx x) = 0)
    (hlip : ∀ x₁ x₂ : ℝᵈ, |v (toCpx x₁) - v (toCpx x₂)| ≤ C * ‖x₁ - x₂‖)
    (hg : ∀ z : ℂᵈ, v (toCpx (reVec z)) ≤ v z ∧ v z ≤ v (toCpx (reVec z)) + ρv * ‖imVec z‖) :
    BoundedOnCompact v := by
  have hbound : ∀ x : ℝᵈ, |v (toCpx x)| ≤ C * ‖x‖ := by
    intro x
    have h := hlip x 0
    simp only [sub_zero] at h
    rw [h0 0 (by simp)] at h
    simpa using h
  intro R
  refine ⟨(C + ρv) * Real.sqrt (d : ℝ) * max R 0, fun z hz => ?_⟩
  have hR : (0:ℝ) ≤ max R 0 := le_max_right _ _
  have hd : (0:ℝ) ≤ Real.sqrt (d : ℝ) := Real.sqrt_nonneg _
  have hz' : ‖z‖ ≤ max R 0 := le_trans hz (le_max_left _ _)
  obtain ⟨hg1, hg2⟩ := hg z
  have h1 : -(Real.sqrt (d : ℝ) * ‖z‖) ≤ ‖reVec z‖ := by
    have h2 : (0:ℝ) ≤ ‖reVec z‖ := norm_nonneg _
    linarith [norm_reVec_le z]
  have hlow : -((C + ρv) * Real.sqrt (d : ℝ) * max R 0) ≤ v z := by
    have h3 : -(C * ‖reVec z‖) ≤ v (toCpx (reVec z)) := by
      have hb := hbound (reVec z)
      linarith [neg_abs_le (v (toCpx (reVec z)))]
    have h4 : C * ‖reVec z‖ ≤ C * (Real.sqrt (d : ℝ) * ‖z‖) :=
      mul_le_mul_of_nonneg_left (norm_reVec_le z) hC
    have h5 : Real.sqrt (d : ℝ) * ‖z‖ ≤ Real.sqrt (d : ℝ) * max R 0 :=
      mul_le_mul_of_nonneg_left hz' hd
    have h6 : ρv * ‖imVec z‖ ≤ ρv * (Real.sqrt (d : ℝ) * max R 0) := by
      refine mul_le_mul (le_refl ρv) ?_ (norm_nonneg _) hρv
      exact le_trans (norm_imVec_le z) (mul_le_mul_of_nonneg_left hz' hd)
    nlinarith [hlip, h3, h4, h5, h6, hg1, hg2, hC, hρv, hR, hd]
  have hup : v z ≤ (C + ρv) * Real.sqrt (d : ℝ) * max R 0 := by
    have h3 : v (toCpx (reVec z)) ≤ C * ‖reVec z‖ :=
      le_trans (le_abs_self _) (hbound (reVec z))
    have h4 : C * ‖reVec z‖ ≤ C * (Real.sqrt (d : ℝ) * ‖z‖) :=
      mul_le_mul_of_nonneg_left (norm_reVec_le z) hC
    have h5 : Real.sqrt (d : ℝ) * ‖z‖ ≤ Real.sqrt (d : ℝ) * max R 0 :=
      mul_le_mul_of_nonneg_left hz' hd
    have h6 : ρv * ‖imVec z‖ ≤ ρv * (Real.sqrt (d : ℝ) * max R 0) := by
      refine mul_le_mul (le_refl ρv) ?_ (norm_nonneg _) hρv
      exact le_trans (norm_imVec_le z) (mul_le_mul_of_nonneg_left hz' hd)
    nlinarith [h3, h4, h5, h6, hg2, hC, hρv, hR, hd]
  rw [abs_le]
  exact ⟨hlow, hup⟩

/-- **`∂∂̄ φ ≥ κ`** for the §5 weight. -/
theorem dbarDbarPos_section5Phi (hd : 1 ≤ d) {CLip ρ : ℝ} (hCLip : 0 ≤ CLip) (hρ : 0 < ρ)
    {u u0 : ℂᵈ → ℝ} (hupsh : IsPSH u) (hu0psh : IsPSH u0)
    (huzero : ∀ x : ℝᵈ, ‖x‖ ≤ 2 → u (toCpx x) = 0)
    (hulip : ∀ x₁ x₂ : ℝᵈ, |u (toCpx x₁) - u (toCpx x₂)| ≤ CLip * ‖x₁ - x₂‖)
    (hugrowth : ∀ z : ℂᵈ, u (toCpx (reVec z)) ≤ u z ∧
      u z ≤ u (toCpx (reVec z)) + ρ * ‖imVec z‖)
    (hu0zero : ∀ x : ℝᵈ, ‖x‖ ≤ 2 → u0 (toCpx x) = 0)
    (hu0lip : ∀ x₁ x₂ : ℝᵈ, |u0 (toCpx x₁) - u0 (toCpx x₂)| ≤ 1 * ‖x₁ - x₂‖)
    (hu0growth : ∀ z : ℂᵈ, u0 (toCpx (reVec z)) ≤ u0 z ∧
      u0 z ≤ u0 (toCpx (reVec z)) + (1 / 2) * ‖imVec z‖) :
    DbarDbarPos (section5Phi ρ u u0) (section5Kappa ρ) := by
  have hbdd : BoundedOnCompact u :=
    boundedOnCompact_of_hyp hCLip hρ.le huzero hulip hugrowth
  have hbdd0 : BoundedOnCompact u0 :=
    boundedOnCompact_of_hyp zero_le_one (by norm_num) hu0zero hu0lip hu0growth
  have h1 : DbarDbarPos (fun z => 2 * u z) (fun _ : ℂᵈ => (0:ℝ)) :=
    isPSH_dbarDbarPos (hupsh.const_mul (by norm_num)) (hbdd.const_mul 2)
      (by simpa only [mul_comm] using hupsh.1.measurable.const_mul (2:ℝ))
  have h2 : DbarDbarPos (logWeight (d := d)) (fun _ : ℂᵈ => (0:ℝ)) :=
    dbarDbarPos_logWeight (d := d) hd
  have h3 : DbarDbarPos (fun z => ρ * u0 z) (fun _ : ℂᵈ => (0:ℝ)) :=
    isPSH_dbarDbarPos (hu0psh.const_mul hρ.le) (hbdd0.const_mul ρ)
      (by simpa only [mul_comm] using hu0psh.1.measurable.const_mul ρ)
  have h4 : DbarDbarPos (fun z => (ρ / 2) * (imNorm z - 1))
      (fun z => (ρ / 8) / (imNorm z) ^ 3) := dbarDbarPos_imWeight (d := d) ρ hρ
  have h := ((h1.add h2).add h3).add h4
  convert h using 1 <;> funext z <;> simp only [section5Phi, section5Kappa, Pi.add_apply] <;> ring

/-! ### Upper bounds for the weight `φ` -/

lemma sum_sq_eq_norm_sq (z : ℂᵈ) :
    ∑ j, ‖z j‖ ^ 2 = ‖reVec z‖ ^ 2 + ‖imVec z‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [reVec_apply, imVec_apply, Real.norm_eq_abs, sq_abs]
  rw [Complex.sq_norm, Complex.normSq_apply]; ring

lemma logWeight_le (z : ℂᵈ) :
    logWeight z ≤ 20 * (d : ℝ) * Real.log (1 + ‖reVec z‖)
      + 20 * (d : ℝ) * Real.log (1 + ‖imVec z‖) := by
  have h1 : ∑ j, ‖z j‖ ^ 2 ≤ (1 + ‖reVec z‖ + ‖imVec z‖) ^ 2 := by
    rw [sum_sq_eq_norm_sq]
    nlinarith [norm_nonneg (reVec z), norm_nonneg (imVec z)]
  have h2 : (0:ℝ) < 1 + ‖reVec z‖ + ‖imVec z‖ := by positivity
  have hbig : 1 ≤ (1 + ‖reVec z‖ + ‖imVec z‖) ^ 2 := by
    nlinarith [norm_nonneg (reVec z), norm_nonneg (imVec z)]
  have h3 : Real.log (∑ j, ‖z j‖ ^ 2) ≤ Real.log ((1 + ‖reVec z‖ + ‖imVec z‖) ^ 2) := by
    rcases eq_or_lt_of_le (sum_sq_nonneg z) with h0 | h0
    · rw [← h0, Real.log_zero]
      exact Real.log_nonneg hbig
    · exact Real.log_le_log h0 h1
  have h4 : Real.log ((1 + ‖reVec z‖ + ‖imVec z‖) ^ 2)
      = 2 * Real.log (1 + ‖reVec z‖ + ‖imVec z‖) := by
    rw [Real.log_pow]; push_cast; ring
  have hx : (0:ℝ) < 1 + ‖reVec z‖ := by positivity
  have hy : (0:ℝ) < 1 + ‖imVec z‖ := by positivity
  have h5 : Real.log (1 + ‖reVec z‖ + ‖imVec z‖)
      ≤ Real.log (1 + ‖reVec z‖) + Real.log (1 + ‖imVec z‖) := by
    have hxy : 1 + ‖reVec z‖ + ‖imVec z‖ ≤ (1 + ‖reVec z‖) * (1 + ‖imVec z‖) := by
      nlinarith [norm_nonneg (reVec z), norm_nonneg (imVec z)]
    calc Real.log (1 + ‖reVec z‖ + ‖imVec z‖)
        ≤ Real.log ((1 + ‖reVec z‖) * (1 + ‖imVec z‖)) :=
          Real.log_le_log (by positivity) hxy
      _ = Real.log (1 + ‖reVec z‖) + Real.log (1 + ‖imVec z‖) := Real.log_mul hx.ne' hy.ne'
  have hlog : Real.log (∑ j, ‖z j‖ ^ 2)
      ≤ 2 * (Real.log (1 + ‖reVec z‖) + Real.log (1 + ‖imVec z‖)) := by linarith
  calc logWeight z = 10 * (d : ℝ) * Real.log (∑ j, ‖z j‖ ^ 2) := rfl
    _ ≤ 10 * (d : ℝ) * (2 * (Real.log (1 + ‖reVec z‖) + Real.log (1 + ‖imVec z‖))) :=
        mul_le_mul_of_nonneg_left hlog (by positivity)
    _ = 20 * (d : ℝ) * Real.log (1 + ‖reVec z‖)
        + 20 * (d : ℝ) * Real.log (1 + ‖imVec z‖) := by ring

lemma imNorm_sub_one_le (z : ℂᵈ) : imNorm z - 1 ≤ ‖imVec z‖ := by
  have h1 : (imNorm z) ^ 2 = 1 + ‖imVec z‖ ^ 2 := by
    rw [imNorm_sq, EuclideanSpace.norm_sq_eq]
    simp only [imVec_apply, Real.norm_eq_abs, sq_abs]
  have h2 : 1 ≤ imNorm z := one_le_imNorm z
  nlinarith [h1, h2, norm_nonneg (imVec z)]

/-- **The upper bound on the §5 weight `φ`**: it grows at most linearly in `|Im z|`. -/
lemma section5Phi_le {ρ lam B1 B2 : ℝ} (hρ : 0 < ρ) (hlam : 0 < lam)
    (habs1 : ∀ t : ℝ, 0 ≤ t → 20 * (d:ℝ) * Real.log (1 + t) ≤ (ρ / 2) * t + B1)
    (habs2 : ∀ t : ℝ, 0 ≤ t → 20 * (d:ℝ) * Real.log (1 + t)
      - ρ * lam * (Real.smoothTransition (t / 5 - 1) * (t / (Real.log (2 + t)) ^ 2)) ≤ B2)
    {u u0 : ℂᵈ → ℝ} (hunonpos : ∀ x : ℝᵈ, u (toCpx x) ≤ 0)
    (hugrowth : ∀ z : ℂᵈ, u (toCpx (reVec z)) ≤ u z ∧
      u z ≤ u (toCpx (reVec z)) + ρ * ‖imVec z‖)
    (hu0growth : ∀ z : ℂᵈ, u0 (toCpx (reVec z)) ≤ u0 z ∧
      u0 z ≤ u0 (toCpx (reVec z)) + (1 / 2) * ‖imVec z‖)
    (hu0le : ∀ x : ℝᵈ, u0 (toCpx x) ≤ lam * omega0 x) :
    ∀ z : ℂᵈ, section5Phi ρ u u0 z ≤ 4 * ρ * ‖imVec z‖ + (B1 + B2) := by
  intro z
  have hy : (0:ℝ) ≤ ‖imVec z‖ := norm_nonneg _
  have hre : (0:ℝ) ≤ ‖reVec z‖ := norm_nonneg _
  -- `2u`
  have hA : 2 * u z ≤ 2 * ρ * ‖imVec z‖ := by
    have h := (hugrowth z).2
    have h2 := hunonpos (reVec z)
    linarith [h, h2]
  -- `ρ u₀`
  have hB : ρ * u0 z ≤ ρ * u0 (toCpx (reVec z)) + (ρ / 2) * ‖imVec z‖ := by
    have h := (hu0growth z).2
    have h2 : ρ * u0 z ≤ ρ * (u0 (toCpx (reVec z)) + (1 / 2) * ‖imVec z‖) :=
      mul_le_mul_of_nonneg_left h hρ.le
    linarith
  -- the cutoff term
  have hlog1 : Real.log (1 + ‖reVec z‖) ≤ Real.log (2 + ‖reVec z‖) :=
    Real.log_le_log (by linarith) (by linarith)
  have hchi : 0 ≤ Real.smoothTransition (‖reVec z‖ / 5 - 1) := Real.smoothTransition.nonneg _
  have hquo : 0 ≤ ‖reVec z‖ / (Real.log (2 + ‖reVec z‖)) ^ 2 := div_nonneg hre (sq_nonneg _)
  have hC : ρ * u0 (toCpx (reVec z))
      ≤ -ρ * lam * (Real.smoothTransition (‖reVec z‖ / 5 - 1)
        * (‖reVec z‖ / (Real.log (2 + ‖reVec z‖)) ^ 2)) := by
    have h := hu0le (reVec z)
    have h2 : lam * omega0 (reVec z) = -lam * (Real.smoothTransition (‖reVec z‖ / 5 - 1)
        * (‖reVec z‖ / (Real.log (2 + ‖reVec z‖)) ^ 2)) := by
      rw [omega0]; ring
    rw [h2] at h
    have h3 : ρ * u0 (toCpx (reVec z)) ≤ ρ * (-lam * (Real.smoothTransition (‖reVec z‖ / 5 - 1)
        * (‖reVec z‖ / (Real.log (2 + ‖reVec z‖)) ^ 2))) :=
      mul_le_mul_of_nonneg_left h hρ.le
    linarith
  have hD : Real.log (1 + ‖reVec z‖)
      ≤ Real.log (2 + ‖reVec z‖) := hlog1
  have hE : 20 * (d:ℝ) * Real.log (1 + ‖reVec z‖) + ρ * u0 (toCpx (reVec z))
      ≤ B2 := by
    have h := habs2 (‖reVec z‖) hre
    have h2 : 20 * (d:ℝ) * Real.log (1 + ‖reVec z‖) + ρ * u0 (toCpx (reVec z))
        ≤ 20 * (d:ℝ) * Real.log (2 + ‖reVec z‖)
          - ρ * lam * (Real.smoothTransition (‖reVec z‖ / 5 - 1)
            * (‖reVec z‖ / (Real.log (2 + ‖reVec z‖)) ^ 2)) := by
      have := mul_le_mul_of_nonneg_left hlog1 (by positivity : (0:ℝ) ≤ 20 * (d:ℝ))
      linarith
    linarith
  have hF : 20 * (d:ℝ) * Real.log (1 + ‖imVec z‖) ≤ (ρ / 2) * ‖imVec z‖ + B1 :=
    habs1 ‖imVec z‖ hy
  have hG : (ρ / 2) * (imNorm z - 1) ≤ (ρ / 2) * ‖imVec z‖ :=
    mul_le_mul_of_nonneg_left (imNorm_sub_one_le z) (by positivity)
  have hρY : 0 ≤ ρ * ‖imVec z‖ := mul_nonneg hρ.le hy
  rw [section5Phi]
  linarith [hA, hB, hC, hD, hE, hF, hG, hρY, logWeight_le z]

/-! ### The size of `∂̄h`, and the Hörmander test integrand -/

/-- `‖∂̄_j h(z)‖ ≤ B` whenever `‖fderiv ℝ h z‖ ≤ B`. -/
lemma norm_dbarFun_le {h : ℂᵈ → ℂ} {B : ℝ} (hB : ∀ z : ℂᵈ, ‖fderiv ℝ h z‖ ≤ B) (z : ℂᵈ)
    (j : Fin d) : ‖dbarFun h z j‖ ≤ B := by
  have hB0 : (0:ℝ) ≤ B := le_trans (norm_nonneg _) (hB z)
  have h2 : ‖fderiv ℝ h z (Pi.single j (1:ℂ))‖ ≤ B := by
    have := (fderiv ℝ h z).le_opNorm (Pi.single j (1:ℂ))
    rw [Pi.norm_single, norm_one, mul_one] at this
    exact le_trans this (hB z)
  have h3 : ‖fderiv ℝ h z (Pi.single j Complex.I)‖ ≤ B := by
    have := (fderiv ℝ h z).le_opNorm (Pi.single j Complex.I)
    rw [Pi.norm_single, Complex.norm_I, mul_one] at this
    exact le_trans this (hB z)
  have h4 : ‖fderiv ℝ h z (Pi.single j (1:ℂ))
      + Complex.I * fderiv ℝ h z (Pi.single j Complex.I)‖ ≤ 2 * B := by
    calc ‖fderiv ℝ h z (Pi.single j (1:ℂ))
        + Complex.I * fderiv ℝ h z (Pi.single j Complex.I)‖
        ≤ ‖fderiv ℝ h z (Pi.single j (1:ℂ))‖
          + ‖Complex.I * fderiv ℝ h z (Pi.single j Complex.I)‖ := norm_add_le _ _
      _ = ‖fderiv ℝ h z (Pi.single j (1:ℂ))‖
          + ‖fderiv ℝ h z (Pi.single j Complex.I)‖ := by rw [norm_mul, Complex.norm_I, one_mul]
      _ ≤ B + B := add_le_add h2 h3
      _ = 2 * B := by ring
  rw [dbarFun, partialZbar, norm_div]
  have h5 : ‖(2:ℂ)‖ = 2 := by norm_num
  rw [h5]
  linarith

/-- The pointwise size of `∂̄h` for the bump of §5. -/
lemma formNormSq_dbarFun_bumpC_le {B : ℝ}
    (hB : ∀ z : ℂᵈ, ‖fderiv ℝ (bumpC (d := d)) z‖ ≤ B) (z : ℂᵈ) :
    formNormSq (dbarFun (bumpC (d := d))) z ≤ (d : ℝ) * B ^ 2 := by
  have hB0 : (0:ℝ) ≤ B := le_trans (norm_nonneg _) (hB z)
  calc formNormSq (dbarFun (bumpC (d := d))) z
      = ∑ j, ‖dbarFun (bumpC (d := d)) z j‖ ^ 2 := rfl
    _ ≤ ∑ _j : Fin d, B ^ 2 :=
        Finset.sum_le_sum fun j _ => by
          have h := norm_dbarFun_le hB z j
          nlinarith [norm_nonneg (dbarFun (bumpC (d := d)) z j)]
    _ = (d : ℝ) * B ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

end Submission.FUP
