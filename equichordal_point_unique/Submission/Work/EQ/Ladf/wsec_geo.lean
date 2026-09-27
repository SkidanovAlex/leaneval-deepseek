import Mathlib
import Submission.Work.EQ.DefsCore
import Submission.Work.EQ.CycleDefs
import Submission.Work.EQ.HeteroAlgebra
import Submission.Work.EQ.H0_tail_bounded
import Submission.Work.EQ.germCHelpers
import Submission.Work.EQ.fwdC_germC

/-!
# Explicit values of the non-principal branch at the axis points

`A₁ = (-1/2,0)` and `A₂ = (1/2,0)`; the non-principal image is `(3/2,0)` resp. `(-3/2,0)`.
-/

namespace Work.EQ.Ladf

open Work.EQ Complex Filter _root_.Topology
open scoped Topology

/-- The other backward image of `A₁ = (-1/2,0)` is `(3/2, 0)`. -/
theorem invBranch_false_A1 {a : ℝ} (ha1 : a < 1) :
    invBranch a false ((-1 / 2 : ℂ), (0 : ℂ)) = ((3 / 2 : ℂ), (0 : ℂ)) := by
  have h1a : (0 : ℝ) < (1 - a) / 2 := by linarith
  have h1ane : ((1 - a) / 2 : ℝ) ≠ 0 := ne_of_gt h1a
  have hca : (-1 / 2 : ℂ) + ((a / 2 : ℝ) : ℂ) = ((-(1 - a) / 2 : ℝ) : ℂ) := by
    rw [show (-1 / 2 : ℂ) = ((-1 / 2 : ℝ) : ℂ) by norm_num, ← Complex.ofReal_add]
    congr 1
    ring
  have hρ : (((-1 / 2 : ℂ) + ((a / 2 : ℝ) : ℂ)) ^ 2 + (0 : ℂ) ^ 2) ^ (1 / 2 : ℂ)
      = (((1 - a) / 2 : ℝ) : ℂ) := by
    rw [hca, zero_pow (by norm_num), add_zero, ← Complex.ofReal_pow]
    rw [ofReal_cpow_half (x := (-(1 - a) / 2) ^ 2) (by positivity)]
    congr 1
    rw [Real.sqrt_sq_eq_abs, abs_of_nonpos (by linarith)]
    ring
  have hkey : ((-1 / 2 : ℂ) + ((a / 2 : ℝ) : ℂ)) / (((1 - a) / 2 : ℝ) : ℂ) = (-1 : ℂ) := by
    have hB : (((1 - a) / 2 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr h1ane
    rw [div_eq_iff hB]
    push_cast
    ring
  rw [invBranch]
  simp only [Bool.false_eq_true, ↓reduceIte, neg_one_mul]
  rw [hρ]
  have hsplit : -((-1 / 2 : ℂ) + ((a / 2 : ℝ) : ℂ)) / (((1 - a) / 2 : ℝ) : ℂ)
      = -((((-1 / 2 : ℂ) + ((a / 2 : ℝ) : ℂ)) / (((1 - a) / 2 : ℝ) : ℂ))) := by
    rw [neg_div]
  refine Prod.ext ?_ ?_
  · simp only [hsplit, hkey]
    norm_num
  · simp only [zero_div, neg_zero, add_zero]

/-- The other backward image of `A₂ = (1/2,0)` is `(-3/2, 0)`. -/
theorem invBranch_false_A2 {a : ℝ} (ha0 : 0 < a) :
    invBranch a false ((1 / 2 : ℂ), (0 : ℂ)) = ((-3 / 2 : ℂ), (0 : ℂ)) := by
  have h1a : (0 : ℝ) < (1 + a) / 2 := by linarith
  have h1ane : ((1 + a) / 2 : ℝ) ≠ 0 := ne_of_gt h1a
  have hca : (1 / 2 : ℂ) + ((a / 2 : ℝ) : ℂ) = (((1 + a) / 2 : ℝ) : ℂ) := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num, ← Complex.ofReal_add]
    congr 1
    ring
  have hρ : (((1 / 2 : ℂ) + ((a / 2 : ℝ) : ℂ)) ^ 2 + (0 : ℂ) ^ 2) ^ (1 / 2 : ℂ)
      = (((1 + a) / 2 : ℝ) : ℂ) := by
    rw [hca, zero_pow (by norm_num), add_zero, ← Complex.ofReal_pow]
    rw [ofReal_cpow_half (x := ((1 + a) / 2) ^ 2) (by positivity)]
    congr 1
    rw [Real.sqrt_sq (le_of_lt h1a)]
  have hkey : ((1 / 2 : ℂ) + ((a / 2 : ℝ) : ℂ)) / (((1 + a) / 2 : ℝ) : ℂ) = (1 : ℂ) := by
    have hB : (((1 + a) / 2 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr h1ane
    rw [div_eq_iff hB]
    push_cast
    ring
  rw [invBranch]
  simp only [Bool.false_eq_true, ↓reduceIte, neg_one_mul]
  rw [hρ]
  have hsplit : -((1 / 2 : ℂ) + ((a / 2 : ℝ) : ℂ)) / (((1 + a) / 2 : ℝ) : ℂ)
      = -((((1 / 2 : ℂ) + ((a / 2 : ℝ) : ℂ)) / (((1 + a) / 2 : ℝ) : ℂ))) := by
    rw [neg_div]
  refine Prod.ext ?_ ?_
  · simp only [hsplit, hkey]
    norm_num
  · simp only [zero_div, neg_zero, add_zero]

/-- The other forward image of `A₁ = (-1/2,0)` is `(3/2, 0)`. -/
theorem fwdAlt_A1 {a : ℝ} (ha0 : 0 < a) :
    fwdAlt a ((-1 / 2 : ℂ), (0 : ℂ)) = ((3 / 2 : ℂ), (0 : ℂ)) := by
  have h1a : (0 : ℝ) < (1 + a) / 2 := by linarith
  have hx : ((((1 + a) / 2 : ℝ) : ℂ)) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt h1a)
  have hsub : subO2 a ((-1 / 2 : ℂ), (0 : ℂ)) = (((-(1 + a) / 2 : ℝ) : ℂ), (0 : ℂ)) := by
    refine Prod.ext ?_ ?_
    · show (-1 / 2 : ℂ) - ((a / 2 : ℝ) : ℂ) = (((-(1 + a) / 2 : ℝ)) : ℂ)
      push_cast; ring
    · show (0 : ℂ) = (0 : ℂ); ring
  have hbsq : bsq (((-(1 + a) / 2 : ℝ) : ℂ), (0 : ℂ)) = ((((1 + a) / 2) ^ 2 : ℝ) : ℂ) := by
    rw [bsq]; push_cast; ring
  have hbrho : brho (((-(1 + a) / 2 : ℝ) : ℂ), (0 : ℂ)) = (((1 + a) / 2 : ℝ) : ℂ) := by
    rw [brho, hbsq, ofReal_cpow_half (x := ((1 + a) / 2) ^ 2) (by positivity),
      Real.sqrt_sq (le_of_lt h1a)]
  have hsc : ((((1 + a) / 2 : ℝ) : ℂ))⁻¹ * (((-(1 + a) / 2 : ℝ)) : ℂ) = (-1 : ℂ) := by
    field_simp
    push_cast
    ring
  rw [fwdAlt, hsub, hbrho, Prod.smul_mk, smul_eq_mul, hsc]
  refine Prod.ext ?_ ?_
  · norm_num
  · simp

/-- The other forward image of `A₂ = (1/2,0)` is `(-3/2, 0)`. -/
theorem fwdAlt_A2 {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    fwdAlt a ((1 / 2 : ℂ), (0 : ℂ)) = ((-3 / 2 : ℂ), (0 : ℂ)) := by
  have h1a : (0 : ℝ) < (1 - a) / 2 := by linarith
  have hx : ((((1 - a) / 2 : ℝ) : ℂ)) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt h1a)
  have hsub : subO2 a ((1 / 2 : ℂ), (0 : ℂ)) = ((((1 - a) / 2 : ℝ) : ℂ), (0 : ℂ)) := by
    refine Prod.ext ?_ ?_
    · show (1 / 2 : ℂ) - ((a / 2 : ℝ) : ℂ) = ((((1 - a) / 2 : ℝ)) : ℂ)
      push_cast; ring
    · show (0 : ℂ) = (0 : ℂ); ring
  have hbsq : bsq ((((1 - a) / 2 : ℝ) : ℂ), (0 : ℂ)) = ((((1 - a) / 2) ^ 2 : ℝ) : ℂ) := by
    rw [bsq]; push_cast; ring
  have hbrho : brho ((((1 - a) / 2 : ℝ) : ℂ), (0 : ℂ)) = (((1 - a) / 2 : ℝ) : ℂ) := by
    rw [brho, hbsq, ofReal_cpow_half (x := ((1 - a) / 2) ^ 2) (by positivity),
      Real.sqrt_sq (le_of_lt h1a)]
  have hsc : ((((1 - a) / 2 : ℝ) : ℂ))⁻¹ * ((((1 - a) / 2 : ℝ)) : ℂ) = (1 : ℂ) := by
    field_simp
  rw [fwdAlt, hsub, hbrho, Prod.smul_mk, smul_eq_mul, hsc]
  refine Prod.ext ?_ ?_
  · norm_num
  · simp

/-- The backward radicand at `A₁ = (-1/2,0)` lies in the slit plane. -/
theorem slitPlane_subO1_A1 {a : ℝ} (ha1 : a < 1) :
    (((-1 / 2 : ℂ) + ((a / 2 : ℝ) : ℂ)) ^ 2 + (0 : ℂ) ^ 2) ∈ Complex.slitPlane := by
  have hca : (-1 / 2 : ℂ) + ((a / 2 : ℝ) : ℂ) = ((-(1 - a) / 2 : ℝ) : ℂ) := by
    rw [show (-1 / 2 : ℂ) = ((-1 / 2 : ℝ) : ℂ) by norm_num, ← Complex.ofReal_add]
    congr 1; ring
  have h2 : ((-(1 - a) / 2 : ℝ) : ℂ) ^ 2 + (0 : ℂ) ^ 2
      = ((((1 - a) / 2) ^ 2 : ℝ) : ℂ) := by push_cast; ring
  rw [hca, h2]
  exact Complex.ofReal_mem_slitPlane.mpr (by positivity)

/-- The forward radicand at `A₂ = (1/2,0)` lies in the slit plane. -/
theorem slitPlane_subO2_A2 {a : ℝ} (ha1 : a < 1) :
    (((1 / 2 : ℂ) - ((a / 2 : ℝ) : ℂ)) ^ 2 + (0 : ℂ) ^ 2) ∈ Complex.slitPlane := by
  have hca : (1 / 2 : ℂ) - ((a / 2 : ℝ) : ℂ) = (((1 - a) / 2 : ℝ) : ℂ) := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num, ← Complex.ofReal_sub]
    congr 1; ring
  have h2 : (((1 - a) / 2 : ℝ) : ℂ) ^ 2 + (0 : ℂ) ^ 2 = ((((1 - a) / 2) ^ 2 : ℝ) : ℂ) := by
    push_cast; ring
  rw [hca, h2]
  exact Complex.ofReal_mem_slitPlane.mpr (by positivity)

/-- Near `A₁` the non-principal backward image stays at distance `≥ 1` from `A₁`. -/
theorem invBranch_false_far_A1 {a : ℝ} (ha1 : a < 1) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ Q : ℂ × ℂ, ‖Q - ((-1 / 2 : ℂ), (0 : ℂ))‖ < ρ →
      1 ≤ ‖invBranch a false Q - ((-1 / 2 : ℂ), (0 : ℂ))‖ := by
  have hcont : ContinuousAt (invBranch a false) ((-1 / 2 : ℂ), (0 : ℂ)) :=
    continuousAt_invBranch (slitPlane_subO1_A1 ha1)
  have hval : invBranch a false ((-1 / 2 : ℂ), (0 : ℂ)) = ((3 / 2 : ℂ), (0 : ℂ)) :=
    invBranch_false_A1 ha1
  have hset : {Q : ℂ × ℂ | dist (invBranch a false Q) ((3 / 2 : ℂ), (0 : ℂ)) < 1 / 2}
      ∈ 𝓝 ((-1 / 2 : ℂ), (0 : ℂ)) :=
    Filter.mem_of_superset
      (hcont.eventually (Metric.ball_mem_nhds (invBranch a false ((-1 / 2 : ℂ), (0 : ℂ)))
        (by norm_num : (0 : ℝ) < 1 / 2)))
      (fun Q hQ => by
        show dist (invBranch a false Q) ((3 / 2 : ℂ), (0 : ℂ)) < 1 / 2
        have h1 : dist (invBranch a false Q)
            (invBranch a false ((-1 / 2 : ℂ), (0 : ℂ))) < 1 / 2 := Metric.mem_ball.mp hQ
        rwa [hval] at h1)
  obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhds_iff.mp hset
  refine ⟨ρ, hρ, fun Q hQ => ?_⟩
  have h1 : ‖invBranch a false Q - ((3 / 2 : ℂ), (0 : ℂ))‖ < 1 / 2 := by
    have h2 : dist (invBranch a false Q) ((3 / 2 : ℂ), (0 : ℂ)) < 1 / 2 :=
      hball (by rw [Metric.mem_ball, dist_eq_norm]; exact hQ)
    rwa [dist_eq_norm] at h2
  have h2 : ‖((3 / 2 : ℂ), (0 : ℂ)) - ((-1 / 2 : ℂ), (0 : ℂ))‖ = 2 := by
    rw [Prod.norm_def]; norm_num
  have h3 : ‖((3 / 2 : ℂ), (0 : ℂ)) - ((-1 / 2 : ℂ), (0 : ℂ))‖
      ≤ ‖((3 / 2 : ℂ), (0 : ℂ)) - invBranch a false Q‖
        + ‖invBranch a false Q - ((-1 / 2 : ℂ), (0 : ℂ))‖ := by
    have h := norm_add_le (((3 / 2 : ℂ), (0 : ℂ)) - invBranch a false Q)
      (invBranch a false Q - ((-1 / 2 : ℂ), (0 : ℂ)))
    simpa using h
  have h4 : ‖((3 / 2 : ℂ), (0 : ℂ)) - invBranch a false Q‖
      = ‖invBranch a false Q - ((3 / 2 : ℂ), (0 : ℂ))‖ := norm_sub_rev _ _
  linarith

/-- `fwdAlt a` is continuous at `A₂ = (1/2,0)`. -/
theorem continuousAt_fwdAlt_A2 {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    ContinuousAt (fwdAlt a) ((1 / 2 : ℂ), (0 : ℂ)) := by
  have hsub : ContinuousAt (fun P : ℂ × ℂ => subO2 a P) ((1 / 2 : ℂ), (0 : ℂ)) :=
    (continuous_subO2 a).continuousAt
  have hb : ContinuousAt (fun P : ℂ × ℂ => bsq (subO2 a P)) ((1 / 2 : ℂ), (0 : ℂ)) :=
    (continuous_bsq.comp (continuous_subO2 a)).continuousAt
  have hslit : bsq (subO2 a ((1 / 2 : ℂ), (0 : ℂ))) ∈ Complex.slitPlane := by
    have h : bsq (subO2 a ((1 / 2 : ℂ), (0 : ℂ)))
        = (((1 / 2 : ℂ) - ((a / 2 : ℝ) : ℂ)) ^ 2 + (0 : ℂ) ^ 2) := rfl
    rw [h]; exact slitPlane_subO2_A2 ha1
  have hcpow : ContinuousAt (fun P : ℂ × ℂ => (bsq (subO2 a P)) ^ (1 / 2 : ℂ))
      ((1 / 2 : ℂ), (0 : ℂ)) := hb.cpow continuousAt_const hslit
  have hbrho : ContinuousAt (fun P : ℂ × ℂ => brho (subO2 a P)) ((1 / 2 : ℂ), (0 : ℂ)) := by
    simpa only [brho] using hcpow
  have hne : brho (subO2 a ((1 / 2 : ℂ), (0 : ℂ))) ≠ 0 :=
    brho_ne_zero (Complex.slitPlane_ne_zero hslit)
  have hinv : ContinuousAt (fun P : ℂ × ℂ => (brho (subO2 a P))⁻¹) ((1 / 2 : ℂ), (0 : ℂ)) :=
    hbrho.inv₀ hne
  have hsmul : ContinuousAt (fun P : ℂ × ℂ => (brho (subO2 a P))⁻¹ • subO2 a P)
      ((1 / 2 : ℂ), (0 : ℂ)) := hinv.smul hsub
  have hneg : ContinuousAt (fun P : ℂ × ℂ => -P) ((1 / 2 : ℂ), (0 : ℂ)) := continuousAt_id.neg
  have hfun : fwdAlt a = fun P : ℂ × ℂ => -P - (brho (subO2 a P))⁻¹ • subO2 a P := rfl
  rw [hfun]
  exact hneg.sub hsmul

/-- Near `A₂` the non-principal forward image stays at distance `≥ 1` from `A₂`. -/
theorem fwdAlt_far_A2 {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ P : ℂ × ℂ, ‖P - ((1 / 2 : ℂ), (0 : ℂ))‖ < ρ →
      1 ≤ ‖fwdAlt a P - ((1 / 2 : ℂ), (0 : ℂ))‖ := by
  have hcont : ContinuousAt (fwdAlt a) ((1 / 2 : ℂ), (0 : ℂ)) := continuousAt_fwdAlt_A2 ha0 ha1
  have hval : fwdAlt a ((1 / 2 : ℂ), (0 : ℂ)) = ((-3 / 2 : ℂ), (0 : ℂ)) := fwdAlt_A2 ha0 ha1
  have hset : {P : ℂ × ℂ | dist (fwdAlt a P) ((-3 / 2 : ℂ), (0 : ℂ)) < 1 / 2}
      ∈ 𝓝 ((1 / 2 : ℂ), (0 : ℂ)) :=
    Filter.mem_of_superset
      (hcont.eventually (Metric.ball_mem_nhds (fwdAlt a ((1 / 2 : ℂ), (0 : ℂ)))
        (by norm_num : (0 : ℝ) < 1 / 2)))
      (fun P hP => by
        show dist (fwdAlt a P) ((-3 / 2 : ℂ), (0 : ℂ)) < 1 / 2
        have h1 : dist (fwdAlt a P) (fwdAlt a ((1 / 2 : ℂ), (0 : ℂ))) < 1 / 2 :=
          Metric.mem_ball.mp hP
        rwa [hval] at h1)
  obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhds_iff.mp hset
  refine ⟨ρ, hρ, fun P hP => ?_⟩
  have h1 : ‖fwdAlt a P - ((-3 / 2 : ℂ), (0 : ℂ))‖ < 1 / 2 := by
    have h2 : dist (fwdAlt a P) ((-3 / 2 : ℂ), (0 : ℂ)) < 1 / 2 :=
      hball (by rw [Metric.mem_ball, dist_eq_norm]; exact hP)
    rwa [dist_eq_norm] at h2
  have h2 : ‖((-3 / 2 : ℂ), (0 : ℂ)) - ((1 / 2 : ℂ), (0 : ℂ))‖ = 2 := by
    rw [Prod.norm_def]; norm_num
  have h3 : ‖((-3 / 2 : ℂ), (0 : ℂ)) - ((1 / 2 : ℂ), (0 : ℂ))‖
      ≤ ‖((-3 / 2 : ℂ), (0 : ℂ)) - fwdAlt a P‖
        + ‖fwdAlt a P - ((1 / 2 : ℂ), (0 : ℂ))‖ := by
    have h := norm_add_le (((-3 / 2 : ℂ), (0 : ℂ)) - fwdAlt a P)
      (fwdAlt a P - ((1 / 2 : ℂ), (0 : ℂ)))
    simpa using h
  have h4 : ‖((-3 / 2 : ℂ), (0 : ℂ)) - fwdAlt a P‖
      = ‖fwdAlt a P - ((-3 / 2 : ℂ), (0 : ℂ))‖ := norm_sub_rev _ _
  linarith

end Work.EQ.Ladf
