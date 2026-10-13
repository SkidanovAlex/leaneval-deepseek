import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.Spaces.cs_integral
import Submission.Work.FTS.EllipticEst.remov.Ebs.abs_integral_mul_le_sqrt

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory

namespace Work.FTS.EllipticEst.remov

/-- The weight `cos⁴/σ`, `σ t = sin (2t)^{2-γ}`, is bounded by `(π/4)^4` on the right half
`(ν, π/2)` of the slice, for `ν ≥ π/4` and `1 ≤ γ ≤ 3/2`.

Writing `ε = π/2 - t`, `cos t = sin ε ≤ ε` and Jordan's inequality
`sin (2t) = sin (2ε) ≥ (2/π)(2ε) = (4/π)ε` give `σ ≥ ((4/π)ε)^{2-γ} ≥ (4/π)ε`; hence
`cos⁴t/σ ≤ ε⁴/((4/π)ε) = (π/4)ε³ ≤ (π/4)⁴`. -/
lemma cos4_div_sigma_le_const (γ : ℝ) (hγ1 : 1 ≤ γ) (hγ2 : γ ≤ 3 / 2) {ν : ℝ}
    (hν : ν ∈ Set.Ico (Real.pi / 4) (Real.pi / 2)) {t : ℝ}
    (ht : t ∈ Set.Ioo ν (Real.pi / 2)) :
    (Real.cos t) ^ 4 / Real.rpow (Real.sin (2 * t)) (2 - γ) ≤ (Real.pi / 4) ^ 4 := by
  have hν4 : Real.pi / 4 ≤ ν := hν.1
  have ht1 : ν < t := ht.1
  have ht2 : t < Real.pi / 2 := ht.2
  have hπne : Real.pi ≠ 0 := Real.pi_ne_zero
  set ε : ℝ := Real.pi / 2 - t with hε
  have hεpos : 0 < ε := by rw [hε]; linarith
  have hεle : ε ≤ Real.pi / 4 := by rw [hε]; linarith
  have hεne : ε ≠ 0 := ne_of_gt hεpos
  have hsin_eq : Real.sin (2 * t) = Real.sin (2 * ε) := by
    have h2 : 2 * ε = Real.pi - 2 * t := by rw [hε]; ring
    rw [h2, Real.sin_pi_sub]
  have h2ε_nn : 0 ≤ 2 * ε := by linarith
  have h2ε_le : 2 * ε ≤ Real.pi / 2 := by linarith
  have hjordan : 2 / Real.pi * (2 * ε) ≤ Real.sin (2 * ε) := Real.mul_le_sin h2ε_nn h2ε_le
  have hσge : 4 / Real.pi * ε ≤ Real.rpow (Real.sin (2 * t)) (2 - γ) := by
    have hσge' : Real.rpow (4 / Real.pi * ε) (2 - γ) ≤
        Real.rpow (Real.sin (2 * t)) (2 - γ) := by
      have hbase : 2 / Real.pi * (2 * ε) = 4 / Real.pi * ε := by ring
      rw [hsin_eq, ← hbase]
      exact Real.rpow_le_rpow (by positivity) hjordan (by linarith)
    have hbase1 : 4 / Real.pi * ε ≤ 1 := by
      have h1 : 4 / Real.pi * (Real.pi / 4) = 1 := by field_simp
      calc 4 / Real.pi * ε ≤ 4 / Real.pi * (Real.pi / 4) :=
            mul_le_mul_of_nonneg_left hεle (by positivity)
        _ = 1 := h1
    have hrp : 4 / Real.pi * ε ≤ Real.rpow (4 / Real.pi * ε) (2 - γ) := by
      have h := Real.rpow_le_rpow_of_exponent_ge (x := 4 / Real.pi * ε) (y := 1) (z := 2 - γ)
        (by positivity) hbase1 (by linarith)
      rwa [Real.rpow_one] at h
    exact le_trans hrp hσge'
  have hcos_eq : Real.cos t = Real.sin ε := by
    rw [hε]; exact (Real.sin_pi_div_two_sub t).symm
  have hcos_le : Real.cos t ≤ ε := by
    rw [hcos_eq]; exact Real.sin_le (le_of_lt hεpos)
  have hcos_nn : 0 ≤ Real.cos t := by
    rw [hcos_eq]
    refine Real.sin_nonneg_of_mem_Icc ⟨le_of_lt hεpos, ?_⟩
    linarith [hεle, Real.pi_pos]
  have hcos4_le : (Real.cos t) ^ 4 ≤ ε ^ 4 := pow_le_pow_left₀ hcos_nn hcos_le 4
  have hbasepos : 0 < 4 / Real.pi * ε := by positivity
  calc (Real.cos t) ^ 4 / Real.rpow (Real.sin (2 * t)) (2 - γ)
      ≤ (Real.cos t) ^ 4 / (4 / Real.pi * ε) :=
        div_le_div_of_nonneg_left (pow_nonneg hcos_nn 4) hbasepos hσge
    _ ≤ ε ^ 4 / (4 / Real.pi * ε) :=
        div_le_div_of_nonneg_right hcos4_le (le_of_lt hbasepos)
    _ = (Real.pi / 4) * ε ^ 3 := by field_simp
    _ ≤ (Real.pi / 4) * (Real.pi / 4) ^ 3 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (le_of_lt hεpos) hεle 3) (by positivity)
    _ = (Real.pi / 4) ^ 4 := by ring

/-- `cos⁴/σ` is integrable on `(ν, π/2)`, `σ t = sin (2t)^{2-γ}`, `1 ≤ γ ≤ 3/2`,
`ν ∈ [π/4, π/2)`: it is a bounded function on a set of finite measure. -/
lemma integrableOn_cos4_div_sigma (γ : ℝ) (hγ1 : 1 ≤ γ) (hγ2 : γ ≤ 3 / 2) {ν : ℝ}
    (hν : ν ∈ Set.Ico (Real.pi / 4) (Real.pi / 2)) :
    MeasureTheory.IntegrableOn
      (fun t => (Real.cos t) ^ 4 / Real.rpow (Real.sin (2 * t)) (2 - γ))
      (Set.Ioo ν (Real.pi / 2)) := by
  have hγ0 : 0 ≤ 2 - γ := by linarith
  have hcontσ : Continuous (fun t : ℝ => Real.rpow (Real.sin (2 * t)) (2 - γ)) :=
    (Real.continuous_rpow_const hγ0).comp
      (Real.continuous_sin.comp (continuous_const.mul continuous_id))
  refine MeasureTheory.IntegrableOn.of_bound ?_ ?_ ((Real.pi / 4) ^ 4) ?_
  · rw [Real.volume_Ioo]; exact ENNReal.ofReal_lt_top
  · exact (((Real.continuous_cos.pow 4).measurable).div hcontσ.measurable).aestronglyMeasurable
  · refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioo).mpr
      (Filter.Eventually.of_forall (fun t ht => ?_))
    have hnn : 0 ≤ (Real.cos t) ^ 4 / Real.rpow (Real.sin (2 * t)) (2 - γ) :=
      div_nonneg (pow_nonneg (Real.cos_nonneg_of_mem_Icc (by
        constructor <;> linarith [ht.1, ht.2, hν.1, Real.pi_pos])) 4)
        (le_of_lt (Real.rpow_pos_of_pos (Real.sin_pos_of_pos_of_lt_pi
          (by linarith [ht.1, hν.1, Real.pi_pos]) (by linarith [ht.2, Real.pi_pos])) _))
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    exact cos4_div_sigma_le_const γ hγ1 hγ2 hν ht

/-- Weighted Cauchy–Schwarz on the right half of the slice: the `g`-part of the tail.

For `ν ∈ [π/4, π/2)`, `g` a.e.-strongly-measurable and `g²σ` integrable on `(ν, π/2)`
(`σ = sin(2t)^{2-γ}`, `1 ≤ γ ≤ 3/2`), the function `|g|cos²` is integrable there and

  `∫_{Ioo ν (π/2)} |g t| cos²t ≤ √(Cw · ∫_{Ioo ν (π/2)} g²σ) · (π/2-ν)^{(3+γ)/2}`

whenever `∫_{Ioo ν (π/2)} cos⁴/σ ≤ Cw (π/2-ν)^{3+γ}`.

Proof: write `|g|cos² = (√σ·|g|)·(cos²/√σ)` (σ > 0 on the open interval) and apply
Cauchy–Schwarz; `∫(√σ g)² = ∫σg²` and `∫(cos²/√σ)² = ∫cos⁴/σ`.  Integrability of `|g|cos²`
follows from the pointwise AM–GM bound `|g|cos² ≤ g²σ/2 + (cos⁴/σ)/2` together with the
boundedness of `cos⁴/σ` near the endpoints (it is bounded by `1/(2 sin ν)^{2-γ}` on `[ν, π/2]`).
Note that `cos⁴/σ` and `cos⁶/σ` are *unconditionally* integrable on `(ν, π/2)` for `ν > 0`. -/
theorem slice_bd_tail_g (γ : ℝ) (hγ1 : 1 ≤ γ) (hγ2 : γ ≤ 3 / 2) {g : ℝ → ℝ} {Cw ν : ℝ}
    (hCw : 0 ≤ Cw) (hν : ν ∈ Set.Ico (Real.pi / 4) (Real.pi / 2))
    (hGm : MeasureTheory.AEStronglyMeasurable g
      (MeasureTheory.volume.restrict (Set.Ioo ν (Real.pi / 2))))
    (hG : MeasureTheory.IntegrableOn
      (fun t => (g t) ^ 2 * Real.rpow (Real.sin (2 * t)) (2 - γ))
      (Set.Ioo ν (Real.pi / 2)))
    (hI4 : (∫ t in ν..(Real.pi / 2),
        (Real.cos t) ^ 4 / Real.rpow (Real.sin (2 * t)) (2 - γ))
        ≤ Cw * (Real.pi / 2 - ν) ^ (3 + γ)) :
    (MeasureTheory.IntegrableOn (fun t => |g t| * (Real.cos t) ^ 2)
        (Set.Ioo ν (Real.pi / 2)))
      ∧ (∫ t in Set.Ioo ν (Real.pi / 2), |g t| * (Real.cos t) ^ 2
          ≤ Real.sqrt (Cw * (∫ t in Set.Ioo ν (Real.pi / 2),
                (g t) ^ 2 * Real.rpow (Real.sin (2 * t)) (2 - γ)))
            * (Real.pi / 2 - ν) ^ ((3 + γ) / 2)) := by
  have hν4 : Real.pi / 4 ≤ ν := hν.1
  have hνlt : ν < Real.pi / 2 := hν.2
  have hbpos : 0 < Real.pi / 2 - ν := by linarith
  have hbnonneg : 0 ≤ Real.pi / 2 - ν := le_of_lt hbpos
  have hγ0 : 0 ≤ 2 - γ := by linarith
  have hσpos : ∀ t ∈ Set.Ioo ν (Real.pi / 2), 0 < Real.rpow (Real.sin (2 * t)) (2 - γ) := by
    intro t ht
    refine Real.rpow_pos_of_pos ?_ _
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith [ht.1, hν4, Real.pi_pos])
      (by linarith [ht.2, Real.pi_pos])
  -- pointwise identities on the interval, and their a.e. versions
  have hpt_u : ∀ t ∈ Set.Ioo ν (Real.pi / 2),
      (g t) ^ 2 * Real.rpow (Real.sin (2 * t)) (2 - γ)
        = (Real.sqrt (Real.rpow (Real.sin (2 * t)) (2 - γ)) * |g t|) ^ 2 := by
    intro t ht
    rw [mul_pow, Real.sq_sqrt (le_of_lt (hσpos t ht)), sq_abs]
    ring
  have hae_u : (fun t => (g t) ^ 2 * Real.rpow (Real.sin (2 * t)) (2 - γ))
      =ᵐ[MeasureTheory.volume.restrict (Set.Ioo ν (Real.pi / 2))]
      (fun t => (Real.sqrt (Real.rpow (Real.sin (2 * t)) (2 - γ)) * |g t|) ^ 2) :=
    (MeasureTheory.ae_restrict_iff' measurableSet_Ioo).mpr
      (Filter.Eventually.of_forall (fun t ht => hpt_u t ht))
  have hpt_v : ∀ t ∈ Set.Ioo ν (Real.pi / 2),
      (Real.cos t) ^ 4 / Real.rpow (Real.sin (2 * t)) (2 - γ)
        = ((Real.cos t) ^ 2 / Real.sqrt (Real.rpow (Real.sin (2 * t)) (2 - γ))) ^ 2 := by
    intro t ht
    rw [div_pow, Real.sq_sqrt (le_of_lt (hσpos t ht)), ← pow_mul]
  have hae_v : (fun t => (Real.cos t) ^ 4 / Real.rpow (Real.sin (2 * t)) (2 - γ))
      =ᵐ[MeasureTheory.volume.restrict (Set.Ioo ν (Real.pi / 2))]
      (fun t => ((Real.cos t) ^ 2 / Real.sqrt (Real.rpow (Real.sin (2 * t)) (2 - γ))) ^ 2) :=
    (MeasureTheory.ae_restrict_iff' measurableSet_Ioo).mpr
      (Filter.Eventually.of_forall (fun t ht => hpt_v t ht))
  have hpt_uv : ∀ t ∈ Set.Ioo ν (Real.pi / 2),
      (Real.sqrt (Real.rpow (Real.sin (2 * t)) (2 - γ)) * |g t|)
          * ((Real.cos t) ^ 2 / Real.sqrt (Real.rpow (Real.sin (2 * t)) (2 - γ)))
        = |g t| * (Real.cos t) ^ 2 := by
    intro t ht
    have hne : Real.sqrt (Real.rpow (Real.sin (2 * t)) (2 - γ)) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.mpr (hσpos t ht))
    calc (Real.sqrt (Real.rpow (Real.sin (2 * t)) (2 - γ)) * |g t|)
          * ((Real.cos t) ^ 2 / Real.sqrt (Real.rpow (Real.sin (2 * t)) (2 - γ)))
        = ((Real.cos t) ^ 2 / Real.sqrt (Real.rpow (Real.sin (2 * t)) (2 - γ)))
          * (Real.sqrt (Real.rpow (Real.sin (2 * t)) (2 - γ)) * |g t|) := by
          rw [mul_comm]
      _ = (((Real.cos t) ^ 2 / Real.sqrt (Real.rpow (Real.sin (2 * t)) (2 - γ)))
          * Real.sqrt (Real.rpow (Real.sin (2 * t)) (2 - γ))) * |g t| := by
          rw [mul_assoc]
      _ = (Real.cos t) ^ 2 * |g t| := by rw [div_mul_cancel₀ _ hne]
      _ = |g t| * (Real.cos t) ^ 2 := by rw [mul_comm]
  have hae_uv : (fun t => (Real.sqrt (Real.rpow (Real.sin (2 * t)) (2 - γ)) * |g t|)
      * ((Real.cos t) ^ 2 / Real.sqrt (Real.rpow (Real.sin (2 * t)) (2 - γ))))
      =ᵐ[MeasureTheory.volume.restrict (Set.Ioo ν (Real.pi / 2))]
      (fun t => |g t| * (Real.cos t) ^ 2) :=
    (MeasureTheory.ae_restrict_iff' measurableSet_Ioo).mpr
      (Filter.Eventually.of_forall (fun t ht => hpt_uv t ht))
  have hcontσ : Continuous (fun t : ℝ => Real.rpow (Real.sin (2 * t)) (2 - γ)) :=
    (Real.continuous_rpow_const hγ0).comp
      (Real.continuous_sin.comp (continuous_const.mul continuous_id))
  -- the two factors are `L²`
  have hu : MeasureTheory.MemLp
      (fun t => Real.sqrt (Real.rpow (Real.sin (2 * t)) (2 - γ)) * |g t|) 2
      (MeasureTheory.volume.restrict (Set.Ioo ν (Real.pi / 2))) := by
    have haesm : MeasureTheory.AEStronglyMeasurable
        (fun t => Real.sqrt (Real.rpow (Real.sin (2 * t)) (2 - γ)) * |g t|)
        (MeasureTheory.volume.restrict (Set.Ioo ν (Real.pi / 2))) :=
      ((Real.continuous_sqrt.comp hcontσ).aestronglyMeasurable).mul
        (by simpa [Real.norm_eq_abs] using hGm.norm)
    exact (MeasureTheory.memLp_two_iff_integrable_sq haesm).mpr (hG.congr hae_u)
  have hv : MeasureTheory.MemLp
      (fun t => (Real.cos t) ^ 2 / Real.sqrt (Real.rpow (Real.sin (2 * t)) (2 - γ))) 2
      (MeasureTheory.volume.restrict (Set.Ioo ν (Real.pi / 2))) := by
    have hmeas : Measurable
        (fun t : ℝ => (Real.cos t) ^ 2 / Real.sqrt (Real.rpow (Real.sin (2 * t)) (2 - γ))) :=
      ((Real.continuous_cos.pow 2).measurable).div
        (Real.continuous_sqrt.comp hcontσ).measurable
    exact (MeasureTheory.memLp_two_iff_integrable_sq hmeas.aestronglyMeasurable).mpr
      ((integrableOn_cos4_div_sigma γ hγ1 hγ2 hν).congr hae_v)
  -- the set-integral form of the hypothesis
  have hI4set : (∫ t in Set.Ioo ν (Real.pi / 2),
      (Real.cos t) ^ 4 / Real.rpow (Real.sin (2 * t)) (2 - γ))
      ≤ Cw * (Real.pi / 2 - ν) ^ (3 + γ) := by
    have h := hI4
    rwa [intervalIntegral.integral_of_le (le_of_lt hνlt),
      MeasureTheory.integral_Ioc_eq_integral_Ioo] at h
  -- Cauchy–Schwarz
  have hcs := Ebs.abs_integral_mul_le_sqrt hu hv
  have hmain : (∫ t in Set.Ioo ν (Real.pi / 2),
        (Real.sqrt (Real.rpow (Real.sin (2 * t)) (2 - γ)) * |g t|)
          * ((Real.cos t) ^ 2 / Real.sqrt (Real.rpow (Real.sin (2 * t)) (2 - γ))))
      = (∫ t in Set.Ioo ν (Real.pi / 2), |g t| * (Real.cos t) ^ 2) :=
    integral_congr_ae hae_uv
  have hIu : (∫ t in Set.Ioo ν (Real.pi / 2),
        (Real.sqrt (Real.rpow (Real.sin (2 * t)) (2 - γ)) * |g t|) ^ 2)
      = (∫ t in Set.Ioo ν (Real.pi / 2),
          (g t) ^ 2 * Real.rpow (Real.sin (2 * t)) (2 - γ)) :=
    integral_congr_ae hae_u.symm
  have hIv : (∫ t in Set.Ioo ν (Real.pi / 2),
        ((Real.cos t) ^ 2 / Real.sqrt (Real.rpow (Real.sin (2 * t)) (2 - γ))) ^ 2)
      = (∫ t in Set.Ioo ν (Real.pi / 2),
          (Real.cos t) ^ 4 / Real.rpow (Real.sin (2 * t)) (2 - γ)) :=
    integral_congr_ae hae_v.symm
  have hsqrt_rpow : Real.sqrt ((Real.pi / 2 - ν) ^ (3 + γ))
      = (Real.pi / 2 - ν) ^ ((3 + γ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hbnonneg]
    congr 1
    ring
  have hcoef : Real.sqrt (∫ t in Set.Ioo ν (Real.pi / 2),
        (g t) ^ 2 * Real.rpow (Real.sin (2 * t)) (2 - γ)) * Real.sqrt Cw
      = Real.sqrt (Cw * (∫ t in Set.Ioo ν (Real.pi / 2),
          (g t) ^ 2 * Real.rpow (Real.sin (2 * t)) (2 - γ))) := by
    rw [mul_comm (Real.sqrt _), Real.sqrt_mul hCw]
  refine ⟨?_, ?_⟩
  · exact (hu.integrable_mul hv).congr hae_uv
  · calc (∫ t in Set.Ioo ν (Real.pi / 2), |g t| * (Real.cos t) ^ 2)
        = (∫ t in Set.Ioo ν (Real.pi / 2),
            (Real.sqrt (Real.rpow (Real.sin (2 * t)) (2 - γ)) * |g t|)
              * ((Real.cos t) ^ 2 / Real.sqrt (Real.rpow (Real.sin (2 * t)) (2 - γ)))) :=
          hmain.symm
      _ ≤ |∫ t in Set.Ioo ν (Real.pi / 2),
            (Real.sqrt (Real.rpow (Real.sin (2 * t)) (2 - γ)) * |g t|)
              * ((Real.cos t) ^ 2 / Real.sqrt (Real.rpow (Real.sin (2 * t)) (2 - γ)))| :=
          le_abs_self _
      _ ≤ Real.sqrt (∫ t in Set.Ioo ν (Real.pi / 2),
              (Real.sqrt (Real.rpow (Real.sin (2 * t)) (2 - γ)) * |g t|) ^ 2)
            * Real.sqrt (∫ t in Set.Ioo ν (Real.pi / 2),
              ((Real.cos t) ^ 2 / Real.sqrt (Real.rpow (Real.sin (2 * t)) (2 - γ))) ^ 2) :=
          hcs
      _ = Real.sqrt (∫ t in Set.Ioo ν (Real.pi / 2),
              (g t) ^ 2 * Real.rpow (Real.sin (2 * t)) (2 - γ))
            * Real.sqrt (∫ t in Set.Ioo ν (Real.pi / 2),
              (Real.cos t) ^ 4 / Real.rpow (Real.sin (2 * t)) (2 - γ)) := by
          rw [hIu, hIv]
      _ ≤ Real.sqrt (∫ t in Set.Ioo ν (Real.pi / 2),
              (g t) ^ 2 * Real.rpow (Real.sin (2 * t)) (2 - γ))
            * Real.sqrt (Cw * (Real.pi / 2 - ν) ^ (3 + γ)) :=
          mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hI4set) (Real.sqrt_nonneg _)
      _ = Real.sqrt (∫ t in Set.Ioo ν (Real.pi / 2),
              (g t) ^ 2 * Real.rpow (Real.sin (2 * t)) (2 - γ))
            * (Real.sqrt Cw * (Real.pi / 2 - ν) ^ ((3 + γ) / 2)) := by
          rw [Real.sqrt_mul hCw, hsqrt_rpow]
      _ = Real.sqrt (Cw * (∫ t in Set.Ioo ν (Real.pi / 2),
              (g t) ^ 2 * Real.rpow (Real.sin (2 * t)) (2 - γ)))
            * (Real.pi / 2 - ν) ^ ((3 + γ) / 2) := by
          rw [← mul_assoc, hcoef]

end Work.FTS.EllipticEst.remov
