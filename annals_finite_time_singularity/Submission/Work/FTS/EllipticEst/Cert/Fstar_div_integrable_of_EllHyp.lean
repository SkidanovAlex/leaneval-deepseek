/-
Copyright: work module for the Elgindi finite-time singularity project.

# Integrability of `r ↦ F_*(F)(r)/r` for the data of `EllHyp`

The angular moment `F_*(F)(z) = ∫_0^{π/2} F(z,θ) sin θ cos²θ dθ` of the elliptic chapter is the
whole singular part of the source: `L₁₂(F)(z) = 3 ∫_z^∞ F_*(F)(ρ)/ρ dρ` (see
`Work.Elliptic.L12_eq_radial`).  Every statement about the singular term `G` therefore needs the
integrability of `ρ ↦ F_*(F)(ρ)/ρ` on `(0,∞)`, which is what this module provides for the data
`Work.FTS.EllipticEst.EllHyp α k F Ψ`.

## The argument

Write `w(r) = (1+r)²/r²` and `S = sin(2θ)`.  Two facts drive the proof.

* **(measurability)** On the open quadrant `Q0 = (0,∞) × (0,π/2)` the source is the elliptic
  operator, `F = bslOp α Ψ` (`IsBslSol`).  Since `Ψ` is smooth on a neighbourhood of the closed
  quadrant, `bslOp α Ψ` is `C^∞` on `Q0` (`Work.FTS.EllipticEst.Cert.SmoothOpBsll`), so
  `p ↦ bslOp α Ψ p.1 p.2 · sinCos2 p.2` agrees with the continuous function
  `p ↦ F p.1 p.2 · sinCos2 p.2` off the null set `(0,∞) × {0,π/2}`.  Hence the parametric
  integral `r ↦ F_*(F)(r)` is a.e. strongly measurable on `(0,∞)`
  (`AEStronglyMeasurable.integral_prod_right'`).

* **(the bound)** With `X(r,θ) := ‖F(r,θ)·sinCos2 θ‖ₑ · ‖r‖ₑ⁻¹` one has, for `r > 0`,
  `‖F_*(F)(r)/r‖ₑ ≤ ∫⁻θ X(r,θ)` (`enorm_integral_le_lintegral_enorm` + `lintegral_mul_const_le`),
  and for every `θ ∈ Iθ` the weighted Young inequality

    `|F(r,θ)|·sinCos2 θ/r ≤ (F(r,θ)·(w(r)/sin(2θ)^{η/2}))² + ((r·w(r))⁻¹)²`

  (Young's inequality `2uv ≤ u² + v²` applied to `u = |F|·w(r)/sin(2θ)^{η/2}` and
  `v = sinCos2 θ/(r·w(r)/sin(2θ)^{η/2})`, using `sinCos2 θ ≤ 1` and `sin(2θ) ≤ 1`).  The first
  term is exactly the `i = 0` summand of the `ℋ^k`-integrand, hence dominated by
  `HkIntegrand α k F`; the second one does not depend on `θ` and is integrable in `r` because
  `((r·w(r))⁻¹)² = (r/(1+r)²)² ≤ min(r², r⁻²)`
  (`Work.FTS.EllipticEst.Cert.HasFiniteIntegralWInvSq`).  The two parts of the double `lintegral`
  are separated with `lintegral_add_right'` (the constant-in-`θ` part is measurable), the
  constant-in-`θ` integral is computed with `lintegral_const`, and the first part is estimated by
  the honest `ℋ^k` mass, whose integrability on `[0,∞)` is `HkMem`.
-/

import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Topology.Separation.CompletelyRegular
import Submission.Work.FTS.EllipticEst.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.Elliptic.PsiStar_ode
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.Cert.SmoothOpBsll
import Submission.Work.FTS.EllipticEst.Cert.HasFiniteIntegralWInvSq

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Cert

set_option autoImplicit false
set_option maxHeartbeats 2000000

variable {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ}

/-! ## 1. Elementary angular facts -/

theorem sin_two_nonneg_of_mem_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Real.sin (2 * θ) := by
  rw [Work.Spaces.Iθ] at hθ
  exact Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

theorem sin_two_le_one_of_mem_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    Real.sin (2 * θ) ≤ 1 := by
  rw [Work.Spaces.Iθ] at hθ
  exact Real.sin_le_one _

theorem sinCos2_nonneg_of_mem_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Work.Elliptic.sinCos2 θ := by
  rw [Work.Elliptic.sinCos2]
  exact mul_nonneg
    (Real.sin_nonneg_of_nonneg_of_le_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])) (sq_nonneg _)

theorem sinCos2_le_one (θ : ℝ) : Work.Elliptic.sinCos2 θ ≤ 1 := by
  rw [Work.Elliptic.sinCos2]
  have hc : Real.cos θ ^ 2 ≤ 1 := by
    nlinarith [Real.abs_cos_le_one θ, sq_abs (Real.cos θ), abs_nonneg (Real.cos θ)]
  have h1 : Real.sin θ * Real.cos θ ^ 2 ≤ 1 * Real.cos θ ^ 2 :=
    mul_le_mul_of_nonneg_right (Real.sin_le_one θ) (sq_nonneg _)
  have h2 : (1 : ℝ) * Real.cos θ ^ 2 ≤ 1 * 1 :=
    mul_le_mul_of_nonneg_left hc zero_le_one
  linarith

/-- `((r·w(r))⁻¹)² = (r/(1+r)²)²`, the explicit form of the radial weight's square. -/
theorem w_inv_sq_eq (r : ℝ) (hr : 0 < r) :
    ((r * Work.Spaces.w r)⁻¹) ^ 2 = (r / (1 + r) ^ 2) ^ 2 := by
  have h1 : r * Work.Spaces.w r = (1 + r) ^ 2 / r := by
    rw [Work.Spaces.w]; field_simp
  rw [h1, inv_div]

/-! ## 2. The weighted Young inequality -/

/-- **Weighted Young inequality.**  For `r > 0`, `0 ≤ σ ≤ 1`, `0 < T ≤ 1` and `x : ℝ`,

  `|x|·σ/r ≤ (x·(w(r)/T^{η/2}))² + ((r·w(r))⁻¹)²`.

It is Young's inequality `2uv ≤ u² + v²` applied to `u = |x|·w(r)/T^{η/2}` and
`v = σ/(r·w(r)/T^{η/2})`; the small factors `σ² ≤ 1` and `T^η ≤ 1` turn the second square into
`((r·w(r))⁻¹)²`. -/
theorem young_weighted (x r T σ : ℝ) (hr : 0 < r) (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1)
    (hT0 : 0 < T) (hT1 : T ≤ 1) :
    |x| * σ / r ≤ (x * (Work.Spaces.w r / T ^ (Work.Spaces.eta / 2))) ^ 2
      + ((r * Work.Spaces.w r)⁻¹) ^ 2 := by
  have hw : 0 < Work.Spaces.w r := by
    rw [Work.Spaces.w]; positivity
  have hTp : 0 < T ^ (Work.Spaces.eta / 2) := Real.rpow_pos_of_pos hT0 _
  set A : ℝ := Work.Spaces.w r / T ^ (Work.Spaces.eta / 2) with hA
  have hAp : 0 < A := div_pos hw hTp
  set u : ℝ := |x| * A with hu
  set v : ℝ := σ / (r * A) with hv
  have hu0 : 0 ≤ u := mul_nonneg (abs_nonneg _) hAp.le
  have hv0 : 0 ≤ v := div_nonneg hσ (mul_pos hr hAp).le
  have huv : u * v = |x| * σ / r := by
    rw [hu, hv]; field_simp
  have hu2 : u ^ 2 = (x * A) ^ 2 := by rw [hu, mul_pow, sq_abs, mul_pow]
  have hv_le : v ≤ (r * Work.Spaces.w r)⁻¹ := by
    have hstep : v = σ * T ^ (Work.Spaces.eta / 2) / (r * Work.Spaces.w r) := by
      rw [hv, hA, ← mul_div_assoc, div_div_eq_mul_div]
    rw [hstep, inv_eq_one_div]
    refine div_le_div_of_nonneg_right ?_ (mul_pos hr hw).le
    have hTle : T ^ (Work.Spaces.eta / 2) ≤ 1 :=
      Real.rpow_le_one hT0.le hT1
        (by norm_num [Work.Spaces.eta] : (0 : ℝ) ≤ Work.Spaces.eta / 2)
    calc σ * T ^ (Work.Spaces.eta / 2) ≤ 1 * 1 :=
          mul_le_mul hσ1 hTle hTp.le zero_le_one
      _ = 1 := by ring
  have hv2 : v ^ 2 ≤ ((r * Work.Spaces.w r)⁻¹) ^ 2 := by
    have hc : 0 ≤ (r * Work.Spaces.w r)⁻¹ := inv_nonneg.mpr (mul_pos hr hw).le
    calc v ^ 2 = v * v := by ring
      _ ≤ (r * Work.Spaces.w r)⁻¹ * v := mul_le_mul hv_le (le_refl v) hv0 hc
      _ ≤ (r * Work.Spaces.w r)⁻¹ * (r * Work.Spaces.w r)⁻¹ :=
          mul_le_mul (le_refl _) hv_le hv0 hc
      _ = ((r * Work.Spaces.w r)⁻¹) ^ 2 := by ring
  have hamgm : u * v ≤ (u ^ 2 + v ^ 2) / 2 := by nlinarith [sq_nonneg (u - v)]
  have hmid : u ^ 2 + v ^ 2 ≤ 2 * (x * A) ^ 2 + 2 * ((r * Work.Spaces.w r)⁻¹) ^ 2 := by
    nlinarith [hu2, hv2]
  have hfin : |x| * σ / r ≤ (x * A) ^ 2 + ((r * Work.Spaces.w r)⁻¹) ^ 2 := by
    nlinarith [huv.le, hamgm, hmid]
  rw [hA] at hfin
  exact hfin

/-! ## 3. Measurability of the angular moment -/

theorem Iθ_ae_eq_Ioo : (Work.Spaces.Iθ : Set ℝ) =ᵐ[volume] Set.Ioo 0 (π / 2) :=
  MeasureTheory.Ioo_ae_eq_Icc.symm

theorem prod_restrict_eq :
    ((volume.restrict (Set.Ioi 0)).prod (volume.restrict Work.Spaces.Iθ) : Measure (ℝ × ℝ))
      = (volume : Measure (ℝ × ℝ)).restrict Work.FTS.EllipticEst.Q0 := by
  have hv : (volume : Measure (ℝ × ℝ)) = volume.prod volume := Measure.volume_eq_prod ℝ ℝ
  rw [Measure.prod_restrict, hv]
  exact Measure.restrict_congr_set
    (MeasureTheory.Measure.set_prod_ae_eq Filter.EventuallyEq.rfl Iθ_ae_eq_Ioo)

/-- `p ↦ F p.1 p.2 · sinCos2 p.2` is a.e. strongly measurable for the product of the restricted
measures, because off the null set `(0,∞) × {0,π/2}` it agrees with the continuous function
`p ↦ bslOp α Ψ p.1 p.2 · sinCos2 p.2`. -/
theorem aesm_F_mul_sinCos2 (α : ℝ) (F Ψ : ℝ → ℝ → ℝ) (hsm : Work.Spaces.SmoothNbhd Ψ)
    (hsol : Work.Elliptic.IsBslSol α F Ψ) :
    AEStronglyMeasurable (fun p : ℝ × ℝ => F p.1 p.2 * Work.Elliptic.sinCos2 p.2)
      ((volume.restrict (Set.Ioi 0)).prod (volume.restrict Work.Spaces.Iθ)) := by
  have hsin : Continuous fun θ : ℝ => Work.Elliptic.sinCos2 θ := by
    have h : Continuous fun θ : ℝ => Real.sin θ * Real.cos θ ^ 2 :=
      Real.continuous_sin.mul (Real.continuous_cos.pow 2)
    exact h
  have hcont : ContinuousOn (fun p : ℝ × ℝ => Work.Elliptic.bslOp α Ψ p.1 p.2
      * Work.Elliptic.sinCos2 p.2) Work.FTS.EllipticEst.Q0 :=
    ((SmoothOpBsll α Ψ hsm).continuousOn).mul (hsin.comp_continuousOn continuousOn_snd)
  have h1 : AEStronglyMeasurable (fun p : ℝ × ℝ => Work.Elliptic.bslOp α Ψ p.1 p.2
      * Work.Elliptic.sinCos2 p.2)
      ((volume.restrict (Set.Ioi 0)).prod (volume.restrict Work.Spaces.Iθ)) := by
    rw [prod_restrict_eq]
    exact hcont.aestronglyMeasurable Work.FTS.EllipticEst.isOpen_Q0.measurableSet
  refine h1.congr ?_
  rw [Filter.EventuallyEq, MeasureTheory.ae_iff]
  have hIθ_meas : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  set A : Set (ℝ × ℝ) := (Set.Ioi 0)ᶜ ×ˢ Set.univ with hAdef
  set B : Set (ℝ × ℝ) := Set.univ ×ˢ (Work.Spaces.Iθ)ᶜ with hBdef
  set C : Set (ℝ × ℝ) := Set.Ioi 0 ×ˢ ({0} ∪ ({π / 2} : Set ℝ)) with hCdef
  have hAnull : ((volume.restrict (Set.Ioi 0)).prod (volume.restrict Work.Spaces.Iθ)) A = 0 := by
    rw [hAdef, Measure.prod_prod]
    have h : (volume.restrict (Set.Ioi (0 : ℝ))) (Set.Ioi (0 : ℝ))ᶜ = 0 := by
      rw [Measure.restrict_apply measurableSet_Ioi.compl, Set.compl_inter_self, measure_empty]
    rw [h, zero_mul]
  have hBnull : ((volume.restrict (Set.Ioi 0)).prod (volume.restrict Work.Spaces.Iθ)) B = 0 := by
    rw [hBdef, Measure.prod_prod]
    have h : (volume.restrict Work.Spaces.Iθ) (Work.Spaces.Iθ)ᶜ = 0 := by
      rw [Measure.restrict_apply hIθ_meas.compl, Set.compl_inter_self, measure_empty]
    rw [h, mul_zero]
  have hCnull : ((volume.restrict (Set.Ioi 0)).prod (volume.restrict Work.Spaces.Iθ)) C = 0 := by
    rw [hCdef, Measure.prod_prod]
    have hθ0 : (volume.restrict Work.Spaces.Iθ) ({0} ∪ ({π / 2} : Set ℝ)) = 0 := by
      refine le_antisymm ?_ zero_le
      calc (volume.restrict Work.Spaces.Iθ) ({0} ∪ ({π / 2} : Set ℝ))
          ≤ (volume.restrict Work.Spaces.Iθ) {0}
            + (volume.restrict Work.Spaces.Iθ) ({π / 2} : Set ℝ) := measure_union_le _ _
        _ = volume ({0} ∩ Work.Spaces.Iθ) + volume (({π / 2} : Set ℝ) ∩ Work.Spaces.Iθ) := by
            rw [Measure.restrict_apply (measurableSet_singleton 0),
              Measure.restrict_apply (measurableSet_singleton (π / 2))]
        _ = 0 := by
            rw [measure_mono_null (Set.inter_subset_left) Real.volume_singleton,
              measure_mono_null (Set.inter_subset_left) Real.volume_singleton, add_zero]
    rw [hθ0, mul_zero]
  have hsub : {a : ℝ × ℝ | ¬ (Work.Elliptic.bslOp α Ψ a.1 a.2 * Work.Elliptic.sinCos2 a.2
      = F a.1 a.2 * Work.Elliptic.sinCos2 a.2)} ⊆ A ∪ B ∪ C := by
    intro p hp
    simp only [Set.mem_setOf_eq] at hp
    by_contra hbad
    have hA : ¬ (p ∈ A) := fun h => hbad (Or.inl (Or.inl h))
    have hB : ¬ (p ∈ B) := fun h => hbad (Or.inl (Or.inr h))
    have hC : ¬ (p ∈ C) := fun h => hbad (Or.inr h)
    have hp1 : p.1 ∈ Set.Ioi (0 : ℝ) := by
      by_contra h
      exact hA ⟨h, trivial⟩
    have hp2 : p.2 ∈ Work.Spaces.Iθ := by
      by_contra h
      exact hB ⟨trivial, h⟩
    have hp3 : p.2 ∉ ({0} ∪ ({π / 2} : Set ℝ)) := fun h => hC ⟨hp1, h⟩
    have h0 : 0 < p.2 := lt_of_le_of_ne hp2.1 (fun h => hp3 (Or.inl h.symm))
    have h1 : p.2 < π / 2 := lt_of_le_of_ne hp2.2 (fun h => hp3 (Or.inr h))
    exact hp (by rw [hsol.1 p.1 hp1 p.2 h0 h1])
  have hz : ((volume.restrict (Set.Ioi 0)).prod (volume.restrict Work.Spaces.Iθ)) (A ∪ B ∪ C) = 0 := by
    refine le_antisymm ?_ zero_le
    calc ((volume.restrict (Set.Ioi 0)).prod (volume.restrict Work.Spaces.Iθ)) (A ∪ B ∪ C)
        ≤ ((volume.restrict (Set.Ioi 0)).prod (volume.restrict Work.Spaces.Iθ)) (A ∪ B)
          + ((volume.restrict (Set.Ioi 0)).prod (volume.restrict Work.Spaces.Iθ)) C :=
          measure_union_le _ _
      _ ≤ (((volume.restrict (Set.Ioi 0)).prod (volume.restrict Work.Spaces.Iθ)) A
              + ((volume.restrict (Set.Ioi 0)).prod (volume.restrict Work.Spaces.Iθ)) B)
            + ((volume.restrict (Set.Ioi 0)).prod (volume.restrict Work.Spaces.Iθ)) C :=
          add_le_add (measure_union_le A B) le_rfl
      _ = 0 := by rw [hAnull, hBnull, hCnull, add_zero, add_zero]
  exact measure_mono_null hsub hz

/-- `r ↦ F_*(F)(r)` is a.e. strongly measurable on `(0,∞)` for the data of `EllHyp`. -/
theorem aesm_Fstar (α : ℝ) (F Ψ : ℝ → ℝ → ℝ) (hsm : Work.Spaces.SmoothNbhd Ψ)
    (hsol : Work.Elliptic.IsBslSol α F Ψ) :
    AEStronglyMeasurable (fun r : ℝ => Work.Elliptic.Fstar F r)
      (volume.restrict (Set.Ioi 0)) := by
  have h1 := (aesm_F_mul_sinCos2 α F Ψ hsm hsol).integral_prod_right'
  simpa only [Work.Elliptic.Fstar] using h1

/-! ## 4. The pointwise bound in `ℝ≥0∞` -/

/-- **The pointwise `ℝ≥0∞` step.**  For `r > 0` and `θ ∈ Iθ`,

  `‖x·sinCos2 θ‖ₑ · ‖r‖ₑ⁻¹ ≤ ofReal ((x·(w(r)/sin(2θ)^{η/2}))²) + ofReal (((r·w(r))⁻¹)²)`. -/
theorem enorm_step (x r : ℝ) (hr : 0 < r) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    ‖x * Work.Elliptic.sinCos2 θ‖ₑ * (‖r‖ₑ)⁻¹
      ≤ ENNReal.ofReal ((x * (Work.Spaces.w r / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        + ENNReal.ofReal (((r * Work.Spaces.w r)⁻¹) ^ 2) := by
  have hσ0 : 0 ≤ Work.Elliptic.sinCos2 θ := sinCos2_nonneg_of_mem_Iθ hθ
  have hσ1 : Work.Elliptic.sinCos2 θ ≤ 1 := sinCos2_le_one θ
  have hnormr : (‖r‖ₑ : ℝ≥0∞) = ENNReal.ofReal r := by
    rw [Real.enorm_eq_ofReal_abs, abs_of_pos hr]
  have hLHS : ‖x * Work.Elliptic.sinCos2 θ‖ₑ * (‖r‖ₑ)⁻¹
      = ENNReal.ofReal (|x| * Work.Elliptic.sinCos2 θ / r) := by
    have hxn : ‖x * Work.Elliptic.sinCos2 θ‖ₑ
        = ENNReal.ofReal (|x| * Work.Elliptic.sinCos2 θ) := by
      rw [Real.enorm_eq_ofReal_abs, abs_mul, abs_of_nonneg hσ0]
    rw [hxn, hnormr, ← ENNReal.ofReal_inv_of_pos hr,
      ← ENNReal.ofReal_mul (mul_nonneg (abs_nonneg x) hσ0), div_eq_mul_inv]
  rw [hLHS]
  rcases eq_or_lt_of_le hσ0 with hσeq | hσpos
  · have hzero : Work.Elliptic.sinCos2 θ = 0 := by linarith
    rw [hzero]
    simp only [mul_zero, zero_div, ENNReal.ofReal_zero]
    exact zero_le
  · have hT0 : 0 < Real.sin (2 * θ) := by
      have hsin : 0 < Real.sin θ := by
        rw [Work.Elliptic.sinCos2] at hσpos
        by_contra hcon
        push_neg at hcon
        have hle : Real.sin θ * Real.cos θ ^ 2 ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg hcon (sq_nonneg _)
        linarith
      have hcos : 0 < Real.cos θ := by
        rw [Work.Elliptic.sinCos2] at hσpos
        have hc2 : Real.cos θ ^ 2 ≠ 0 := by
          intro h
          have : Real.sin θ * Real.cos θ ^ 2 = 0 := by rw [h, mul_zero]
          linarith
        have hcne : Real.cos θ ≠ 0 := fun h => hc2 (by rw [h]; ring)
        have hc0 : 0 ≤ Real.cos θ :=
          Real.cos_nonneg_of_mem_Icc
            ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2, Real.pi_pos]⟩
        exact lt_of_le_of_ne hc0 (Ne.symm hcne)
      rw [Real.sin_two_mul]
      positivity
    have hT1 : Real.sin (2 * θ) ≤ 1 := sin_two_le_one_of_mem_Iθ hθ
    calc ENNReal.ofReal (|x| * Work.Elliptic.sinCos2 θ / r)
        ≤ ENNReal.ofReal ((x * (Work.Spaces.w r / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
            + ((r * Work.Spaces.w r)⁻¹) ^ 2) :=
          ENNReal.ofReal_le_ofReal (young_weighted x r (Real.sin (2 * θ))
            (Work.Elliptic.sinCos2 θ) hr hσ0 hσ1 hT0 hT1)
      _ = ENNReal.ofReal ((x * (Work.Spaces.w r / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
            + ENNReal.ofReal (((r * Work.Spaces.w r)⁻¹) ^ 2) :=
          ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _)

/-! ## 5. The main estimate -/

theorem Fstar_div_integrable_of_EllHyp (α : ℝ) (k : ℕ) (F Ψ : ℝ → ℝ → ℝ) (hα : 0 < α)
    (hHyp : Work.FTS.EllipticEst.EllHyp α k F Ψ) :
    MeasureTheory.IntegrableOn (fun r : ℝ => Work.Elliptic.Fstar F r / r) (Set.Ioi 0) := by
  have hsm : Work.Spaces.SmoothNbhd Ψ := hHyp.smoothNbhd
  have hsol : Work.Elliptic.IsBslSol α F Ψ := hHyp.sol
  have hmem : Work.Spaces.HkMem α k F := hHyp.memF
  have hIθ_meas : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  have hVne : (volume Work.Spaces.Iθ : ℝ≥0∞) ≠ ⊤ := by
    rw [show Work.Spaces.Iθ = Set.Icc 0 (π / 2) from rfl, Real.volume_Icc]
    exact ENNReal.ofReal_ne_top
  have hVlt : (volume Work.Spaces.Iθ : ℝ≥0∞) < ⊤ := lt_top_iff_ne_top.mpr hVne
  have hAESM : AEStronglyMeasurable (fun r : ℝ => Work.Elliptic.Fstar F r / r)
      (volume.restrict (Set.Ioi 0)) :=
    aestronglyMeasurable_iff_aemeasurable.mpr
      ((aesm_Fstar α F Ψ hsm hsol).aemeasurable.div measurable_id.aemeasurable)
  refine ⟨hAESM, ?_⟩
  show (∫⁻ r in Set.Ioi 0, ‖Work.Elliptic.Fstar F r / r‖ₑ) < ∞
  set XX : ℝ → ℝ≥0∞ := fun r => ∫⁻ θ in Work.Spaces.Iθ,
      ‖F r θ * Work.Elliptic.sinCos2 θ‖ₑ * (‖r‖ₑ)⁻¹ with hXX
  set AA : ℝ → ℝ≥0∞ := fun r => ∫⁻ θ in Work.Spaces.Iθ,
      ENNReal.ofReal ((F r θ * (Work.Spaces.w r / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
    with hAA
  set BB : ℝ → ℝ≥0∞ := fun r => ENNReal.ofReal (((r * Work.Spaces.w r)⁻¹) ^ 2)
    * volume Work.Spaces.Iθ with hBB
  have hstep1 : (∫⁻ r in Set.Ioi 0, ‖Work.Elliptic.Fstar F r / r‖ₑ)
      ≤ ∫⁻ r in Set.Ioi 0, XX r := by
    refine lintegral_mono_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with r hr
    have hdiv : ‖Work.Elliptic.Fstar F r / r‖ₑ = ‖Work.Elliptic.Fstar F r‖ₑ * (‖r‖ₑ)⁻¹ := by
      have hrn : |r| = r := abs_of_pos hr
      have h1 : ‖Work.Elliptic.Fstar F r / r‖ₑ
          = ENNReal.ofReal (|Work.Elliptic.Fstar F r| / r) := by
        rw [Real.enorm_eq_ofReal_abs, abs_div, hrn]
      have h2 : ENNReal.ofReal (|Work.Elliptic.Fstar F r| / r)
          = ‖Work.Elliptic.Fstar F r‖ₑ * (‖r‖ₑ)⁻¹ := by
        have hnormr : (‖r‖ₑ : ℝ≥0∞) = ENNReal.ofReal r := by
          rw [Real.enorm_eq_ofReal_abs, abs_of_pos hr]
        rw [ENNReal.ofReal_div_of_pos hr, div_eq_mul_inv, hnormr, Real.enorm_eq_ofReal_abs]
      rw [h1, h2]
    calc ‖Work.Elliptic.Fstar F r / r‖ₑ
        = ‖Work.Elliptic.Fstar F r‖ₑ * (‖r‖ₑ)⁻¹ := hdiv
      _ ≤ (∫⁻ θ in Work.Spaces.Iθ, ‖F r θ * Work.Elliptic.sinCos2 θ‖ₑ) * (‖r‖ₑ)⁻¹ :=
          mul_le_mul_of_nonneg_right
            (MeasureTheory.enorm_integral_le_lintegral_enorm _) zero_le
      _ ≤ ∫⁻ θ in Work.Spaces.Iθ, ‖F r θ * Work.Elliptic.sinCos2 θ‖ₑ * (‖r‖ₑ)⁻¹ :=
          MeasureTheory.lintegral_mul_const_le _ _
      _ = XX r := by rw [hXX]
  have hstep2 : ∫⁻ r in Set.Ioi 0, XX r ≤ ∫⁻ r in Set.Ioi 0, (AA r + BB r) := by
    refine lintegral_mono_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with r hr
    have hsplit : (∫⁻ θ in Work.Spaces.Iθ,
          (ENNReal.ofReal ((F r θ * (Work.Spaces.w r / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
            + ENNReal.ofReal (((r * Work.Spaces.w r)⁻¹) ^ 2)))
        = AA r + BB r := by
      rw [hAA, hBB]
      rw [MeasureTheory.lintegral_add_right' _
        (aemeasurable_const :
          AEMeasurable (fun _ : ℝ => ENNReal.ofReal (((r * Work.Spaces.w r)⁻¹) ^ 2))
            (volume.restrict Work.Spaces.Iθ))]
      rw [MeasureTheory.lintegral_const, Measure.restrict_apply_univ]
    rw [hXX, ← hsplit]
    refine lintegral_mono_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem hIθ_meas] with θ hθ
    exact enorm_step (F r θ) r hr hθ
  have hBB_aem : AEMeasurable BB (volume.restrict (Set.Ioi 0)) := by
    have hcont : ContinuousOn (fun r : ℝ => ENNReal.ofReal ((r / (1 + r) ^ 2) ^ 2))
        (Set.Ioi 0) :=
      ENNReal.continuous_ofReal.comp_continuousOn (by
        refine (ContinuousOn.div ?_ ?_ ?_).pow 2
        · exact continuousOn_id
        · fun_prop
        · intro r hr
          have hr' : (0 : ℝ) < r := Set.mem_Ioi.mp hr
          positivity)
    have h1 : AEMeasurable (fun r : ℝ => ENNReal.ofReal ((r / (1 + r) ^ 2) ^ 2))
        (volume.restrict (Set.Ioi 0)) := hcont.aemeasurable measurableSet_Ioi
    have h2 : AEMeasurable (fun r : ℝ => ENNReal.ofReal ((r / (1 + r) ^ 2) ^ 2)
        * volume Work.Spaces.Iθ) (volume.restrict (Set.Ioi 0)) := h1.mul_const _
    have h2' : AEStronglyMeasurable (fun r : ℝ => ENNReal.ofReal ((r / (1 + r) ^ 2) ^ 2)
        * volume Work.Spaces.Iθ) (volume.restrict (Set.Ioi 0)) :=
      aestronglyMeasurable_iff_aemeasurable.mpr h2
    have h3 : AEStronglyMeasurable BB (volume.restrict (Set.Ioi 0)) := by
      refine h2'.congr ?_
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with r hr
      show ENNReal.ofReal ((r / (1 + r) ^ 2) ^ 2) * volume Work.Spaces.Iθ
        = ENNReal.ofReal (((r * Work.Spaces.w r)⁻¹) ^ 2) * volume Work.Spaces.Iθ
      rw [w_inv_sq_eq r hr]
    exact h3.aemeasurable
  have hstep3 : ∫⁻ r in Set.Ioi 0, (AA r + BB r)
      = (∫⁻ r in Set.Ioi 0, AA r) + (∫⁻ r in Set.Ioi 0, BB r) :=
    MeasureTheory.lintegral_add_right' _ hBB_aem
  have hAfin : (∫⁻ r in Set.Ioi 0, AA r) < ⊤ := by
    have h1 : ∫⁻ r in Set.Ioi 0, AA r
        ≤ ∫⁻ r in Set.Ioi 0, ∫⁻ θ in Work.Spaces.Iθ,
            ENNReal.ofReal (Work.Spaces.HkIntegrand α k F r θ) := by
      rw [hAA]
      refine lintegral_mono fun r => lintegral_mono fun θ => ?_
      exact ENNReal.ofReal_le_ofReal
        (Work.Spaces.sq_le_HkIntegrand_z α k F r θ 0 (Nat.zero_le k))
    have h2 : ∫⁻ r in Set.Ioi 0, ∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal (Work.Spaces.HkIntegrand α k F r θ)
        = ∫⁻ r in Set.Ioi 0,
            ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F r θ) := by
      refine lintegral_congr_ae ?_
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with r hr
      refine (MeasureTheory.ofReal_integral_eq_lintegral_ofReal
        (hmem.1 r (show r ∈ Work.Spaces.Iz from le_of_lt (Set.mem_Ioi.mp hr)))
        (Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α k F r θ)).symm
    have h3 : ∫⁻ r in Set.Ioi 0,
          ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F r θ)
        ≤ ∫⁻ r in Work.Spaces.Iz,
            ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F r θ) :=
      lintegral_mono_set
        (by intro x hx; exact show x ∈ Work.Spaces.Iz from le_of_lt (Set.mem_Ioi.mp hx))
    have h4 : (∫⁻ r in Work.Spaces.Iz,
          ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F r θ)) < ⊤ := by
      have heq : (fun r : ℝ => ENNReal.ofReal
            (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F r θ))
          = fun r : ℝ => ‖(∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F r θ)‖ₑ := by
        funext r
        rw [Real.enorm_eq_ofReal_abs,
          abs_of_nonneg (integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α k F r θ)]
      rw [heq]
      exact hmem.2.2
    have h23 : (∫⁻ r in Set.Ioi 0, ∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal (Work.Spaces.HkIntegrand α k F r θ))
        ≤ ∫⁻ r in Work.Spaces.Iz,
            ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F r θ) :=
      h2.le.trans h3
    exact lt_of_le_of_lt (h1.trans h23) h4
  have hBfin : (∫⁻ r in Set.Ioi 0, BB r) < ⊤ := by
    have h1 : ∫⁻ r in Set.Ioi 0, BB r
        = (∫⁻ r in Set.Ioi 0, ENNReal.ofReal (((r * Work.Spaces.w r)⁻¹) ^ 2))
          * volume Work.Spaces.Iθ := by
      show (∫⁻ r in Set.Ioi 0, ENNReal.ofReal (((r * Work.Spaces.w r)⁻¹) ^ 2)
            * volume Work.Spaces.Iθ)
          = (∫⁻ r in Set.Ioi 0, ENNReal.ofReal (((r * Work.Spaces.w r)⁻¹) ^ 2))
            * volume Work.Spaces.Iθ
      exact MeasureTheory.lintegral_mul_const' _ _ hVne
    have h2 : (∫⁻ r in Set.Ioi 0, ENNReal.ofReal (((r * Work.Spaces.w r)⁻¹) ^ 2)) < ⊤ := by
      have heq : (fun r : ℝ => ENNReal.ofReal (((r * Work.Spaces.w r)⁻¹) ^ 2))
          = fun r : ℝ => ‖((r * Work.Spaces.w r)⁻¹) ^ 2‖ₑ := by
        funext r
        rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (sq_nonneg _)]
      rw [heq]
      exact HasFiniteIntegralWInvSq
    rw [h1]
    exact ENNReal.mul_lt_top h2 hVlt
  calc (∫⁻ r in Set.Ioi 0, ‖Work.Elliptic.Fstar F r / r‖ₑ)
      ≤ ∫⁻ r in Set.Ioi 0, XX r := hstep1
    _ ≤ ∫⁻ r in Set.Ioi 0, (AA r + BB r) := hstep2
    _ = (∫⁻ r in Set.Ioi 0, AA r) + (∫⁻ r in Set.Ioi 0, BB r) := hstep3
    _ < ⊤ := ENNReal.add_lt_top.mpr ⟨hAfin, hBfin⟩

end Work.FTS.EllipticEst.Cert
