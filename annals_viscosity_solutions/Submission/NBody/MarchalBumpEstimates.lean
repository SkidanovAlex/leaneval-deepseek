import Submission.NBody.MarchalBump
import Submission.NBody.LYZRatio
import Submission.Commons.Analysis.Calculus.deriv_clamped_affine_smul_ae

/-!
# The kinetic cost of the symmetric bump

Part of the assembly of Marchal's theorem (see `Submission/ROADMAP.md`, section "SESSION 29"):
after the scaling identity of the transfer step, the kinetic part of the action difference of the
symmetric bump is

  `λ^{1/3} · ∫_0^T (massInner m (deriv Q t) (deriv d t) + ‖deriv d t‖_[m]² / 2) dt`,

where `d = stdCoef δ T · u₀` is the standard variation.  Since `deriv d = -(‖δ‖)⁻¹ • u₀` a.e. on
the window `(T-‖δ‖, T)` and `0` before it (`deriv_stdPert_ae`), this is a cost of order `‖δ‖`,
while the potential gain is of order `‖δ‖^{1/2}` — which is what makes small `‖δ‖` win.

Everything in this file is fully proved.
-/

open ViscositySolutions Filter Gradient
open Set Real Metric Finset InnerProductSpace MeasureTheory
open scoped BigOperators Topology

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable [MeasurableSpace E] [BorelSpace E]
variable {N : ℕ}

namespace Submission.NBody

lemma massInner_le_weightedNorm_mul (m : Fin N → ℝ) (hm : ∀ i, 0 ≤ m i) (v w : EN E N) :
    massInner m v w ≤ ‖v‖_[m] * ‖w‖_[m] := by
  rw [massInner_eq_inner_massScale' hm, weightedNorm_eq_norm_massScale hm,
    weightedNorm_eq_norm_massScale hm]
  exact real_inner_le_norm _ _

lemma neg_massInner_le_weightedNorm_mul (m : Fin N → ℝ) (hm : ∀ i, 0 ≤ m i) (v w : EN E N) :
    -massInner m v w ≤ ‖v‖_[m] * ‖w‖_[m] := by
  have h : massInner m v (-w) = -massInner m v w := by
    simp only [massInner, PiLp.neg_apply, inner_neg_right, mul_neg, Finset.sum_neg_distrib]
  have h1 : ‖(-w : EN E N)‖_[m] = ‖w‖_[m] := by
    rw [show (-w : EN E N) = (-1:ℝ) • w from by simp, weightedNorm_smul (fun i => hm i),
      abs_neg, abs_one, one_mul]
  have h2 := massInner_le_weightedNorm_mul m hm v (-w)
  rw [h1] at h2
  rw [← h]
  exact h2

/-- **The kinetic cost of the bump on its window.**  `b = -(‖δ‖)⁻¹ • u₀` is the derivative of the
standard variation and `‖δ‖` its window length. -/
theorem bump_kinetic_bound {m : Fin N → ℝ} (hm : ∀ i, 0 ≤ m i) (δ : E) (T Cd : ℝ)
    (u₀ : EN E N) (hT : 0 < T) (hCd : 0 ≤ Cd) (hδ : δ ≠ 0) (hδT : ‖δ‖ ≤ T / 2)
    (Q : ℝ → EN E N) (hQ : ∀ t ∈ Set.Ioc (0:ℝ) T, ‖deriv Q t‖_[m] ≤ Cd * t ^ (-(1:ℝ)/3)) :
    ∫ t in (T - ‖δ‖)..T,
        (2 * massInner m (deriv Q t) ((-(‖δ‖)⁻¹) • u₀) + ‖(-(‖δ‖)⁻¹) • u₀‖_[m] ^ 2)
      ≤ 2 * Cd * ‖u₀‖_[m] * (T / 2) ^ (-(1:ℝ)/3) + ‖u₀‖_[m] ^ 2 / ‖δ‖ := by
  have hd : (0:ℝ) < ‖δ‖ := norm_pos_iff.mpr hδ
  have hTd : (0:ℝ) < T - ‖δ‖ := by linarith
  have hge : T / 2 ≤ T - ‖δ‖ := by linarith
  set G : ℝ → ℝ := fun t => 2 * Cd * ‖u₀‖_[m] * t ^ (-(1:ℝ)/3) / ‖δ‖ + ‖u₀‖_[m] ^ 2 / ‖δ‖ ^ 2
    with hG
  have hbn : ‖(-(‖δ‖)⁻¹) • u₀‖_[m] ^ 2 = (‖u₀‖_[m] / ‖δ‖) ^ 2 := by
    rw [weightedNorm_smul (fun i => hm i), abs_neg, abs_of_pos (inv_pos.mpr hd),
      inv_mul_eq_div]
  have hpowint : IntervalIntegrable (fun t : ℝ => t ^ (-(1:ℝ)/3)) volume (T - ‖δ‖) T :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num : (-1:ℝ) < -(1:ℝ)/3)
  have hGint1 : IntervalIntegrable (fun t : ℝ => 2 * Cd * ‖u₀‖_[m] * t ^ (-(1:ℝ)/3) / ‖δ‖)
      volume (T - ‖δ‖) T := by
    have h := (hpowint.const_mul (2 * Cd * ‖u₀‖_[m])).div_const (‖δ‖)
    simpa only [mul_assoc] using h
  have hGint : IntervalIntegrable G volume (T - ‖δ‖) T := by
    have hpowint : IntervalIntegrable (fun t : ℝ => t ^ (-(1:ℝ)/3)) volume (T - ‖δ‖) T :=
      intervalIntegral.intervalIntegrable_rpow' (by norm_num : (-1:ℝ) < -(1:ℝ)/3)
    have h1 : IntervalIntegrable (fun t : ℝ => 2 * Cd * ‖u₀‖_[m] * t ^ (-(1:ℝ)/3) / ‖δ‖)
        volume (T - ‖δ‖) T := by
      have h2 := (hpowint.const_mul (2 * Cd * ‖u₀‖_[m])).div_const (‖δ‖)
      simpa only [mul_assoc] using h2
    exact h1.add intervalIntegrable_const
  have hle : ∀ t ∈ Set.Ioc (T - ‖δ‖) T,
      ‖2 * massInner m (deriv Q t) ((-(‖δ‖)⁻¹) • u₀) + ‖(-(‖δ‖)⁻¹) • u₀‖_[m] ^ 2‖ ≤ G t := by
    intro t ht
    have htI : t ∈ Set.Ioc (0:ℝ) T := ⟨lt_trans hTd ht.1, ht.2⟩
    have ht0 : (0:ℝ) < t := lt_trans hTd ht.1
    have hu : ‖deriv Q t‖_[m] ≤ Cd * t ^ (-(1:ℝ)/3) := hQ t htI
    have hkey : massInner m (deriv Q t) ((-(‖δ‖)⁻¹) • u₀)
        = -(‖δ‖)⁻¹ * massInner m (deriv Q t) u₀ := massInner_smul_right m _ _ _
    have habs : |massInner m (deriv Q t) u₀| ≤ ‖deriv Q t‖_[m] * ‖u₀‖_[m] := by
      rw [abs_le]
      constructor
      · have hh := neg_massInner_le_weightedNorm_mul m hm (deriv Q t) u₀
        linarith
      · exact massInner_le_weightedNorm_mul m hm (deriv Q t) u₀
    have hbn : ‖(-(‖δ‖)⁻¹) • u₀‖_[m] ^ 2 = (‖u₀‖_[m] / ‖δ‖) ^ 2 := by
      rw [weightedNorm_smul (fun i => hm i), abs_neg, abs_of_pos (inv_pos.mpr hd),
        inv_mul_eq_div]
    have hinv : (0:ℝ) ≤ (‖δ‖)⁻¹ := inv_nonneg.mpr hd.le
    have htri : ‖2 * massInner m (deriv Q t) ((-(‖δ‖)⁻¹) • u₀) + ‖(-(‖δ‖)⁻¹) • u₀‖_[m] ^ 2‖
        ≤ 2 * (‖δ‖)⁻¹ * |massInner m (deriv Q t) u₀| + (‖u₀‖_[m] / ‖δ‖) ^ 2 := by
      have h1 : |2 * (-(‖δ‖)⁻¹ * massInner m (deriv Q t) u₀)|
          = 2 * (‖δ‖)⁻¹ * |massInner m (deriv Q t) u₀| := by
        have heq : 2 * (-(‖δ‖)⁻¹ * massInner m (deriv Q t) u₀)
            = (2 * (‖δ‖)⁻¹) * (-(massInner m (deriv Q t) u₀)) := by ring
        rw [heq, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 * (‖δ‖)⁻¹), abs_neg]
      rw [hkey, hbn]
      calc |2 * (-(‖δ‖)⁻¹ * massInner m (deriv Q t) u₀) + (‖u₀‖_[m] / ‖δ‖) ^ 2|
          ≤ |2 * (-(‖δ‖)⁻¹ * massInner m (deriv Q t) u₀)| + |(‖u₀‖_[m] / ‖δ‖) ^ 2| :=
            abs_add_le _ _
        _ = 2 * (‖δ‖)⁻¹ * |massInner m (deriv Q t) u₀| + |(‖u₀‖_[m] / ‖δ‖) ^ 2| := by rw [h1]
        _ = 2 * (‖δ‖)⁻¹ * |massInner m (deriv Q t) u₀| + (‖u₀‖_[m] / ‖δ‖) ^ 2 := by
            congr 1
            exact abs_of_nonneg (sq_nonneg _)
    refine htri.trans ?_
    have h2 : 2 * (‖δ‖)⁻¹ * |massInner m (deriv Q t) u₀|
        ≤ 2 * (‖δ‖)⁻¹ * (‖deriv Q t‖_[m] * ‖u₀‖_[m]) :=
      mul_le_mul_of_nonneg_left habs (by positivity)
    have h6 : (‖δ‖)⁻¹ * (‖deriv Q t‖_[m] * ‖u₀‖_[m])
        ≤ (‖δ‖)⁻¹ * ((Cd * t ^ (-(1:ℝ)/3)) * ‖u₀‖_[m]) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hu (weightedNorm_nonneg m u₀)) hinv
    have h7 : 2 * (‖δ‖)⁻¹ * |massInner m (deriv Q t) u₀|
        ≤ 2 * (‖δ‖)⁻¹ * ((Cd * t ^ (-(1:ℝ)/3)) * ‖u₀‖_[m]) := h2.trans (by linarith [h6])
    have hG' : G t = 2 * (‖δ‖)⁻¹ * ((Cd * t ^ (-(1:ℝ)/3)) * ‖u₀‖_[m])
        + (‖u₀‖_[m] / ‖δ‖) ^ 2 := by
      rw [hG]; ring
    rw [hG']
    linarith [h7]
  have hFint : IntervalIntegrable
      (fun t : ℝ => 2 * massInner m (deriv Q t) ((-(‖δ‖)⁻¹) • u₀) + ‖(-(‖δ‖)⁻¹) • u₀‖_[m] ^ 2)
      volume (T - ‖δ‖) T := by
    refine hGint.mono_fun' ?_ ?_
    · have h1 : Measurable (fun t : ℝ => massInner m (deriv Q t) ((-(‖δ‖)⁻¹) • u₀)) := by
        have hc : Continuous (fun v : EN E N => massInner m v ((-(‖δ‖)⁻¹) • u₀)) := by
          simp only [massInner]
          fun_prop
        exact hc.measurable.comp (measurable_deriv Q)
      exact ((h1.const_mul 2).add measurable_const).aestronglyMeasurable
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_uIoc] with t ht
      rw [Set.uIoc_of_le (by linarith : T - ‖δ‖ ≤ T)] at ht
      rw [Real.norm_eq_abs]
      exact hle t ht
  have hmono : (∫ t in (T - ‖δ‖)..T,
        2 * massInner m (deriv Q t) ((-(‖δ‖)⁻¹) • u₀) + ‖(-(‖δ‖)⁻¹) • u₀‖_[m] ^ 2)
      ≤ ∫ t in (T - ‖δ‖)..T, G t :=
    intervalIntegral.integral_mono_on_of_le_Ioo (by linarith : T - ‖δ‖ ≤ T)
      hFint hGint (fun t ht => (le_abs_self _).trans (hle t ⟨ht.1, ht.2.le⟩))
  refine hmono.trans ?_
  have hpow : ∫ t in (T - ‖δ‖)..T, t ^ (-(1:ℝ)/3)
      = (3:ℝ)/2 * (T ^ ((2:ℝ)/3) - (T - ‖δ‖) ^ ((2:ℝ)/3)) := by
    rw [integral_rpow (Or.inl (by norm_num : (-1:ℝ) < -(1:ℝ)/3)),
      show (-(1:ℝ)/3 + 1) = (2:ℝ)/3 by norm_num]
    ring
  have hGval : ∫ t in (T - ‖δ‖)..T, G t
      = (∫ t in (T - ‖δ‖)..T, t ^ (-(1:ℝ)/3)) * (2 * Cd * ‖u₀‖_[m] / ‖δ‖)
        + ‖u₀‖_[m] ^ 2 / ‖δ‖ ^ 2 * (T - (T - ‖δ‖)) := by
    rw [hG, intervalIntegral.integral_add hGint1 intervalIntegrable_const]
    congr 1
    · rw [intervalIntegral.integral_div, intervalIntegral.integral_const_mul]
      ring
    · rw [intervalIntegral.integral_const]
      simp only [smul_eq_mul]
      ring
  have hIntBound : ∫ t in (T - ‖δ‖)..T, t ^ (-(1:ℝ)/3)
      ≤ (T - ‖δ‖) ^ (-(1:ℝ)/3) * ‖δ‖ := by
    have hmono := intervalIntegral.integral_mono_on_of_le_Ioo (by linarith : T - ‖δ‖ ≤ T)
      hpowint (intervalIntegrable_const (c := (T - ‖δ‖) ^ (-(1:ℝ)/3)))
      (fun t ht => Real.rpow_le_rpow_of_nonpos hTd ht.1.le (by norm_num))
    rw [intervalIntegral.integral_const] at hmono
    simp only [smul_eq_mul] at hmono
    rw [show T - (T - ‖δ‖) = ‖δ‖ by ring] at hmono
    simpa only [mul_comm] using hmono
  have hb1 : (T - ‖δ‖) ^ (-(1:ℝ)/3) ≤ (T / 2) ^ (-(1:ℝ)/3) :=
    Real.rpow_le_rpow_of_nonpos (by linarith : (0:ℝ) < T / 2) hge (by norm_num)
  have hconst : (‖u₀‖_[m] ^ 2 / ‖δ‖ ^ 2) * ‖δ‖ = ‖u₀‖_[m] ^ 2 / ‖δ‖ := by
    field_simp
  have hstep : (∫ t in (T - ‖δ‖)..T, t ^ (-(1:ℝ)/3)) * (2 * Cd * ‖u₀‖_[m] / ‖δ‖)
      ≤ 2 * Cd * ‖u₀‖_[m] * (T / 2) ^ (-(1:ℝ)/3) := by
    have hnn : (0:ℝ) ≤ 2 * Cd * ‖u₀‖_[m] / ‖δ‖ := by
      refine div_nonneg (mul_nonneg (by linarith) (weightedNorm_nonneg m u₀)) hd.le
    have hnn2 : (0:ℝ) ≤ 2 * Cd * ‖u₀‖_[m] := mul_nonneg (by linarith) (weightedNorm_nonneg m u₀)
    calc (∫ t in (T - ‖δ‖)..T, t ^ (-(1:ℝ)/3)) * (2 * Cd * ‖u₀‖_[m] / ‖δ‖)
        ≤ ((T - ‖δ‖) ^ (-(1:ℝ)/3) * ‖δ‖) * (2 * Cd * ‖u₀‖_[m] / ‖δ‖) :=
          mul_le_mul_of_nonneg_right hIntBound hnn
      _ = (T - ‖δ‖) ^ (-(1:ℝ)/3) * (2 * Cd * ‖u₀‖_[m]) := by
          field_simp
      _ ≤ (T / 2) ^ (-(1:ℝ)/3) * (2 * Cd * ‖u₀‖_[m]) :=
          mul_le_mul_of_nonneg_right hb1 hnn2
      _ = 2 * Cd * ‖u₀‖_[m] * (T / 2) ^ (-(1:ℝ)/3) := by ring
  rw [hGval]
  rw [show T - (T - ‖δ‖) = ‖δ‖ by ring, hconst]
  linarith [hstep]


/-- The derivative of the standard perturbation is the expected piecewise constant, almost
everywhere (it fails only at the kinks `T - ‖δ‖` and `T`, a null set). -/
lemma deriv_stdPert_ae {m : Fin N → ℝ} {k : Finset (Fin N)} {i₀ : Fin N}
    (δ : E) (T : ℝ) (hδ : δ ≠ 0) :
    (fun t : ℝ => deriv (fun s : ℝ => stdPert m k i₀ δ T s) t)
      =ᵐ[MeasureTheory.volume.restrict (Set.Ioc (0:ℝ) T)]
    (fun t : ℝ =>
      (if t ≤ T - ‖δ‖ then (0 : EN E N) else (-(‖δ‖)⁻¹) • stdPertVec m k i₀ δ)) := by
  have hfun : (fun s : ℝ => stdPert m k i₀ δ T s)
      = fun s : ℝ => stdCoef δ T s • stdPertVec m k i₀ δ := by
    funext s
    exact stdPert_eq_smul_stdPertVec δ T s
  rw [hfun]
  have hnorm : ‖(PiLp.single 2 i₀ δ : EN E N)‖ = ‖δ‖ := by
    simpa using PiLp.norm_single (p := 2) (β := fun _ : Fin N => E) i₀ δ
  have hδ' : (PiLp.single 2 i₀ δ : EN E N) ≠ 0 := by
    rw [← norm_pos_iff, hnorm]
    exact norm_pos_iff.mpr hδ
  have h := Commons.Analysis.Calculus.deriv_clamped_affine_smul_ae (PiLp.single 2 i₀ δ : EN E N) T hδ'
    (stdPertVec m k i₀ δ)
  rw [hnorm] at h
  simpa only [stdCoef] using h

end Submission.NBody
