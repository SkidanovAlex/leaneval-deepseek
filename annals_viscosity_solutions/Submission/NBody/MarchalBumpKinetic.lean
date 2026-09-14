import Submission.NBody.MarchalBumpIntegrable

/-!
# The kinetic cost of the symmetric bump

`bump_kinetic_bound` (`MarchalBumpEstimates`) bounds the integral of the kinetic difference of the
standard variation over its window `(T - ‖δ‖, T)`.  This module converts it into the form needed by
the transfer identity `bump_real_action_eq`, namely the integral over the *whole* window `(0,T)` of
`massInner m q̇ ḋ + ½‖ḋ‖²`, where `d` is the standard variation (which vanishes on `(0, T - ‖δ‖)`).

All results in this file are fully proved.
-/

open ViscositySolutions Filter Gradient
open Set Real Metric Finset InnerProductSpace MeasureTheory
open scoped BigOperators Topology

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable [MeasurableSpace E] [BorelSpace E]
variable [Nontrivial E]
variable {N : ℕ}

namespace Submission.NBody

theorem bump_kinetic_cost {m : Fin N → ℝ} (hm : ∀ i, 0 < m i) {k : Finset (Fin N)} {i₀ : Fin N}
    (δ : E) (hδ : δ ≠ 0) {lam T t₀ : ℝ} (hT : 0 < T) (hδT : ‖δ‖ ≤ T / 2)
    {Cd : ℝ} (hCd : 0 ≤ Cd) {γ : ℝ → EN E N}
    (hvel : ∀ t ∈ Ioc (0:ℝ) T, ‖deriv (bumpRescaled m k γ t₀ lam) t‖_[m] ≤ Cd * t ^ (-(1:ℝ)/3)) :
    ∫ s in (0:ℝ)..T, (massInner m (deriv (bumpRescaled m k γ t₀ lam) s)
          (deriv (stdVarVec m k i₀ δ T) s)
        + (1 / 2) * ‖deriv (stdVarVec m k i₀ δ T) s‖_[m] ^ 2)
      ≤ Cd * ‖stdPertVec m k i₀ δ‖_[m] * (T / 2) ^ (-(1:ℝ)/3)
        + ‖stdPertVec m k i₀ δ‖_[m] ^ 2 / (2 * ‖δ‖) := by
  classical
  have hd : (0:ℝ) < ‖δ‖ := norm_pos_iff.mpr hδ
  have hdT : 0 < T - ‖δ‖ := by linarith
  have hge : T / 2 ≤ T - ‖δ‖ := by linarith
  set u₀ : EN E N := stdPertVec m k i₀ δ with hu₀
  set W : EN E N := (-(‖δ‖)⁻¹) • u₀ with hW
  have hWnorm : ‖W‖_[m] = ‖u₀‖_[m] * ‖δ‖⁻¹ := by
    rw [hW, weightedNorm_smul (fun i => (hm i).le), abs_neg, abs_of_pos (inv_pos.mpr hd),
      mul_comm]
  set H' : ℝ → ℝ := fun s => massInner m (deriv (bumpRescaled m k γ t₀ lam) s) W
    + (1 / 2) * ‖W‖_[m] ^ 2 with hH'
  set J : ℝ → ℝ := fun s => if s ≤ T - ‖δ‖ then 0 else H' s with hJ
  -- (i) the integrand equals `J` almost everywhere
  have hae := deriv_stdVarVec_ae (m := m) (k := k) (i₀ := i₀) δ T hδ
  have hae' : ∀ᵐ s ∂(volume : Measure ℝ), s ∈ Set.Ioc (0:ℝ) T →
      deriv (stdVarVec m k i₀ δ T) s = stdVarVecDeriv m k i₀ δ T s :=
    (MeasureTheory.ae_restrict_iff' measurableSet_Ioc).mp hae
  have hstep1 : ∫ s in (0:ℝ)..T, (massInner m (deriv (bumpRescaled m k γ t₀ lam) s)
        (deriv (stdVarVec m k i₀ δ T) s) + (1 / 2) * ‖deriv (stdVarVec m k i₀ δ T) s‖_[m] ^ 2)
      = ∫ s in (0:ℝ)..T, J s := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hae'] with s hs hsIoc
    have hIoc : s ∈ Set.Ioc (0:ℝ) T := by rwa [Set.uIoc_of_le hT.le] at hsIoc
    rw [hs hIoc]
    by_cases hle : s ≤ T - ‖δ‖
    · have hV : stdVarVecDeriv m k i₀ δ T s = 0 := by rw [stdVarVecDeriv, if_pos hle]
      simp only [hJ, hV, if_pos hle, mul_zero, weightedNorm_zero, add_zero]
      simp [massInner]
    · have hV : stdVarVecDeriv m k i₀ δ T s = W := by
        rw [stdVarVecDeriv, if_neg hle, hW]
      simp only [hJ, hV, if_neg hle]
      rfl
  -- (ii) integrability of `H'` on the window
  have hH'int : IntervalIntegrable H' volume (T - ‖δ‖) T := by
    set A₀ : ℝ := ‖u₀‖_[m] * ‖δ‖⁻¹ with hA₀
    have hA₀nn : 0 ≤ A₀ := mul_nonneg (weightedNorm_nonneg m _) (inv_nonneg.mpr (norm_nonneg δ))
    have hWn : ‖W‖_[m] = A₀ := by rw [hWnorm, hA₀]
    have hmeas : AEStronglyMeasurable H' (volume.restrict (Set.uIoc (T - ‖δ‖) T)) := by
      have hco : Continuous (fun v : EN E N => massInner m v W) := by
        unfold massInner
        fun_prop
      exact ((hco.measurable.comp (measurable_deriv _)).add measurable_const).aestronglyMeasurable
    refine (intervalIntegrable_const (c := Cd * A₀ * (T / 2) ^ (-(1:ℝ)/3) + (1 / 2) * A₀ ^ 2)
      (a := T - ‖δ‖) (b := T)).mono_fun' hmeas ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_uIoc] with s hs
    rw [Set.uIoc_of_le (by linarith : T - ‖δ‖ ≤ T)] at hs
    have hspos : 0 < s := lt_of_lt_of_le hdT hs.1.le
    have hsIoc : s ∈ Set.Ioc (0:ℝ) T := ⟨hspos, hs.2⟩
    have h1 : ‖deriv (bumpRescaled m k γ t₀ lam) s‖_[m] ≤ Cd * s ^ (-(1:ℝ)/3) := hvel s hsIoc
    have h2 : s ^ (-(1:ℝ)/3) ≤ (T / 2) ^ (-(1:ℝ)/3) :=
      Real.rpow_le_rpow_of_nonpos (by linarith : (0:ℝ) < T / 2) (le_trans hge hs.1.le)
        (by norm_num)
    have h8 : Cd * s ^ (-(1:ℝ)/3) ≤ Cd * (T / 2) ^ (-(1:ℝ)/3) :=
      mul_le_mul_of_nonneg_left h2 hCd
    have h3 : massInner m (deriv (bumpRescaled m k γ t₀ lam) s) W
        ≤ ‖deriv (bumpRescaled m k γ t₀ lam) s‖_[m] * A₀ := by
      rw [← hWn]
      exact massInner_le_weightedNorm_mul m (fun i => (hm i).le) _ _
    have h4 : -massInner m (deriv (bumpRescaled m k γ t₀ lam) s) W
        ≤ ‖deriv (bumpRescaled m k γ t₀ lam) s‖_[m] * A₀ := by
      rw [← hWn]
      exact neg_massInner_le_weightedNorm_mul m (fun i => (hm i).le) _ _
    have h10 : ‖deriv (bumpRescaled m k γ t₀ lam) s‖_[m] * A₀
        ≤ Cd * s ^ (-(1:ℝ)/3) * A₀ := mul_le_mul_of_nonneg_right h1 hA₀nn
    have h11 : Cd * s ^ (-(1:ℝ)/3) * A₀ ≤ Cd * (T / 2) ^ (-(1:ℝ)/3) * A₀ :=
      mul_le_mul_of_nonneg_right h8 hA₀nn
    have hub : massInner m (deriv (bumpRescaled m k γ t₀ lam) s) W + (1 / 2) * ‖W‖_[m] ^ 2
        ≤ Cd * A₀ * (T / 2) ^ (-(1:ℝ)/3) + (1 / 2) * A₀ ^ 2 := by
      rw [hWn]
      have heq : Cd * (T / 2) ^ (-(1:ℝ)/3) * A₀ = Cd * A₀ * (T / 2) ^ (-(1:ℝ)/3) := by ring
      linarith [h3, h10, h11, heq]
    have hlb : -(Cd * A₀ * (T / 2) ^ (-(1:ℝ)/3) + (1 / 2) * A₀ ^ 2)
        ≤ massInner m (deriv (bumpRescaled m k γ t₀ lam) s) W + (1 / 2) * ‖W‖_[m] ^ 2 := by
      rw [hWn]
      have heq : Cd * (T / 2) ^ (-(1:ℝ)/3) * A₀ = Cd * A₀ * (T / 2) ^ (-(1:ℝ)/3) := by ring
      linarith [h4, h10, h11, heq, sq_nonneg A₀]
    rw [Real.norm_eq_abs, hH', abs_le]
    exact ⟨hlb, hub⟩
  -- (iii) `J` is integrable on both halves
  have hJ1 : IntervalIntegrable J volume (0:ℝ) (T - ‖δ‖) :=
    IntervalIntegrable.congr (f := fun _ : ℝ => (0:ℝ)) (g := J)
      (fun x hx => by
        rw [Set.uIoc_of_le hdT.le] at hx
        have hxle : x ≤ T - ‖δ‖ := (Set.mem_Ioc.mp hx).2
        simp only [hJ, if_pos hxle])
      (intervalIntegrable_const (c := (0:ℝ)))
  have hJ2 : IntervalIntegrable J volume (T - ‖δ‖) T := by
    refine hH'int.congr_ae ?_
    have hnull : ∀ᵐ x : ℝ ∂(volume.restrict (Set.Ioc (T - ‖δ‖) T)), x ≠ T - ‖δ‖ := by
      rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
      have h : ∀ᵐ x : ℝ ∂(volume : Measure ℝ), x ≠ T - ‖δ‖ := by
        rw [MeasureTheory.ae_iff]; simp
      filter_upwards [h] with x hx _
      exact hx
    rw [Set.uIoc_of_le (by linarith : T - ‖δ‖ ≤ T)]
    filter_upwards [hnull, MeasureTheory.ae_restrict_mem measurableSet_Ioc] with x hx hxIoc
    simp only [hH', hJ, if_neg (not_le.mpr hxIoc.1)]
  have hstep2 : (∫ s in (0:ℝ)..(T - ‖δ‖), J s) + (∫ s in (T - ‖δ‖)..T, J s)
      = ∫ s in (0:ℝ)..T, J s :=
    intervalIntegral.integral_add_adjacent_intervals hJ1 hJ2
  have hJzero : ∫ s in (0:ℝ)..(T - ‖δ‖), J s = 0 := by
    have heq : Set.EqOn J (fun _ : ℝ => (0:ℝ)) (Set.uIcc (0:ℝ) (T - ‖δ‖)) := by
      intro x hx
      rw [Set.uIcc_of_le hdT.le] at hx
      have hxle : x ≤ T - ‖δ‖ := (Set.mem_Icc.mp hx).2
      simp only [hJ, if_pos hxle]
    rw [intervalIntegral.integral_congr heq, intervalIntegral.integral_zero]
  -- (iv) on the right half, `J = H'` a.e.
  have hstep3 : ∫ s in (T - ‖δ‖)..T, J s = ∫ s in (T - ‖δ‖)..T, H' s := by
    refine intervalIntegral.integral_congr_ae ?_
    have hnull : ∀ᵐ x : ℝ ∂(volume : Measure ℝ), x ≠ T - ‖δ‖ := by
      rw [MeasureTheory.ae_iff]; simp
    filter_upwards [hnull] with x hx hxu
    rw [Set.uIoc_of_le (by linarith : T - ‖δ‖ ≤ T)] at hxu
    simp only [hJ, if_neg (not_le.mpr hxu.1)]
  -- (v) `H'` is half the integrand of `bump_kinetic_bound`
  have hstep4 : ∫ s in (T - ‖δ‖)..T, H' s
      = (1 / 2) * ∫ s in (T - ‖δ‖)..T,
          (2 * massInner m (deriv (bumpRescaled m k γ t₀ lam) s) W + ‖W‖_[m] ^ 2) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun s _ => ?_
    rw [hH']
    ring
  have hbound := bump_kinetic_bound (m := m) (fun i => (hm i).le) δ T Cd u₀ hT hCd hδ hδT
    (bumpRescaled m k γ t₀ lam) hvel
  have hhalf : (1 / 2) * (2 * Cd * ‖u₀‖_[m] * (T / 2) ^ (-(1:ℝ)/3)
        + ‖u₀‖_[m] ^ 2 / ‖δ‖)
      = Cd * ‖u₀‖_[m] * (T / 2) ^ (-(1:ℝ)/3) + ‖u₀‖_[m] ^ 2 / (2 * ‖δ‖) := by
    field_simp
  calc ∫ s in (0:ℝ)..T, (massInner m (deriv (bumpRescaled m k γ t₀ lam) s)
          (deriv (stdVarVec m k i₀ δ T) s)
        + (1 / 2) * ‖deriv (stdVarVec m k i₀ δ T) s‖_[m] ^ 2)
      = ∫ s in (0:ℝ)..T, J s := hstep1
    _ = (∫ s in (0:ℝ)..(T - ‖δ‖), J s) + (∫ s in (T - ‖δ‖)..T, J s) := hstep2.symm
    _ = (0:ℝ) + (∫ s in (T - ‖δ‖)..T, J s) := by rw [hJzero]
    _ = ∫ s in (T - ‖δ‖)..T, H' s := by rw [zero_add, hstep3]
    _ = (1 / 2) * ∫ s in (T - ‖δ‖)..T,
        (2 * massInner m (deriv (bumpRescaled m k γ t₀ lam) s) W + ‖W‖_[m] ^ 2) := hstep4
    _ ≤ (1 / 2) * (2 * Cd * ‖u₀‖_[m] * (T / 2) ^ (-(1:ℝ)/3) + ‖u₀‖_[m] ^ 2 / ‖δ‖) :=
        mul_le_mul_of_nonneg_left hbound (by norm_num)
    _ = Cd * ‖u₀‖_[m] * (T / 2) ^ (-(1:ℝ)/3) + ‖u₀‖_[m] ^ 2 / (2 * ‖δ‖) := hhalf

end Submission.NBody
