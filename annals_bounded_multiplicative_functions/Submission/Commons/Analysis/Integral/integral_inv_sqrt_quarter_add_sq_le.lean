import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Commons.Analysis.Integral

open scoped Real
open MeasureTheory

set_option autoImplicit false

theorem integral_inv_sqrt_quarter_add_sq_le (T : ℝ) (hT : 1 ≤ T) :
    (∫ t : ℝ in -T..T, (Real.sqrt (1 / 4 + t ^ 2))⁻¹) ≤ 4 + 2 * Real.log T := by
  set f : ℝ → ℝ := fun t => (Real.sqrt (1 / 4 + t ^ 2))⁻¹ with hf
  have hsq_pos : ∀ t : ℝ, 0 < 1 / 4 + t ^ 2 := by
    intro t; nlinarith [sq_nonneg t]
  have hfpos : ∀ t : ℝ, 0 < Real.sqrt (1 / 4 + t ^ 2) := fun t => by
    rw [Real.sqrt_pos]; exact hsq_pos t
  have hfcont : Continuous f := by
    rw [hf]
    apply Continuous.inv₀
    · exact Real.continuous_sqrt.comp (by continuity)
    · intro t; exact ne_of_gt (hfpos t)
  have hint : ∀ a b : ℝ, IntervalIntegrable f volume a b := fun a b =>
    hfcont.intervalIntegrable a b
  -- pointwise bound on [1,T]
  have hle_inv : ∀ x ∈ Set.Icc (1:ℝ) T, f x ≤ x⁻¹ := by
    intro x hx
    have hxpos : 0 < x := lt_of_lt_of_le one_pos hx.1
    have hle : x ≤ Real.sqrt (1 / 4 + x ^ 2) := by
      have h1 : Real.sqrt (x ^ 2) ≤ Real.sqrt (1 / 4 + x ^ 2) := by
        apply Real.sqrt_le_sqrt
        nlinarith [sq_nonneg x]
      rwa [Real.sqrt_sq (le_of_lt hxpos)] at h1
    rw [hf]
    rw [inv_le_inv₀ (hfpos x) hxpos]
    exact hle
  -- integral bound over [1,T]
  have hT_int : (∫ x in (1:ℝ)..T, f x) ≤ Real.log T := by
    have hg : IntervalIntegrable (fun x : ℝ => x⁻¹) volume (1:ℝ) T := by
      apply ContinuousOn.intervalIntegrable
      rw [Set.uIcc_of_le hT]
      exact continuousOn_inv₀.mono (fun x hx => by
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        linarith [hx.1])
    have hmono := intervalIntegral.integral_mono_on hT (hint 1 T) hg hle_inv
    rw [integral_inv_of_pos one_pos (lt_of_lt_of_le one_pos hT)] at hmono
    simpa using hmono
  -- integral bound over [-1,1]
  have hmid : (∫ x in (-1:ℝ)..1, f x) ≤ 4 := by
    have hconst : IntervalIntegrable (fun _ : ℝ => (2:ℝ)) volume (-1:ℝ) 1 :=
      continuous_const.intervalIntegrable _ _
    have hle2 : ∀ x ∈ Set.Icc (-1:ℝ) 1, f x ≤ 2 := by
      intro x hx
      have hhalf : (1/2 : ℝ) ≤ Real.sqrt (1 / 4 + x ^ 2) := by
        rw [Real.le_sqrt (by norm_num) (le_of_lt (hsq_pos x))]
        nlinarith [sq_nonneg x]
      have h2 : (Real.sqrt (1 / 4 + x ^ 2))⁻¹ ≤ (2:ℝ) := by
        have h := (inv_le_inv₀ (hfpos x) (show (0:ℝ) < (1/2:ℝ) by norm_num)).2 hhalf
        have hone : ((1/2:ℝ))⁻¹ = 2 := by norm_num
        rwa [hone] at h
      rwa [hf]
    have hmono := intervalIntegral.integral_mono_on (by norm_num : (-1:ℝ) ≤ 1) (hint (-1) 1) hconst hle2
    rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
    norm_num at hmono
    exact hmono
  -- integral bound over [-T,-1]
  have hleft : (∫ x in (-T)..(-1:ℝ), f x) ≤ Real.log T := by
    have heven : ∀ x : ℝ, f (-x) = f x := by
      intro x; rw [hf]; simp only [neg_sq]
    have heq : (∫ x in (-T)..(-1:ℝ), f x) = ∫ x in (1:ℝ)..T, f x := by
      have h1 : (∫ x in (-T)..(-1:ℝ), f x) = ∫ x in (-T)..(-1:ℝ), f (-x) := by
        apply intervalIntegral.integral_congr
        intro x _
        exact (heven x).symm
      rw [h1, intervalIntegral.integral_comp_neg]
      norm_num
    rw [heq]
    exact hT_int
  -- split
  have hsplit1 : (∫ x in (-T)..(-1:ℝ), f x) + (∫ x in (-1:ℝ)..(1:ℝ), f x)
      = ∫ x in (-T)..(1:ℝ), f x :=
    intervalIntegral.integral_add_adjacent_intervals (hint (-T) (-1)) (hint (-1) 1)
  have hsplit2 : (∫ x in (-T)..(1:ℝ), f x) + (∫ x in (1:ℝ)..T, f x)
      = ∫ x in (-T)..T, f x :=
    intervalIntegral.integral_add_adjacent_intervals (hint (-T) 1) (hint 1 T)
  have hsum : (∫ x in (-T)..T, f x)
      = (∫ x in (-T)..(-1:ℝ), f x) + (∫ x in (-1:ℝ)..(1:ℝ), f x) + (∫ x in (1:ℝ)..T, f x) := by
    rw [← hsplit2, ← hsplit1]
  rw [hsum]
  linarith [hleft, hmid, hT_int]

end Commons.Analysis.Integral