import Mathlib

/-!
# The local mass is bounded by the integrated Fejér kernel

For a nonnegative, continuous, compactly supported `f : ℝ → ℝ`, a scale `T ≥ 1` and a
Fejér-type weight `sinc (π ·)²` that is at least `3/5` on `[-1/3, 1/3]`, the total mass of the
local averages of `f` at scale `1/T` is controlled by the double integral of `f` against the
rescaled kernel `(T/3) * sinc (π ((T/3)(z-u)))² * f u`:

  `(T/5) * ∫ z, f z * (∫_{z-1/T}^{z+1/T} f) ≤ ∫ z, f z * ∫ u, (T/3) sinc (π (T/3)(z-u))² f u`.

The proof is pointwise in `z`: on the interval `|z - u| ≤ 1/T` the rescaled kernel is at least
`T/5` by the hypothesis on `sinc`, and `f ≥ 0` everywhere; integrating the resulting pointwise
inequality over `u` (against the full line, using nonnegativity outside the interval) and then
multiplying by `f z ≥ 0` and integrating over `z` gives the claim.
-/

open MeasureTheory

namespace Work.GM.Affine

theorem local_mass_le_kernel_integral (T : ℝ) (hT : 1 ≤ T) (f : ℝ → ℝ) (hf : Continuous f)
    (hcs : HasCompactSupport f) (hnn : ∀ u, 0 ≤ f u)
    (hsin : ∀ y : ℝ, |y| ≤ 1 / 3 → (3 / 5 : ℝ) ≤ Real.sinc (Real.pi * y) ^ 2) :
    (T / 5) * ∫ z : ℝ, f z * (∫ u in Set.Icc (z - 1 / T) (z + 1 / T), f u)
      ≤ ∫ z : ℝ, f z * ∫ u : ℝ, (T / 3) * Real.sinc (Real.pi * ((T / 3) * (z - u))) ^ 2 * f u := by
  have hTpos : 0 < T := by linarith
  have hT3 : (0:ℝ) ≤ T / 3 := by linarith
  have hT5 : (0:ℝ) ≤ T / 5 := by linarith
  have hf_int : Integrable f := hf.integrable_of_hasCompactSupport hcs
  -- the elementary bound `sinc² ≤ 1`
  have hsq1 : ∀ x : ℝ, Real.sinc x ^ 2 ≤ 1 := by
    intro x
    have h := Real.abs_sinc_le_one x
    have h2 : Real.sinc x ^ 2 = |Real.sinc x| ^ 2 := (sq_abs _).symm
    nlinarith [h, abs_nonneg (Real.sinc x)]
  -- the rescaled kernel is bounded by `(T/3) f`
  have hpt : ∀ z u : ℝ,
      (T / 3) * Real.sinc (Real.pi * ((T / 3) * (z - u))) ^ 2 * f u ≤ (T / 3) * f u := by
    intro z u
    calc (T / 3) * Real.sinc (Real.pi * ((T / 3) * (z - u))) ^ 2 * f u
        ≤ (T / 3) * 1 * f u :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hsq1 _) hT3) (hnn u)
      _ = (T / 3) * f u := by ring
  -- integrability of the rescaled kernel against `f`, for each fixed `z`
  have hGint : ∀ z : ℝ, Integrable (fun u : ℝ =>
      (T / 3) * Real.sinc (Real.pi * ((T / 3) * (z - u))) ^ 2 * f u) := by
    intro z
    apply MeasureTheory.Integrable.mono' (hf_int.const_mul (T / 3))
    · fun_prop
    · filter_upwards with u
      rw [Real.norm_eq_abs]
      have hGnn : (0:ℝ) ≤ (T / 3) * Real.sinc (Real.pi * ((T / 3) * (z - u))) ^ 2 * f u :=
        mul_nonneg (mul_nonneg hT3 (sq_nonneg _)) (hnn u)
      rw [abs_of_nonneg hGnn]
      exact hpt z u
  -- the key pointwise-in-`z` inequality
  have hkey : ∀ z : ℝ, (T / 5) * (∫ u in Set.Icc (z - 1 / T) (z + 1 / T), f u)
      ≤ ∫ u : ℝ, (T / 3) * Real.sinc (Real.pi * ((T / 3) * (z - u))) ^ 2 * f u := by
    intro z
    set S : Set ℝ := Set.Icc (z - 1 / T) (z + 1 / T) with hS
    have hSmeas : MeasurableSet S := measurableSet_Icc
    have hSin : ∀ u ∈ S, (T / 5) * f u
        ≤ (T / 3) * Real.sinc (Real.pi * ((T / 3) * (z - u))) ^ 2 * f u := by
      intro u hu
      rw [hS] at hu
      have hzu : |z - u| ≤ 1 / T := by
        rw [abs_le]
        exact ⟨by linarith [hu.2], by linarith [hu.1]⟩
      have harg : |(T / 3) * (z - u)| ≤ 1 / 3 := by
        rw [abs_mul, abs_of_nonneg hT3]
        calc (T / 3) * |z - u| ≤ (T / 3) * (1 / T) := mul_le_mul_of_nonneg_left hzu hT3
          _ = 1 / 3 := by field_simp
      have hs := hsin ((T / 3) * (z - u)) harg
      calc (T / 5) * f u = (T / 3) * (3 / 5) * f u := by ring
        _ ≤ (T / 3) * Real.sinc (Real.pi * ((T / 3) * (z - u))) ^ 2 * f u :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs hT3) (hnn u)
    have hind : ∀ u : ℝ, S.indicator (fun u : ℝ => (T / 5) * f u) u
        ≤ (T / 3) * Real.sinc (Real.pi * ((T / 3) * (z - u))) ^ 2 * f u := by
      intro u
      rw [Set.indicator_apply]
      split_ifs with hu
      · exact hSin u hu
      · exact mul_nonneg (mul_nonneg hT3 (sq_nonneg _)) (hnn u)
    have hFint : Integrable (S.indicator (fun u : ℝ => (T / 5) * f u)) := by
      apply MeasureTheory.Integrable.mono' (hGint z)
      · exact (Continuous.aestronglyMeasurable
          (by fun_prop : Continuous fun u : ℝ => (T / 5) * f u)).indicator hSmeas
      · filter_upwards with u
        have hgnn : (0:ℝ) ≤ S.indicator (fun u : ℝ => (T / 5) * f u) u := by
          rw [Set.indicator_apply]
          split_ifs with hu
          · exact mul_nonneg hT5 (hnn u)
          · exact le_refl 0
        rw [Real.norm_eq_abs, abs_of_nonneg hgnn]
        exact hind u
    have hmono := MeasureTheory.integral_mono hFint (hGint z) hind
    rwa [MeasureTheory.integral_indicator hSmeas, MeasureTheory.integral_const_mul] at hmono
  -- measurability/integrability of `z ↦ f z * ∫ u, kernel(z,u) f u`
  have hBsm : StronglyMeasurable (fun z : ℝ =>
      ∫ u : ℝ, (T / 3) * Real.sinc (Real.pi * ((T / 3) * (z - u))) ^ 2 * f u) := by
    apply StronglyMeasurable.integral_prod_right
    exact (by fun_prop : Continuous (Function.uncurry (fun z u : ℝ =>
      (T / 3) * Real.sinc (Real.pi * ((T / 3) * (z - u))) ^ 2 * f u))).stronglyMeasurable
  have hRint : Integrable (fun z : ℝ =>
      f z * ∫ u : ℝ, (T / 3) * Real.sinc (Real.pi * ((T / 3) * (z - u))) ^ 2 * f u) := by
    apply MeasureTheory.Integrable.mono' (hf_int.const_mul ((T / 3) * ∫ u, f u))
    · exact (Continuous.aestronglyMeasurable hf).mul hBsm.aestronglyMeasurable
    · filter_upwards with z
      have hBnn : (0:ℝ) ≤
          ∫ u : ℝ, (T / 3) * Real.sinc (Real.pi * ((T / 3) * (z - u))) ^ 2 * f u :=
        MeasureTheory.integral_nonneg (fun u => mul_nonneg (mul_nonneg hT3 (sq_nonneg _)) (hnn u))
      have hBle : (∫ u : ℝ, (T / 3) * Real.sinc (Real.pi * ((T / 3) * (z - u))) ^ 2 * f u)
          ≤ (T / 3) * ∫ u, f u := by
        rw [← MeasureTheory.integral_const_mul]
        exact MeasureTheory.integral_mono (hGint z) (hf_int.const_mul (T / 3)) (fun u => hpt z u)
      have hRnn : (0:ℝ) ≤
          f z * ∫ u : ℝ, (T / 3) * Real.sinc (Real.pi * ((T / 3) * (z - u))) ^ 2 * f u :=
        mul_nonneg (hnn z) hBnn
      rw [Real.norm_eq_abs, abs_of_nonneg hRnn]
      calc f z * (∫ u : ℝ, (T / 3) * Real.sinc (Real.pi * ((T / 3) * (z - u))) ^ 2 * f u)
          ≤ f z * ((T / 3) * ∫ u, f u) := mul_le_mul_of_nonneg_left hBle (hnn z)
        _ = ((T / 3) * ∫ u, f u) * f z := by ring
  -- assemble: multiply the pointwise bound by `f z ≥ 0` and integrate in `z`
  have h1 : 0 ≤ᵐ[volume] (fun z : ℝ =>
      (T / 5) * (f z * (∫ u in Set.Icc (z - 1 / T) (z + 1 / T), f u))) := by
    filter_upwards with z
    exact mul_nonneg hT5 (mul_nonneg (hnn z) (MeasureTheory.integral_nonneg (fun u => hnn u)))
  have h2 : (fun z : ℝ => (T / 5) * (f z * (∫ u in Set.Icc (z - 1 / T) (z + 1 / T), f u)))
      ≤ᵐ[volume] (fun z : ℝ =>
        f z * ∫ u : ℝ, (T / 3) * Real.sinc (Real.pi * ((T / 3) * (z - u))) ^ 2 * f u) := by
    filter_upwards with z
    calc (T / 5) * (f z * (∫ u in Set.Icc (z - 1 / T) (z + 1 / T), f u))
        = f z * ((T / 5) * (∫ u in Set.Icc (z - 1 / T) (z + 1 / T), f u)) := by ring
      _ ≤ f z * (∫ u : ℝ, (T / 3) * Real.sinc (Real.pi * ((T / 3) * (z - u))) ^ 2 * f u) :=
          mul_le_mul_of_nonneg_left (hkey z) (hnn z)
  have hmono := MeasureTheory.integral_mono_of_nonneg h1 hRint h2
  rwa [MeasureTheory.integral_const_mul] at hmono

end Work.GM.Affine
