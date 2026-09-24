import Mathlib

/-!
# Overlapping window counting (`Σ_f ∫_{[c,d]} 1_{|x-f| ≤ κ} h ≤ C ∫_{[c,d]} h`)

If every point `x ∈ [c,d]` is covered by at most `C` of the windows
`[f - κ, f + κ]` (`f ∈ Fr`), and `h ≥ 0` is continuous on `[c,d]`, then the total
mass of `h` counted with multiplicity over the windows is at most `C` times the
mass of `h` on `[c,d]`.

The proof is the standard one: swap the (finite) sum and the integral
(`MeasureTheory.integral_finsetSum`), and compare the integrand
`#{f : |x - f| ≤ κ} * h x ≤ C * h x` pointwise.  Integrability of every window
function is obtained from the uniform bound on `h` on the compact interval
(`IsCompact.exists_isMaxOn`).
-/

namespace Work.GM.Energy.EnergyCore

open MeasureTheory
open scoped BigOperators

set_option autoImplicit false

/-- A finite sum of `if P i then a else 0` is the number of `i` with `P i`, times `a`. -/
lemma sum_ite_const_eq_card_mul {ι : Type*} (s : Finset ι) (P : ι → Prop) [DecidablePred P]
    (a : ℝ) : ∑ i ∈ s, (if P i then a else 0) = (s.filter P).card * a := by
  rw [Finset.sum_ite]
  simp [Finset.sum_const, nsmul_eq_mul]

/-- The window function `x ↦ if |x - f| ≤ κ then h x else 0` is the indicator of the
closed interval `[f - κ, f + κ]` times `h`. -/
lemma window_eq_indicator {f κ : ℝ} {h : ℝ → ℝ} :
    (fun x : ℝ => (if |x - f| ≤ κ then h x else 0)) = (Set.Icc (f - κ) (f + κ)).indicator h := by
  funext x
  have key : x ∈ Set.Icc (f - κ) (f + κ) ↔ |x - f| ≤ κ := by
    rw [Set.mem_Icc, abs_le]
    constructor <;> intro hx <;> exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  by_cases hx : x ∈ Set.Icc (f - κ) (f + κ)
  · rw [Set.indicator_of_mem hx, if_pos (key.mp hx)]
  · rw [Set.indicator_of_notMem hx, if_neg (fun hc => hx (key.mpr hc))]

theorem sum_window_le {Fr : Finset ℝ} {c d C κ : ℝ} (hcd : c ≤ d) (hC : 0 ≤ C) {h : ℝ → ℝ}
    (hh : ContinuousOn h (Set.Icc c d)) (h0 : ∀ x ∈ Set.Icc c d, 0 ≤ h x)
    (hcard : ∀ x ∈ Set.Icc c d, ((Fr.filter (fun f => |x - f| ≤ κ)).card : ℝ) ≤ C) :
    ∑ f ∈ Fr, ∫ x in c..d, (if |x - f| ≤ κ then h x else 0) ≤ C * ∫ x in c..d, h x := by
  classical
  have hc_mem : c ∈ Set.Icc c d := ⟨le_rfl, hcd⟩
  -- a uniform bound for `h` on the compact interval `[c,d]`
  obtain ⟨x₀, hx₀mem, hmax⟩ := isCompact_Icc.exists_isMaxOn ⟨c, hc_mem⟩ hh
  have hM0 : 0 ≤ h x₀ := le_trans (h0 c hc_mem) (hmax hc_mem)
  have hMle : ∀ x ∈ Set.Icc c d, h x ≤ h x₀ := fun x hx => hmax hx
  -- `h` is a.e. strongly measurable on `(c,d]`
  have hae : AEStronglyMeasurable h (volume.restrict (Set.Ioc c d)) :=
    hh.aestronglyMeasurable_of_subset_isCompact isCompact_Icc measurableSet_Ioc
      Set.Ioc_subset_Icc_self
  -- each window function is integrable
  have hInt : ∀ f : ℝ, Integrable (fun x : ℝ => (if |x - f| ≤ κ then h x else 0))
        (volume.restrict (Set.Ioc c d)) := by
    intro f
    have h1 : Integrable ((Set.Icc (f - κ) (f + κ)).indicator h)
        (volume.restrict (Set.Ioc c d)) := by
      refine Integrable.of_bound ?_ (h x₀) ?_
      · exact hae.indicator measurableSet_Icc
      · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
        have hxI : x ∈ Set.Icc c d := Set.Ioc_subset_Icc_self hx
        rw [Set.indicator_apply]
        by_cases hxi : x ∈ Set.Icc (f - κ) (f + κ)
        · rw [if_pos hxi, Real.norm_eq_abs, abs_of_nonneg (h0 x hxI)]
          exact hMle x hxI
        · rw [if_neg hxi, norm_zero]
          exact hM0
    rwa [← window_eq_indicator] at h1
  -- swap the finite sum and the integral
  have hsum : ∑ f ∈ Fr, ∫ x in Set.Ioc c d, (if |x - f| ≤ κ then h x else 0)
      = ∫ x in Set.Ioc c d, ∑ f ∈ Fr, (if |x - f| ≤ κ then h x else 0) :=
    (MeasureTheory.integral_finsetSum (μ := volume.restrict (Set.Ioc c d)) Fr
      (f := fun f x => if |x - f| ≤ κ then h x else 0) (fun f _ => hInt f)).symm
  -- the integrand is bounded by `C * h` and is nonnegative
  have hle_ae : (fun x : ℝ => ∑ f ∈ Fr, (if |x - f| ≤ κ then h x else 0))
      ≤ᵐ[volume.restrict (Set.Ioc c d)] (fun x : ℝ => C * h x) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    have hxI : x ∈ Set.Icc c d := Set.Ioc_subset_Icc_self hx
    rw [sum_ite_const_eq_card_mul Fr (fun f => |x - f| ≤ κ) (h x)]
    exact mul_le_mul_of_nonneg_right (hcard x hxI) (h0 x hxI)
  have hnonneg_ae : (0 : ℝ → ℝ) ≤ᵐ[volume.restrict (Set.Ioc c d)]
      (fun x : ℝ => ∑ f ∈ Fr, (if |x - f| ≤ κ then h x else 0)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    have hxI : x ∈ Set.Icc c d := Set.Ioc_subset_Icc_self hx
    exact Finset.sum_nonneg fun f _ => by
      by_cases hc : |x - f| ≤ κ
      · rw [if_pos hc]; exact h0 x hxI
      · rw [if_neg hc]
  have hCh_int : Integrable (fun x : ℝ => C * h x) (volume.restrict (Set.Ioc c d)) := by
    refine Integrable.of_bound (hae.const_mul C) (C * h x₀) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    have hxI : x ∈ Set.Icc c d := Set.Ioc_subset_Icc_self hx
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hC (h0 x hxI))]
    exact mul_le_mul_of_nonneg_left (hMle x hxI) hC
  simp only [intervalIntegral.integral_of_le hcd]
  rw [hsum]
  calc ∫ x in Set.Ioc c d, ∑ f ∈ Fr, (if |x - f| ≤ κ then h x else 0)
      ≤ ∫ x in Set.Ioc c d, C * h x :=
        MeasureTheory.integral_mono_of_nonneg hnonneg_ae hCh_int hle_ae
    _ = C * ∫ x in Set.Ioc c d, h x := MeasureTheory.integral_const_mul C h

end Work.GM.Energy.EnergyCore
