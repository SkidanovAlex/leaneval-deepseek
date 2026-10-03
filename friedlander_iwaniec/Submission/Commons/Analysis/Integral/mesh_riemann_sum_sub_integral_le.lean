import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

namespace Commons.Analysis.Integral

open MeasureTheory Filter Finset intervalIntegral
open scoped BigOperators Topology

theorem mesh_riemann_sum_sub_integral_le {n : ℕ} (F F' : ℝ → ℂ) {h M : ℝ} (hh : 0 < h) (hM : 0 ≤ M)
    (hderiv : ∀ t ∈ Set.Icc (0 : ℝ) ((n : ℝ) * h), HasDerivAt F (F' t) t)
    (hbound : ∀ t ∈ Set.Icc (0 : ℝ) ((n : ℝ) * h), ‖F' t‖ ≤ M) :
    ‖h * (∑ p ∈ Finset.range n, F ((p : ℝ) * h)) - ∫ t in (0 : ℝ)..((n : ℝ) * h), F t‖
      ≤ h * ((n : ℝ) * h) * M := by
  have hcont : ContinuousOn F (Set.Icc (0 : ℝ) ((n : ℝ) * h)) :=
    fun x hx => (hderiv x hx).continuousAt.continuousWithinAt
  have ha_nonneg : ∀ p : ℕ, 0 ≤ (p : ℝ) * h :=
    fun p => mul_nonneg (Nat.cast_nonneg p) (le_of_lt hh)
  have hmono : ∀ p : ℕ, (p : ℝ) * h ≤ (((p + 1 : ℕ)) : ℝ) * h := by
    intro p
    apply mul_le_mul_of_nonneg_right _ (le_of_lt hh)
    push_cast; linarith
  have hale : ∀ p : ℕ, p ≤ n → (p : ℝ) * h ≤ (n : ℝ) * h := by
    intro p hp
    apply mul_le_mul_of_nonneg_right _ (le_of_lt hh)
    exact_mod_cast hp
  have hdiff : ∀ p : ℕ, (((p + 1 : ℕ)) : ℝ) * h - (p : ℝ) * h = h := by
    intro p; push_cast; ring
  -- interval integrability on each mesh cell
  have hIntF : ∀ p : ℕ, p < n → IntervalIntegrable F volume ((p : ℝ) * h) ((((p + 1 : ℕ)) : ℝ) * h) := by
    intro p hp
    apply ContinuousOn.intervalIntegrable
    apply hcont.mono
    rw [Set.uIcc_of_le (hmono p)]
    intro x hx
    exact ⟨by linarith [hx.1, ha_nonneg p],
           by linarith [hx.2, hale (p + 1) (by omega)]⟩
  -- split the integral into mesh cells
  have hI : ∫ t in (0 : ℝ)..((n : ℝ) * h), F t
      = ∑ p ∈ Finset.range n, ∫ t in ((p : ℝ) * h)..((((p + 1 : ℕ)) : ℝ) * h), F t := by
    have h := sum_integral_adjacent_intervals (μ := volume) (f := F)
        (a := fun k : ℕ => (k : ℝ) * h) (n := n)
        (fun k hk => hIntF k hk)
    simp only [Nat.cast_zero, zero_mul] at h
    exact h.symm
  -- rewrite each Riemann term via the constant integral on a cell
  have hcell : ∀ p : ℕ, p < n →
      ∫ t in ((p : ℝ) * h)..((((p + 1 : ℕ)) : ℝ) * h), (F ((p : ℝ) * h) - F t)
        = h * F ((p : ℝ) * h) - ∫ t in ((p : ℝ) * h)..((((p + 1 : ℕ)) : ℝ) * h), F t := by
    intro p hp
    rw [intervalIntegral.integral_sub intervalIntegrable_const (hIntF p hp)]
    congr 1
    rw [intervalIntegral.integral_const, hdiff p, Complex.real_smul]
  -- exact identity for the error
  have key : h * (∑ p ∈ Finset.range n, F ((p : ℝ) * h)) - ∫ t in (0 : ℝ)..((n : ℝ) * h), F t
      = ∑ p ∈ Finset.range n,
          ∫ t in ((p : ℝ) * h)..((((p + 1 : ℕ)) : ℝ) * h), (F ((p : ℝ) * h) - F t) := by
    rw [hI, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun p hp => (hcell p (Finset.mem_range.mp hp)).symm
  -- bound each cell error
  have hterm : ∀ p ∈ Finset.range n,
      ‖∫ t in ((p : ℝ) * h)..((((p + 1 : ℕ)) : ℝ) * h), (F ((p : ℝ) * h) - F t)‖ ≤ M * h * h := by
    intro p hp
    have hpn : p < n := Finset.mem_range.mp hp
    have hle := hmono p
    have hbnd : ∀ t ∈ Set.uIoc ((p : ℝ) * h) ((((p + 1 : ℕ)) : ℝ) * h),
        ‖F ((p : ℝ) * h) - F t‖ ≤ M * h := by
      intro t ht
      rw [Set.uIoc_of_le hle] at ht
      have hap_mem : (p : ℝ) * h ∈ Set.Icc (0 : ℝ) ((n : ℝ) * h) :=
        ⟨ha_nonneg p, hale p (le_of_lt hpn)⟩
      have ht_mem : t ∈ Set.Icc (0 : ℝ) ((n : ℝ) * h) :=
        ⟨by linarith [ht.1, ha_nonneg p],
         by linarith [ht.2, hale (p + 1) (by omega)]⟩
      have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
        (f := F) (f' := F') (s := Set.Icc (0 : ℝ) ((n : ℝ) * h)) (C := M)
        (fun x hx => (hderiv x hx).hasDerivWithinAt)
        (fun x hx => hbound x hx)
        (convex_Icc 0 ((n : ℝ) * h)) ht_mem hap_mem
      calc ‖F ((p : ℝ) * h) - F t‖ ≤ M * ‖(p : ℝ) * h - t‖ := hmvt
        _ = M * (t - (p : ℝ) * h) := by
              rw [Real.norm_eq_abs, abs_of_nonpos (by linarith [ht.1])]; ring
        _ ≤ M * h := by
              apply mul_le_mul_of_nonneg_left _ hM
              linarith [ht.2, hdiff p]
    calc ‖∫ t in ((p : ℝ) * h)..((((p + 1 : ℕ)) : ℝ) * h), (F ((p : ℝ) * h) - F t)‖
        ≤ (M * h) * |((((p + 1 : ℕ)) : ℝ) * h - (p : ℝ) * h)| :=
          intervalIntegral.norm_integral_le_of_norm_le_const hbnd
      _ = M * h * h := by rw [hdiff p, abs_of_nonneg (le_of_lt hh)]
  rw [key]
  calc ‖∑ p ∈ Finset.range n,
          ∫ t in ((p : ℝ) * h)..((((p + 1 : ℕ)) : ℝ) * h), (F ((p : ℝ) * h) - F t)‖
      ≤ ∑ p ∈ Finset.range n,
          ‖∫ t in ((p : ℝ) * h)..((((p + 1 : ℕ)) : ℝ) * h), (F ((p : ℝ) * h) - F t)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ p ∈ Finset.range n, M * h * h := Finset.sum_le_sum hterm
    _ = h * ((n : ℝ) * h) * M := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        ring

end Commons.Analysis.Integral