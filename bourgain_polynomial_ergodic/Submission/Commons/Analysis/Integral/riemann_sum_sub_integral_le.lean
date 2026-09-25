import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

namespace Commons.Analysis.Integral

open MeasureTheory Filter Finset intervalIntegral
open scoped BigOperators Topology

/-- Error bound for the right Riemann sum approximation of an integral of a `C¹`
function on `[0,1]`: if `‖F'‖ ≤ M` then
`|(1/P) ∑_{p<P} F (p/P) - ∫_0^1 F| ≤ M/P`.  This is the elementary comparison used to
replace a Weyl sum by its continuous (integral) analogue on the major arcs. -/
theorem riemann_sum_sub_integral_le (F F' : ℝ → ℂ) {M : ℝ} (hM : 0 ≤ M)
    (hderiv : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt F (F' t) t)
    (hbound : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖F' t‖ ≤ M)
    (P : ℕ) (hP : 0 < P) :
    ‖(P : ℂ)⁻¹ * ∑ p ∈ Finset.range P, F ((p : ℝ) / P) - ∫ t in (0 : ℝ)..1, F t‖
      ≤ M / P := by
  have hPpos : (0 : ℝ) < (P : ℝ) := by exact_mod_cast hP
  have hPne : (P : ℝ) ≠ 0 := ne_of_gt hPpos
  -- Continuity of `F` on `[0,1]`.
  have hcont : ContinuousOn F (Set.Icc (0 : ℝ) 1) :=
    fun x hx => (hderiv x hx).continuousAt.continuousWithinAt
  -- Elementary bounds on the grid points.
  have ha_nonneg : ∀ p : ℕ, (0 : ℝ) ≤ (p : ℝ) / P :=
    fun p => div_nonneg (Nat.cast_nonneg p) (le_of_lt hPpos)
  have ha_le_one : ∀ p : ℕ, p < P → (p : ℝ) / P ≤ 1 := by
    intro p hp
    rw [div_le_one hPpos]
    exact_mod_cast (le_of_lt hp)
  have hsucc_le_one : ∀ p : ℕ, p < P → (↑(p + 1) : ℝ) / P ≤ 1 := by
    intro p hp
    rw [div_le_one hPpos]
    have : p + 1 ≤ P := Nat.succ_le_of_lt hp
    exact_mod_cast this
  have hmono : ∀ p : ℕ, (p : ℝ) / P ≤ (↑(p + 1) : ℝ) / P := by
    intro p
    apply div_le_div_of_nonneg_right _ (le_of_lt hPpos)
    push_cast; linarith
  have hdiff : ∀ p : ℕ, (↑(p + 1) : ℝ) / P - (p : ℝ) / P = 1 / P := by
    intro p
    rw [← sub_div]
    have : (↑(p + 1) : ℝ) - (p : ℝ) = 1 := by push_cast; ring
    rw [this]
  -- Interval integrability of `F` on each cell.
  have hIntF : ∀ p : ℕ, p < P → IntervalIntegrable F volume ((p : ℝ) / P) ((↑(p + 1) : ℝ) / P) := by
    intro p hp
    apply ContinuousOn.intervalIntegrable
    apply hcont.mono
    rw [Set.uIcc_of_le (hmono p)]
    intro x hx
    exact ⟨by linarith [hx.1, ha_nonneg p], by linarith [hx.2, hsucc_le_one p hp]⟩
  -- Step 1 : split the integral over `[0,1]` into the `P` cells.
  have hI : ∫ t in (0 : ℝ)..1, F t
      = ∑ p ∈ Finset.range P, ∫ t in ((p : ℝ) / P)..((↑(p + 1) : ℝ) / P), F t := by
    have h := sum_integral_adjacent_intervals (μ := volume) (f := F)
        (a := fun k : ℕ => (k : ℝ) / P) (n := P)
        (fun k hk => hIntF k hk)
    rw [Nat.cast_zero, zero_div, div_self hPne] at h
    exact h.symm
  -- Step 2 : rewrite each Riemann term as the integral of a constant.
  have hcell : ∀ p : ℕ, p < P →
      ∫ t in ((p : ℝ) / P)..((↑(p + 1) : ℝ) / P), (F ((p : ℝ) / P) - F t)
        = (P : ℂ)⁻¹ * F ((p : ℝ) / P)
            - ∫ t in ((p : ℝ) / P)..((↑(p + 1) : ℝ) / P), F t := by
    intro p hp
    rw [intervalIntegral.integral_sub intervalIntegrable_const (hIntF p hp)]
    congr 1
    rw [intervalIntegral.integral_const]
    rw [hdiff p, Complex.real_smul]
    congr 1
    rw [one_div, Complex.ofReal_inv, Complex.ofReal_natCast]
  -- Step 3 : the exact identity for the error.
  have key : (P : ℂ)⁻¹ * ∑ p ∈ Finset.range P, F ((p : ℝ) / P) - ∫ t in (0 : ℝ)..1, F t
      = ∑ p ∈ Finset.range P,
          ∫ t in ((p : ℝ) / P)..((↑(p + 1) : ℝ) / P), (F ((p : ℝ) / P) - F t) := by
    rw [hI, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun p hp => (hcell p (Finset.mem_range.mp hp)).symm
  -- Step 4 : bound each summand.
  have hterm : ∀ p ∈ Finset.range P,
      ‖∫ t in ((p : ℝ) / P)..((↑(p + 1) : ℝ) / P), (F ((p : ℝ) / P) - F t)‖
        ≤ (M / P) * (1 / P) := by
    intro p hp
    have hpP : p < P := Finset.mem_range.mp hp
    have hle := hmono p
    have hbnd : ∀ t ∈ Set.uIoc ((p : ℝ) / P) ((↑(p + 1) : ℝ) / P),
        ‖F ((p : ℝ) / P) - F t‖ ≤ M / P := by
      intro t ht
      rw [Set.uIoc_of_le hle] at ht
      have ha_mem : (p : ℝ) / P ∈ Set.Icc (0 : ℝ) 1 := ⟨ha_nonneg p, ha_le_one p hpP⟩
      have ht_mem : t ∈ Set.Icc (0 : ℝ) 1 :=
        ⟨by linarith [ht.1, ha_nonneg p], by linarith [ht.2, hsucc_le_one p hpP]⟩
      have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
        (f := F) (f' := F') (s := Set.Icc (0 : ℝ) 1) (C := M)
        (fun x hx => (hderiv x hx).hasDerivWithinAt)
        (fun x hx => hbound x hx)
        (convex_Icc 0 1) ha_mem ht_mem
      calc ‖F ((p : ℝ) / P) - F t‖ = ‖F t - F ((p : ℝ) / P)‖ := by
              rw [← norm_neg]; congr 1; ring
        _ ≤ M * ‖t - (p : ℝ) / P‖ := hmvt
        _ = M * (t - (p : ℝ) / P) := by
              rw [Real.norm_eq_abs, abs_of_nonneg (by linarith [ht.1])]
        _ ≤ M * (1 / P) := by
              apply mul_le_mul_of_nonneg_left _ hM
              linarith [ht.2, hdiff p]
        _ = M / P := by rw [mul_one_div]
    calc ‖∫ t in ((p : ℝ) / P)..((↑(p + 1) : ℝ) / P), (F ((p : ℝ) / P) - F t)‖
        ≤ (M / P) * |(↑(p + 1) : ℝ) / P - (p : ℝ) / P| :=
          intervalIntegral.norm_integral_le_of_norm_le_const hbnd
      _ = (M / P) * (1 / P) := by
          rw [hdiff p, abs_of_nonneg (div_nonneg zero_le_one (le_of_lt hPpos))]
  rw [key]
  calc ‖∑ p ∈ Finset.range P,
          ∫ t in ((p : ℝ) / P)..((↑(p + 1) : ℝ) / P), (F ((p : ℝ) / P) - F t)‖
      ≤ ∑ p ∈ Finset.range P,
          ‖∫ t in ((p : ℝ) / P)..((↑(p + 1) : ℝ) / P), (F ((p : ℝ) / P) - F t)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ p ∈ Finset.range P, (M / P) * (1 / P) := Finset.sum_le_sum hterm
    _ = M / P := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        field_simp

end Commons.Analysis.Integral