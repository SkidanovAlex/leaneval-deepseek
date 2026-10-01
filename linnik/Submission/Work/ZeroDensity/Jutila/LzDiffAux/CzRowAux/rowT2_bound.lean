import Mathlib
import Submission.Work.ZeroDensity.Jutila.LzDiffAux.CzRowAuxDefs

namespace Work.ZeroDensity.Jutila.LzDiffAux.CzRowAux

open Finset
open Work.ZeroDensity.Jutila.LzDiffAux
open Work.ZeroDensity.Jutila.BzCross

noncomputable section

/-- For squarefree `r` one has `r ≤ kap r = ∏_{p | r}(p+1)`. -/
lemma rowT2_aux_cast_le_kap {r : ℕ} (hr : Squarefree r) :
    (r : ℝ) ≤ Work.ZeroDensity.Jutila.kap r := by
  unfold Work.ZeroDensity.Jutila.kap
  have hprod : (∏ p ∈ r.primeFactors, (p : ℝ)) = (r : ℝ) := by
    rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hr]
  rw [← hprod]
  apply Finset.prod_le_prod₀
  · intro p hp; positivity
  · intro p hp; linarith

/-- `|rowCoef t r| ≤ 1/r` for `1 ≤ r`. -/
lemma rowT2_aux_rowCoef_abs_le {t r : ℕ} (hr : 1 ≤ r) :
    |rowCoef t r| ≤ 1 / (r : ℝ) := by
  have hr0 : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (by omega : 0 < r)
  unfold rowCoef
  split_ifs with h
  · by_cases hs : Squarefree r
    · have hmuR : |(ArithmeticFunction.moebius r : ℝ)| = 1 := by
        rw [← Int.cast_abs, ArithmeticFunction.abs_moebius_eq_one_of_squarefree hs]
        norm_num
      rw [abs_div, hmuR, abs_of_pos (Work.ZeroDensity.Jutila.kap_pos r)]
      exact one_div_le_one_div_of_le hr0 (rowT2_aux_cast_le_kap hs)
    · rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hs]
      simp only [Int.cast_zero, abs_zero, zero_div]
      exact div_nonneg zero_le_one hr0.le
  · rw [abs_zero]
    exact div_nonneg zero_le_one hr0.le

/-- `|γ_r| ≤ X_r / (⌊y/r⌋·r)` where `X_r = y - ⌊y/r⌋·r = rowRem y r`, for `0 < y`, `1 ≤ r ≤ y`. -/
lemma rowT2_aux_gam_abs_le {y : ℝ} {r : ℕ} (hy : 0 < y) (hr : 1 ≤ r)
    (hry : (r : ℝ) ≤ y) :
    |rowGam y r| ≤ rowRem y r / (((⌊y / (r : ℝ)⌋₊ : ℕ) : ℝ) * (r : ℝ)) := by
  have hr0 : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (by omega : 0 < r)
  set C : ℕ := ⌊y / (r : ℝ)⌋₊ with hCdef
  set D : ℝ := (C : ℝ) * (r : ℝ) with hDdef
  have hCge1 : 1 ≤ C := by
    rw [hCdef]
    exact (Nat.one_le_floor_iff _).mpr ((le_div_iff₀ hr0).mpr (by simpa using hry))
  have hCge1R : (1 : ℝ) ≤ (C : ℝ) := by exact_mod_cast hCge1
  have hDpos : 0 < D := by rw [hDdef]; exact mul_pos (by linarith) hr0
  have hDge : (r : ℝ) ≤ D := by
    rw [hDdef]
    calc (r : ℝ) = 1 * (r : ℝ) := by ring
      _ ≤ (C : ℝ) * (r : ℝ) := mul_le_mul_of_nonneg_right hCge1R hr0.le
  have hDle : D ≤ y := by
    have hCle : (C : ℝ) ≤ y / (r : ℝ) := by rw [hCdef]; exact Nat.floor_le (by positivity)
    rw [hDdef]
    calc (C : ℝ) * (r : ℝ) ≤ (y / (r : ℝ)) * (r : ℝ) :=
          mul_le_mul_of_nonneg_right hCle hr0.le
      _ = y := div_mul_cancel₀ y hr0.ne'
  have hDgt : y - (r : ℝ) < D := by
    have hClt : y / (r : ℝ) < (C : ℝ) + 1 := by rw [hCdef]; exact Nat.lt_floor_add_one _
    have h2 : y < ((C : ℝ) + 1) * (r : ℝ) := (div_lt_iff₀ hr0).mp hClt
    rw [hDdef]; linarith
  have hrem : rowRem y r = y - D := by
    unfold rowRem
    rw [hDdef, hCdef]
  have hlog_nonpos : Real.log (D / y) ≤ 0 :=
    Real.log_nonpos (le_of_lt (div_pos hDpos hy)) ((div_le_one hy).mpr hDle)
  have hgam : rowGam y r = Real.log (D / y) := by
    unfold rowGam
    rw [hDdef, hCdef]
  rw [hgam, abs_of_nonpos hlog_nonpos, hrem]
  have h1 : -Real.log (D / y) = Real.log (y / D) := by
    rw [← Real.log_inv, inv_div]
  rw [h1]
  have h2 := Real.log_le_sub_one_of_pos (div_pos hy hDpos)
  have h3 : y / D - 1 = (y - D) / D := by
    rw [sub_div, div_self hDpos.ne']
  rw [← h3]
  exact h2

/-- Pointwise bound: `|rowCoef t r| · y · |γ_r| ≤ 2` for `1 ≤ r ≤ y`. -/
lemma rowT2_aux_ptwise {y : ℝ} {t r : ℕ} (hy : 0 < y) (hr : 1 ≤ r)
    (hry : (r : ℝ) ≤ y) :
    |rowCoef t r| * (y * |rowGam y r|) ≤ 2 := by
  have hr0 : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (by omega : 0 < r)
  set C : ℕ := ⌊y / (r : ℝ)⌋₊ with hCdef
  set D : ℝ := (C : ℝ) * (r : ℝ) with hDdef
  have hCge1 : 1 ≤ C := by
    rw [hCdef]
    exact (Nat.one_le_floor_iff _).mpr ((le_div_iff₀ hr0).mpr (by simpa using hry))
  have hCge1R : (1 : ℝ) ≤ (C : ℝ) := by exact_mod_cast hCge1
  have hDpos : 0 < D := by rw [hDdef]; exact mul_pos (by linarith) hr0
  have hDge : (r : ℝ) ≤ D := by
    rw [hDdef]
    calc (r : ℝ) = 1 * (r : ℝ) := by ring
      _ ≤ (C : ℝ) * (r : ℝ) := mul_le_mul_of_nonneg_right hCge1R hr0.le
  have hDgt : y - (r : ℝ) < D := by
    have hClt : y / (r : ℝ) < (C : ℝ) + 1 := by rw [hCdef]; exact Nat.lt_floor_add_one _
    have h2 : y < ((C : ℝ) + 1) * (r : ℝ) := (div_lt_iff₀ hr0).mp hClt
    rw [hDdef]; linarith
  have hDhalf : y / 2 < D := by linarith
  have hrem : rowRem y r = y - D := by
    unfold rowRem
    rw [hDdef, hCdef]
  have hrem_lt : rowRem y r < (r : ℝ) := by rw [hrem]; linarith
  have hrc := rowT2_aux_rowCoef_abs_le (t := t) hr
  have hgam := rowT2_aux_gam_abs_le (y := y) hy hr hry
  have hpos1 : 0 ≤ 1 / (r : ℝ) := div_nonneg zero_le_one hr0.le
  calc |rowCoef t r| * (y * |rowGam y r|)
      ≤ (1 / (r : ℝ)) * (y * (rowRem y r / D)) :=
        mul_le_mul hrc (mul_le_mul_of_nonneg_left hgam hy.le)
          (mul_nonneg hy.le (abs_nonneg _)) hpos1
    _ ≤ 2 := by
        have hlt : (1 / (r : ℝ)) * (y * (rowRem y r / D)) < 2 := by
          have hstep : (1 / (r : ℝ)) * (y * (rowRem y r / D))
              = y * rowRem y r / ((r : ℝ) * D) := by
            field_simp
          rw [hstep, div_lt_iff₀ (mul_pos hr0 hDpos)]
          have h1 : y * rowRem y r < y * (r : ℝ) := mul_lt_mul_of_pos_left hrem_lt hy
          have h2 : y * (r : ℝ) < 2 * ((r : ℝ) * D) := by
            have hyD : y < 2 * D := by linarith
            calc y * (r : ℝ) < (2 * D) * (r : ℝ) := mul_lt_mul_of_pos_right hyD hr0
              _ = 2 * ((r : ℝ) * D) := by ring
          linarith
        exact le_of_lt hlt

/-- `|y · rowT2 y Y t r1| ≤ 2 · Σ_{r ≤ r1} (|log(Y/r)| + 1)`. -/
lemma rowT2_abs_le {y Y : ℝ} {t r1 : ℕ} (hy : 0 < y)
    (hry : ∀ r ∈ Finset.Icc 1 r1, 1 ≤ r ∧ (r : ℝ) ≤ y) :
    |y * rowT2 y Y t r1|
      ≤ 2 * ∑ r ∈ Finset.Icc 1 r1, (|Real.log (Y / (r : ℝ))| + 1) := by
  have h1 : |y * rowT2 y Y t r1|
      ≤ ∑ r ∈ Finset.Icc 1 r1, |Real.log (Y / (r : ℝ)) - 1| * 2 := by
    rw [rowT2, Finset.mul_sum]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun r hr => ?_)
    obtain ⟨hr1, _⟩ := Finset.mem_Icc.mp hr
    have hP := rowT2_aux_ptwise (y := y) (t := t) hy hr1 (hry r hr).2
    have heq : y * (rowCoef t r * ((Real.log (Y / (r : ℝ)) - 1) * rowGam y r))
        = rowCoef t r * ((Real.log (Y / (r : ℝ)) - 1) * (y * rowGam y r)) := by ring
    rw [heq, abs_mul, abs_mul, abs_mul, abs_of_pos hy]
    have hkey : |rowCoef t r| * (|Real.log (Y / (r : ℝ)) - 1| * (y * |rowGam y r|))
        = |Real.log (Y / (r : ℝ)) - 1| * (|rowCoef t r| * (y * |rowGam y r|)) := by ring
    rw [hkey]
    exact mul_le_mul_of_nonneg_left hP (abs_nonneg _)
  calc |y * rowT2 y Y t r1|
      ≤ ∑ r ∈ Finset.Icc 1 r1, |Real.log (Y / (r : ℝ)) - 1| * 2 := h1
    _ ≤ ∑ r ∈ Finset.Icc 1 r1, (|Real.log (Y / (r : ℝ))| + 1) * 2 := by
        apply Finset.sum_le_sum
        intro r hr
        have hle : |Real.log (Y / (r : ℝ)) - 1| ≤ |Real.log (Y / (r : ℝ))| + 1 := by
          refine abs_sub_le_iff.mpr ⟨?_, ?_⟩
          · linarith [le_abs_self (Real.log (Y / (r : ℝ)))]
          · linarith [neg_le_abs (Real.log (Y / (r : ℝ)))]
        exact mul_le_mul_of_nonneg_right hle (by norm_num)
    _ = 2 * ∑ r ∈ Finset.Icc 1 r1, (|Real.log (Y / (r : ℝ))| + 1) := by
        rw [← Finset.sum_mul]; ring

lemma rowT2_bound {w y : ℝ} {t r1 : ℕ} {K : ℝ} (hw : 0 < w) (hy : 0 < y) (ht : 1 ≤ t)
    (hry : ∀ r ∈ Finset.Icc 1 r1, 1 ≤ r ∧ (r : ℝ) ≤ y)
    (hS : ∑ r ∈ Finset.Icc 1 r1,
        (|Real.log (Work.ZeroDensity.Jutila.BzCross.czY w y t / (r : ℝ))| + 1)
      ≤ K * Work.ZeroDensity.Jutila.BzCross.czY w y t)
    (hK : 0 ≤ K) :
    |y * Work.ZeroDensity.Jutila.LzDiffAux.rowT2 y (Work.ZeroDensity.Jutila.BzCross.czY w y t) t r1|
      ≤ 2 * K * Work.ZeroDensity.Jutila.BzCross.czY w y t := by
  set Y := Work.ZeroDensity.Jutila.BzCross.czY w y t with hY
  have hS' : ∑ r ∈ Finset.Icc 1 r1, (|Real.log (Y / (r : ℝ))| + 1) ≤ K * Y := by
    rw [hY]
    exact hS
  calc |y * rowT2 y Y t r1|
      ≤ 2 * ∑ r ∈ Finset.Icc 1 r1, (|Real.log (Y / (r : ℝ))| + 1) :=
        rowT2_abs_le (Y := Y) (t := t) (r1 := r1) hy hry
    _ ≤ 2 * (K * Y) := mul_le_mul_of_nonneg_left hS' (by norm_num)
    _ = 2 * K * Y := by ring

end

end Work.ZeroDensity.Jutila.LzDiffAux.CzRowAux
