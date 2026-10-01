import Mathlib
import Submission.Work.ZeroDensity.Jutila.bvDefs
import Submission.Work.LinnikAreas.Density4.sum_abs_selLam_le
import Submission.Commons.NumberTheory.Moebius.log_moebius_lcm_sq_swap

/-!
# The weight of the difference of two truncated von Mangoldt sums

For real cutoffs `1 < w < y` the difference

  `Lz y n - Lz w n = Σ_{d ∣ n, d ≤ y} μ(d)·log(y/d) − Σ_{d ∣ n, d ≤ w} μ(d)·log(w/d)`

is the divisor sum of the single weight

  `bvLam w y d = μ(d)·(log(y/d)·1_{d ≤ y} − log(w/d)·1_{d ≤ w})`,

which equals `μ(d)·log(y/w)·bvW w y d` (`bvW` from `bvDefs`).

This file collects that vocabulary together with the exact identities that turn
`Σ_{n ≤ N} (Lz y n − Lz w n)²` into the double sum `Σ_{d,e} bvLam d·bvLam e·⌊N/lcm d e⌋`
and the elementary size bound `Σ_{d ≤ y} |bvLam w y d| ≤ 2y`.
-/

namespace Work.ZeroDensity.Jutila

open Finset
open scoped BigOperators

noncomputable section

/-- **The weight of the difference of two truncated von Mangoldt sums.**
`bvLam w y d = μ(d)·(log(y/d)·1_{d ≤ y} − log(w/d)·1_{d ≤ w})`. -/
def bvLam (w y : ℝ) (d : ℕ) : ℝ :=
  (ArithmeticFunction.moebius d : ℝ) *
    ((if (d : ℝ) ≤ y then Real.log (y / (d : ℝ)) else 0)
      - (if (d : ℝ) ≤ w then Real.log (w / (d : ℝ)) else 0))

/-- `log(y/d) - log(w/d) = log(y/w)` for positive `w, y, d`. -/
lemma log_sub_log_div {w y d : ℝ} (hw : 0 < w) (hy : 0 < y) (hd : 0 < d) :
    Real.log (y / d) - Real.log (w / d) = Real.log (y / w) := by
  have h1 : Real.log (y / d) = Real.log y - Real.log d := Real.log_div hy.ne' hd.ne'
  have h2 : Real.log (w / d) = Real.log w - Real.log d := Real.log_div hw.ne' hd.ne'
  have h3 : Real.log (y / w) = Real.log y - Real.log w := Real.log_div hy.ne' hw.ne'
  rw [h1, h2, h3]; ring

/-- **The difference identity**: `Lz y n − Lz w n = Σ_{d ∣ n} bvLam w y d`. -/
theorem Lz_sub_eq_sum_bvLam (w y : ℝ) (n : ℕ) :
    Lz y n - Lz w n = ∑ d ∈ n.divisors, bvLam w y d := by
  rw [Lz, Lz, Finset.sum_filter, Finset.sum_filter, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun d _ => ?_)
  simp only [bvLam, mul_sub, mul_ite, mul_zero]

/-- **`bvLam` is `μ` times `log(y/w)` times the Barban–Vehov weight `bvW`.** -/
theorem bvLam_eq_mu_bvW {w y : ℝ} (hw : 1 < w) (hwy : w < y) {d : ℕ} (hd : 1 ≤ d) :
    bvLam w y d = (ArithmeticFunction.moebius d : ℝ) * Real.log (y / w) * bvW w y d := by
  have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
  have hw0 : 0 < w := by linarith
  have hy0 : 0 < y := by linarith
  have hyw : 0 < Real.log (y / w) := Real.log_pos ((one_lt_div hw0).mpr hwy)
  by_cases hdw : (d : ℝ) ≤ w
  · have hdy : (d : ℝ) ≤ y := le_trans hdw hwy.le
    rw [bvLam, if_pos hdy, if_pos hdw, log_sub_log_div hw0 hy0 hd0,
      bvW_of_le hw hwy hd hdw]
    ring
  · have hwd : w < (d : ℝ) := lt_of_not_ge hdw
    by_cases hdy : (d : ℝ) ≤ y
    · have hywle : y / (d : ℝ) ≤ y / w := by
        rw [div_le_div_iff₀ hd0 hw0]
        exact (mul_lt_mul_of_pos_left hwd hy0).le
      have hge1 : 1 ≤ y / (d : ℝ) := by rw [le_div_iff₀ hd0, one_mul]; exact hdy
      have hb : bvW w y d = Real.log (y / (d : ℝ)) / Real.log (y / w) := by
        rw [bvW, min_eq_right (by
              rw [div_le_one hyw]
              exact Real.log_le_log (div_pos hy0 hd0) hywle),
          max_eq_right (div_nonneg (Real.log_nonneg hge1) hyw.le)]
      rw [bvLam, if_pos hdy, if_neg hdw, sub_zero, hb]
      field_simp
    · have hdy' : y < (d : ℝ) := lt_of_not_ge hdy
      rw [bvLam, if_neg hdy, if_neg hdw, sub_zero, bvW_of_ge hw hwy hd hdy'.le]
      ring

/-- The weight vanishes for `d ≥ y`. -/
theorem bvLam_eq_zero_of_ge {w y : ℝ} (hw : 1 < w) (hwy : w < y) {d : ℕ} (hd : 1 ≤ d)
    (hdy : y ≤ (d : ℝ)) : bvLam w y d = 0 := by
  rw [bvLam_eq_mu_bvW hw hwy hd, bvW_of_ge hw hwy hd hdy, mul_zero]

/-- The weight is bounded by `log(y/d)` on `d ≤ y`. -/
theorem abs_bvLam_le_log {w y : ℝ} (hw : 1 < w) (hwy : w < y) {d : ℕ} (hd : 1 ≤ d)
    (hdy : (d : ℝ) ≤ y) : |bvLam w y d| ≤ Real.log (y / (d : ℝ)) := by
  have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
  have hw0 : 0 < w := by linarith
  have hy0 : 0 < y := by linarith
  have hge1 : 1 ≤ y / (d : ℝ) := by rw [le_div_iff₀ hd0, one_mul]; exact hdy
  have hlogpos : 0 ≤ Real.log (y / (d : ℝ)) := Real.log_nonneg hge1
  have hyw : 0 < Real.log (y / w) := Real.log_pos ((one_lt_div hw0).mpr hwy)
  have hmu : |((ArithmeticFunction.moebius d : ℤ) : ℝ)| ≤ 1 := by
    have h := ArithmeticFunction.abs_moebius_le_one (n := d)
    have h2 : ((|ArithmeticFunction.moebius d| : ℤ) : ℝ) ≤ 1 := by exact_mod_cast h
    rwa [Int.cast_abs] at h2
  by_cases hdw : (d : ℝ) ≤ w
  · rw [bvLam, if_pos hdy, if_pos hdw, log_sub_log_div hw0 hy0 hd0, abs_mul,
      abs_of_nonneg hyw.le]
    have hle : y / w ≤ y / (d : ℝ) := by
      rw [div_le_div_iff₀ hw0 hd0]
      exact mul_le_mul_of_nonneg_left hdw hy0.le
    calc |((ArithmeticFunction.moebius d : ℤ) : ℝ)| * Real.log (y / w)
        ≤ 1 * Real.log (y / w) := mul_le_mul_of_nonneg_right hmu hyw.le
      _ = Real.log (y / w) := by ring
      _ ≤ Real.log (y / (d : ℝ)) := Real.log_le_log (div_pos hy0 hw0) hle
  · rw [bvLam, if_pos hdy, if_neg hdw, sub_zero, abs_mul, abs_of_nonneg hlogpos]
    calc |((ArithmeticFunction.moebius d : ℤ) : ℝ)| * Real.log (y / (d : ℝ))
        ≤ 1 * Real.log (y / (d : ℝ)) := mul_le_mul_of_nonneg_right hmu hlogpos
      _ = Real.log (y / (d : ℝ)) := by ring

/-- **The swap identity**: the square of the difference of the two truncated
von Mangoldt sums is the double sum over the divisor pairs with the lcm count. -/
theorem sum_sq_Lz_sub_eq_lcm {w y : ℝ} (hw : 1 < w) (hwy : w < y) (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, (Lz y n - Lz w n) ^ 2)
      = ∑ d ∈ Finset.Icc 1 ⌊y⌋₊, ∑ e ∈ Finset.Icc 1 ⌊y⌋₊,
          bvLam w y d * bvLam w y e * ((N / Nat.lcm d e : ℕ) : ℝ) := by
  have hy0 : 0 < y := by linarith
  have hn : ∀ n ∈ Finset.Icc 1 N,
      (Lz y n - Lz w n) ^ 2
        = (∑ d ∈ n.divisors.filter (fun d : ℕ => d ≤ ⌊y⌋₊), bvLam w y d) ^ 2 := by
    intro n _
    rw [Lz_sub_eq_sum_bvLam]
    congr 1
    refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
    intro x hx hxs
    have hxlt : ⌊y⌋₊ < x := by
      by_contra hle
      exact hxs (Finset.mem_filter.mpr ⟨hx, le_of_not_gt hle⟩)
    exact bvLam_eq_zero_of_ge hw hwy (Nat.pos_of_mem_divisors hx)
      (le_of_lt ((Nat.floor_lt hy0.le).mp hxlt))
  rw [Finset.sum_congr rfl hn]
  exact Commons.NumberTheory.Moebius.sum_sq_truncated_eq_lcm_sum_general N ⌊y⌋₊ (bvLam w y)

/-- `Σ_{d ≤ ⌊y⌋} log(y/d) ≤ 2y` for `1 ≤ y`. -/
theorem sum_log_div_floor_le (y : ℝ) (hy : 1 ≤ y) :
    (∑ d ∈ Finset.Icc 1 ⌊y⌋₊, Real.log (y / (d : ℝ))) ≤ 2 * y := by
  rcases Nat.eq_zero_or_pos ⌊y⌋₊ with h | h
  · rw [h]; simp; linarith
  have hy0 : 0 < y := by linarith
  have hn0 : (0 : ℝ) < (⌊y⌋₊ : ℝ) := by exact_mod_cast h
  have hsplit : (∑ d ∈ Finset.Icc 1 ⌊y⌋₊, Real.log (y / (d : ℝ)))
      = (∑ d ∈ Finset.Icc 1 ⌊y⌋₊, Real.log ((⌊y⌋₊ : ℝ) / (d : ℝ)))
        + (⌊y⌋₊ : ℝ) * Real.log (y / (⌊y⌋₊ : ℝ)) := by
    have hterm : ∀ d ∈ Finset.Icc 1 ⌊y⌋₊,
        Real.log (y / (d : ℝ))
          = Real.log ((⌊y⌋₊ : ℝ) / (d : ℝ)) + Real.log (y / (⌊y⌋₊ : ℝ)) := by
      intro d hd
      have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
      have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
      rw [← Real.log_mul (div_ne_zero hn0.ne' hd0.ne') (div_ne_zero hy0.ne' hn0.ne')]
      congr 1
      field_simp
    rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_const, Nat.card_Icc,
      Nat.add_sub_cancel, nsmul_eq_mul]
  have h1 : (∑ d ∈ Finset.Icc 1 ⌊y⌋₊, Real.log ((⌊y⌋₊ : ℝ) / (d : ℝ))) ≤ (⌊y⌋₊ : ℝ) :=
    Work.LinnikAreas.Density4.sum_log_div_le ⌊y⌋₊ h
  have h2 : (⌊y⌋₊ : ℝ) * Real.log (y / (⌊y⌋₊ : ℝ)) ≤ 1 := by
    have hylt : y < (⌊y⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one y
    have hle : y / (⌊y⌋₊ : ℝ) ≤ 1 + 1 / (⌊y⌋₊ : ℝ) := by
      rw [div_le_iff₀ hn0]
      have h3 : y ≤ ((⌊y⌋₊ : ℝ) + 1) := le_of_lt hylt
      field_simp
      linarith
    have hpos : 0 < 1 + 1 / (⌊y⌋₊ : ℝ) := by positivity
    have hlog : Real.log (y / (⌊y⌋₊ : ℝ)) ≤ 1 / (⌊y⌋₊ : ℝ) := by
      calc Real.log (y / (⌊y⌋₊ : ℝ)) ≤ Real.log (1 + 1 / (⌊y⌋₊ : ℝ)) :=
            Real.log_le_log (div_pos hy0 hn0) hle
        _ ≤ 1 / (⌊y⌋₊ : ℝ) := by
            have hh := Real.log_le_sub_one_of_pos hpos
            have he : 1 + 1 / (⌊y⌋₊ : ℝ) - 1 = 1 / (⌊y⌋₊ : ℝ) := by ring
            linarith [hh, he ▸ hh]
    calc (⌊y⌋₊ : ℝ) * Real.log (y / (⌊y⌋₊ : ℝ)) ≤ (⌊y⌋₊ : ℝ) * (1 / (⌊y⌋₊ : ℝ)) :=
          mul_le_mul_of_nonneg_left hlog hn0.le
      _ = 1 := by field_simp
  have h3 : (⌊y⌋₊ : ℝ) ≤ y := Nat.floor_le (by linarith)
  rw [hsplit]
  linarith [h1, h2, h3]

/-- **Elementary size bound on the difference weights**: `Σ_{d ≤ y} |bvLam w y d| ≤ 2y`. -/
theorem sum_abs_bvLam_le {w y : ℝ} (hw : 1 < w) (hwy : w < y) (hy : 1 ≤ y) :
    (∑ d ∈ Finset.Icc 1 ⌊y⌋₊, |bvLam w y d|) ≤ 2 * y := by
  have hy0 : 0 < y := by linarith
  refine le_trans (Finset.sum_le_sum ?_) (sum_log_div_floor_le y hy)
  intro d hd
  obtain ⟨hd1, hdy⟩ := Finset.mem_Icc.mp hd
  exact abs_bvLam_le_log hw hwy hd1 ((Nat.le_floor_iff hy0.le).mp hdy)

end

end Work.ZeroDensity.Jutila
