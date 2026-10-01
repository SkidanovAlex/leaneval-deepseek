import Mathlib
import Submission.Work.ZeroDensity.Jutila.bvDefs
import Submission.Work.ZeroDensity.Jutila.grahamDefs
import Submission.Work.LinnikAreas.Density4.vonMangoldt_sq_sum_bound
import Submission.Work.LinnikAreas.Density4.vonMangoldt_sq_sum_lower

/-!
# Assembly of the two-sided Graham (Barban–Vehov) estimate

This file contains the bookkeeping that reduces

  `Σ_{n ≤ N} Lz_w(n)·Lz_y(n) = N·log w + O(N)`      (`1 < w ≤ y ≤ N`)

to the four analytic inputs of Graham's proof (Graham, J. Number Theory **10** (1978), §3):

* the *easy* case `w·y ≤ N` of the mixed sum (`grahamEasyCase`),
* `Σ_{n ≤ N} Λ(n)² = N log N + O(N)`     (the `S₁` term; here assembled from the workspace's
  `vonMangoldt_sq_sum_bound`/`_lower`),
* `Σ_{n ≤ N} Λ(n)·Bz_z(n) = −N log(N/z) + O(N)`  (the `S₂` term),
* `Σ_{n ≤ N} Bz_w(n)·Bz_y(n) = N log(N/y) + O(N)` (the `S₃` term),

via the exact pointwise splitting `Lz z n = Λ(n) + Bz z n` (`n ≥ 2`, `grahamDefs.lean`):

  `Σ_{n ≤ N} Lz_w Lz_y = log w·log y + Σ Λ² + Σ Λ·Bz_w + Σ Λ·Bz_y + Σ Bz_w·Bz_y`,

whose right-hand side is `N log w + O(N)` by the four inputs.
-/

namespace Work.ZeroDensity.Jutila

open Finset

noncomputable section

/-- `Lz z 1 = log z` for `z ≥ 1`. -/
lemma Lz_one_eq (z : ℝ) (hz : 1 ≤ z) : Lz z 1 = Real.log z := by
  have h1 : (1 : ℕ).divisors.filter (fun d : ℕ => (d : ℝ) ≤ z) = {1} := by
    rw [Nat.divisors_one]
    refine Finset.filter_true_of_mem ?_
    intro d hd
    rw [Finset.mem_singleton] at hd
    subst hd
    simpa using hz
  rw [Lz, h1, Finset.sum_singleton]
  simp

/-- `Bz z 1 = 0` for `z ≥ 1`. -/
lemma Bz_one_eq_zero {z : ℝ} (hz : 1 ≤ z) : Bz z 1 = 0 :=
  Bz_eq_zero_of_le (z := z) (n := 1) (by linarith) (by simpa using hz)

/-- **Second moment of the von Mangoldt function**, assembled from the workspace's two halves
(`vonMangoldt_sq_sum_bound` and `vonMangoldt_sq_sum_lower`). -/
theorem vonMangoldtSqEval_here :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N →
      |(∑ n ∈ Finset.Icc 1 N, ArithmeticFunction.vonMangoldt n ^ 2) - (N : ℝ) * Real.log N|
        ≤ C * (N : ℝ) := by
  obtain ⟨C₁, hC₁, h₁⟩ := Work.LinnikAreas.Density4.vonMangoldt_sq_sum_bound
  obtain ⟨C₂, hC₂, h₂⟩ := Work.LinnikAreas.Density4.vonMangoldt_sq_sum_lower
  refine ⟨max C₁ C₂, lt_max_of_lt_left hC₁, fun N hN => ?_⟩
  have hb : (∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.vonMangoldt n) ^ 2)
      ≤ (N : ℝ) * Real.log (N : ℝ) + C₁ * (N : ℝ) := h₁ N hN
  have hl : (N : ℝ) * Real.log (N : ℝ) - C₂ * (N : ℝ)
      ≤ ∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.vonMangoldt n) ^ 2 := h₂ N hN
  have hNnn : (0 : ℝ) ≤ (N : ℝ) := by positivity
  have hb' : C₁ * (N : ℝ) ≤ max C₁ C₂ * (N : ℝ) :=
    mul_le_mul_of_nonneg_right (le_max_left C₁ C₂) hNnn
  have hl' : C₂ * (N : ℝ) ≤ max C₁ C₂ * (N : ℝ) :=
    mul_le_mul_of_nonneg_right (le_max_right C₁ C₂) hNnn
  rw [abs_le]
  constructor <;> linarith

/-- `(log N)² ≤ 4N` for `N ≥ 1`. -/
lemma log_sq_le_four_mul (N : ℕ) (hN : 1 ≤ N) :
    (Real.log (N : ℝ)) ^ 2 ≤ 4 * (N : ℝ) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hs : (1 : ℝ) ≤ Real.sqrt (N : ℝ) := Real.one_le_sqrt.mpr (by exact_mod_cast hN)
  have hspos : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hNpos
  have hlog : Real.log (N : ℝ) = 2 * Real.log (Real.sqrt (N : ℝ)) := by
    rw [Real.log_sqrt (le_of_lt hNpos)]; ring
  have hb : Real.log (Real.sqrt (N : ℝ)) ≤ Real.sqrt (N : ℝ) - 1 :=
    Real.log_le_sub_one_of_pos hspos
  have hnn : 0 ≤ Real.log (Real.sqrt (N : ℝ)) := Real.log_nonneg hs
  have hsq : (Real.log (N : ℝ)) ^ 2 ≤ (2 * (Real.sqrt (N : ℝ) - 1)) ^ 2 := by
    rw [hlog]
    exact pow_le_pow_left₀ (by linarith) (by linarith) 2
  have hfinal : (2 * (Real.sqrt (N : ℝ) - 1)) ^ 2 ≤ 4 * (N : ℝ) := by
    have hsqr := Real.sq_sqrt (le_of_lt hNpos)
    nlinarith [hs, hsqr]
  linarith

/-- The termwise identity on `Icc 2 N`: for `n ≥ 2`, `Lz w n·Lz y n` splits into
`Λ(n)² + Λ(n)Bz_w(n) + Λ(n)Bz_y(n) + Bz_w(n)Bz_y(n)`. -/
lemma cross_termwise {w y : ℝ} (hw : 0 < w) (hy : 0 < y) {n : ℕ} (hn : 2 ≤ n) :
    Lz w n * Lz y n
      = (ArithmeticFunction.vonMangoldt n) ^ 2
        + ArithmeticFunction.vonMangoldt n * Bz w n
        + ArithmeticFunction.vonMangoldt n * Bz y n
        + Bz w n * Bz y n := by
  rw [Lz_eq_vonMangoldt_add_Bz hw hn, Lz_eq_vonMangoldt_add_Bz hy hn]
  ring

/-- **The exact splitting of the cross moment.**  For `1 ≤ w`, `1 ≤ y` and `1 ≤ N`,
`Σ_{n ≤ N} Lz_w(n)·Lz_y(n)` equals `log w·log y` (the term `n = 1`) plus the four quadratic
pieces `Σ Λ²`, `Σ Λ·Bz_w`, `Σ Λ·Bz_y`, `Σ Bz_w·Bz_y`. -/
theorem cross_eq_split {w y : ℝ} (hw : 1 ≤ w) (hy : 1 ≤ y) {N : ℕ} (hN : 1 ≤ N) :
    (∑ n ∈ Finset.Icc 1 N, Lz w n * Lz y n)
      = Real.log w * Real.log y
        + (∑ n ∈ Finset.Icc 1 N, ArithmeticFunction.vonMangoldt n ^ 2)
        + (∑ n ∈ Finset.Icc 1 N, ArithmeticFunction.vonMangoldt n * Bz w n)
        + (∑ n ∈ Finset.Icc 1 N, ArithmeticFunction.vonMangoldt n * Bz y n)
        + (∑ n ∈ Finset.Icc 1 N, Bz w n * Bz y n) := by
  have hw0 : (0:ℝ) < w := by linarith
  have hy0 : (0:ℝ) < y := by linarith
  -- split off the term `n = 1`
  have hsplit : Finset.Icc 1 N = insert 1 (Finset.Icc 2 N) := by
    ext n; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  have hnotmem : (1:ℕ) ∉ Finset.Icc 2 N := by simp [Finset.mem_Icc]
  have hLHS : (∑ n ∈ Finset.Icc 1 N, Lz w n * Lz y n)
      = Lz w 1 * Lz y 1 + ∑ n ∈ Finset.Icc 2 N, Lz w n * Lz y n := by
    rw [hsplit, Finset.sum_insert hnotmem]
  have h1 : Lz w 1 * Lz y 1 = Real.log w * Real.log y := by
    rw [Lz_one_eq w hw, Lz_one_eq y hy]
  -- the four pieces, as sums over `Icc 2 N`
  have hmid : (∑ n ∈ Finset.Icc 2 N, Lz w n * Lz y n)
      = (∑ n ∈ Finset.Icc 2 N, (ArithmeticFunction.vonMangoldt n) ^ 2)
        + (∑ n ∈ Finset.Icc 2 N, ArithmeticFunction.vonMangoldt n * Bz w n)
        + (∑ n ∈ Finset.Icc 2 N, ArithmeticFunction.vonMangoldt n * Bz y n)
        + (∑ n ∈ Finset.Icc 2 N, Bz w n * Bz y n) := by
    rw [Finset.sum_congr rfl (fun n hn => cross_termwise hw0 hy0 (Finset.mem_Icc.mp hn).1),
      Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
  -- sums over `Icc 2 N` are the same as sums over `Icc 1 N`
  have hshift : ∀ f : ℕ → ℝ, f 1 = 0 →
      (∑ n ∈ Finset.Icc 2 N, f n) = ∑ n ∈ Finset.Icc 1 N, f n := by
    intro f hf
    refine Finset.sum_subset (fun n hn => ?_) ?_
    · have hn' := Finset.mem_Icc.mp hn
      exact Finset.mem_Icc.mpr ⟨le_trans (by norm_num : (1:ℕ) ≤ 2) hn'.1, hn'.2⟩
    · intro x hx hx'
      have hx1 : x = 1 := by
        have h1 : 1 ≤ x := (Finset.mem_Icc.mp hx).1
        have h2 : x < 2 := by
          by_contra h
          exact hx' (Finset.mem_Icc.mpr ⟨not_lt.mp h, (Finset.mem_Icc.mp hx).2⟩)
        omega
      rw [hx1]; exact hf
  have hΛ : ArithmeticFunction.vonMangoldt 1 = 0 := ArithmeticFunction.vonMangoldt_apply_one
  have hBw : Bz w 1 = 0 := Bz_one_eq_zero hw
  have hBy : Bz y 1 = 0 := Bz_one_eq_zero hy
  have hA : (∑ n ∈ Finset.Icc 2 N, (ArithmeticFunction.vonMangoldt n) ^ 2)
      = ∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.vonMangoldt n) ^ 2 :=
    hshift (fun n => (ArithmeticFunction.vonMangoldt n) ^ 2) (by rw [hΛ]; ring)
  have hBw' : (∑ n ∈ Finset.Icc 2 N, ArithmeticFunction.vonMangoldt n * Bz w n)
      = ∑ n ∈ Finset.Icc 1 N, ArithmeticFunction.vonMangoldt n * Bz w n :=
    hshift (fun n => ArithmeticFunction.vonMangoldt n * Bz w n) (by rw [hΛ]; ring)
  have hBy' : (∑ n ∈ Finset.Icc 2 N, ArithmeticFunction.vonMangoldt n * Bz y n)
      = ∑ n ∈ Finset.Icc 1 N, ArithmeticFunction.vonMangoldt n * Bz y n :=
    hshift (fun n => ArithmeticFunction.vonMangoldt n * Bz y n) (by rw [hΛ]; ring)
  have hZ : (∑ n ∈ Finset.Icc 2 N, Bz w n * Bz y n)
      = ∑ n ∈ Finset.Icc 1 N, Bz w n * Bz y n :=
    hshift (fun n => Bz w n * Bz y n) (by rw [hBw]; ring)
  rw [hLHS, h1, hmid, hA, hBw', hBy', hZ]
  ring

/-- **The assembly**: the two-sided Graham estimate follows from the four analytic inputs. -/
theorem grahamCrossTwoSided_of
    (hEasy : ∃ C : ℝ, 0 < C ∧ ∀ z₁ z₂ : ℝ, 1 ≤ z₁ → z₁ ≤ z₂ → ∀ N : ℕ, z₂ ≤ (N : ℝ) →
      |(∑ n ∈ Finset.Icc 1 N, Lz z₁ n * Lz z₂ n) - (N : ℝ) * Real.log z₁|
        ≤ C * ((N : ℝ) + z₁ * z₂))
    (hSq : ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N →
      |(∑ n ∈ Finset.Icc 1 N, ArithmeticFunction.vonMangoldt n ^ 2) - (N : ℝ) * Real.log N|
        ≤ C * (N : ℝ))
    (hMul : ∃ C : ℝ, 0 < C ∧ ∀ z : ℝ, 1 ≤ z → ∀ N : ℕ, z ≤ (N : ℝ) →
      |(∑ n ∈ Finset.Icc 1 N, ArithmeticFunction.vonMangoldt n * Bz z n)
        + (N : ℝ) * Real.log ((N : ℝ) / z)| ≤ C * (N : ℝ))
    (hCross : ∃ C : ℝ, 0 < C ∧ ∀ w y : ℝ, 1 ≤ w → w ≤ y → ∀ N : ℕ, y ≤ (N : ℝ) →
      |(∑ n ∈ Finset.Icc 1 N, Bz w n * Bz y n) - (N : ℝ) * Real.log ((N : ℝ) / y)|
        ≤ C * (N : ℝ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ w y : ℝ, 1 < w → w ≤ y → ∀ N : ℕ, y ≤ (N : ℝ) →
      |(∑ n ∈ Finset.Icc 1 N, Lz w n * Lz y n) - (N : ℝ) * Real.log w| ≤ C * (N : ℝ) := by
  obtain ⟨C₁, hC₁, hE⟩ := hEasy
  obtain ⟨C₂, hC₂, hS⟩ := hSq
  obtain ⟨C₃, hC₃, hM⟩ := hMul
  obtain ⟨C₄, hC₄, hX⟩ := hCross
  refine ⟨2 * C₁ + C₂ + 2 * C₃ + C₄ + 4, by positivity, ?_⟩
  intro w y hw hwy N hyN
  have hw1 : (1 : ℝ) ≤ w := le_of_lt hw
  have hy1 : (1 : ℝ) ≤ y := le_trans hw1 hwy
  have hwpos : 0 < w := by linarith
  have hypos : 0 < y := by linarith
  have hN1 : 1 ≤ N := by
    have : (1 : ℝ) ≤ (N : ℝ) := le_trans hy1 hyN
    exact_mod_cast this
  have hNnn : (0 : ℝ) ≤ (N : ℝ) := by positivity
  have hlogw : 0 ≤ Real.log w := Real.log_nonneg hw1
  have hlogy : 0 ≤ Real.log y := Real.log_nonneg hy1
  have hN2 : 1 < N := by
    have : (1 : ℝ) < (N : ℝ) := lt_of_lt_of_le hw (le_trans hwy hyN)
    exact_mod_cast this
  have hlogNpos : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN2)
  have hlog_le : Real.log w ≤ Real.log (N : ℝ) :=
    Real.log_le_log hwpos (by exact_mod_cast (le_trans hwy hyN))
  have hlogy_le : Real.log y ≤ Real.log (N : ℝ) :=
    Real.log_le_log hypos (by exact_mod_cast hyN)
  -- `log w · log y ≤ 4·N`
  have hprod : Real.log w * Real.log y ≤ 4 * (N : ℝ) := by
    have h2 : Real.log w * Real.log y ≤ Real.log (N : ℝ) * Real.log (N : ℝ) :=
      mul_le_mul hlog_le hlogy_le hlogy (le_of_lt hlogNpos)
    have h3 : Real.log (N : ℝ) * Real.log (N : ℝ) ≤ 4 * (N : ℝ) := by
      simpa [pow_two] using log_sq_le_four_mul N hN1
    linarith
  by_cases hcase : w * y ≤ (N : ℝ)
  · -- easy case `w·y ≤ N`
    have h := hE w y hw1 hwy N hyN
    have hle : (N : ℝ) + w * y ≤ 2 * (N : ℝ) := by linarith
    have h2 : C₁ * ((N : ℝ) + w * y) ≤ C₁ * (2 * (N : ℝ)) :=
      mul_le_mul_of_nonneg_left hle hC₁.le
    have h3 : C₁ * (2 * (N : ℝ)) ≤ (2 * C₁ + C₂ + 2 * C₃ + C₄ + 4) * (N : ℝ) := by
      have : (0:ℝ) ≤ C₂ + 2 * C₃ + C₄ + 2 := by positivity
      nlinarith [hNnn, hC₁.le]
    linarith [h, h2, h3]
  · -- hard case `N < w·y`: the exact splitting
    have hident := cross_eq_split hw1 hy1 hN1
    have hsq := abs_le.mp (hS N hN1)
    have hmw := abs_le.mp (hM w hw1 N (le_trans hwy hyN))
    have hmy := abs_le.mp (hM y hy1 N hyN)
    have hcr := abs_le.mp (hX w y hw1 hwy N hyN)
    have hdivw : Real.log ((N : ℝ) / w) = Real.log (N : ℝ) - Real.log w :=
      Real.log_div (by positivity) (ne_of_gt hwpos)
    have hdivy : Real.log ((N : ℝ) / y) = Real.log (N : ℝ) - Real.log y :=
      Real.log_div (by positivity) (ne_of_gt hypos)
    have key : (∑ n ∈ Finset.Icc 1 N, Lz w n * Lz y n) - (N : ℝ) * Real.log w
        = (Real.log w * Real.log y)
          + ((∑ n ∈ Finset.Icc 1 N, ArithmeticFunction.vonMangoldt n ^ 2)
              - (N : ℝ) * Real.log N)
          + ((∑ n ∈ Finset.Icc 1 N, ArithmeticFunction.vonMangoldt n * Bz w n)
              + (N : ℝ) * Real.log ((N : ℝ) / w))
          + ((∑ n ∈ Finset.Icc 1 N, ArithmeticFunction.vonMangoldt n * Bz y n)
              + (N : ℝ) * Real.log ((N : ℝ) / y))
          + ((∑ n ∈ Finset.Icc 1 N, Bz w n * Bz y n)
              - (N : ℝ) * Real.log ((N : ℝ) / y)) := by
      rw [hident, hdivw, hdivy]
      ring
    rw [key, abs_le]
    constructor
    · -- lower bound
      nlinarith [hprod, hsq.1, hmw.1, hmy.1, hcr.1, hNnn, hC₁.le, hC₂.le, hC₃.le, hC₄.le]
    · -- upper bound
      nlinarith [hprod, hsq.2, hmw.2, hmy.2, hcr.2, hNnn, hC₁.le, hC₂.le, hC₃.le, hC₄.le]

end

end Work.ZeroDensity.Jutila
