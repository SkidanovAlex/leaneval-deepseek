import Mathlib

/-!
# Vocabulary for the Barban–Vehov / Graham estimate (Jutila's Lemma 4)

The Barban–Vehov (Selberg) weights with real cutoffs `1 < w < y` are

  `bvW w y d = 1` for `d ≤ w`, `= log (y/d) / log (y/w)` for `w < d ≤ y`, `= 0` for `y < d`,

realised here as `max 0 (min 1 (log (y/d) / log (y/w)))`.  They are the divisor-sum weights of
the *difference* of the two truncated von Mangoldt sums

  `Lz z n = Σ_{d ∣ n, d ≤ z} μ(d)·log (z/d)`   (`z` a real cutoff),

namely `Σ_{d ∣ n} μ(d)·bvW w y d = (Lz y n − Lz w n) / log (y/w)`.

We also record the truncated Möbius divisor sum `P t n = Σ_{d ∣ n, d ≤ t} μ(d)`.
-/

namespace Work.ZeroDensity.Jutila

open Finset

noncomputable section

/-- **Jutila's truncated von Mangoldt sum.** `Lz z n = Σ_{d ∣ n, d ≤ z} μ(d)·log(z/d)`. -/
def Lz (z : ℝ) (n : ℕ) : ℝ :=
  ∑ d ∈ n.divisors.filter (fun d : ℕ => (d : ℝ) ≤ z),
    (ArithmeticFunction.moebius d : ℝ) * Real.log (z / (d : ℝ))

/-- **The truncated Möbius divisor sum.** `P t n = Σ_{d ∣ n, d ≤ t} μ(d)`. -/
def P (t : ℝ) (n : ℕ) : ℝ :=
  ∑ d ∈ n.divisors.filter (fun d : ℕ => (d : ℝ) ≤ t), (ArithmeticFunction.moebius d : ℝ)

/-- **The Barban–Vehov weight.** `bvW w y d = max 0 (min 1 (log(y/d)/log(y/w)))`, i.e. the
tent-shaped weight of Jutila's Lemma 4 (with real cutoffs `1 < w < y`). -/
def bvW (w y : ℝ) (d : ℕ) : ℝ := max 0 (min 1 (Real.log (y / (d : ℝ)) / Real.log (y / w)))

/-- The weight `bvW` is nonnegative. -/
lemma bvW_nonneg (w y : ℝ) (d : ℕ) : 0 ≤ bvW w y d := le_max_left _ _

/-- The weight `bvW w y d ≤ 1`. -/
lemma bvW_le_one (w y : ℝ) (d : ℕ) : bvW w y d ≤ 1 :=
  max_le (by norm_num) (min_le_left _ _)

/-- For `d ≤ w` (and `1 < w < y`, `d ≥ 1`) the Barban–Vehov weight is `1`. -/
lemma bvW_of_le {w y : ℝ} (hw : 1 < w) (hwy : w < y) {d : ℕ} (hd1 : 1 ≤ d)
    (hd : (d : ℝ) ≤ w) : bvW w y d = 1 := by
  have hw0 : 0 < w := by linarith
  have hy0 : 0 < y := by linarith
  have hd0 : 0 < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
  have hyw : 0 < Real.log (y / w) := Real.log_pos (by rw [lt_div_iff₀ hw0]; simpa using hwy)
  have hmono : Real.log (y / w) ≤ Real.log (y / (d : ℝ)) := by
    apply Real.log_le_log (by positivity)
    rw [div_le_div_iff₀ hw0 hd0]
    nlinarith
  have hge : 1 ≤ Real.log (y / (d : ℝ)) / Real.log (y / w) := by
    rw [le_div_iff₀ hyw, one_mul]; exact hmono
  rw [bvW, min_eq_left hge, max_eq_right (by norm_num : (0:ℝ) ≤ 1)]

/-- For `y ≤ d` (and `1 < w < y`, `d ≥ 1`) the Barban–Vehov weight is `0`. -/
lemma bvW_of_ge {w y : ℝ} (hw : 1 < w) (hwy : w < y) {d : ℕ} (hd1 : 1 ≤ d)
    (hd : y ≤ (d : ℝ)) : bvW w y d = 0 := by
  have hw0 : 0 < w := by linarith
  have hy0 : 0 < y := by linarith
  have hd0 : 0 < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
  have hyw : 0 < Real.log (y / w) := Real.log_pos (by rw [lt_div_iff₀ hw0]; simpa using hwy)
  have hlog : Real.log (y / (d : ℝ)) ≤ 0 := by
    apply Real.log_nonpos
    · positivity
    · rw [div_le_one hd0]; exact hd
  have hle : Real.log (y / (d : ℝ)) / Real.log (y / w) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg hlog (le_of_lt hyw)
  rw [bvW, min_eq_right (le_trans hle (by norm_num : (0:ℝ) ≤ 1)), max_eq_left hle]

end

end Work.ZeroDensity.Jutila
