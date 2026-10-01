import Mathlib
import Submission.Work.ZeroDensity.Jutila.BzCross.czReindexDefs
import Submission.Work.ZeroDensity.Jutila.LzDiffAux.SumDivisorsIccSwap

/-!
# Row 4 of the Region II `r`-sum bounds

For `R = czR w N q` we prove that the weighted `r`-sum
`Σ_{r ≤ R} (Σ_{d ∣ r} d^{-1/2}) · (czTmax w y N q r / w)²`
is `O(R³/y²)`, uniformly in `w ≤ y`, `N < w·y`, `q` (and in fact with the absolute constant
`3`, independent of `c`).

The proof has three elementary inputs:

* `czTmax w y N q r ≤ w·r/y` for `r ≥ 1`, because the floor cut-off in `czTmax` is
  `⌊w/(⌊y/r⌋+1)⌋ ≤ w/(y/r) = w·r/y` and the `min` with `czT` only lowers it.  Hence the weight
  is at most `(r/y)²` and, after squaring, the `r²`-weight matches the `R³` in the answer.
* the divisor reindexing `Σ_{r ≤ R} Σ_{d ∣ r} F d r = Σ_{d ≤ R} Σ_{m ≤ R/d} F d (d·m)`
  (`SumDivisorsIccSwap`), which turns `d^{-1/2}·(d·m)²` into the factorizable
  `d^{-1/2}·d²·m²`;
* the two elementary bounds `Σ_{m ≤ K} m² ≤ K³` and `Σ_{d ≤ T} d^{-1/2}/d ≤ 3`
  (the latter by telescoping with `2/√(d-1) - 2/√d`).

The last sum is `≤ 3` rather than exactly `ζ(3/2) ≈ 2.61`, which is harmless here since the
constant is existentially quantified.  The hypotheses `1 ≤ w ≤ y` only serve to make `y > 0`;
`N < w·y` and the very definition of `czR` are not used beyond ensuring the sums are finite.
-/

namespace Work.ZeroDensity.Jutila.LzDiffAux

open Finset
open Work.ZeroDensity.Jutila

noncomputable section

/-- **Size of the cut-off.**  For `r ≥ 1` the cut-off `czTmax w y N q r` is at most `w·r/y`:
its second (floor) argument is `⌊w/(⌊y/r⌋+1)⌋ ≤ w/(⌊y/r⌋+1) ≤ w/(y/r) = w·r/y`. -/
lemma czTmax_cast_mul_le_lz {w y : ℝ} (hw : 0 < w) (hy : 0 < y) (N q r : ℕ) (hr : 1 ≤ r) :
    (BzCross.czTmax w y N q r : ℝ) ≤ w * (r : ℝ) / y := by
  have hr0 : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (by omega : 0 < r)
  have hfloor : y / (r : ℝ) ≤ ((⌊y / (r : ℝ)⌋₊ : ℕ) : ℝ) + 1 :=
    le_of_lt (Nat.lt_floor_add_one _)
  have hkey : y ≤ (((⌊y / (r : ℝ)⌋₊ : ℕ) : ℝ) + 1) * (r : ℝ) := by
    have h := mul_le_mul_of_nonneg_right hfloor hr0.le
    rwa [div_mul_cancel₀ y (ne_of_gt hr0)] at h
  have hposA : (0 : ℝ) < (((⌊y / (r : ℝ)⌋₊ : ℕ) : ℝ) + 1) := by positivity
  have hstep : w / (((⌊y / (r : ℝ)⌋₊ : ℕ) : ℝ) + 1) ≤ w * (r : ℝ) / y := by
    rw [div_le_iff₀ hposA, div_mul_eq_mul_div, le_div_iff₀ hy]
    nlinarith [hkey, hw]
  have hle : BzCross.czTmax w y N q r
      ≤ ⌊w / (((⌊y / (r : ℝ)⌋₊ : ℕ) : ℝ) + 1)⌋₊ := by
    rw [BzCross.czTmax]
    exact min_le_right _ _
  calc (BzCross.czTmax w y N q r : ℝ)
      ≤ (⌊w / (((⌊y / (r : ℝ)⌋₊ : ℕ) : ℝ) + 1)⌋₊ : ℝ) := by exact_mod_cast hle
    _ ≤ w / (((⌊y / (r : ℝ)⌋₊ : ℕ) : ℝ) + 1) := Nat.floor_le (by positivity)
    _ ≤ w * (r : ℝ) / y := hstep

/-- Consequently the squared weight satisfies `(czTmax/w)² ≤ (r/y)²`. -/
lemma czTmax_div_sq_le_lz {w y : ℝ} (hw : 0 < w) (hy : 0 < y) (N q r : ℕ) (hr : 1 ≤ r) :
    ((BzCross.czTmax w y N q r : ℝ) / w) ^ 2 ≤ ((r : ℝ) / y) ^ 2 := by
  have h := czTmax_cast_mul_le_lz hw hy N q r hr
  have hle : (BzCross.czTmax w y N q r : ℝ) / w ≤ (r : ℝ) / y := by
    rw [div_le_iff₀ hw]
    have hcomm : (r : ℝ) / y * w = w * (r : ℝ) / y := by ring
    linarith [h, hcomm]
  exact pow_le_pow_left₀ (div_nonneg (Nat.cast_nonneg _) hw.le) hle 2

/-- `Σ_{m ≤ K} m² ≤ K³`: there are `K` terms, each at most `K²`. -/
lemma sum_sq_le_cube_lz (K : ℕ) :
    (∑ m ∈ Finset.Icc 1 K, (m : ℝ) ^ 2) ≤ (K : ℝ) ^ 3 := by
  calc (∑ m ∈ Finset.Icc 1 K, (m : ℝ) ^ 2)
      ≤ ∑ _m ∈ Finset.Icc 1 K, (K : ℝ) ^ 2 := by
        refine Finset.sum_le_sum (fun m hm => ?_)
        have hmK : (m : ℝ) ≤ (K : ℝ) := by
          exact_mod_cast (Finset.mem_Icc.mp hm).2
        exact pow_le_pow_left₀ (by positivity) hmK 2
    _ = (K : ℝ) * (K : ℝ) ^ 2 := by
        rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
    _ = (K : ℝ) ^ 3 := by ring

/-- A square-root inequality: for `x = y + 1`, `x, y > 0` one has `(2x+1)·√y ≤ 2x·√x`. -/
private lemma sqrt_key_lz {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (hxy : x = y + 1) :
    (2 * x + 1) * Real.sqrt y ≤ 2 * x * Real.sqrt x := by
  have h1 : (2 * x + 1) * Real.sqrt y = Real.sqrt ((2 * x + 1) ^ 2 * y) := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  have h2 : (2 * x) * Real.sqrt x = Real.sqrt ((2 * x) ^ 2 * x) := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  rw [h1, h2, Real.sqrt_le_sqrt_iff (by positivity)]
  rw [hxy]
  nlinarith [hy.le]

/-- **Termwise telescoping bound.**  For `d ≥ 2`,
`1/(√d · d) ≤ 2/√(d-1) - 2/√d`. -/
private lemma inv_sqrt_mul_inv_term_le_lz (d : ℕ) (hd : 2 ≤ d) :
    (1 : ℝ) / Real.sqrt (d : ℝ) * (1 / (d : ℝ))
      ≤ 2 / Real.sqrt (((d - 1 : ℕ) : ℝ)) - 2 / Real.sqrt ((d : ℝ)) := by
  have hd0 : 0 < d := by omega
  have hx0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd0
  have hy0 : (0 : ℝ) < ((d - 1 : ℕ) : ℝ) := by
    have : 0 < d - 1 := by omega
    exact_mod_cast this
  have hxy : (d : ℝ) = ((d - 1 : ℕ) : ℝ) + 1 := by
    have hnat : d = (d - 1) + 1 := by omega
    exact_mod_cast hnat
  have hkey := sqrt_key_lz hx0 hy0 hxy
  have hsne : Real.sqrt (d : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hx0)
  have hmain : (2 * (d : ℝ) + 1) / ((d : ℝ) * Real.sqrt (d : ℝ))
      ≤ 2 / Real.sqrt (((d - 1 : ℕ) : ℝ)) := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < (d : ℝ) * Real.sqrt (d : ℝ)),
      div_mul_eq_mul_div, le_div_iff₀ (Real.sqrt_pos.mpr hy0)]
    nlinarith [hkey]
  rw [le_sub_iff_add_le]
  have hadd : (1 : ℝ) / Real.sqrt (d : ℝ) * (1 / (d : ℝ)) + 2 / Real.sqrt (d : ℝ)
      = (2 * (d : ℝ) + 1) / ((d : ℝ) * Real.sqrt (d : ℝ)) := by
    have hxne : (d : ℝ) ≠ 0 := ne_of_gt hx0
    field_simp
    ring
  rw [hadd]
  exact hmain

/-- **The reciprocal-square-root sum is bounded.**  `Σ_{d ≤ T} d^{-1/2}/d ≤ 3`, by telescoping
with `3 - 2/√T`. -/
lemma sum_inv_sqrt_mul_inv_le_three_lz (T : ℕ) :
    (∑ d ∈ Finset.Icc 1 T, (1 : ℝ) / Real.sqrt (d : ℝ) * (1 / (d : ℝ))) ≤ 3 := by
  have hmain : ∀ T : ℕ,
      (∑ d ∈ Finset.Icc 1 T, (1 : ℝ) / Real.sqrt (d : ℝ) * (1 / (d : ℝ)))
        ≤ 3 - 2 / Real.sqrt (T : ℝ) := by
    intro T
    induction T with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_Icc_succ_top (Nat.le_add_left 1 n)]
      rcases Nat.eq_zero_or_pos n with hn | hn
      · subst hn
        have hemp : Finset.Icc 1 0 = (∅ : Finset ℕ) := by
          rw [Finset.Icc_eq_empty_iff]; omega
        rw [hemp, Finset.sum_empty, zero_add]
        norm_num [Real.sqrt_one]
      · have hn1 : 2 ≤ n + 1 := by omega
        have hterm := inv_sqrt_mul_inv_term_le_lz (n + 1) hn1
        rw [show (n + 1 - 1 : ℕ) = n from by omega] at hterm
        calc (∑ d ∈ Finset.Icc 1 n, (1 : ℝ) / Real.sqrt (d : ℝ) * (1 / (d : ℝ)))
              + ((1 : ℝ) / Real.sqrt (((n + 1 : ℕ)) : ℝ) * (1 / (((n + 1 : ℕ)) : ℝ)))
            ≤ (3 - 2 / Real.sqrt ((n : ℕ) : ℝ))
              + (2 / Real.sqrt ((n : ℕ) : ℝ) - 2 / Real.sqrt (((n + 1 : ℕ)) : ℝ)) :=
              add_le_add ih hterm
          _ = 3 - 2 / Real.sqrt (((n + 1 : ℕ)) : ℝ) := by ring
  have h := hmain T
  have hpos : (0 : ℝ) ≤ 2 / Real.sqrt (T : ℝ) :=
    div_nonneg (by norm_num) (Real.sqrt_nonneg _)
  linarith

/-- **The `(r/y)²`-weighted divisor sum.**  For `R ≥ 0` and `y > 0`,
`Σ_{r ≤ R} (Σ_{d ∣ r} d^{-1/2})·(r/y)² ≤ 3·R³/y²`. -/
lemma row4_core_lz (R : ℕ) {y : ℝ} (hy : 0 < y) :
    (∑ r ∈ Finset.Icc 1 R, (∑ d ∈ r.divisors, 1 / Real.sqrt (d : ℝ)) * ((r : ℝ) / y) ^ 2)
      ≤ 3 * ((R : ℝ) ^ 3 / y ^ 2) := by
  have hswap : (∑ r ∈ Finset.Icc 1 R, ∑ d ∈ r.divisors,
        (1 / Real.sqrt (d : ℝ)) * ((r : ℝ) / y) ^ 2)
      = ∑ d ∈ Finset.Icc 1 R, ∑ m ∈ Finset.Icc 1 (R / d),
          (1 / Real.sqrt (d : ℝ)) * (((d * m : ℕ) : ℝ) / y) ^ 2 :=
    SumDivisorsIccSwap (fun d r => (1 / Real.sqrt (d : ℝ)) * ((r : ℝ) / y) ^ 2) R
  calc (∑ r ∈ Finset.Icc 1 R, (∑ d ∈ r.divisors, 1 / Real.sqrt (d : ℝ)) * ((r : ℝ) / y) ^ 2)
      = ∑ r ∈ Finset.Icc 1 R, ∑ d ∈ r.divisors,
          (1 / Real.sqrt (d : ℝ)) * ((r : ℝ) / y) ^ 2 := by
        refine Finset.sum_congr rfl (fun r _ => ?_)
        rw [Finset.sum_mul]
    _ = ∑ d ∈ Finset.Icc 1 R, ∑ m ∈ Finset.Icc 1 (R / d),
          (1 / Real.sqrt (d : ℝ)) * (((d * m : ℕ) : ℝ) / y) ^ 2 := hswap
    _ = ∑ d ∈ Finset.Icc 1 R, ((1 / Real.sqrt (d : ℝ)) * ((d : ℝ) / y) ^ 2)
          * (∑ m ∈ Finset.Icc 1 (R / d), (m : ℝ) ^ 2) := by
        refine Finset.sum_congr rfl (fun d _ => ?_)
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun m _ => ?_)
        push_cast
        ring
    _ ≤ ∑ d ∈ Finset.Icc 1 R, ((1 / Real.sqrt (d : ℝ)) * ((d : ℝ) / y) ^ 2)
          * (((R / d : ℕ) : ℝ) ^ 3) := by
        refine Finset.sum_le_sum (fun d hd => ?_)
        have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
        have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
        have hnn : 0 ≤ (1 / Real.sqrt (d : ℝ)) * ((d : ℝ) / y) ^ 2 :=
          mul_nonneg (div_nonneg (by norm_num) (Real.sqrt_nonneg _)) (sq_nonneg _)
        exact mul_le_mul_of_nonneg_left (sum_sq_le_cube_lz (R / d)) hnn
    _ ≤ ∑ d ∈ Finset.Icc 1 R, ((1 / Real.sqrt (d : ℝ)) * (1 / (d : ℝ)))
          * ((R : ℝ) ^ 3 / y ^ 2) := by
        refine Finset.sum_le_sum (fun d hd => ?_)
        have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
        have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
        have hRd : (((R / d : ℕ)) : ℝ) ≤ (R : ℝ) / (d : ℝ) := Nat.cast_div_le
        have hcube : ((((R / d : ℕ)) : ℝ) ^ 3) ≤ ((R : ℝ) / (d : ℝ)) ^ 3 :=
          pow_le_pow_left₀ (Nat.cast_nonneg _) hRd 3
        have hnn : 0 ≤ (1 / Real.sqrt (d : ℝ)) * ((d : ℝ) / y) ^ 2 :=
          mul_nonneg (div_nonneg (by norm_num) (Real.sqrt_nonneg _)) (sq_nonneg _)
        refine le_trans (mul_le_mul_of_nonneg_left hcube hnn) (le_of_eq ?_)
        have hsne : Real.sqrt (d : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hd0)
        have hdne : (d : ℝ) ≠ 0 := ne_of_gt hd0
        have hyne : y ≠ 0 := ne_of_gt hy
        field_simp
    _ = (∑ d ∈ Finset.Icc 1 R, (1 / Real.sqrt (d : ℝ)) * (1 / (d : ℝ)))
          * ((R : ℝ) ^ 3 / y ^ 2) := by
        rw [Finset.sum_mul]
    _ ≤ 3 * ((R : ℝ) ^ 3 / y ^ 2) :=
        mul_le_mul_of_nonneg_right (sum_inv_sqrt_mul_inv_le_three_lz R)
          (div_nonneg (pow_nonneg (Nat.cast_nonneg R) 3) (sq_nonneg y))

theorem CzRIIRow4Final (c : ℝ) (hc : 0 < c) :
  ∃ C : ℝ, 0 < C ∧ ∀ (w y : ℝ) (N : ℕ) (q : ℕ), 1 ≤ w → w ≤ y → (N:ℝ) < w*y →
      (∑ r ∈ Finset.Icc 1 (Work.ZeroDensity.Jutila.czR w N q),
        (∑ d ∈ r.divisors, 1/Real.sqrt (d:ℝ))
        * (((Work.ZeroDensity.Jutila.BzCross.czTmax w y N q r : ℝ)/w)^2))
        ≤ C * ((Work.ZeroDensity.Jutila.czR w N q : ℝ)^3/y^2) := by
  refine ⟨3, by norm_num, ?_⟩
  intro w y N q hw1 hwy hNwy
  have hw : (0 : ℝ) < w := by linarith
  have hy : (0 : ℝ) < y := by linarith
  refine le_trans ?_ (row4_core_lz (czR w N q) hy)
  refine Finset.sum_le_sum (fun r hr => ?_)
  have hr1 : 1 ≤ r := (Finset.mem_Icc.mp hr).1
  refine mul_le_mul_of_nonneg_left (czTmax_div_sq_le_lz hw hy N q r hr1) ?_
  exact Finset.sum_nonneg (fun d _ => div_nonneg (by norm_num) (Real.sqrt_nonneg _))

end

end Work.ZeroDensity.Jutila.LzDiffAux
