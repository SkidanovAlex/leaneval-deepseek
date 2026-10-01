import Mathlib
import Submission.Work.ZeroDensity.Jutila.bvDefs
import Submission.Work.ZeroDensity.Jutila.SumStepsMulP

/-!
# Step decomposition of the difference of two truncated von Mangoldt sums

`Lz z n = Σ_{d ∣ n, d ≤ z} μ(d)·log(z/d)` and `P t n = Σ_{d ∣ n, d ≤ t} μ(d)` (`bvDefs.lean`).
The main result `LzSubEqSumSteps` writes `Lz y n - Lz w n` (`1 < w < y`) as the sum over the
integer cutoffs `j ∈ [⌊w⌋₊, ⌊y⌋₊]` of the step weights
`stepW w y j = log (min y (j+1)) - log (max w j)` times `P j n`.

The proof expands both sides over the divisors of `n`:
`Lz z n = Σ_{d ∣ n} [d ≤ z]·μ(d)·log(z/d)`, and `Σ_{d ∣ n} μ(d)·bvW(d)` bookkeeping at the level
of a single divisor `d` reduces to the step identity `stepWFilter`: summing the step weights over
the cutoffs `j ≥ d` telescopes to `log⁺(y/d) - log⁺(w/d)`.  The reindexing of the double sum (the
swap of the sums over the cutoffs `j` and the divisors `d`) is `SumStepsMulP`.

## Main result

* `LzSubEqSumSteps` : the step decomposition.

## Intermediate steps

* `iccFilterEq` : `(Icc a b).filter (d ≤ ·) = Icc (max a d) b`.
* `iccEqIcoSucc` : `Icc a b = Ico a (b+1)`.
* `stepLogSum` : telescoping of `log (min y (j+1)) - log j` over `j ∈ [d, ⌊y⌋₊]`.
* `stepWFull` : the full step sum equals `log (y/w)`.
* `stepWFilter` : the per-divisor step identity.
-/

namespace Work.ZeroDensity.Jutila

/-- `(Icc a b).filter (d ≤ ·) = Icc (max a d) b`. -/
lemma iccFilterEq (a b d : ℕ) :
    (Finset.Icc a b).filter (fun j => d ≤ j) = Finset.Icc (max a d) b := by
  ext j
  simp only [Finset.mem_filter, Finset.mem_Icc]
  omega

/-- `Icc a b = Ico a (b+1)`. -/
lemma iccEqIcoSucc (a b : ℕ) : Finset.Icc a b = Finset.Ico a (b + 1) := by
  ext x; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega

/-- **Telescoping of the truncated log steps.**  For `1 ≤ d ≤ y`,
`∑_{j=d}^{⌊y⌋₊} (log (min y (j+1)) - log j) = log (y/d)`.  Indeed `min y (j+1) = j+1` for
`j < ⌊y⌋₊` while `min y (⌊y⌋₊+1) = y`, so the interior terms cancel. -/
lemma stepLogSum {y : ℝ} (hy : 0 ≤ y) {d : ℕ} (hd : 1 ≤ d) (hdy : (d : ℝ) ≤ y) :
    ∑ j ∈ Finset.Icc d ⌊y⌋₊,
        (Real.log (min y ((j : ℝ) + 1)) - Real.log (j : ℝ)) = Real.log (y / (d : ℝ)) := by
  have hy0 : 0 < y := lt_of_lt_of_le (by exact_mod_cast (show (0:ℕ) < d by omega)) hdy
  have hd0 : (((d : ℕ)) : ℝ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
  have hdK : d ≤ ⌊y⌋₊ := Nat.le_floor hdy
  have hKy : ((⌊y⌋₊ : ℕ) : ℝ) ≤ y := Nat.floor_le hy
  have hstep : ∀ j ∈ Finset.Icc d ⌊y⌋₊,
      (Real.log (min y ((j : ℝ) + 1)) - Real.log (j : ℝ))
        = Real.log (min y (((j + 1 : ℕ) : ℝ))) - Real.log (min y ((j : ℕ) : ℝ)) := by
    intro j hj
    have hjK : j ≤ ⌊y⌋₊ := (Finset.mem_Icc.mp hj).2
    have hjy : (j : ℝ) ≤ y := le_trans (by exact_mod_cast hjK) hKy
    simp only [Nat.cast_add, Nat.cast_one, min_eq_right hjy]
  rw [Finset.sum_congr rfl hstep]
  rw [iccEqIcoSucc]
  have htel := Finset.sum_Ico_sub (f := fun t : ℕ => Real.log (min y (t : ℝ)))
      (m := d) (n := ⌊y⌋₊ + 1) (show d ≤ ⌊y⌋₊ + 1 by omega)
  rw [htel]
  have hcast : (((⌊y⌋₊ + 1 : ℕ)) : ℝ) = ((⌊y⌋₊ : ℕ) : ℝ) + 1 := by push_cast; ring
  have hK1 : y ≤ ((⌊y⌋₊ : ℕ) : ℝ) + 1 := le_of_lt (Nat.lt_floor_add_one y)
  rw [hcast, min_eq_left hK1, min_eq_right hdy]
  rw [Real.log_div (ne_of_gt hy0) hd0]

/-- **The full step sum.**  For `1 < w < y` the step weights over the integer cutoffs in
`[⌊w⌋₊, ⌊y⌋₊]` sum to `log (y/w)`.  Split off the bottom cutoff `j = ⌊w⌋₊`: the remaining sum
telescopes (`stepLogSum`) and the bottom term supplies `log ⌊w⌋₊ - log w`. -/
lemma stepWFull {w y : ℝ} (hw : 1 < w) (hwy : w < y) :
    ∑ j ∈ Finset.Icc ⌊w⌋₊ ⌊y⌋₊,
        (Real.log (min y ((j : ℝ) + 1)) - Real.log (max w (j : ℝ))) = Real.log (y / w) := by
  have hw0 : 0 < w := by linarith
  have hy0 : 0 < y := lt_trans hw0 hwy
  have hk1 : 1 ≤ ⌊w⌋₊ := Nat.le_floor (show (((1:ℕ)) : ℝ) ≤ w by push_cast; linarith)
  have hkw : ((⌊w⌋₊ : ℕ) : ℝ) ≤ w := Nat.floor_le (le_of_lt hw0)
  have hky : ((⌊w⌋₊ : ℕ) : ℝ) ≤ y := le_of_lt (lt_of_le_of_lt hkw hwy)
  have hk0 : (((⌊w⌋₊ : ℕ)) : ℝ) ≠ 0 := by exact_mod_cast (by omega : ⌊w⌋₊ ≠ 0)
  have h1 := stepLogSum (le_of_lt hy0) hk1 hky
  have h2 : ∑ j ∈ Finset.Icc ⌊w⌋₊ ⌊y⌋₊,
        (Real.log (j : ℝ) - Real.log (max w (j : ℝ)))
      = Real.log ((⌊w⌋₊ : ℕ) : ℝ) - Real.log w := by
    rw [Finset.sum_eq_single ⌊w⌋₊]
    · rw [max_eq_left hkw]
    · intro j hj hjk
      have hlt : ⌊w⌋₊ < j := lt_of_le_of_ne (Finset.mem_Icc.mp hj).1 (Ne.symm hjk)
      have hwj : w ≤ (j : ℝ) := by
        have hle : ⌊w⌋₊ + 1 ≤ j := hlt
        have hle' : ((⌊w⌋₊ : ℕ) : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast hle
        linarith [Nat.lt_floor_add_one w]
      rw [max_eq_right hwj, sub_self]
    · intro hmem
      exact absurd (Finset.mem_Icc.mpr ⟨le_rfl, Nat.floor_le_floor (le_of_lt hwy)⟩) hmem
  have hsum : ∑ j ∈ Finset.Icc ⌊w⌋₊ ⌊y⌋₊,
        (Real.log (min y ((j : ℝ) + 1)) - Real.log (max w (j : ℝ)))
      = ∑ j ∈ Finset.Icc ⌊w⌋₊ ⌊y⌋₊, (Real.log (min y ((j : ℝ) + 1)) - Real.log (j : ℝ))
        + ∑ j ∈ Finset.Icc ⌊w⌋₊ ⌊y⌋₊, (Real.log (j : ℝ) - Real.log (max w (j : ℝ))) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ring
  rw [hsum, h1, h2]
  rw [Real.log_div (ne_of_gt hy0) hk0, Real.log_div (ne_of_gt hy0) (ne_of_gt hw0)]
  ring

/-- **The per-divisor step identity.**  For `1 < w < y` and `d ≥ 1`, the step weights with
cutoff `j ≥ d` sum to `log⁺(y/d) - log⁺(w/d)`, rendered with `if`.  If `d ≤ w` the range is all
of `[⌊w⌋₊, ⌊y⌋₊]` and the sum is `log (y/w) = log (y/d) - log (w/d)` (`stepWFull`); if `w < d ≤ y`
then `max w j = j` throughout and the sum telescopes (`stepLogSum`); if `y < d` the range is
empty and both truncations vanish. -/
lemma stepWFilter {w y : ℝ} (hw : 1 < w) (hwy : w < y) {d : ℕ} (hd : 1 ≤ d) :
    ∑ j ∈ (Finset.Icc ⌊w⌋₊ ⌊y⌋₊).filter (fun j => d ≤ j),
        (Real.log (min y ((j : ℝ) + 1)) - Real.log (max w (j : ℝ)))
      = (if (d : ℝ) ≤ y then Real.log (y / (d : ℝ)) else 0)
        - (if (d : ℝ) ≤ w then Real.log (w / (d : ℝ)) else 0) := by
  have hw0 : 0 < w := by linarith
  have hy0 : 0 < y := lt_trans hw0 hwy
  have hkw : ((⌊w⌋₊ : ℕ) : ℝ) ≤ w := Nat.floor_le (le_of_lt hw0)
  have hky : ((⌊y⌋₊ : ℕ) : ℝ) ≤ y := Nat.floor_le (le_of_lt hy0)
  have hd0 : ((d : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (by omega : d ≠ 0)
  rw [iccFilterEq]
  by_cases hdw : (d : ℝ) ≤ w
  · have hdk : d ≤ ⌊w⌋₊ := Nat.le_floor hdw
    rw [Nat.max_eq_left hdk, if_pos (le_of_lt (lt_of_le_of_lt hdw hwy)), if_pos hdw]
    rw [stepWFull hw hwy]
    rw [Real.log_div (ne_of_gt hy0) hd0, Real.log_div (ne_of_gt hw0) hd0,
        Real.log_div (ne_of_gt hy0) (ne_of_gt hw0)]
    ring
  · have hwd : w < (d : ℝ) := lt_of_not_ge hdw
    have hkwd : ⌊w⌋₊ < d := by
      have hlt : ((⌊w⌋₊ : ℕ) : ℝ) < (d : ℝ) := lt_of_le_of_lt hkw hwd
      exact_mod_cast hlt
    rw [Nat.max_eq_right (le_of_lt hkwd), if_neg hdw]
    by_cases hdy : (d : ℝ) ≤ y
    · rw [if_pos hdy]
      have hcongr : ∀ j ∈ Finset.Icc d ⌊y⌋₊,
          (Real.log (min y ((j : ℝ) + 1)) - Real.log (max w (j : ℝ)))
            = (Real.log (min y ((j : ℝ) + 1)) - Real.log (j : ℝ)) := by
        intro j hj
        have hdj : d ≤ j := (Finset.mem_Icc.mp hj).1
        have hwj : w ≤ (j : ℝ) := by
          have hlt' : ((d : ℕ) : ℝ) ≤ (j : ℝ) := by exact_mod_cast hdj
          linarith
        rw [max_eq_right hwj]
      rw [Finset.sum_congr rfl hcongr, stepLogSum (le_of_lt hy0) hd hdy, sub_zero]
    · rw [if_neg hdy, sub_zero]
      have hKd : ⌊y⌋₊ < d := by
        have hlt : ((⌊y⌋₊ : ℕ) : ℝ) < (d : ℝ) := lt_of_le_of_lt hky (lt_of_not_ge hdy)
        exact_mod_cast hlt
      rw [Finset.Icc_eq_empty (by omega : ¬ d ≤ ⌊y⌋₊), Finset.sum_empty]

/-- **Step decomposition of the difference of the two truncated von Mangoldt sums.**
`Lz z n = Σ_{d ∣ n, d ≤ z} μ(d)·log(z/d)` and `P t n = Σ_{d ∣ n, d ≤ t} μ(d)` (`bvDefs.lean`).
For `1 < w < y` and every `n`, the difference of the two truncated von Mangoldt sums is the sum
of `P j n` over the integer cutoffs `j ∈ [⌊w⌋₊, ⌊y⌋₊]`, weighted by the `log`-lengths
`stepW w y j = log (min y (j+1)) - log (max w j)` of the pieces of the partition of `[w,y]` cut
at the integers.

Proof route: expand both sides over divisors.  `Lz y n - Lz w n = Σ_{d ∣ n} μ d · (log (y/d)⁺ -
log (w/d)⁺)` where `x⁺ = max x 0`; swapping the two finite sums it suffices to prove, for each
`d ≥ 1` with `(d:ℝ) ≤ y`,
  `Σ_{j ∈ Icc ⌊w⌋₊ ⌊y⌋₊, d ≤ j} (log (min y (j+1)) - log (max w j)) = log (y / max w d)`,
which is `log⁺ (y/d) - log⁺ (w/d)`: the summands vanish for `j < d`, and for `j ≥ d` the
telescoping `Σ_{j=m}^{⌊y⌋₊}(log (min y (j+1)) - log j) = log y - log m` gives it. -/
theorem LzSubEqSumSteps {w y : ℝ} (hw : 1 < w) (hwy : w < y) (n : ℕ) :
    Lz y n - Lz w n
      = ∑ j ∈ Finset.Icc ⌊w⌋₊ ⌊y⌋₊,
          (Real.log (min y ((j : ℝ) + 1)) - Real.log (max w (j : ℝ))) * (P (j : ℝ) n) := by
  have hLz : ∀ z : ℝ, Lz z n = ∑ d ∈ n.divisors,
      (if (d : ℝ) ≤ z then (ArithmeticFunction.moebius d : ℝ) * Real.log (z / (d : ℝ))
        else 0) := by
    intro z
    rw [Lz, Finset.sum_filter]
  have hR : (∑ j ∈ Finset.Icc ⌊w⌋₊ ⌊y⌋₊,
        (Real.log (min y ((j : ℝ) + 1)) - Real.log (max w (j : ℝ))) * (P (j : ℝ) n))
      = ∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℝ) *
          ∑ j ∈ (Finset.Icc ⌊w⌋₊ ⌊y⌋₊).filter (fun j => d ≤ j),
            (Real.log (min y ((j : ℝ) + 1)) - Real.log (max w (j : ℝ))) :=
    SumStepsMulP (Finset.Icc ⌊w⌋₊ ⌊y⌋₊)
      (fun j => Real.log (min y ((j : ℝ) + 1)) - Real.log (max w (j : ℝ))) n
  rw [hR, hLz y, hLz w, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun d hdmem => ?_)
  obtain ⟨hdvd, hn0⟩ := Nat.mem_divisors.mp hdmem
  have hd1 : 1 ≤ d := Nat.pos_of_dvd_of_pos hdvd (Nat.pos_of_ne_zero hn0)
  have hd_eq : (∑ j ∈ (Finset.Icc ⌊w⌋₊ ⌊y⌋₊).filter (fun j => d ≤ j),
        (Real.log (min y ((j : ℝ) + 1)) - Real.log (max w (j : ℝ))))
      = (if (d : ℝ) ≤ y then Real.log (y / (d : ℝ)) else 0)
        - (if (d : ℝ) ≤ w then Real.log (w / (d : ℝ)) else 0) :=
    stepWFilter hw hwy hd1
  rw [hd_eq]
  by_cases h1 : (d : ℝ) ≤ y <;> by_cases h2 : (d : ℝ) ≤ w <;>
    simp only [h1, h2, if_true, if_false, mul_zero, sub_zero, zero_sub, mul_sub]
  all_goals ring

end Work.ZeroDensity.Jutila
