import Mathlib
import Submission.Work.ZeroDensity.Jutila.BzCross.BzCrossDefs
import Submission.Work.LinnikAreas.Density4.BzS3.S3InnerDefs

namespace Work.LinnikAreas2

/-- `⌊w/t⌋₊ < m ↔ mt > w` for `t ≥ 1`, `w ≥ 1`. -/
lemma cz_floor_lt_iff_aux (w : ℝ) (t : ℕ) (hw : 1 ≤ w) (ht : 1 ≤ t) (m : ℕ) :
    ⌊w / (t : ℝ)⌋₊ < m ↔ w < ((m * t : ℕ) : ℝ) := by
  have ht0 : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht
  rw [Nat.floor_lt (div_nonneg (by linarith : (0 : ℝ) ≤ w) (Nat.cast_nonneg t)),
    Nat.cast_mul, div_lt_iff₀ ht0]

/-- `log(mt/w) = log m − log(w/t)`. -/
lemma cz_log_div_left_aux (w : ℝ) (t : ℕ) (m : ℕ) (hw : 1 ≤ w) (ht : 1 ≤ t)
    (hm : 1 ≤ m) :
    Real.log (((m * t : ℕ) : ℝ) / w)
      = Real.log (m : ℝ) - Work.ZeroDensity.Jutila.czAl w t := by
  have hw0 : (0 : ℝ) < w := by linarith
  have ht0 : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht
  have hm0 : (0 : ℝ) < (m : ℝ) := by
    have : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    linarith
  rw [Nat.cast_mul, Real.log_div (mul_ne_zero (ne_of_gt hm0) (ne_of_gt ht0)) (ne_of_gt hw0),
    Real.log_mul (ne_of_gt hm0) (ne_of_gt ht0), Work.ZeroDensity.Jutila.czAl,
    Real.log_div (ne_of_gt hw0) (ne_of_gt ht0)]
  ring

/-- `log(mr/y) = log m − log(y/r)`. -/
lemma cz_log_div_right_aux (y : ℝ) (r : ℕ) (m : ℕ) (hy : 1 ≤ y) (hr : 1 ≤ r)
    (hm : 1 ≤ m) :
    Real.log (((m * r : ℕ) : ℝ) / y)
      = Real.log (m : ℝ) - Work.ZeroDensity.Jutila.czBe y r := by
  have hy0 : (0 : ℝ) < y := by linarith
  have hr0 : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have hm0 : (0 : ℝ) < (m : ℝ) := by
    have : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    linarith
  rw [Nat.cast_mul, Real.log_div (mul_ne_zero (ne_of_gt hm0) (ne_of_gt hr0)) (ne_of_gt hy0),
    Real.log_mul (ne_of_gt hm0) (ne_of_gt hr0), Work.ZeroDensity.Jutila.czBe,
    Real.log_div (ne_of_gt hy0) (ne_of_gt hr0)]
  ring

/-- Pointwise comparison of the `m`-summand with the `s3G` summand. -/
lemma cz_pointwise_aux (w y : ℝ) (r t : ℕ) (hw : 1 ≤ w) (hy : 1 ≤ y) (hr : 1 ≤ r)
    (ht : 1 ≤ t) (m : ℕ) :
    (if Nat.Coprime m (r * t) ∧ w < ((m * t : ℕ) : ℝ) ∧ y < ((m * r : ℕ) : ℝ)
      then ((ArithmeticFunction.moebius m : ℝ)) ^ 2 *
        Real.log (((m * t : ℕ) : ℝ) / w) * Real.log (((m * r : ℕ) : ℝ) / y)
      else 0)
      = (if (Nat.Coprime m (r * t) ∧ Squarefree m) ∧
          Work.ZeroDensity.Jutila.czLo w y r t < m
        then (Real.log (m : ℝ) - Work.ZeroDensity.Jutila.czAl w t) *
          (Real.log (m : ℝ) - Work.ZeroDensity.Jutila.czBe y r)
        else 0) := by
  have hfloor : Work.ZeroDensity.Jutila.czLo w y r t < m ↔
      w < ((m * t : ℕ) : ℝ) ∧ y < ((m * r : ℕ) : ℝ) := by
    rw [Work.ZeroDensity.Jutila.czLo, max_lt_iff, cz_floor_lt_iff_aux w t hw ht m,
      cz_floor_lt_iff_aux y r hy hr m]
  by_cases hsq : Squarefree m
  · have hm2 : ((ArithmeticFunction.moebius m : ℝ)) ^ 2 = 1 := by
      have h := ArithmeticFunction.moebius_sq_eq_one_of_squarefree hsq
      rw [← Int.cast_pow, h]
      norm_num
    by_cases hQ : Nat.Coprime m (r * t) ∧ w < ((m * t : ℕ) : ℝ) ∧ y < ((m * r : ℕ) : ℝ)
    · have hQ' : (Nat.Coprime m (r * t) ∧ Squarefree m) ∧
          Work.ZeroDensity.Jutila.czLo w y r t < m :=
        ⟨⟨hQ.1, hsq⟩, hfloor.mpr ⟨hQ.2.1, hQ.2.2⟩⟩
      rw [if_pos hQ, if_pos hQ']
      have hm1 : 1 ≤ m := by
        obtain ⟨-, hwt, -⟩ := hQ
        have hpos : (0 : ℝ) < ((m * t : ℕ) : ℝ) := by linarith
        exact Nat.one_le_iff_ne_zero.mpr (fun h => by
          rw [h] at hpos
          simp at hpos)
      rw [hm2, cz_log_div_left_aux w t m hw ht hm1, cz_log_div_right_aux y r m hy hr hm1]
      ring
    · have hQ' : ¬ ((Nat.Coprime m (r * t) ∧ Squarefree m) ∧
          Work.ZeroDensity.Jutila.czLo w y r t < m) := by
        rintro ⟨⟨hc, -⟩, hlt⟩
        obtain ⟨h1, h2⟩ := hfloor.mp hlt
        exact hQ ⟨hc, h1, h2⟩
      simp only [if_neg hQ, if_neg hQ']
  · have hm2 : ((ArithmeticFunction.moebius m : ℝ)) ^ 2 = 0 := by
      have h := ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq
      rw [← Int.cast_pow, h]
      norm_num
    have hQ' : ¬ ((Nat.Coprime m (r * t) ∧ Squarefree m) ∧
        Work.ZeroDensity.Jutila.czLo w y r t < m) := by
      rintro ⟨⟨-, hs⟩, -⟩
      exact hsq hs
    rw [if_neg hQ', hm2]
    by_cases hQ : Nat.Coprime m (r * t) ∧ w < ((m * t : ℕ) : ℝ) ∧ y < ((m * r : ℕ) : ℝ)
    · rw [if_pos hQ]
      ring
    · rw [if_neg hQ]

/-- The inner `m`-sum of the reindexed cross sum equals the difference of the two `s3G` values.
Given `czLo w y r t ≤ czUp N q r t`, the sum over `m ≤ czUp` with `(m,rt)=1`, `mt > w`, `mr > y` of
`μ(m)²·log(mt/w)·log(mr/y)` equals `s3G (rt) (log(w/t)) (log(y/r)) czUp − s3G (rt) (log(w/t)) (log(y/r)) czLo`:
`μ(m)²` is the squarefree indicator, `mt > w ⟺ ⌊w/t⌋ < m` and `mr > y ⟺ ⌊y/r⌋ < m` reduce the
range to `czLo < m ≤ czUp`, and `log(mt/w) = log m − log(w/t)`, `log(mr/y) = log m − log(y/r)`. -/
theorem cz_inner_eq_s3G (w y : ℝ) (N q r t : ℕ) (hw : 1 ≤ w) (hy : 1 ≤ y)
    (hr : 1 ≤ r) (ht : 1 ≤ t)
    (hBX : Work.ZeroDensity.Jutila.czLo w y r t ≤ Work.ZeroDensity.Jutila.czUp N q r t) :
    (∑ m ∈ (Finset.Icc 1 (Work.ZeroDensity.Jutila.czUp N q r t)).filter
        (fun m => Nat.Coprime m (r * t) ∧ w < ((m * t : ℕ) : ℝ) ∧ y < ((m * r : ℕ) : ℝ)),
      ((ArithmeticFunction.moebius m : ℝ)) ^ 2 *
        Real.log (((m * t : ℕ) : ℝ) / w) * Real.log (((m * r : ℕ) : ℝ) / y))
      = Work.LinnikAreas.Density4.BzS3.s3G (r * t) (Work.ZeroDensity.Jutila.czAl w t)
            (Work.ZeroDensity.Jutila.czBe y r) (Work.ZeroDensity.Jutila.czUp N q r t)
        - Work.LinnikAreas.Density4.BzS3.s3G (r * t) (Work.ZeroDensity.Jutila.czAl w t)
            (Work.ZeroDensity.Jutila.czBe y r) (Work.ZeroDensity.Jutila.czLo w y r t) := by
  have hs : (Finset.Icc 1 (Work.ZeroDensity.Jutila.czLo w y r t)).filter
        (fun m => Nat.Coprime m (r * t) ∧ Squarefree m)
      ⊆ (Finset.Icc 1 (Work.ZeroDensity.Jutila.czUp N q r t)).filter
        (fun m => Nat.Coprime m (r * t) ∧ Squarefree m) := by
    intro m hm
    simp only [Finset.mem_filter, Finset.mem_Icc] at hm ⊢
    exact ⟨⟨hm.1.1, le_trans hm.1.2 hBX⟩, hm.2⟩
  have hsu : (Finset.Icc 1 (Work.ZeroDensity.Jutila.czUp N q r t)).filter
          (fun m => Nat.Coprime m (r * t) ∧ Squarefree m) \
        (Finset.Icc 1 (Work.ZeroDensity.Jutila.czLo w y r t)).filter
          (fun m => Nat.Coprime m (r * t) ∧ Squarefree m)
      = (Finset.Icc 1 (Work.ZeroDensity.Jutila.czUp N q r t)).filter
          (fun m => (Nat.Coprime m (r * t) ∧ Squarefree m) ∧
            Work.ZeroDensity.Jutila.czLo w y r t < m) := by
    ext m
    simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨⟨hm1, hmM⟩, hc, hs'⟩, hnot⟩
      exact ⟨⟨hm1, hmM⟩, ⟨⟨hc, hs'⟩, by
        by_contra hle
        exact hnot ⟨⟨hm1, by omega⟩, hc, hs'⟩⟩⟩
    · rintro ⟨⟨hm1, hmM⟩, ⟨⟨hc, hs'⟩, hlt⟩⟩
      exact ⟨⟨⟨hm1, hmM⟩, hc, hs'⟩, by rintro ⟨⟨-, hle⟩, -⟩; omega⟩
  rw [Finset.sum_filter]
  rw [Finset.sum_congr rfl (fun m _ => cz_pointwise_aux w y r t hw hy hr ht m)]
  simp only [Work.LinnikAreas.Density4.BzS3.s3G]
  rw [Finset.sum_filter, Finset.sum_filter]
  rw [← Finset.sum_filter, ← Finset.sum_filter, ← Finset.sum_filter]
  rw [← hsu]
  have key := Finset.sum_sdiff
    (s₁ := (Finset.Icc 1 (Work.ZeroDensity.Jutila.czLo w y r t)).filter
        (fun m => Nat.Coprime m (r * t) ∧ Squarefree m))
    (s₂ := (Finset.Icc 1 (Work.ZeroDensity.Jutila.czUp N q r t)).filter
        (fun m => Nat.Coprime m (r * t) ∧ Squarefree m)) hs
    (f := fun m => (Real.log (m : ℝ) - Work.ZeroDensity.Jutila.czAl w t) *
      (Real.log (m : ℝ) - Work.ZeroDensity.Jutila.czBe y r))
  linarith [key]

end Work.LinnikAreas2
