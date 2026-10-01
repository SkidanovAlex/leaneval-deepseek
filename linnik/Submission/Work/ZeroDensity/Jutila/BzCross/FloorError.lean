import Mathlib
import Submission.Work.ZeroDensity.Jutila.BzCross.BzCrossDefs
import Submission.Work.LinnikAreas.JutilaPieces.S3FloorReduce
import Submission.Work.ZeroDensity.Jutila.BzCross.FloorPointwise
import Submission.Work.ZeroDensity.Jutila.BzCross.FloorSumLog
import Submission.Work.ZeroDensity.Jutila.BzCross.FloorInvSq
set_option autoImplicit false

namespace Work.ZeroDensity.Jutila.BzCross

open Finset

noncomputable section

/-! ### helpers -/

/-- the real cut-off `N/(qrt)`. -/
private def czX (N q r t : ℕ) : ℝ := (N : ℝ) / ((q : ℝ) * (r : ℝ) * (t : ℝ))

private lemma czUp_eq_floor (N q r t : ℕ) :
    (czUp N q r t : ℝ) = ((⌊czX N q r t⌋₊ : ℕ) : ℝ) := by
  rw [czUp, czX]
  rw [show (q : ℝ) * (r : ℝ) * (t : ℝ) = ((q * r * t : ℕ) : ℝ) by push_cast; ring]
  rw [Nat.floor_div_eq_div]

private lemma czLogAlpha (w : ℝ) (N q r t : ℕ) (hw : 0 < w) (hN : 1 ≤ N) (hq : 1 ≤ q)
    (hr : 1 ≤ r) (ht : 1 ≤ t) :
    Real.log (czX N q r t) - czAl w t
      = Real.log (((N : ℝ) / ((q : ℝ) * w)) / (r : ℝ)) := by
  have hq0 : (0:ℝ) < (q:ℝ) := by exact_mod_cast hq
  have hr0 : (0:ℝ) < (r:ℝ) := by exact_mod_cast hr
  have ht0 : (0:ℝ) < (t:ℝ) := by exact_mod_cast ht
  have hN0 : (0:ℝ) < (N:ℝ) := by exact_mod_cast hN
  have hX : (0:ℝ) < (N:ℝ) / ((q:ℝ) * (r:ℝ) * (t:ℝ)) := by positivity
  have hwt : (0:ℝ) < w / (t:ℝ) := by positivity
  rw [czX, czAl, ← Real.log_div (ne_of_gt hX) (ne_of_gt hwt)]
  congr 1
  field_simp

private lemma czLogBe (y : ℝ) (N q r t : ℕ) (hy : 0 < y) (hN : 1 ≤ N) (hq : 1 ≤ q)
    (hr : 1 ≤ r) (ht : 1 ≤ t) :
    Real.log (czX N q r t) - czBe y r
      = Real.log (((N : ℝ) / ((q : ℝ) * y)) / (t : ℝ)) := by
  have hq0 : (0:ℝ) < (q:ℝ) := by exact_mod_cast hq
  have hr0 : (0:ℝ) < (r:ℝ) := by exact_mod_cast hr
  have ht0 : (0:ℝ) < (t:ℝ) := by exact_mod_cast ht
  have hN0 : (0:ℝ) < (N:ℝ) := by exact_mod_cast hN
  have hX : (0:ℝ) < (N:ℝ) / ((q:ℝ) * (r:ℝ) * (t:ℝ)) := by positivity
  have hyr : (0:ℝ) < y / (r:ℝ) := by positivity
  rw [czX, czBe, ← Real.log_div (ne_of_gt hX) (ne_of_gt hyr)]
  congr 1
  field_simp

/-- the summand of the difference `czModelFloor − czModelCont`. -/
private def czFl (w y : ℝ) (N q r t : ℕ) : ℝ :=
  czMM r t * (czMain (r * t) (czAl w t) (czBe y r) ((⌊czX N q r t⌋₊ : ℕ) : ℝ)
    - czMain (r * t) (czAl w t) (czBe y r) (czX N q r t))

/-- **The floor error of the two-sided `S₃` model is `O(N)` in the hard range.**  With
`czModelFloor` (the model sum using `s3main` at the floor cut-off `⌊N/(qrt)⌋`) and `czModelCont`
(the same sum with the real cut-off `N/(qrt)`), for `1 ≤ w ≤ y` and `y ≤ N < w·y`,

  `|czModelFloor w y N − czModelCont w y N| ≤ C·N`.

ROUTE.  The one-sided (square-cut-off) analogue is FULLY PROVED as
`Work.LinnikAreas.JutilaPieces.S3FloorReduce` (`Submission/Work/LinnikAreas/JutilaPieces/S3FloorReduce.lean`,
together with its definitions in `JutilaPieces/S3FloorDefs.lean`), for
`2 ≤ z ≤ N < z²`: there the difference `s3exact − s3cont` is expanded as a sum of bracket terms
`kSD_sub` bounded by `|log(Y/(Y−1))|-type` quantities and summed by Abel summation
(`abel_identity`) against the harmonic-type sums.  The two-sided case is the same computation with
the two shifts `α = log(w/t)`, `β = log(y/r)`: the pointwise difference
`s3main c α β ⌊X⌋ − czMain c α β X` (with `X = N/(qrt)` real, `czMain` from
`BzCrossDefs`) is bounded by `(6/π²)·(C + |log X − α|·|log X − β| + |log X − α| + |log X − β|)`
times a factor `1 + (1/X)`, because `|⌊X⌋ − X| ≤ 1` and both `⌊X⌋`, `X ≥ 1`; the summation over
`q ≤ ⌊N/y⌋`, `r ≤ ⌊N/(qw)⌋`, `t ≤ ⌊N/(qy)⌋` is then identical in structure to the Abel-error
summation of `BzCross.AbelError`: the pair `(log(N/(qw)) − log r, log(N/(qy)) − log t)` matches the
`r`- and `t`-ranges, each pair-sum is `≪ (N/(q w))^{1/2}(N/(q y))^{1/2}`, and the total is
`≪ N^{3/2}/√(w y) ≤ N` because `N < w·y`. -/
theorem FloorError :
    ∃ C : ℝ, 0 < C ∧ ∀ (w y : ℝ) (N : ℕ), 1 ≤ w → w ≤ y → y ≤ (N : ℝ) → (N : ℝ) < w * y →
      |czModelFloor w y N - czModelCont w y N| ≤ C * (N : ℝ) := by
  refine ⟨200, by norm_num, ?_⟩
  intro w y N hw hwy hyN hNwy
  have hy1 : 1 ≤ y := le_trans hw hwy
  have hN1 : 1 ≤ N := by
    have h : (1:ℝ) ≤ (N:ℝ) := by
      have h2 : (1:ℝ) ≤ y := by exact_mod_cast hy1
      linarith
    exact_mod_cast h
  have hw0 : 0 < w := lt_of_lt_of_le zero_lt_one hw
  have hy0 : 0 < y := lt_of_lt_of_le zero_lt_one hy1
  have hN0 : (0:ℝ) < (N:ℝ) := by exact_mod_cast hN1
  have hfloor : czModelFloor w y N
      = ∑ q ∈ Finset.Icc 1 (czQ y N), ∑ r ∈ Finset.Icc 1 (czR w N q),
          ∑ t ∈ Finset.Icc 1 (czT y N q), czMM r t *
            czMain (r * t) (czAl w t) (czBe y r) (((⌊czX N q r t⌋₊ : ℕ)) : ℝ) := by
    unfold czModelFloor
    refine Finset.sum_congr rfl (fun q _ => Finset.sum_congr rfl (fun r _ =>
      Finset.sum_congr rfl (fun t _ => ?_)))
    rw [← czUp_eq_floor]
    rw [czMain_natCast]
  have hdiff : czModelFloor w y N - czModelCont w y N
      = ∑ q ∈ Finset.Icc 1 (czQ y N), ∑ r ∈ Finset.Icc 1 (czR w N q),
          ∑ t ∈ Finset.Icc 1 (czT y N q), czFl w y N q r t := by
    rw [hfloor]
    unfold czModelCont czFl
    simp only [czX]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun r _ => ?_)
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    ring
  have hperq : ∀ q ∈ Finset.Icc 1 (czQ y N),
      |∑ r ∈ Finset.Icc 1 (czR w N q), ∑ t ∈ Finset.Icc 1 (czT y N q), czFl w y N q r t|
        ≤ 54 * ((N : ℝ) / ((q : ℝ) * w)) * ((N : ℝ) / ((q : ℝ) * y)) := by
    intro q hq
    have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hq).1
    have hq0 : (0:ℝ) < (q:ℝ) := by exact_mod_cast hq1
    set U : ℝ := (N:ℝ)/((q:ℝ)*w) with hUdef
    set V : ℝ := (N:ℝ)/((q:ℝ)*y) with hVdef
    have hU0 : 0 < U := by rw [hUdef]; positivity
    have hV0 : 0 < V := by rw [hVdef]; positivity
    have hUR : (⌊U⌋₊ : ℕ) = czR w N q := by rw [hUdef]; simp only [czR]
    have hVT : (⌊V⌋₊ : ℕ) = czT y N q := by rw [hVdef]; simp only [czT]
    have hpt : ∀ r ∈ Finset.Icc 1 (czR w N q), ∀ t ∈ Finset.Icc 1 (czT y N q),
        |czFl w y N q r t| ≤ 6 * (Real.log (U / (r:ℝ)) + 1) * (Real.log (V / (t:ℝ)) + 1) := by
      intro r hr t ht
      obtain ⟨hr1, hrR⟩ := Finset.mem_Icc.mp hr
      obtain ⟨ht1, htT⟩ := Finset.mem_Icc.mp ht
      have hr0 : (0:ℝ) < (r:ℝ) := by exact_mod_cast hr1
      have ht0 : (0:ℝ) < (t:ℝ) := by exact_mod_cast ht1
      have hrU : (r:ℝ) ≤ U := by
        have h1 : ((r:ℝ)) ≤ ((czR w N q : ℕ) : ℝ) := by exact_mod_cast hrR
        have h2 : ((czR w N q : ℕ) : ℝ) ≤ U := by
          rw [hUdef]; simp only [czR]; exact Nat.floor_le (by positivity)
        linarith
      have htV : (t:ℝ) ≤ V := by
        have h1 : ((t:ℝ)) ≤ ((czT y N q : ℕ) : ℝ) := by exact_mod_cast htT
        have h2 : ((czT y N q : ℕ) : ℝ) ≤ V := by
          rw [hVdef]; simp only [czT]; exact Nat.floor_le (by positivity)
        linarith
      have hX1 : 1 ≤ czX N q r t := by
        rw [czX, one_le_div (by positivity)]
        have hUV : (r:ℝ) * (t:ℝ) ≤ U * V :=
          mul_le_mul hrU htV (le_of_lt ht0) (le_of_lt hU0)
        have hqUV : (q:ℝ) * ((r:ℝ)*(t:ℝ)) ≤ (q:ℝ) * (U*V) :=
          mul_le_mul_of_nonneg_left hUV (le_of_lt hq0)
        have hqUV2 : (q:ℝ) * (U*V) = (N:ℝ)^2 / ((q:ℝ)*w*y) := by
          rw [hUdef, hVdef] <;> field_simp <;> ring
        have hle : (N:ℝ)^2 / ((q:ℝ)*w*y) ≤ (N:ℝ) := by
          rw [div_le_iff₀ (by positivity)]
          have hqwy : (N:ℝ) ≤ (q:ℝ)*w*y := by
            have h3 : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq1
            nlinarith [hNwy, le_of_lt hw0, le_of_lt hy0, le_of_lt hN0]
          nlinarith [mul_le_mul_of_nonneg_left hqwy (le_of_lt hN0)]
        calc (q:ℝ)*(r:ℝ)*(t:ℝ) = (q:ℝ)*((r:ℝ)*(t:ℝ)) := by ring
          _ ≤ (q:ℝ)*(U*V) := hqUV
          _ = (N:ℝ)^2/((q:ℝ)*w*y) := hqUV2
          _ ≤ (N:ℝ) := hle
      have hu : 0 ≤ Real.log (czX N q r t) - czAl w t := by
        rw [czLogAlpha w N q r t hw0 hN1 hq1 hr1 ht1]
        apply Real.log_nonneg
        rw [one_le_div hr0]
        linarith
      have hv : 0 ≤ Real.log (czX N q r t) - czBe y r := by
        rw [czLogBe y N q r t hy0 hN1 hq1 hr1 ht1]
        apply Real.log_nonneg
        rw [one_le_div ht0]
        linarith
      have hpw := FloorPointwise (r*t) (czAl w t) (czBe y r) (czX N q r t) hX1 hu hv
      rw [czLogAlpha w N q r t hw0 hN1 hq1 hr1 ht1,
          czLogBe y N q r t hy0 hN1 hq1 hr1 ht1] at hpw
      have hmm : |czMM r t| ≤ 1 := by
        rw [czMM]
        split_ifs with hc
        · rw [abs_mul]
          have h1 : |((ArithmeticFunction.moebius r : ℤ) : ℝ)| ≤ 1 := by
            rw [← Int.cast_abs]; exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := r)
          have h2 : |((ArithmeticFunction.moebius t : ℤ) : ℝ)| ≤ 1 := by
            rw [← Int.cast_abs]; exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := t)
          calc |((ArithmeticFunction.moebius r : ℤ) : ℝ)| * |((ArithmeticFunction.moebius t : ℤ) : ℝ)|
              ≤ 1 * 1 := mul_le_mul h1 h2 (abs_nonneg _) (by norm_num)
            _ = 1 := by norm_num
        · simp
      rw [czFl, abs_mul]
      refine le_trans (mul_le_mul hmm hpw (abs_nonneg _) (by norm_num)) ?_
      rw [hUdef, hVdef] <;> simp
    calc |∑ r ∈ Finset.Icc 1 (czR w N q), ∑ t ∈ Finset.Icc 1 (czT y N q), czFl w y N q r t|
        ≤ ∑ r ∈ Finset.Icc 1 (czR w N q), |∑ t ∈ Finset.Icc 1 (czT y N q), czFl w y N q r t| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ r ∈ Finset.Icc 1 (czR w N q), ∑ t ∈ Finset.Icc 1 (czT y N q), |czFl w y N q r t| :=
          Finset.sum_le_sum (fun r _ => Finset.abs_sum_le_sum_abs _ _)
      _ ≤ ∑ r ∈ Finset.Icc 1 (czR w N q), ∑ t ∈ Finset.Icc 1 (czT y N q),
            6 * (Real.log (U/(r:ℝ)) + 1) * (Real.log (V/(t:ℝ)) + 1) :=
          Finset.sum_le_sum (fun r hr => Finset.sum_le_sum (fun t ht => hpt r hr t ht))
      _ = 6 * (∑ r ∈ Finset.Icc 1 (czR w N q), (Real.log (U/(r:ℝ)) + 1))
            * (∑ t ∈ Finset.Icc 1 (czT y N q), (Real.log (V/(t:ℝ)) + 1)) := by
          rw [← Finset.sum_mul_sum]
          rw [← Finset.mul_sum]
      _ ≤ 6 * (3 * ((czR w N q : ℕ) : ℝ)) * (3 * ((czT y N q : ℕ) : ℝ)) := by
          have h1 : (∑ r ∈ Finset.Icc 1 (czR w N q), (Real.log (U/(r:ℝ)) + 1))
              ≤ 3 * ((czR w N q : ℕ) : ℝ) := by
            have h := FloorSumLog U hU0
            rwa [hUR] at h
          have h2 : (∑ t ∈ Finset.Icc 1 (czT y N q), (Real.log (V/(t:ℝ)) + 1))
              ≤ 3 * ((czT y N q : ℕ) : ℝ) := by
            have h := FloorSumLog V hV0
            rwa [hVT] at h
          have hann : 0 ≤ ∑ r ∈ Finset.Icc 1 (czR w N q), (Real.log (U/(r:ℝ)) + 1) := by
            apply Finset.sum_nonneg
            intro r hr
            obtain ⟨hr1, hrR⟩ := Finset.mem_Icc.mp hr
            have hr0 : (0:ℝ) < (r:ℝ) := by exact_mod_cast hr1
            have hrU : (r:ℝ) ≤ U := by
              have h1 : ((r:ℝ)) ≤ ((czR w N q : ℕ) : ℝ) := by exact_mod_cast hrR
              have h2 : ((czR w N q : ℕ) : ℝ) ≤ U := by
                rw [hUdef]; simp only [czR]; exact Nat.floor_le (by positivity)
              linarith
            have h3 : 1 ≤ U / (r:ℝ) := (one_le_div hr0).mpr hrU
            have := Real.log_nonneg h3
            linarith
          have hbnn : 0 ≤ ∑ t ∈ Finset.Icc 1 (czT y N q), (Real.log (V/(t:ℝ)) + 1) := by
            apply Finset.sum_nonneg
            intro t ht'
            obtain ⟨ht1, htT⟩ := Finset.mem_Icc.mp ht'
            have ht0 : (0:ℝ) < (t:ℝ) := by exact_mod_cast ht1
            have htV : (t:ℝ) ≤ V := by
              have h1 : ((t:ℝ)) ≤ ((czT y N q : ℕ) : ℝ) := by exact_mod_cast htT
              have h2 : ((czT y N q : ℕ) : ℝ) ≤ V := by
                rw [hVdef]; simp only [czT]; exact Nat.floor_le (by positivity)
              linarith
            have h3 : 1 ≤ V / (t:ℝ) := (one_le_div ht0).mpr htV
            have := Real.log_nonneg h3
            linarith
          nlinarith [h1, h2, hann, hbnn, mul_le_mul h1 h2 hbnn (by positivity)]
      _ = 54 * ((czR w N q : ℕ) : ℝ) * ((czT y N q : ℕ) : ℝ) := by ring
      _ ≤ 54 * U * V := by
          have hR : ((czR w N q : ℕ):ℝ) ≤ U := by
            rw [hUdef]; simp only [czR]; exact Nat.floor_le (by positivity)
          have hT : ((czT y N q : ℕ):ℝ) ≤ V := by
            rw [hVdef]; simp only [czT]; exact Nat.floor_le (by positivity)
          have hR0 : (0:ℝ) ≤ ((czR w N q : ℕ):ℝ) := by positivity
          have hT0 : (0:ℝ) ≤ ((czT y N q : ℕ):ℝ) := by positivity
          nlinarith [hR, hT, hR0, hT0, mul_le_mul hR hT hT0 (le_of_lt hU0)]
      _ = 54 * ((N:ℝ)/((q:ℝ)*w)) * ((N:ℝ)/((q:ℝ)*y)) := by rw [hUdef, hVdef]
  have hfinal : |czModelFloor w y N - czModelCont w y N|
      ≤ ∑ q ∈ Finset.Icc 1 (czQ y N),
          54 * ((N:ℝ)/((q:ℝ)*w)) * ((N:ℝ)/((q:ℝ)*y)) := by
    rw [hdiff]
    exact le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum hperq)
  calc |czModelFloor w y N - czModelCont w y N|
      ≤ ∑ q ∈ Finset.Icc 1 (czQ y N),
          54 * ((N:ℝ)/((q:ℝ)*w)) * ((N:ℝ)/((q:ℝ)*y)) := hfinal
    _ = 54 * ((N:ℝ)^2/(w*y)) * (∑ q ∈ Finset.Icc 1 (czQ y N), 1/((q:ℝ)^2)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro q hq
        have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hq).1
        have hq0 : (q:ℝ) ≠ 0 := by positivity
        have hw0' : w ≠ 0 := ne_of_gt hw0
        have hy0' : y ≠ 0 := ne_of_gt hy0
        field_simp <;> ring
    _ ≤ 54 * ((N:ℝ)^2/(w*y)) * 2 := by
        have h := FloorInvSq (czQ y N)
        exact mul_le_mul_of_nonneg_left h (by positivity)
    _ ≤ 200 * (N:ℝ) := by
        have hN2 : (N:ℝ)^2/(w*y) ≤ (N:ℝ) := by
          rw [div_le_iff₀ (by positivity)]
          nlinarith [le_of_lt hNwy, le_of_lt hN0]
        nlinarith [hN2, le_of_lt hN0]

end
end Work.ZeroDensity.Jutila.BzCross

