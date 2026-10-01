import Mathlib
import Submission.Work.LinnikAreas.Density4.LamRDefs
import Submission.Work.LinnikAreas.Density4.BzHard.S3_eq_quadruple
import Submission.Work.LinnikAreas.Density4.BzS3.S3InnerDefs
import Submission.Work.LinnikAreas.Density4.BzS3.S3RestrictedDefs

namespace Work.LinnikAreas.Density4.BzS3

open Finset

noncomputable section

/-- **Range reduction for a triple sum.**  If a summand `F q r t` vanishes whenever
`⌊N/z⌋ < q`, or `q ≤ ⌊N/z⌋` but `⌊N/(qz)⌋ < r`, or `r ≤ ⌊N/(qz)⌋` but `⌊N/(qz)⌋ < t`,
then the full triple sum over `1 ≤ q,r,t ≤ N` collapses to the restricted ranges
`q ≤ ⌊N/z⌋`, `r,t ≤ ⌊N/(qz)⌋`. -/
lemma sum_Icc_triple_reduce (F : ℕ → ℕ → ℕ → ℝ) (z N : ℕ)
    (hzero : ∀ q r t, 1 ≤ q → 1 ≤ r → 1 ≤ t →
      (N / z < q ∨ N / (q * z) < r ∨ N / (q * z) < t) → F q r t = 0) :
    (∑ q ∈ Finset.Icc 1 N, ∑ r ∈ Finset.Icc 1 N, ∑ t ∈ Finset.Icc 1 N, F q r t)
      = ∑ q ∈ Finset.Icc 1 (N / z), ∑ r ∈ Finset.Icc 1 (N / (q * z)),
          ∑ t ∈ Finset.Icc 1 (N / (q * z)), F q r t := by
  have hqzero : ∀ q ∈ Finset.Icc 1 N, q ∉ Finset.Icc 1 (N / z) →
      (∑ r ∈ Finset.Icc 1 N, ∑ t ∈ Finset.Icc 1 N, F q r t) = 0 := by
    intro q hq hqnot
    have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hq).1
    have hNq : N / z < q := not_le.mp fun h => hqnot (Finset.mem_Icc.mpr ⟨hq1, h⟩)
    refine Finset.sum_eq_zero fun r hr => Finset.sum_eq_zero fun t ht => ?_
    exact hzero q r t hq1 (Finset.mem_Icc.mp hr).1 (Finset.mem_Icc.mp ht).1 (Or.inl hNq)
  rw [(Finset.sum_subset (Finset.Icc_subset_Icc_right (Nat.div_le_self N z)) hqzero).symm]
  refine Finset.sum_congr rfl fun q hq => ?_
  have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hq).1
  have hrzero : ∀ r ∈ Finset.Icc 1 N, r ∉ Finset.Icc 1 (N / (q * z)) →
      (∑ t ∈ Finset.Icc 1 N, F q r t) = 0 := by
    intro r hr hrnot
    have hr1 : 1 ≤ r := (Finset.mem_Icc.mp hr).1
    have hNr : N / (q * z) < r := not_le.mp fun h => hrnot (Finset.mem_Icc.mpr ⟨hr1, h⟩)
    refine Finset.sum_eq_zero fun t ht => ?_
    exact hzero q r t hq1 hr1 (Finset.mem_Icc.mp ht).1 (Or.inr (Or.inl hNr))
  rw [(Finset.sum_subset (Finset.Icc_subset_Icc_right (Nat.div_le_self N (q * z))) hrzero).symm]
  refine Finset.sum_congr rfl fun r hr => ?_
  have hr1 : 1 ≤ r := (Finset.mem_Icc.mp hr).1
  refine (Finset.sum_subset (Finset.Icc_subset_Icc_right (Nat.div_le_self N (q * z)))
    (fun t ht htnot => ?_)).symm
  have ht1 : 1 ≤ t := (Finset.mem_Icc.mp ht).1
  have hNt : N / (q * z) < t := not_le.mp fun h => htnot (Finset.mem_Icc.mpr ⟨ht1, h⟩)
  exact hzero q r t hq1 hr1 ht1 (Or.inr (Or.inr hNt))

/-- **The restricted (double-sum) form of the reindexed `B_z`-square sum.**
For `2 ≤ z` and `N < z²`, `Σ_{n ≤ N} B_z(n)²` equals the sum over `1 ≤ q ≤ N/z` and
`1 ≤ r, t ≤ N/(qz)` of the multiplier `[r ⟂ t]·μ(r)·μ(t)` times the difference of the two inner
sums `s3G (r*t) (log(z/t)) (log(z/r))` at the cut-offs `⌊N/(qrt)⌋` and `max ⌊z/t⌋ ⌊z/r⌋`.

A reviewer checked this against `S3_eq_quadruple` (the exact quadruple form
`Σ_{q,r,t} muP(r,t)·Jq`): the terms with `q > N/z`, `r > N/(qz)`, `t > N/(qz)` vanish by
`Jq_eq_zero`, and on the restricted range `Jq_eq_Gd` identifies the inner `m`-sum with the
`s3G`-difference; numerically `Σ Bz²` agrees with the right-hand side for
`(z,N) = (2,3),(3,8),(4,15),(5,24),(6,35),(7,48)`.

Ingredients (all available in the workspace):
* `Work.LinnikAreas.Density4.BzHard.S3_eq_quadruple`;
* `Work.LinnikAreas.Density4.BzS3.S3RestrictedDefs` — the objects `muP`, `Jq`, `Gd` and the
  reindexing results `Jq_eq_Gd`, `Jq_eq_zero`, `inner_filter_eq`, `sum_filter_Icc_sub_Icc`,
  `log_mul_div_eq`;
* `Work.LinnikAreas.Density4.BzS3.S3InnerDefs` — the definitions of `s3G`, `s3main`, `s3c`;
* `Work.LinnikAreas.Density4.LamRDefs` — the definition of `Bz`.
The ranges come from `z < mt`, `z < mr`, `qrtm ≤ N`; the logarithms use
`log m − log(z/t) = log(mt/z)` and `log m − log(z/r) = log(mr/z)`. -/
theorem S3_eq_restricted (z N : ℕ) (hz : 2 ≤ z) (hN : N < z * z) :
    ∑ n ∈ Finset.Icc 1 N, Work.LinnikAreas.Density4.Bz z n ^ 2 =
      ∑ q ∈ Finset.Icc 1 (N / z), ∑ r ∈ Finset.Icc 1 (N / (q * z)),
        ∑ t ∈ Finset.Icc 1 (N / (q * z)),
          (if r.Coprime t then
            (ArithmeticFunction.moebius r : ℝ) * (ArithmeticFunction.moebius t : ℝ) else 0) *
          (Work.LinnikAreas.Density4.BzS3.s3G (r * t) (Real.log ((z : ℝ) / (t : ℝ)))
              (Real.log ((z : ℝ) / (r : ℝ))) (N / (q * r * t)) -
           Work.LinnikAreas.Density4.BzS3.s3G (r * t) (Real.log ((z : ℝ) / (t : ℝ)))
              (Real.log ((z : ℝ) / (r : ℝ))) (max (z / t) (z / r))) := by
  have hzpos : 0 < z := by omega
  rw [Work.LinnikAreas.Density4.BzHard.S3_eq_quadruple z N hz hN]
  -- Step 1: identify the quadruple summand with `muP r t * Jq z N q r t`.
  have hquad : (∑ q ∈ Finset.Icc 1 N, ∑ r ∈ Finset.Icc 1 N, ∑ t ∈ Finset.Icc 1 N,
      (if r.Coprime t then
          (ArithmeticFunction.moebius r : ℝ) * (ArithmeticFunction.moebius t : ℝ) else 0) *
        (∑ m ∈ Finset.Icc 1 N,
          if m.Coprime (r * t) ∧ Squarefree m ∧ z < t * m ∧ z < r * m
              ∧ q * r * t * m ≤ N
            then Real.log (((t * m : ℕ) : ℝ) / (z : ℝ))
                  * Real.log (((r * m : ℕ) : ℝ) / (z : ℝ))
            else 0))
      = ∑ q ∈ Finset.Icc 1 N, ∑ r ∈ Finset.Icc 1 N, ∑ t ∈ Finset.Icc 1 N,
          muP r t * Jq z N q r t := by
    refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun r _ =>
      Finset.sum_congr rfl fun t _ => ?_
    simp only [muP, Jq]
  rw [hquad]
  -- Step 2: the summand vanishes outside the restricted ranges.
  rw [sum_Icc_triple_reduce (fun q r t => muP r t * Jq z N q r t) z N ?_]
  · -- Step 3: on the restricted range, `Jq = Gd`, and both sides unfold to the same expression.
    refine Finset.sum_congr rfl fun q hq => Finset.sum_congr rfl fun r hr =>
      Finset.sum_congr rfl fun t ht => ?_
    obtain ⟨hq1, _⟩ := Finset.mem_Icc.mp hq
    obtain ⟨hr1, hrN⟩ := Finset.mem_Icc.mp hr
    obtain ⟨ht1, htN⟩ := Finset.mem_Icc.mp ht
    rw [Jq_eq_Gd z N q r t hzpos (by omega) (by omega) (by omega) hrN htN]
    simp only [muP, Gd]
  · -- vanishing of the summand outside the restricted ranges
    intro q r t hq1 hr1 ht1 h
    rw [Jq_eq_zero z N q r t hzpos hq1 hr1 ht1 h, mul_zero]

end

end Work.LinnikAreas.Density4.BzS3
