import Mathlib
import Submission.Work.ZeroDensity.Jutila.BzCross.BzCrossDefs
import Submission.Work.BzHard.Bz_sq_reindex
import Submission.Work.LinnikAreas2.cz_inner_eq_s3G
import Submission.Work.LinnikAreas2.cz_inner_filter_eq_empty
import Submission.Work.LinnikAreas2.czLo_le_czUp

namespace Work.ZeroDensity.Jutila.BzCross

/-!
# The exact reindexing of the two-sided `S₃` cross sum

This file proves `Work.ZeroDensity.Jutila.BzCross.Reindex`: for `1 ≤ w ≤ y ≤ N`,

  `Σ_{n ≤ N} Bz_w(n)·Bz_y(n) = czCross w y N`

(`czCross` as in `BzCrossDefs.lean`; `Bz_z(n) = Σ_{z < d ∣ n} μ(d)·log(d/z)` as in
`grahamDefs.lean`).

The proof splits into two independent halves:

* **the flat reindexing** `Σ_{2 ≤ n ≤ N} Bz_w(n)·Bz_y(n) = Σ_{q,r,t ≤ N} czE w y N q r t`
  (`czE` = the packaged inner `m`-sum).  It is obtained from the combinatorial bijection
  `Work.BzHard.Bz_reindex_aux` (applied at the cutoff `1`, with the real cutoffs `w`, `y` carried
  inside the summand), the coprimality condition `(gcd d e, cofactors) = 1` on the `e`-sum being
  harmless by `Work.BzHard.moebius_param_vanish`, and the multiplicativity
  `μ(mt)·μ(mr) = μ(r)·μ(t)·μ(m)²` for `(m, rt) = 1` (`Work.BzHard.moebius_param_mul`).
* **the range restriction** `Σ_{q,r,t ≤ N} czE w y N q r t = czCross w y N`: outside the ranges
  `q ≤ ⌊N/y⌋`, `r ≤ ⌊N/(qw)⌋`, `t ≤ ⌊N/(qy)⌋` the inner `m`-filter is empty
  (`cz_inner_filter_eq_empty`), and inside them the inner `m`-sum is the difference of two `s3G`
  values (`cz_inner_eq_s3G`, whose hypothesis `czLo ≤ czUp` is `czLo_le_czUp`).
-/

open Finset

noncomputable section

/-! ## Part 1: the flat reindexing -/

/-- The `(d,e)`-summand of the two-sided `Bz` product expansion: the `log(d/w)`-weighted Möbius
term when `d > w` and `e > y`, and `0` otherwise. -/
private def czZ (w y : ℝ) (d e : ℕ) : ℝ :=
  if w < (d : ℝ) ∧ y < (e : ℝ) then
    ((ArithmeticFunction.moebius d : ℝ) * Real.log ((d : ℝ) / w)) *
      ((ArithmeticFunction.moebius e : ℝ) * Real.log ((e : ℝ) / y))
  else 0

/-- The packaged inner `m`-sum of the reindexed cross sum, i.e. the `(q,r,t)`-summand of the flat
reindexing. -/
private def czE (w y : ℝ) (N q r t : ℕ) : ℝ :=
  if Nat.Coprime r t then
    (ArithmeticFunction.moebius r : ℝ) * (ArithmeticFunction.moebius t : ℝ) *
      (∑ m ∈ (Finset.Icc 1 (N / (q * r * t))).filter
          (fun m => Nat.Coprime m (r * t) ∧ w < ((m * t : ℕ) : ℝ)
            ∧ y < ((m * r : ℕ) : ℝ)),
        ((ArithmeticFunction.moebius m : ℝ)) ^ 2 *
          Real.log (((m * t : ℕ) : ℝ) / w) *
          Real.log (((m * r : ℕ) : ℝ) / y))
  else 0

/-- Multiplicativity of `μ` along the parametrisation `d = mt`, `e = mr`, with the two cutoffs
`log(·/w)` and `log(·/y)`: for `(m, rt) = 1`, `μ(mt)μ(mr) = μ(r)μ(t)μ(m)²`, and the logarithm
factors are carried along untouched. -/
private lemma czBz_weight_pt (w y : ℝ) {m r t : ℕ} (hcop : Nat.Coprime m (r * t)) :
    ((ArithmeticFunction.moebius (m * t) : ℝ) * Real.log (((m * t : ℕ) : ℝ) / w)) *
        ((ArithmeticFunction.moebius (m * r) : ℝ) * Real.log (((m * r : ℕ) : ℝ) / y))
      = (ArithmeticFunction.moebius r : ℝ) * (ArithmeticFunction.moebius t : ℝ) *
          (((ArithmeticFunction.moebius m : ℝ) ^ 2) *
            Real.log (((m * t : ℕ) : ℝ) / w) *
            Real.log (((m * r : ℕ) : ℝ) / y)) := by
  have h1 := Work.BzHard.moebius_param_mul hcop
  calc ((ArithmeticFunction.moebius (m * t) : ℝ) * Real.log (((m * t : ℕ) : ℝ) / w)) *
        ((ArithmeticFunction.moebius (m * r) : ℝ) * Real.log (((m * r : ℕ) : ℝ) / y))
      = ((ArithmeticFunction.moebius (m * t) : ℝ) * (ArithmeticFunction.moebius (m * r) : ℝ)) *
          (Real.log (((m * t : ℕ) : ℝ) / w) * Real.log (((m * r : ℕ) : ℝ) / y)) := by ring
    _ = ((ArithmeticFunction.moebius r : ℝ) * (ArithmeticFunction.moebius t : ℝ) *
          (ArithmeticFunction.moebius m : ℝ) ^ 2) *
          (Real.log (((m * t : ℕ) : ℝ) / w) * Real.log (((m * r : ℕ) : ℝ) / y)) := by rw [h1]
    _ = (ArithmeticFunction.moebius r : ℝ) * (ArithmeticFunction.moebius t : ℝ) *
          (((ArithmeticFunction.moebius m : ℝ) ^ 2) *
            Real.log (((m * t : ℕ) : ℝ) / w) *
            Real.log (((m * r : ℕ) : ℝ) / y)) := by ring

/-- The `czZ`-summand at the parametrised pair `(mt, mr)`, for `(m, rt) = 1`. -/
private lemma czZ_coprime (w y : ℝ) {m r t : ℕ} (hcop : Nat.Coprime m (r * t)) :
    czZ w y (m * t) (m * r)
      = if w < ((m * t : ℕ) : ℝ) ∧ y < ((m * r : ℕ) : ℝ) then
          (ArithmeticFunction.moebius r : ℝ) * (ArithmeticFunction.moebius t : ℝ) *
            (((ArithmeticFunction.moebius m : ℝ) ^ 2) *
              Real.log (((m * t : ℕ) : ℝ) / w) *
              Real.log (((m * r : ℕ) : ℝ) / y))
        else 0 := by
  unfold czZ
  by_cases h : w < ((m * t : ℕ) : ℝ) ∧ y < ((m * r : ℕ) : ℝ)
  · rw [if_pos h, if_pos h]
    exact czBz_weight_pt w y hcop
  · rw [if_neg h, if_neg h]

/-- If `w < mt` and `y < mr` with `1 ≤ w`, `1 ≤ y`, then `1 < mt` and `1 < mr`. -/
private lemma cz_one_lt_of (w y : ℝ) {m r t : ℕ} (hw : 1 ≤ w) (hy : 1 ≤ y)
    (h : w < ((m * t : ℕ) : ℝ) ∧ y < ((m * r : ℕ) : ℝ)) :
    1 < m * t ∧ 1 < m * r := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, ?_⟩
  · have : (1 : ℝ) < ((m * t : ℕ) : ℝ) := lt_of_le_of_lt hw h1
    exact_mod_cast this
  · have : (1 : ℝ) < ((m * r : ℕ) : ℝ) := lt_of_le_of_lt hy h2
    exact_mod_cast this

/-- **Expansion of the `Bz`-product.**  The product of the two `Bz` sums is the double sum over
the divisor pairs `(d,e)` of `czZ`. -/
private lemma czBz_product_expand (w y : ℝ) (n : ℕ) :
    Bz w n * Bz y n
      = ∑ d ∈ n.divisors, ∑ e ∈ n.divisors, czZ w y d e := by
  rw [Bz, Bz, Finset.sum_filter, Finset.sum_filter, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl (fun d _ => Finset.sum_congr rfl (fun e _ => ?_))
  unfold czZ
  by_cases hp : w < (d : ℝ) <;> by_cases hq : y < (e : ℝ) <;> simp [hp, hq]

/-- Summing over all divisors of `n > 0` may be restricted to the divisors `> 1` when the
summand vanishes at `e = 1` (here because `1 ≤ y`). -/
private lemma czZ_sum_divisors_filter_right (w y : ℝ) (hy : 1 ≤ y) {n : ℕ} (hn : 0 < n)
    (d : ℕ) :
    (∑ e ∈ n.divisors, czZ w y d e)
      = ∑ e ∈ n.divisors.filter (fun e => 1 < e), czZ w y d e := by
  refine (Finset.sum_subset (Finset.filter_subset _ _) (fun e he hnot => ?_)).symm
  have hele : e ≤ 1 := by
    by_contra h
    exact hnot (Finset.mem_filter.mpr ⟨he, by omega⟩)
  have he1 : 1 ≤ e := Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp he).1 hn
  have he_eq : e = 1 := le_antisymm hele he1
  unfold czZ
  rw [he_eq]
  simp only [Nat.cast_one]
  rw [if_neg (fun h => absurd h.2 (not_lt.mpr hy))]

/-- Summing over all divisors of `n > 0` may be restricted to the divisors `> 1` when the
summand vanishes at `d = 1` (here because `1 ≤ w`). -/
private lemma czZ_sum_divisors_filter_left (w y : ℝ) (hw : 1 ≤ w) {n : ℕ} (hn : 0 < n) :
    (∑ d ∈ n.divisors, ∑ e ∈ n.divisors, czZ w y d e)
      = ∑ d ∈ n.divisors.filter (fun d => 1 < d), ∑ e ∈ n.divisors, czZ w y d e := by
  refine (Finset.sum_subset (Finset.filter_subset _ _) (fun d hd hnot => ?_)).symm
  have hdle : d ≤ 1 := by
    by_contra h
    exact hnot (Finset.mem_filter.mpr ⟨hd, by omega⟩)
  have hd1 : 1 ≤ d := Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp hd).1 hn
  have hd_eq : d = 1 := le_antisymm hdle hd1
  refine Finset.sum_eq_zero (fun e _ => ?_)
  unfold czZ
  rw [hd_eq]
  simp only [Nat.cast_one]
  rw [if_neg (fun h => absurd h.1 (not_lt.mpr hw))]

/-- The double sum over `n.divisors × n.divisors` of `czZ` may be restricted to the divisors
`> 1`: since `1 ≤ w`, `1 ≤ y`, the summand vanishes whenever `d = 1` or `e = 1`. -/
private lemma czZ_sum_extend (w y : ℝ) (hw : 1 ≤ w) (hy : 1 ≤ y) {n : ℕ} (hn : 2 ≤ n) :
    (∑ d ∈ n.divisors, ∑ e ∈ n.divisors, czZ w y d e)
      = ∑ d ∈ n.divisors.filter (fun d => 1 < d),
          ∑ e ∈ n.divisors.filter (fun e => 1 < e), czZ w y d e := by
  rw [czZ_sum_divisors_filter_left w y hw (by omega : 0 < n)]
  exact Finset.sum_congr rfl
    (fun d _ => czZ_sum_divisors_filter_right w y hy (by omega : 0 < n) d)

/-- The coprimality condition `(gcd d e, cofactors) = 1` may be imposed on the `e`-sum: the terms
failing it vanish by `moebius_param_vanish`. -/
private lemma czZ_sum_cop (w y : ℝ) {s : Finset ℕ} (hs : ∀ e ∈ s, 1 ≤ e) {d : ℕ} (hd : 1 ≤ d) :
    (∑ e ∈ s.filter
        (fun e => Nat.Coprime (Nat.gcd d e) ((e / Nat.gcd d e) * (d / Nat.gcd d e))),
        czZ w y d e)
      = ∑ e ∈ s, czZ w y d e := by
  refine Finset.sum_subset (Finset.filter_subset _ _) (fun e he hne => ?_)
  have hnc : ¬ Nat.Coprime (Nat.gcd d e)
      ((e / Nat.gcd d e) * (d / Nat.gcd d e)) := fun hc =>
    hne (Finset.mem_filter.mpr ⟨he, hc⟩)
  unfold czZ
  by_cases h : w < (d : ℝ) ∧ y < (e : ℝ)
  · rw [if_pos h]
    rcases Work.BzHard.moebius_param_vanish hd (hs e he) hnc with h0 | h0
    · rw [h0]; ring
    · rw [h0]; ring
  · rw [if_neg h]

/-- **Pointwise comparison of the inner `m`-summands.**  For `(r,t) = 1`, the packaged `m`-summand
at the pair `(mt, mr)` equals `μ(r)μ(t)` times the `s3G`-summand `μ(m)²·log(mt/w)·log(mr/y)`, on
the range `w < mt ∧ y < mr` (the `1 < mt ∧ 1 < mr` range is the same, since `1 ≤ w`, `1 ≤ y`). -/
private lemma cz_m_summand (w y : ℝ) (hw : 1 ≤ w) (hy : 1 ≤ y) {m r t : ℕ} :
    (if Nat.Coprime m (r * t) ∧ 1 < m * t ∧ 1 < m * r then czZ w y (m * t) (m * r) else 0)
      = (ArithmeticFunction.moebius r : ℝ) * (ArithmeticFunction.moebius t : ℝ) *
          (if Nat.Coprime m (r * t) ∧ w < ((m * t : ℕ) : ℝ) ∧ y < ((m * r : ℕ) : ℝ)
            then ((ArithmeticFunction.moebius m : ℝ)) ^ 2 *
              Real.log (((m * t : ℕ) : ℝ) / w) * Real.log (((m * r : ℕ) : ℝ) / y) else 0) := by
  by_cases hc' : Nat.Coprime m (r * t)
  · by_cases hB : w < ((m * t : ℕ) : ℝ) ∧ y < ((m * r : ℕ) : ℝ)
    · have hB' : 1 < m * t ∧ 1 < m * r := cz_one_lt_of w y hw hy hB
      rw [if_pos ⟨hc', hB'⟩, czZ_coprime w y hc', if_pos hB, mul_ite, mul_zero,
        if_pos ⟨hc', hB⟩]
    · have hL : (if Nat.Coprime m (r * t) ∧ 1 < m * t ∧ 1 < m * r then
          czZ w y (m * t) (m * r) else 0) = 0 := by
        by_cases hQ : Nat.Coprime m (r * t) ∧ 1 < m * t ∧ 1 < m * r
        · rw [if_pos hQ, czZ_coprime w y hc', if_neg hB]
        · rw [if_neg hQ]
      have hR : (ArithmeticFunction.moebius r : ℝ) * (ArithmeticFunction.moebius t : ℝ) *
          (if Nat.Coprime m (r * t) ∧ w < ((m * t : ℕ) : ℝ) ∧ y < ((m * r : ℕ) : ℝ)
            then ((ArithmeticFunction.moebius m : ℝ)) ^ 2 *
              Real.log (((m * t : ℕ) : ℝ) / w) * Real.log (((m * r : ℕ) : ℝ) / y) else 0) = 0 := by
        rw [if_neg (fun hQ => hB hQ.2), mul_zero]
      rw [hL, hR]
  · have hL : (if Nat.Coprime m (r * t) ∧ 1 < m * t ∧ 1 < m * r then
        czZ w y (m * t) (m * r) else 0) = 0 := by
      rw [if_neg (fun hQ => hc' hQ.1)]
    have hR : (ArithmeticFunction.moebius r : ℝ) * (ArithmeticFunction.moebius t : ℝ) *
        (if Nat.Coprime m (r * t) ∧ w < ((m * t : ℕ) : ℝ) ∧ y < ((m * r : ℕ) : ℝ)
          then ((ArithmeticFunction.moebius m : ℝ)) ^ 2 *
            Real.log (((m * t : ℕ) : ℝ) / w) * Real.log (((m * r : ℕ) : ℝ) / y) else 0) = 0 := by
      rw [if_neg (fun hQ => hc' hQ.1), mul_zero]
    rw [hL, hR]

/-- **The flat reindexing of the two-sided cross sum.**  For `1 ≤ w`, `1 ≤ y`, the product sum
`Σ_{2 ≤ n ≤ N} Bz_w(n)·Bz_y(n)` equals the triple sum over `q, r, t ≤ N` of `[r ⟂ t]·μ(r)μ(t)`
times the inner sum over `m ≤ N/(qrt)` with `(m, rt) = 1`, `mt > w`, `mr > y` of
`μ(m)²·log(mt/w)·log(mr/y)`. -/
private lemma czBz_reindex_flat (w y : ℝ) (N : ℕ) (hw : 1 ≤ w) (hy : 1 ≤ y) :
    (∑ n ∈ Finset.Icc 2 N, Bz w n * Bz y n)
      = ∑ q ∈ Finset.Icc 1 N, ∑ r ∈ Finset.Icc 1 N, ∑ t ∈ Finset.Icc 1 N, czE w y N q r t := by
  have h1 : (∑ n ∈ Finset.Icc 2 N, Bz w n * Bz y n)
      = ∑ n ∈ Finset.Icc 2 N, ∑ d ∈ n.divisors, ∑ e ∈ n.divisors, czZ w y d e :=
    Finset.sum_congr rfl (fun n _ => czBz_product_expand w y n)
  have h2 : (∑ n ∈ Finset.Icc 2 N, ∑ d ∈ n.divisors, ∑ e ∈ n.divisors, czZ w y d e)
      = ∑ n ∈ Finset.Icc 2 N, ∑ d ∈ n.divisors.filter (fun d => 1 < d),
          ∑ e ∈ (n.divisors.filter (fun e => 1 < e)).filter
              (fun e => Nat.Coprime (Nat.gcd d e)
                ((e / Nat.gcd d e) * (d / Nat.gcd d e))), czZ w y d e := by
    refine Finset.sum_congr rfl (fun n hn => ?_)
    have hn2 : 2 ≤ n := (Finset.mem_Icc.mp hn).1
    rw [czZ_sum_extend w y hw hy hn2]
    refine Finset.sum_congr rfl (fun d hd => (czZ_sum_cop w y ?_ ?_).symm)
    · exact fun e he => le_of_lt (Finset.mem_filter.mp he).2
    · exact le_of_lt (Finset.mem_filter.mp hd).2
  have h3 : (∑ n ∈ Finset.Icc 2 N, ∑ d ∈ n.divisors.filter (fun d => 1 < d),
        ∑ e ∈ (n.divisors.filter (fun e => 1 < e)).filter
            (fun e => Nat.Coprime (Nat.gcd d e)
              ((e / Nat.gcd d e) * (d / Nat.gcd d e))), czZ w y d e)
      = ∑ q ∈ Finset.Icc 1 N, ∑ r ∈ Finset.Icc 1 N, ∑ t ∈ Finset.Icc 1 N,
          (if Nat.Coprime r t then
            ∑ m ∈ (Finset.Icc 1 (N / (q * r * t))).filter
                (fun m => Nat.Coprime m (r * t) ∧ 1 < m * t ∧ 1 < m * r),
              czZ w y (m * t) (m * r)
          else 0) :=
    Work.BzHard.Bz_reindex_aux 1 N (by norm_num) (czZ w y)
  have h4 : (∑ q ∈ Finset.Icc 1 N, ∑ r ∈ Finset.Icc 1 N, ∑ t ∈ Finset.Icc 1 N,
          (if Nat.Coprime r t then
            ∑ m ∈ (Finset.Icc 1 (N / (q * r * t))).filter
                (fun m => Nat.Coprime m (r * t) ∧ 1 < m * t ∧ 1 < m * r),
              czZ w y (m * t) (m * r)
          else 0))
      = ∑ q ∈ Finset.Icc 1 N, ∑ r ∈ Finset.Icc 1 N, ∑ t ∈ Finset.Icc 1 N, czE w y N q r t := by
    refine Finset.sum_congr rfl (fun q _ => Finset.sum_congr rfl (fun r _ =>
      Finset.sum_congr rfl (fun t _ => ?_)))
    by_cases hc : Nat.Coprime r t
    · have hsum : (∑ m ∈ (Finset.Icc 1 (N / (q * r * t))).filter
            (fun m => Nat.Coprime m (r * t) ∧ 1 < m * t ∧ 1 < m * r),
            czZ w y (m * t) (m * r))
          = (ArithmeticFunction.moebius r : ℝ) * (ArithmeticFunction.moebius t : ℝ) *
              (∑ m ∈ (Finset.Icc 1 (N / (q * r * t))).filter
                  (fun m => Nat.Coprime m (r * t) ∧ w < ((m * t : ℕ) : ℝ)
                    ∧ y < ((m * r : ℕ) : ℝ)),
                ((ArithmeticFunction.moebius m : ℝ)) ^ 2 *
                  Real.log (((m * t : ℕ) : ℝ) / w) *
                  Real.log (((m * r : ℕ) : ℝ) / y)) := by
        simp only [Finset.sum_filter, Finset.mul_sum]
        exact Finset.sum_congr rfl (fun m _ => cz_m_summand w y hw hy)
      rw [if_pos hc]
      unfold czE
      rw [if_pos hc, hsum]
    · rw [if_neg hc]
      unfold czE
      rw [if_neg hc]
  exact ((h1.trans h2).trans h3).trans h4

/-! ## Part 2: restriction to the ranges of `czCross` -/

/-- `⌊N/a⌋ ≤ N` for `a ≥ 1`. -/
private lemma czCut_le_N (a : ℝ) (N : ℕ) (ha : 1 ≤ a) : ⌊(N : ℝ) / a⌋₊ ≤ N := by
  have hle : (N : ℝ) / a ≤ (N : ℝ) := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < a)]
    nlinarith
  calc ⌊(N : ℝ) / a⌋₊ ≤ ⌊(N : ℝ)⌋₊ := Nat.floor_mono hle
    _ = N := Nat.floor_natCast N

/-- Truncating a sum over `Icc 1 M` at `K ≤ M` is legitimate when the summand vanishes on
`K < x ≤ M`. -/
private lemma sum_Icc_eq_of_eq_zero (M K : ℕ) (hKM : K ≤ M) (f : ℕ → ℝ)
    (hf : ∀ x, K < x → x ≤ M → f x = 0) :
    ∑ x ∈ Finset.Icc 1 M, f x = ∑ x ∈ Finset.Icc 1 K, f x := by
  refine (Finset.sum_subset ?_ ?_).symm
  · intro x hx
    simp only [Finset.mem_Icc] at hx ⊢
    exact ⟨hx.1, le_trans hx.2 hKM⟩
  · intro x hx hxs
    simp only [Finset.mem_Icc] at hx
    have hKx : K < x := by
      by_contra h
      exact hxs (by simp only [Finset.mem_Icc]; exact ⟨hx.1, by omega⟩)
    exact hf x hKx hx.2

/-- `czE` vanishes when the inner `m`-filter is empty. -/
private lemma czE_eq_zero_of_empty (w y : ℝ) (N q r t : ℕ)
    (hempty : (Finset.Icc 1 (N / (q * r * t))).filter
        (fun m => Nat.Coprime m (r * t) ∧ w < ((m * t : ℕ) : ℝ)
          ∧ y < ((m * r : ℕ) : ℝ)) = ∅) :
    czE w y N q r t = 0 := by
  unfold czE
  rw [hempty]
  simp

/-- **The range restriction.**  For `1 ≤ w`, `1 ≤ y`, the triple sum over the full box
`q, r, t ≤ N` of the packaged inner `m`-sum equals `czCross w y N`: outside the ranges
`q ≤ ⌊N/y⌋`, `r ≤ ⌊N/(qw)⌋`, `t ≤ ⌊N/(qy)⌋` the inner filter is empty, and inside them the inner
sum is the difference of the two `s3G` values. -/
private lemma czRestrict (w y : ℝ) (N : ℕ) (hw : 1 ≤ w) (hy : 1 ≤ y) :
    (∑ q ∈ Finset.Icc 1 N, ∑ r ∈ Finset.Icc 1 N, ∑ t ∈ Finset.Icc 1 N, czE w y N q r t)
      = czCross w y N := by
  -- Restriction of the `q`-range to `⌊N/y⌋`.
  have h3a : (∑ q ∈ Finset.Icc 1 N, ∑ r ∈ Finset.Icc 1 N, ∑ t ∈ Finset.Icc 1 N,
        czE w y N q r t)
      = ∑ q ∈ Finset.Icc 1 (czQ y N), ∑ r ∈ Finset.Icc 1 N, ∑ t ∈ Finset.Icc 1 N,
          czE w y N q r t := by
    refine sum_Icc_eq_of_eq_zero N (czQ y N) (czCut_le_N y N hy)
      (fun q => ∑ r ∈ Finset.Icc 1 N, ∑ t ∈ Finset.Icc 1 N, czE w y N q r t) ?_
    intro q hq hqN
    apply Finset.sum_eq_zero
    intro r hr
    apply Finset.sum_eq_zero
    intro t ht
    have hq1 : 1 ≤ q := Nat.succ_le_of_lt (lt_of_le_of_lt (Nat.zero_le _) hq)
    have hr1 : 1 ≤ r := (Finset.mem_Icc.mp hr).1
    have ht1 : 1 ≤ t := (Finset.mem_Icc.mp ht).1
    exact czE_eq_zero_of_empty w y N q r t
      (Work.LinnikAreas2.cz_inner_filter_eq_empty w y N q r t hw hy hq1 hr1 ht1 (Or.inl hq))
  -- Restriction of the `r`-range to `⌊N/(qw)⌋`.
  have h3b : (∑ q ∈ Finset.Icc 1 (czQ y N), ∑ r ∈ Finset.Icc 1 N, ∑ t ∈ Finset.Icc 1 N,
          czE w y N q r t)
      = ∑ q ∈ Finset.Icc 1 (czQ y N), ∑ r ∈ Finset.Icc 1 (czR w N q),
            ∑ t ∈ Finset.Icc 1 N, czE w y N q r t := by
    refine Finset.sum_congr rfl (fun q hq => ?_)
    have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hq).1
    have hX1N : czR w N q ≤ N := by
      have h1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq1
      exact czCut_le_N ((q : ℝ) * w) N (by nlinarith)
    refine sum_Icc_eq_of_eq_zero N (czR w N q) hX1N
      (fun r => ∑ t ∈ Finset.Icc 1 N, czE w y N q r t) ?_
    intro r hr hrN
    apply Finset.sum_eq_zero
    intro t ht
    have hr1 : 1 ≤ r := Nat.succ_le_of_lt (lt_of_le_of_lt (Nat.zero_le _) hr)
    have ht1 : 1 ≤ t := (Finset.mem_Icc.mp ht).1
    exact czE_eq_zero_of_empty w y N q r t
      (Work.LinnikAreas2.cz_inner_filter_eq_empty w y N q r t hw hy hq1 hr1 ht1
        (Or.inr (Or.inl hr)))
  -- Restriction of the `t`-range to `⌊N/(qy)⌋`.
  have h3c : (∑ q ∈ Finset.Icc 1 (czQ y N), ∑ r ∈ Finset.Icc 1 (czR w N q),
            ∑ t ∈ Finset.Icc 1 N, czE w y N q r t)
      = ∑ q ∈ Finset.Icc 1 (czQ y N), ∑ r ∈ Finset.Icc 1 (czR w N q),
            ∑ t ∈ Finset.Icc 1 (czT y N q), czE w y N q r t := by
    refine Finset.sum_congr rfl (fun q hq => ?_)
    refine Finset.sum_congr rfl (fun r hr => ?_)
    have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hq).1
    have hr1 : 1 ≤ r := (Finset.mem_Icc.mp hr).1
    have hX2N : czT y N q ≤ N := by
      have h1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq1
      exact czCut_le_N ((q : ℝ) * y) N (by nlinarith)
    refine sum_Icc_eq_of_eq_zero N (czT y N q) hX2N (fun t => czE w y N q r t) ?_
    intro t ht htN
    have ht1 : 1 ≤ t := Nat.succ_le_of_lt (lt_of_le_of_lt (Nat.zero_le _) ht)
    exact czE_eq_zero_of_empty w y N q r t
      (Work.LinnikAreas2.cz_inner_filter_eq_empty w y N q r t hw hy hq1 hr1 ht1
        (Or.inr (Or.inr ht)))
  -- On the restricted ranges the inner `m`-sum is the `s3G`-difference.
  have h4 : (∑ q ∈ Finset.Icc 1 (czQ y N), ∑ r ∈ Finset.Icc 1 (czR w N q),
            ∑ t ∈ Finset.Icc 1 (czT y N q), czE w y N q r t)
      = czCross w y N := by
    unfold czCross
    refine Finset.sum_congr rfl (fun q hq => Finset.sum_congr rfl (fun r hr =>
      Finset.sum_congr rfl (fun t ht => ?_)))
    have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hq).1
    have hr1 : 1 ≤ r := (Finset.mem_Icc.mp hr).1
    have ht1 : 1 ≤ t := (Finset.mem_Icc.mp ht).1
    by_cases hc : Nat.Coprime r t
    · have hinner := Work.LinnikAreas2.cz_inner_eq_s3G w y N q r t hw hy hr1 ht1
        (Work.LinnikAreas2.czLo_le_czUp w y N q r t hw hy hq1 hr ht)
      unfold czUp at hinner
      unfold czE
      rw [if_pos hc, czMM, if_pos hc]
      unfold czUp
      rw [hinner]
    · unfold czE
      rw [if_neg hc, czMM, if_neg hc, zero_mul]
  exact ((h3a.trans h3b).trans h3c).trans h4

/-! ## The target -/

/-- **Exact reindexing of the two-sided `S₃` cross sum.**  For `1 ≤ w ≤ y` and `y ≤ N`,
`Σ_{n ≤ N} Bz_w(n)·Bz_y(n) = czCross w y N`, with `czCross` as defined in
`Submission/Work/ZeroDensity/Jutila/BzCross/BzCrossDefs.lean`.

ROUTE (all ingredients are already in the workspace):
* the flat two-sided reindexing `Σ_{n≤N}Bz_w Bz_y = Σ_{q,r,t≤N} czG q r t` (`czG` = the packaged
  inner `m`-sum) is proved verbatim as `Work.LinnikAreas2.czBz_reindex`
  (`Submission/Work/LinnikAreas2/czBz_reindex.lean`, currently a `sorry`) — mirror its statement
  and prove it as in `Work.BzHard.Bz_sq_reindex`/`Bz_reindex_aux` with
  `F d e = μ d·log(d/w)·μ e·log(e/y)`, adding the coprimality filter on the `e`-sum (harmless by
  `Work.BzHard.moebius_param_vanish`) and using `Work.BzHard.moebius_param_mul`;
* the range restriction to `q ≤ ⌊N/y⌋`, `r ≤ ⌊N/(qw)⌋`, `t ≤ ⌊N/(qy)⌋` via the emptiness criterion
  `N < q·t·y ∨ N < q·r·w ⟹ inner m-filter empty`, PROVED as
  `Work.LinnikAreas2.cz_inner_filter_eq_empty`;
* `czLo w y r t ≤ czUp N q r t` on the restricted ranges, PROVED as
  `Work.LinnikAreas2.czLo_le_czUp`;
* the inner `m`-sum is `s3G (r*t) (czAl w t) (czBe y r) X` (since
  `log(mt/w) = log m − log(w/t)`), PROVED as `Work.LinnikAreas2.cz_inner_eq_s3G`;
* the assembly is written out (sorry-free apart from the single appeal to `czBz_reindex`) as
  `Work.LinnikAreas2.czCross_eq` (`Submission/Work/LinnikAreas2/czCross_eq.lean`): copy that proof
  and replace the appeal to `czBz_reindex` by your own proof of the flat reindexing. -/
theorem Reindex :
    ∀ (w y : ℝ) (N : ℕ), 1 ≤ w → w ≤ y → y ≤ (N : ℝ) →
      (∑ n ∈ Finset.Icc 1 N, Bz w n * Bz y n) = czCross w y N := by
  intro w y N hw hwy hyN
  have hy1 : 1 ≤ y := le_trans hw hwy
  -- The `n = 1` term vanishes, so the sum may start at `n = 2`.
  have hstep1 : (∑ n ∈ Finset.Icc 1 N, Bz w n * Bz y n)
      = ∑ n ∈ Finset.Icc 2 N, Bz w n * Bz y n := by
    refine (Finset.sum_subset ?_ ?_).symm
    · intro n hn
      simp only [Finset.mem_Icc] at hn ⊢
      omega
    · intro n hn hn2
      rw [Finset.mem_Icc] at hn
      have h2 : ¬ (2 ≤ n) := fun h => hn2 (Finset.mem_Icc.mpr ⟨h, hn.2⟩)
      have hn1 : n = 1 := by omega
      have hBw : Bz w 1 = 0 := Bz_eq_zero_of_le (z := w) (n := 1) (by linarith) (by simpa using hw)
      have hBy : Bz y 1 = 0 := Bz_eq_zero_of_le (z := y) (n := 1) (by linarith) (by simpa using hy1)
      rw [hn1, hBw, hBy, mul_zero]
  exact hstep1.trans ((czBz_reindex_flat w y N hw hy1).trans (czRestrict w y N hw hy1))

end

end Work.ZeroDensity.Jutila.BzCross
