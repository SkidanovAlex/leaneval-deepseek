import Mathlib
import Submission.Work.ZeroDensity.Jutila.grahamDefs
import Submission.Work.ZeroDensity.Jutila.BzCross.BzCrossDefs
import Submission.Work.BzHard.Bz_sq_reindex
import Submission.Work.BzHard.moebius_param_mul
import Submission.Work.BzHard.moebius_param_vanish

namespace Work.ZeroDensity.Jutila.LzAux

open Finset

noncomputable section

/-
Note.  The combinatorial core below (`czZ`, `czE`, `czBz_reindex_flat` and their auxiliary
lemmas) is the flat two-sided divisor reindexing `Σ_{2 ≤ n ≤ N} Bz_w(n)·Bz_y(n) = Σ_{q,r,t} czE`.
It is the exact statement needed for `CzBzReindexTwo`, and it is proved exactly as its one-sided
counterpart `Work.BzHard.Bz_sq_reindex` from `Work.BzHard.Bz_reindex_aux` at the cutoff `1`.
-/

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

/-- **Two-sided reindexing of the `Bz` cross product** (verbatim the statement of
`Work.LinnikAreas2.czBz_reindex`, whose file `Submission/Work/LinnikAreas2/czBz_reindex.lean`
also carries the suggested proof route): for real `1 ≤ w`, `1 ≤ y` and every `N`,
`Σ_{2 ≤ n ≤ N} Bz_w(n)·Bz_y(n)` equals the triple sum over `q, r, t ∈ [1,N]` of `[r ⟂ t]·μ(r)μ(t)`
times the inner `m`-sum over `m ≤ ⌊N/(qrt)⌋`, `(m,rt) = 1`, `mt > w`, `mr > y`, of
`μ(m)²·log(mt/w)·log(mr/y)`.

ROUTE. Expand each `Bz` over its divisors (`Bz w n = Σ_{d ∣ n, w < d} μ(d)·log(d/w)`), so the left
side becomes a sum over triples `(n,d,e)`; then reindex by
`Work.BzHard.Bz_reindex_aux 1 N (by norm_num)` (`Submission/Work/BzHard/Bz_sq_reindex.lean`,
sorry-free) applied to the arbitrary weight
`F d e = if w < (d:ℝ) ∧ y < (e:ℝ) then ((μ d:ℝ)*log((d:ℝ)/w))*((μ e:ℝ)*log((e:ℝ)/y)) else 0`
(the cut-off `z = 1` filters `1 < m*t`, `1 < m*r` are harmless because `w, y ≥ 1` force `F = 0`
there), and rewrite `μ(m·t)·μ(m·r) = μ(m)²·μ(r)·μ(t)` on the surviving terms using
`Work.BzHard.moebius_param_mul` / `moebius_param_vanish`. -/
theorem CzBzReindexTwo (w y : ℝ) (N : ℕ) (hw : 1 ≤ w) (hy : 1 ≤ y) :
    (∑ n ∈ Finset.Icc 2 N, Work.ZeroDensity.Jutila.Bz w n * Work.ZeroDensity.Jutila.Bz y n)
      = ∑ q ∈ Finset.Icc 1 N, ∑ r ∈ Finset.Icc 1 N, ∑ t ∈ Finset.Icc 1 N,
          (if Nat.Coprime r t then
            (ArithmeticFunction.moebius r : ℝ) * (ArithmeticFunction.moebius t : ℝ) *
              (∑ m ∈ (Finset.Icc 1 (N / (q * r * t))).filter
                  (fun m => Nat.Coprime m (r * t) ∧ w < ((m * t : ℕ) : ℝ)
                    ∧ y < ((m * r : ℕ) : ℝ)),
                ((ArithmeticFunction.moebius m : ℝ)) ^ 2 *
                  Real.log (((m * t : ℕ) : ℝ) / w) *
                  Real.log (((m * r : ℕ) : ℝ) / y))
          else 0) := by
  rw [czBz_reindex_flat w y N hw hy]
  refine Finset.sum_congr rfl (fun q _ => Finset.sum_congr rfl (fun r _ =>
    Finset.sum_congr rfl (fun t _ => ?_)))
  simp only [czE]

end

end Work.ZeroDensity.Jutila.LzAux
