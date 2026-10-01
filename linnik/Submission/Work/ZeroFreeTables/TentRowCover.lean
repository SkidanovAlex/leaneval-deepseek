/-
# ZeroFreeTables — TentRowCover

`Work.ZeroFreeTables.TentRowCover`: the rows `tentRows` of the tent table cover the staircase
region `0 < λ₁ ≤ 797/10000`, `λ₂ < (12/11)·log(1/λ₁)`, `λ₂ ≤ 15344/1000`.

Write `b_i`, `c_i` for the second and third components of the `i`-th row (`i = 0,…,26`); the
table is ordered so that `b₀ > b₁ > … > b₂₆` and `c₀ < c₁ < … < c₂₆`.  A point `(λ₁, λ₂)` of the
region is covered by the row of index `k`, where `k` is the last index with `b_k ≥ λ₁` (such an
index exists because `λ₁ ≤ 797/10000 = b₀`): if `k = 26` then `c₂₆ = 15344/1000 ≥ λ₂` by the
truncation hypothesis; otherwise `b_{k+1} < λ₁`, so

`λ₂ < (12/11)·log(1/λ₁) < (12/11)·log(1/b_{k+1}) ≤ c_k`,

the last inequality being the chain condition `tentChain k` of the table.  The covering is
performed below by a `by_cases` waterfall on `λ₁ ≤ b_k`, `k = 26, 25, …, 1`, i.e. by an explicit
case analysis (the finitely many rows make this the shortest route), the final case being the row
`k = 0`, where `λ₁ ≤ b₀` comes from the hypothesis `λ₁ ≤ 797/10000`.

The chain conditions are the 26 transcendental comparisons `(12/11)·log(1/b_{i+1}) ≤ c_i`, each
with a rational slack of about `10⁻³`.  They are reduced to rational arithmetic by
`twelve_elevenths_log_inv_le`, which extracts `(12/11)·log(1/c) ≤ v` from the rational
inequality `1/c ≤ (∑_{i<10} ((11/12)·v/16)^i/i!)^{16}`: the right-hand side is the 16th power of
the ten-term Taylor polynomial of `exp((11/12)v/16)`, hence a lower bound for `exp((11/12)v)`,
and taking logarithms gives the claim.  The scaling by `16` keeps the Taylor relative error
below `10⁻⁶`, far under the `10⁻³` slack available in the chain; the resulting comparison is a
`norm_num` fact in exact rational arithmetic.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.HB88TentIf

open scoped Real BigOperators
noncomputable section

namespace Work.ZeroFreeTables

/-- **The `12/11` logarithm bound.**  If `0 < c`, `0 ≤ v` and the rational inequality
`1/c ≤ (∑_{i<10} ((11/12)·v/16)^i/i!)^{16}` holds, then `(12/11)·log (1/c) ≤ v`. -/
theorem twelve_elevenths_log_inv_le {c v : ℝ} (hc : 0 < c) (hv : 0 ≤ v)
    (h : 1 / c
      ≤ (∑ i ∈ Finset.range 10, (((11 : ℝ)/12) * v / 16) ^ i / ((i.factorial : ℕ) : ℝ)) ^ 16) :
    (12 / 11) * Real.log (1 / c) ≤ v := by
  have hT : (∑ i ∈ Finset.range 10, (((11 : ℝ)/12) * v / 16) ^ i / ((i.factorial : ℕ) : ℝ))
      ≤ Real.exp (((11 : ℝ)/12) * v / 16) := Real.sum_le_exp_of_nonneg (by positivity) 10
  have hexp : Real.exp (((11 : ℝ)/12) * v / 16) ^ 16 = Real.exp (((11 : ℝ)/12) * v) := by
    rw [← Real.exp_nat_mul]; ring_nf
  have hle : 1 / c ≤ Real.exp (((11 : ℝ)/12) * v) := by
    rw [← hexp]
    exact h.trans (pow_le_pow_left₀ (by positivity) hT 16)
  have h2 := Real.log_le_log (show (0 : ℝ) < 1 / c by positivity) hle
  rw [Real.log_exp] at h2
  linarith

/-! ## The 26 chain conditions of the table

Each `tentChain i` is the comparison `(12/11)·log(1/b_{i+1}) ≤ c_i` between the `b`-value of the
row `i+1` and the `c`-value of the row `i`.  All are instances of
`twelve_elevenths_log_inv_le` followed by `norm_num [Finset.sum_range_succ]`. -/

/-- Chain condition `(12/11)·log(1/b₁) ≤ c₀`. -/
lemma tentChain0 : (12 / 11) * Real.log (1 / ((74094301 : ℝ)/10^9)) ≤ ((2840 : ℝ)/1000) := by
  refine twelve_elevenths_log_inv_le (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ]

/-- Chain condition `(12/11)·log(1/b₂) ≤ c₁`. -/
lemma tentChain1 : (12 / 11) * Real.log (1 / ((68101912 : ℝ)/10^9)) ≤ ((2932 : ℝ)/1000) := by
  refine twelve_elevenths_log_inv_le (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ]

/-- Chain condition `(12/11)·log(1/b₃) ≤ c₂`. -/
lemma tentChain2 : (12 / 11) * Real.log (1 / ((61795999 : ℝ)/10^9)) ≤ ((3038 : ℝ)/1000) := by
  refine twelve_elevenths_log_inv_le (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ]

/-- Chain condition `(12/11)·log(1/b₄) ≤ c₃`. -/
lemma tentChain3 : (12 / 11) * Real.log (1 / ((55409734 : ℝ)/10^9)) ≤ ((3157 : ℝ)/1000) := by
  refine twelve_elevenths_log_inv_le (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ]

/-- Chain condition `(12/11)·log(1/b₅) ≤ c₄`. -/
lemma tentChain4 : (12 / 11) * Real.log (1 / ((48960081 : ℝ)/10^9)) ≤ ((3292 : ℝ)/1000) := by
  refine twelve_elevenths_log_inv_le (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ]

/-- Chain condition `(12/11)·log(1/b₆) ≤ c₅`. -/
lemma tentChain5 : (12 / 11) * Real.log (1 / ((42475267 : ℝ)/10^9)) ≤ ((3447 : ℝ)/1000) := by
  refine twelve_elevenths_log_inv_le (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ]

/-- Chain condition `(12/11)·log(1/b₇) ≤ c₆`. -/
lemma tentChain6 : (12 / 11) * Real.log (1 / ((36113688 : ℝ)/10^9)) ≤ ((3624 : ℝ)/1000) := by
  refine twelve_elevenths_log_inv_le (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ]

/-- Chain condition `(12/11)·log(1/b₈) ≤ c₇`. -/
lemma tentChain7 : (12 / 11) * Real.log (1 / ((30064306 : ℝ)/10^9)) ≤ ((3824 : ℝ)/1000) := by
  refine twelve_elevenths_log_inv_le (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ]

/-- Chain condition `(12/11)·log(1/b₉) ≤ c₈`. -/
lemma tentChain8 : (12 / 11) * Real.log (1 / ((24506098 : ℝ)/10^9)) ≤ ((4047 : ℝ)/1000) := by
  refine twelve_elevenths_log_inv_le (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ]

/-- Chain condition `(12/11)·log(1/b₁₀) ≤ c₉`. -/
lemma tentChain9 : (12 / 11) * Real.log (1 / ((19540814 : ℝ)/10^9)) ≤ ((4294 : ℝ)/1000) := by
  refine twelve_elevenths_log_inv_le (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ]

/-- Chain condition `(12/11)·log(1/b₁₁) ≤ c₁₀`. -/
lemma tentChain10 : (12 / 11) * Real.log (1 / ((15075767 : ℝ)/10^9)) ≤ ((4577 : ℝ)/1000) := by
  refine twelve_elevenths_log_inv_le (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ]

/-- Chain condition `(12/11)·log(1/b₁₂) ≤ c₁₁`. -/
lemma tentChain11 : (12 / 11) * Real.log (1 / ((11243108 : ℝ)/10^9)) ≤ ((4897 : ℝ)/1000) := by
  refine twelve_elevenths_log_inv_le (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ]

/-- Chain condition `(12/11)·log(1/b₁₃) ≤ c₁₂`. -/
lemma tentChain12 : (12 / 11) * Real.log (1 / ((8112629 : ℝ)/10^9)) ≤ ((5253 : ℝ)/1000) := by
  refine twelve_elevenths_log_inv_le (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ]

/-- Chain condition `(12/11)·log(1/b₁₄) ≤ c₁₃`. -/
lemma tentChain13 : (12 / 11) * Real.log (1 / ((5668958 : ℝ)/10^9)) ≤ ((5644 : ℝ)/1000) := by
  refine twelve_elevenths_log_inv_le (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ]

/-- Chain condition `(12/11)·log(1/b₁₅) ≤ c₁₄`. -/
lemma tentChain14 : (12 / 11) * Real.log (1 / ((3818746 : ℝ)/10^9)) ≤ ((6075 : ℝ)/1000) := by
  refine twelve_elevenths_log_inv_le (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ]

/-- Chain condition `(12/11)·log(1/b₁₆) ≤ c₁₅`. -/
lemma tentChain15 : (12 / 11) * Real.log (1 / ((2450410 : ℝ)/10^9)) ≤ ((6559 : ℝ)/1000) := by
  refine twelve_elevenths_log_inv_le (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ]

/-- Chain condition `(12/11)·log(1/b₁₇) ≤ c₁₆`. -/
lemma tentChain16 : (12 / 11) * Real.log (1 / ((1499186 : ℝ)/10^9)) ≤ ((7095 : ℝ)/1000) := by
  refine twelve_elevenths_log_inv_le (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ]

/-- Chain condition `(12/11)·log(1/b₁₈) ≤ c₁₇`. -/
lemma tentChain17 : (12 / 11) * Real.log (1 / ((876931 : ℝ)/10^9)) ≤ ((7680 : ℝ)/1000) := by
  refine twelve_elevenths_log_inv_le (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ]

/-- Chain condition `(12/11)·log(1/b₁₉) ≤ c₁₈`. -/
lemma tentChain18 : (12 / 11) * Real.log (1 / ((492221 : ℝ)/10^9)) ≤ ((8310 : ℝ)/1000) := by
  refine twelve_elevenths_log_inv_le (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ]

/-- Chain condition `(12/11)·log(1/b₂₀) ≤ c₁₉`. -/
lemma tentChain19 : (12 / 11) * Real.log (1 / ((266337 : ℝ)/10^9)) ≤ ((8980 : ℝ)/1000) := by
  refine twelve_elevenths_log_inv_le (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ]

/-- Chain condition `(12/11)·log(1/b₂₁) ≤ c₂₀`. -/
lemma tentChain20 : (12 / 11) * Real.log (1 / ((135902 : ℝ)/10^9)) ≤ ((9714 : ℝ)/1000) := by
  refine twelve_elevenths_log_inv_le (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ]

/-- Chain condition `(12/11)·log(1/b₂₂) ≤ c₂₁`. -/
lemma tentChain21 : (12 / 11) * Real.log (1 / ((65275 : ℝ)/10^9)) ≤ ((10514 : ℝ)/1000) := by
  refine twelve_elevenths_log_inv_le (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ]

/-- Chain condition `(12/11)·log(1/b₂₃) ≤ c₂₂`. -/
lemma tentChain22 : (12 / 11) * Real.log (1 / ((29593 : ℝ)/10^9)) ≤ ((11377 : ℝ)/1000) := by
  refine twelve_elevenths_log_inv_le (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ]

/-- Chain condition `(12/11)·log(1/b₂₄) ≤ c₂₃`. -/
lemma tentChain23 : (12 / 11) * Real.log (1 / ((12733 : ℝ)/10^9)) ≤ ((12297 : ℝ)/1000) := by
  refine twelve_elevenths_log_inv_le (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ]

/-- Chain condition `(12/11)·log(1/b₂₅) ≤ c₂₄`. -/
lemma tentChain24 : (12 / 11) * Real.log (1 / ((5224 : ℝ)/10^9)) ≤ ((13269 : ℝ)/1000) := by
  refine twelve_elevenths_log_inv_le (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ]

/-- Chain condition `(12/11)·log(1/b₂₆) ≤ c₂₅`. -/
lemma tentChain25 : (12 / 11) * Real.log (1 / ((2055 : ℝ)/10^9)) ≤ ((14287 : ℝ)/1000) := by
  refine twelve_elevenths_log_inv_le (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ]

/-! ## Membership of the individual rows

Each row of `tentRows` is exhibited as a member with its own lemma, so that the (somewhat
expensive) unfolding of the 27-element list happens once per row rather than once per branch of
the covering case analysis. -/

theorem tentMem0 : ((6/5 : ℝ), (79700000 : ℝ)/10^9, (2840 : ℝ)/1000) ∈ tentRows := by
  simp [tentRows]

theorem tentMem1 : ((6/5 : ℝ), (74094301 : ℝ)/10^9, (2932 : ℝ)/1000) ∈ tentRows := by
  simp [tentRows]

theorem tentMem2 : ((6/5 : ℝ), (68101912 : ℝ)/10^9, (3038 : ℝ)/1000) ∈ tentRows := by
  simp [tentRows]

theorem tentMem3 : ((6/5 : ℝ), (61795999 : ℝ)/10^9, (3157 : ℝ)/1000) ∈ tentRows := by
  simp [tentRows]

theorem tentMem4 : ((23/20 : ℝ), (55409734 : ℝ)/10^9, (3292 : ℝ)/1000) ∈ tentRows := by
  simp [tentRows]

theorem tentMem5 : ((23/20 : ℝ), (48960081 : ℝ)/10^9, (3447 : ℝ)/1000) ∈ tentRows := by
  simp [tentRows]

theorem tentMem6 : ((23/20 : ℝ), (42475267 : ℝ)/10^9, (3624 : ℝ)/1000) ∈ tentRows := by
  simp [tentRows]

theorem tentMem7 : ((23/20 : ℝ), (36113688 : ℝ)/10^9, (3824 : ℝ)/1000) ∈ tentRows := by
  simp [tentRows]

theorem tentMem8 : ((23/20 : ℝ), (30064306 : ℝ)/10^9, (4047 : ℝ)/1000) ∈ tentRows := by
  simp [tentRows]

theorem tentMem9 : ((11/10 : ℝ), (24506098 : ℝ)/10^9, (4294 : ℝ)/1000) ∈ tentRows := by
  simp [tentRows]

theorem tentMem10 : ((11/10 : ℝ), (19540814 : ℝ)/10^9, (4577 : ℝ)/1000) ∈ tentRows := by
  simp [tentRows]

theorem tentMem11 : ((11/10 : ℝ), (15075767 : ℝ)/10^9, (4897 : ℝ)/1000) ∈ tentRows := by
  simp [tentRows]

theorem tentMem12 : ((11/10 : ℝ), (11243108 : ℝ)/10^9, (5253 : ℝ)/1000) ∈ tentRows := by
  simp [tentRows]

theorem tentMem13 : ((11/10 : ℝ), (8112629 : ℝ)/10^9, (5644 : ℝ)/1000) ∈ tentRows := by
  simp [tentRows]

theorem tentMem14 : ((21/20 : ℝ), (5668958 : ℝ)/10^9, (6075 : ℝ)/1000) ∈ tentRows := by
  simp [tentRows]

theorem tentMem15 : ((21/20 : ℝ), (3818746 : ℝ)/10^9, (6559 : ℝ)/1000) ∈ tentRows := by
  simp [tentRows]

theorem tentMem16 : ((21/20 : ℝ), (2450410 : ℝ)/10^9, (7095 : ℝ)/1000) ∈ tentRows := by
  simp [tentRows]

theorem tentMem17 : ((21/20 : ℝ), (1499186 : ℝ)/10^9, (7680 : ℝ)/1000) ∈ tentRows := by
  simp [tentRows]

theorem tentMem18 : ((21/20 : ℝ), (876931 : ℝ)/10^9, (8310 : ℝ)/1000) ∈ tentRows := by
  simp [tentRows]

theorem tentMem19 : ((21/20 : ℝ), (492221 : ℝ)/10^9, (8980 : ℝ)/1000) ∈ tentRows := by
  simp [tentRows]

theorem tentMem20 : ((1 : ℝ), (266337 : ℝ)/10^9, (9714 : ℝ)/1000) ∈ tentRows := by
  simp [tentRows]

theorem tentMem21 : ((1 : ℝ), (135902 : ℝ)/10^9, (10514 : ℝ)/1000) ∈ tentRows := by
  simp [tentRows]

theorem tentMem22 : ((1 : ℝ), (65275 : ℝ)/10^9, (11377 : ℝ)/1000) ∈ tentRows := by
  simp [tentRows]

theorem tentMem23 : ((1 : ℝ), (29593 : ℝ)/10^9, (12297 : ℝ)/1000) ∈ tentRows := by
  simp [tentRows]

theorem tentMem24 : ((1 : ℝ), (12733 : ℝ)/10^9, (13269 : ℝ)/1000) ∈ tentRows := by
  simp [tentRows]

theorem tentMem25 : ((1 : ℝ), (5224 : ℝ)/10^9, (14287 : ℝ)/1000) ∈ tentRows := by
  simp [tentRows]

theorem tentMem26 : ((1 : ℝ), (2055 : ℝ)/10^9, (15344 : ℝ)/1000) ∈ tentRows := by
  simp [tentRows]

/-- **The covering step.**  If `0 < bn < λ₁` and `(12/11)·log (1/bn) ≤ c`, then every `λ₂` with
`λ₂ < (12/11)·log (1/λ₁)` satisfies `λ₂ ≤ c`: indeed `log (1/λ₁) ≤ log (1/bn)` because
`bn ≤ λ₁` and both are positive. -/
lemma tentStep {lam1 lam2 c bn : ℝ} (h1 : 0 < lam1) (hbn : 0 < bn) (hlb : bn < lam1)
    (hc : (12 / 11) * Real.log (1 / bn) ≤ c)
    (h3 : lam2 < (12 / 11) * Real.log (1 / lam1)) : lam2 ≤ c := by
  have hlog : Real.log (1 / lam1) ≤ Real.log (1 / bn) :=
    Real.log_le_log (by positivity) (one_div_le_one_div_of_le hbn hlb.le)
  have h2 : (12 / 11) * Real.log (1 / lam1) ≤ (12 / 11) * Real.log (1 / bn) :=
    mul_le_mul_of_nonneg_left hlog (by norm_num)
  linarith

theorem TentRowCover (lam1 lam2 : ℝ) (h1 : 0 < lam1) (h2 : lam1 ≤ 797 / 10000)
    (h3 : lam2 < (12 / 11) * Real.log (1 / lam1)) (h4 : lam2 ≤ 15344 / 1000) :
    ∃ p ∈ Work.ZeroFreeTables.tentRows, lam1 ≤ p.2.1 ∧ lam2 ≤ p.2.2 := by
  -- case `k = 26`: the last row, whose `c` is `15344/1000`
  by_cases hb26 : lam1 ≤ ((2055 : ℝ)/10^9)
  · exact ⟨((1 : ℝ), (2055 : ℝ)/10^9, (15344 : ℝ)/1000), tentMem26, hb26, h4⟩
  -- case `k = 25`
  by_cases hb25 : lam1 ≤ ((5224 : ℝ)/10^9)
  · refine ⟨((1 : ℝ), (5224 : ℝ)/10^9, (14287 : ℝ)/1000), tentMem25, hb25, ?_⟩
    exact tentStep h1 (by norm_num) (not_le.mp hb26) tentChain25 h3
  -- case `k = 24`
  by_cases hb24 : lam1 ≤ ((12733 : ℝ)/10^9)
  · refine ⟨((1 : ℝ), (12733 : ℝ)/10^9, (13269 : ℝ)/1000), tentMem24, hb24, ?_⟩
    exact tentStep h1 (by norm_num) (not_le.mp hb25) tentChain24 h3
  -- case `k = 23`
  by_cases hb23 : lam1 ≤ ((29593 : ℝ)/10^9)
  · refine ⟨((1 : ℝ), (29593 : ℝ)/10^9, (12297 : ℝ)/1000), tentMem23, hb23, ?_⟩
    exact tentStep h1 (by norm_num) (not_le.mp hb24) tentChain23 h3
  -- case `k = 22`
  by_cases hb22 : lam1 ≤ ((65275 : ℝ)/10^9)
  · refine ⟨((1 : ℝ), (65275 : ℝ)/10^9, (11377 : ℝ)/1000), tentMem22, hb22, ?_⟩
    exact tentStep h1 (by norm_num) (not_le.mp hb23) tentChain22 h3
  -- case `k = 21`
  by_cases hb21 : lam1 ≤ ((135902 : ℝ)/10^9)
  · refine ⟨((1 : ℝ), (135902 : ℝ)/10^9, (10514 : ℝ)/1000), tentMem21, hb21, ?_⟩
    exact tentStep h1 (by norm_num) (not_le.mp hb22) tentChain21 h3
  -- case `k = 20`
  by_cases hb20 : lam1 ≤ ((266337 : ℝ)/10^9)
  · refine ⟨((1 : ℝ), (266337 : ℝ)/10^9, (9714 : ℝ)/1000), tentMem20, hb20, ?_⟩
    exact tentStep h1 (by norm_num) (not_le.mp hb21) tentChain20 h3
  -- case `k = 19`
  by_cases hb19 : lam1 ≤ ((492221 : ℝ)/10^9)
  · refine ⟨((21/20 : ℝ), (492221 : ℝ)/10^9, (8980 : ℝ)/1000), tentMem19, hb19, ?_⟩
    exact tentStep h1 (by norm_num) (not_le.mp hb20) tentChain19 h3
  -- case `k = 18`
  by_cases hb18 : lam1 ≤ ((876931 : ℝ)/10^9)
  · refine ⟨((21/20 : ℝ), (876931 : ℝ)/10^9, (8310 : ℝ)/1000), tentMem18, hb18, ?_⟩
    exact tentStep h1 (by norm_num) (not_le.mp hb19) tentChain18 h3
  -- case `k = 17`
  by_cases hb17 : lam1 ≤ ((1499186 : ℝ)/10^9)
  · refine ⟨((21/20 : ℝ), (1499186 : ℝ)/10^9, (7680 : ℝ)/1000), tentMem17, hb17, ?_⟩
    exact tentStep h1 (by norm_num) (not_le.mp hb18) tentChain17 h3
  -- case `k = 16`
  by_cases hb16 : lam1 ≤ ((2450410 : ℝ)/10^9)
  · refine ⟨((21/20 : ℝ), (2450410 : ℝ)/10^9, (7095 : ℝ)/1000), tentMem16, hb16, ?_⟩
    exact tentStep h1 (by norm_num) (not_le.mp hb17) tentChain16 h3
  -- case `k = 15`
  by_cases hb15 : lam1 ≤ ((3818746 : ℝ)/10^9)
  · refine ⟨((21/20 : ℝ), (3818746 : ℝ)/10^9, (6559 : ℝ)/1000), tentMem15, hb15, ?_⟩
    exact tentStep h1 (by norm_num) (not_le.mp hb16) tentChain15 h3
  -- case `k = 14`
  by_cases hb14 : lam1 ≤ ((5668958 : ℝ)/10^9)
  · refine ⟨((21/20 : ℝ), (5668958 : ℝ)/10^9, (6075 : ℝ)/1000), tentMem14, hb14, ?_⟩
    exact tentStep h1 (by norm_num) (not_le.mp hb15) tentChain14 h3
  -- case `k = 13`
  by_cases hb13 : lam1 ≤ ((8112629 : ℝ)/10^9)
  · refine ⟨((11/10 : ℝ), (8112629 : ℝ)/10^9, (5644 : ℝ)/1000), tentMem13, hb13, ?_⟩
    exact tentStep h1 (by norm_num) (not_le.mp hb14) tentChain13 h3
  -- case `k = 12`
  by_cases hb12 : lam1 ≤ ((11243108 : ℝ)/10^9)
  · refine ⟨((11/10 : ℝ), (11243108 : ℝ)/10^9, (5253 : ℝ)/1000), tentMem12, hb12, ?_⟩
    exact tentStep h1 (by norm_num) (not_le.mp hb13) tentChain12 h3
  -- case `k = 11`
  by_cases hb11 : lam1 ≤ ((15075767 : ℝ)/10^9)
  · refine ⟨((11/10 : ℝ), (15075767 : ℝ)/10^9, (4897 : ℝ)/1000), tentMem11, hb11, ?_⟩
    exact tentStep h1 (by norm_num) (not_le.mp hb12) tentChain11 h3
  -- case `k = 10`
  by_cases hb10 : lam1 ≤ ((19540814 : ℝ)/10^9)
  · refine ⟨((11/10 : ℝ), (19540814 : ℝ)/10^9, (4577 : ℝ)/1000), tentMem10, hb10, ?_⟩
    exact tentStep h1 (by norm_num) (not_le.mp hb11) tentChain10 h3
  -- case `k = 9`
  by_cases hb9 : lam1 ≤ ((24506098 : ℝ)/10^9)
  · refine ⟨((11/10 : ℝ), (24506098 : ℝ)/10^9, (4294 : ℝ)/1000), tentMem9, hb9, ?_⟩
    exact tentStep h1 (by norm_num) (not_le.mp hb10) tentChain9 h3
  -- case `k = 8`
  by_cases hb8 : lam1 ≤ ((30064306 : ℝ)/10^9)
  · refine ⟨((23/20 : ℝ), (30064306 : ℝ)/10^9, (4047 : ℝ)/1000), tentMem8, hb8, ?_⟩
    exact tentStep h1 (by norm_num) (not_le.mp hb9) tentChain8 h3
  -- case `k = 7`
  by_cases hb7 : lam1 ≤ ((36113688 : ℝ)/10^9)
  · refine ⟨((23/20 : ℝ), (36113688 : ℝ)/10^9, (3824 : ℝ)/1000), tentMem7, hb7, ?_⟩
    exact tentStep h1 (by norm_num) (not_le.mp hb8) tentChain7 h3
  -- case `k = 6`
  by_cases hb6 : lam1 ≤ ((42475267 : ℝ)/10^9)
  · refine ⟨((23/20 : ℝ), (42475267 : ℝ)/10^9, (3624 : ℝ)/1000), tentMem6, hb6, ?_⟩
    exact tentStep h1 (by norm_num) (not_le.mp hb7) tentChain6 h3
  -- case `k = 5`
  by_cases hb5 : lam1 ≤ ((48960081 : ℝ)/10^9)
  · refine ⟨((23/20 : ℝ), (48960081 : ℝ)/10^9, (3447 : ℝ)/1000), tentMem5, hb5, ?_⟩
    exact tentStep h1 (by norm_num) (not_le.mp hb6) tentChain5 h3
  -- case `k = 4`
  by_cases hb4 : lam1 ≤ ((55409734 : ℝ)/10^9)
  · refine ⟨((23/20 : ℝ), (55409734 : ℝ)/10^9, (3292 : ℝ)/1000), tentMem4, hb4, ?_⟩
    exact tentStep h1 (by norm_num) (not_le.mp hb5) tentChain4 h3
  -- case `k = 3`
  by_cases hb3 : lam1 ≤ ((61795999 : ℝ)/10^9)
  · refine ⟨((6/5 : ℝ), (61795999 : ℝ)/10^9, (3157 : ℝ)/1000), tentMem3, hb3, ?_⟩
    exact tentStep h1 (by norm_num) (not_le.mp hb4) tentChain3 h3
  -- case `k = 2`
  by_cases hb2 : lam1 ≤ ((68101912 : ℝ)/10^9)
  · refine ⟨((6/5 : ℝ), (68101912 : ℝ)/10^9, (3038 : ℝ)/1000), tentMem2, hb2, ?_⟩
    exact tentStep h1 (by norm_num) (not_le.mp hb3) tentChain2 h3
  -- case `k = 1`
  by_cases hb1 : lam1 ≤ ((74094301 : ℝ)/10^9)
  · refine ⟨((6/5 : ℝ), (74094301 : ℝ)/10^9, (2932 : ℝ)/1000), tentMem1, hb1, ?_⟩
    exact tentStep h1 (by norm_num) (not_le.mp hb2) tentChain1 h3
  -- case `k = 0`: here `λ₁ ≤ 797/10000 = 79700000/10^9`
  refine ⟨((6/5 : ℝ), (79700000 : ℝ)/10^9, (2840 : ℝ)/1000), tentMem0, ?_, ?_⟩
  · linarith [h2]
  · exact tentStep h1 (by norm_num) (not_le.mp hb1) tentChain0 h3

end Work.ZeroFreeTables
