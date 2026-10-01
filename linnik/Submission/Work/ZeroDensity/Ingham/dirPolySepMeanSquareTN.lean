import Mathlib
import Submission.Work.ZeroDensity.Ingham.dirPolySeparatedMVT
import Submission.Work.ZeroDensity.Montgomery.cpow_neg_sigma_add_it
import Submission.Work.ZeroDensity.Montgomery.norm_sq_cpow_neg_sigma
import Submission.Commons.Data.Finset.sum_Icc_eq_sum_log2_blocks

/-!
# The sharp `(T + n)` weighted mean square of a Dirichlet polynomial

The separated-points mean value theorem `Work.ZeroDensity.Ingham.dirPolySeparatedMVT` bounds

`Σ_{t ∈ S} ‖Σ_{n ≤ M} b n · n^{-it}‖² ≤ C (1/δ + log 2M) (T + M) Σ_{n ≤ M} ‖b n‖²`

for a `δ`-separated set `S ⊆ [-T,T]`; the truncation length `M` enters the weight.  To get the
per-coefficient weight `T + n` one splits `Icc 1 N` into the `Nat.log2`-fibers (the dyadic blocks
`{1}`, `(2^k, 2^{k+1}]`), applies the mean value theorem to each block with `δ = 1` (so the block
length `2^{k+1}-1 ≤ 2n` only costs a factor `2` against the weight `T + n`), and applies
Cauchy–Schwarz over the `Nat.log2 N + 1` blocks, which costs the factor
`(log₂N + 1) ≤ 4 log 2N`.  Altogether the loss is `≤ 200 (log 2N)^5`.
-/

set_option maxHeartbeats 1000000

namespace Work.ZeroDensity.Ingham

open scoped Classical BigOperators

noncomputable section

/-- The coefficients of the `k`-th dyadic block: `c n · n^{-σ}` if `Nat.log2 n = k` and `n ≤ N`,
and `0` otherwise. -/
private def blockCoef (N : ℕ) (σ : ℝ) (c : ℕ → ℂ) (k n : ℕ) : ℂ :=
  if Nat.log2 n = k ∧ n ≤ N then c n * (n : ℂ) ^ (-(σ : ℂ)) else 0

/-- The `k`-th block Dirichlet polynomial `t ↦ Σ_{n ∈ (2^k, 2^{k+1}]} c n · n^{-(σ+it)}`, written
as a sum over the full block `1 ≤ n ≤ 2^{k+1} - 1` with the coefficients killed off the fiber. -/
private def blockPoly (N : ℕ) (σ : ℝ) (c : ℕ → ℂ) (k : ℕ) (t : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 (2 ^ (k + 1) - 1),
    blockCoef N σ c k n * (n : ℂ) ^ (-((t : ℂ) * Complex.I))

/-- The fiber of `Icc 1 N` and the fiber of the truncated block `Icc 1 (2^{k+1}-1)` agree. -/
private lemma fiber_eq_block (N k : ℕ) :
    (Finset.Icc 1 (2 ^ (k + 1) - 1)).filter (fun n => Nat.log2 n = k ∧ n ≤ N)
      = (Finset.Icc 1 N).filter (fun n => Nat.log2 n = k) := by
  ext n
  simp only [Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨h1, _⟩, hlog, hle⟩
    exact ⟨⟨h1, hle⟩, hlog⟩
  · rintro ⟨⟨h1, hleN⟩, hlog⟩
    have hn0 : n ≠ 0 := by omega
    have hlt : n < 2 ^ (k + 1) := ((Nat.log2_eq_iff hn0).mp hlog).2
    exact ⟨⟨h1, by omega⟩, hlog, hleN⟩

/-- **Dyadic fiber identity**: the `k`-th `Nat.log2` fiber of `Σ_{n ≤ N} c n · n^{-(σ+it)}` is the
block polynomial `blockPoly`. -/
private lemma dzPoly (N : ℕ) (σ t : ℝ) (c : ℕ → ℂ) (k : ℕ) :
    (∑ n ∈ (Finset.Icc 1 N).filter (fun n => Nat.log2 n = k),
        c n * (n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I)))
      = blockPoly N σ c k t := by
  rw [blockPoly]
  have hR : (∑ n ∈ Finset.Icc 1 (2 ^ (k + 1) - 1),
        blockCoef N σ c k n * (n : ℂ) ^ (-((t : ℂ) * Complex.I)))
      = ∑ n ∈ (Finset.Icc 1 (2 ^ (k + 1) - 1)).filter (fun n => Nat.log2 n = k ∧ n ≤ N),
          c n * (n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I)) := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n hn
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    by_cases hcond : Nat.log2 n = k ∧ n ≤ N
    · rw [show blockCoef N σ c k n = c n * (n : ℂ) ^ (-(σ : ℂ)) from if_pos hcond,
        if_pos hcond]
      rw [Work.ZeroDensity.Montgomery.cpow_neg_sigma_add_it n hn1 σ t]
      ring
    · rw [show blockCoef N σ c k n = 0 from if_neg hcond, if_neg hcond]
      simp
  rw [hR, fiber_eq_block N k]

/-- **Dyadic fiber identity for the squares**: the sum of the squared norms of the block
coefficients over the truncated block is the sum of `‖c n‖² n^{-2σ}` over the fiber. -/
private lemma dzNormSq (N : ℕ) (σ : ℝ) (c : ℕ → ℂ) (k : ℕ) :
    (∑ n ∈ Finset.Icc 1 (2 ^ (k + 1) - 1), ‖blockCoef N σ c k n‖ ^ 2)
      = ∑ n ∈ (Finset.Icc 1 N).filter (fun n => Nat.log2 n = k),
          ‖c n‖ ^ 2 * (n : ℝ) ^ (-(2 * σ)) := by
  have hR : (∑ n ∈ Finset.Icc 1 (2 ^ (k + 1) - 1), ‖blockCoef N σ c k n‖ ^ 2)
      = ∑ n ∈ (Finset.Icc 1 (2 ^ (k + 1) - 1)).filter (fun n => Nat.log2 n = k ∧ n ≤ N),
          ‖c n‖ ^ 2 * (n : ℝ) ^ (-(2 * σ)) := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n hn
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    by_cases hcond : Nat.log2 n = k ∧ n ≤ N
    · rw [show blockCoef N σ c k n = c n * (n : ℂ) ^ (-(σ : ℂ)) from if_pos hcond,
        if_pos hcond]
      rw [norm_mul, mul_pow]
      rw [Work.ZeroDensity.Montgomery.norm_sq_cpow_neg_sigma n hn1 σ]
    · rw [show blockCoef N σ c k n = 0 from if_neg hcond, if_neg hcond]
      simp
  rw [hR, fiber_eq_block N k]

/-- **Dyadic weight comparison.**  If `n` lies in the block `k` then the block length
`2^{k+1} - 1` is at most `2n`, so `T + 2^{k+1} - 1 ≤ 2 (T + n)` for `T ≥ 0`. -/
private lemma dyadicWeightLe {T : ℝ} (hT : 0 ≤ T) (k n : ℕ) (hn0 : 0 < n)
    (hn : Nat.log2 n = k) :
    T + ((2 ^ (k + 1) - 1 : ℕ) : ℝ) ≤ 2 * (T + (n : ℝ)) := by
  have hne : n ≠ 0 := by omega
  have hle : 2 ^ k ≤ n := ((Nat.log2_eq_iff hne).mp hn).1
  have h2n : 2 ^ (k + 1) ≤ 2 * n := by
    have h2 : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; ring
    omega
  have hge1 : 1 ≤ 2 ^ (k + 1) := by
    calc (1 : ℕ) ≤ 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hcast2 : ((2 ^ (k + 1) - 1 : ℕ) : ℝ) ≤ ((2 ^ (k + 1) : ℕ) : ℝ) := by
    rw [Nat.cast_sub hge1, Nat.cast_one]
    linarith
  have hcast1 : ((2 ^ (k + 1) : ℕ) : ℝ) ≤ 2 * (n : ℝ) := by exact_mod_cast h2n
  linarith

/-- **Logarithmic bookkeeping.**  The number `Nat.log2 N + 1` of dyadic blocks and the factor
`1 + 2 log(2N)` are absorbed by `200 (log 2N)^5` (for `N ≥ 1` one has `log 2N ≥ 0.6`). -/
private lemma log2BlocksLogBound (N : ℕ) (hN : 1 ≤ N) :
    ((Nat.log2 N : ℝ) + 1) * (1 + 2 * Real.log (2 * (N : ℝ))) * 2
      ≤ 200 * (Real.log (2 * (N : ℝ))) ^ 5 := by
  have hNne : N ≠ 0 := by omega
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hlog2pos : (0 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hLge : (0.6 : ℝ) ≤ Real.log (2 * (N : ℝ)) := by
    have h1 : Real.log 2 ≤ Real.log (2 * (N : ℝ)) :=
      Real.log_le_log (by norm_num) (by linarith)
    linarith [Real.log_two_gt_d9]
  have hL0 : (0 : ℝ) ≤ Real.log (2 * (N : ℝ)) := le_of_lt (lt_of_lt_of_le (by norm_num) hLge)
  have hpow : 2 ^ Nat.log2 N ≤ N := (Nat.le_log2 hNne).mp le_rfl
  have hpowR : ((2 : ℝ)) ^ (Nat.log2 N) ≤ (N : ℝ) := by exact_mod_cast hpow
  have hlog1 : (Nat.log2 N : ℝ) * Real.log 2 ≤ Real.log (N : ℝ) := by
    have h := Real.log_le_log (by positivity : (0 : ℝ) < (2 : ℝ) ^ (Nat.log2 N)) hpowR
    rwa [Real.log_pow] at h
  have hlog2N : (Nat.log2 N : ℝ) ≤ 2 * Real.log (2 * (N : ℝ)) := by
    have h1 : (Nat.log2 N : ℝ) * Real.log 2 ≤ Real.log (2 * (N : ℝ)) := by
      refine hlog1.trans ?_
      exact Real.log_le_log (by positivity) (by linarith)
    have h2 : (Nat.log2 N : ℝ) ≤ Real.log (2 * (N : ℝ)) / Real.log 2 := by
      rw [le_div_iff₀ hlog2pos]
      exact h1
    have h3 : Real.log (2 * (N : ℝ)) / Real.log 2 ≤ 2 * Real.log (2 * (N : ℝ)) := by
      rw [div_le_iff₀ hlog2pos]
      nlinarith [Real.log_two_gt_d9, hL0]
    exact h2.trans h3
  have hA : (Nat.log2 N : ℝ) + 1 ≤ 4 * Real.log (2 * (N : ℝ)) := by
    have h1 : (1 : ℝ) ≤ 2 * Real.log (2 * (N : ℝ)) := by linarith
    linarith
  have hB : 1 + 2 * Real.log (2 * (N : ℝ)) ≤ 4 * Real.log (2 * (N : ℝ)) := by
    have h1 : (1 : ℝ) ≤ 2 * Real.log (2 * (N : ℝ)) := by linarith
    linarith
  have h4L : (0 : ℝ) ≤ 4 * Real.log (2 * (N : ℝ)) := by linarith
  have hkey : ((Nat.log2 N : ℝ) + 1) * (1 + 2 * Real.log (2 * (N : ℝ)))
      ≤ (4 * Real.log (2 * (N : ℝ))) * (4 * Real.log (2 * (N : ℝ))) :=
    mul_le_mul hA hB (by linarith) h4L
  have hL2 : (0.36 : ℝ) ≤ (Real.log (2 * (N : ℝ))) ^ 2 := by nlinarith [hLge]
  have hL3 : (0.216 : ℝ) ≤ (Real.log (2 * (N : ℝ))) ^ 3 := by
    have h := mul_le_mul hLge hL2 (by norm_num) (by linarith)
    nlinarith [h]
  have h32 : (32 : ℝ) ≤ 200 * (Real.log (2 * (N : ℝ))) ^ 3 := by nlinarith [hL3]
  have hfin : (4 * Real.log (2 * (N : ℝ))) * (4 * Real.log (2 * (N : ℝ))) * 2
      ≤ 200 * (Real.log (2 * (N : ℝ))) ^ 5 := by
    have hsq : (0 : ℝ) ≤ (Real.log (2 * (N : ℝ))) ^ 2 := sq_nonneg _
    calc (4 * Real.log (2 * (N : ℝ))) * (4 * Real.log (2 * (N : ℝ))) * 2
        = 32 * (Real.log (2 * (N : ℝ))) ^ 2 := by ring
      _ ≤ (200 * (Real.log (2 * (N : ℝ))) ^ 3) * (Real.log (2 * (N : ℝ))) ^ 2 :=
          mul_le_mul_of_nonneg_right h32 hsq
      _ = 200 * (Real.log (2 * (N : ℝ))) ^ 5 := by ring
  exact (mul_le_mul_of_nonneg_right hkey (by norm_num)).trans hfin

/-- **Cauchy–Schwarz over the blocks.** -/
private lemma blocksCS (L : ℕ) (v : ℕ → ℂ) :
    ‖∑ k ∈ Finset.range L, v k‖ ^ 2 ≤ (L : ℝ) * ∑ k ∈ Finset.range L, ‖v k‖ ^ 2 := by
  have h1 : ‖∑ k ∈ Finset.range L, v k‖ ≤ ∑ k ∈ Finset.range L, ‖v k‖ := norm_sum_le _ _
  have h2 : (∑ k ∈ Finset.range L, ‖v k‖) ^ 2
      ≤ ((L : ℕ) : ℝ) * ∑ k ∈ Finset.range L, ‖v k‖ ^ 2 := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range L) (fun _ : ℕ => (1 : ℝ))
      (fun k => ‖v k‖)
    simpa [Finset.sum_const, Finset.card_range, nsmul_eq_mul] using h
  calc ‖∑ k ∈ Finset.range L, v k‖ ^ 2 ≤ (∑ k ∈ Finset.range L, ‖v k‖) ^ 2 := by
        have hnn1 : (0 : ℝ) ≤ ‖∑ k ∈ Finset.range L, v k‖ := norm_nonneg _
        have hnn2 : (0 : ℝ) ≤ ∑ k ∈ Finset.range L, ‖v k‖ :=
          Finset.sum_nonneg (fun k _ => norm_nonneg _)
        exact sq_le_sq' (by linarith) h1
    _ ≤ (L : ℝ) * ∑ k ∈ Finset.range L, ‖v k‖ ^ 2 := h2

/-- Mean square of a Dirichlet polynomial at a fixed real part with the sharp `(T+n)` weight: there is an absolute `C > 0` such that for all `N ≥ 1`, `σ ≥ 1/2`, `T ≥ 2`, all coefficients `c : ℕ → ℂ` and every `S : Finset ℝ` with `|t| ≤ T` for all `t ∈ S` and pairwise `≥ 1` separated points, `Σ_{t ∈ S} ‖Σ_{n ≤ N} c n · n^{-(σ+it)}‖² ≤ C (log 2N)^5 Σ_{n ≤ N} ‖c n‖² n^{-2σ} (T + n)`. This is the statement of the (unproved, do-not-use) `Work.ZeroDensity.Ingham.dirPolyMVTSep`; it should be derived from the *proved* `Work.ZeroDensity.Ingham.dirPolySeparatedMVT` (`Σ_{t∈S}‖Σ_{n≤N} b n n^{-it}‖² ≤ C'(1/δ+log 2N)(T+N)Σ‖b n‖²`) by splitting `Icc 1 N` into the dyadic blocks `{1}`, `(2^{k-1}, 2^k]`, applying it to each block with coefficients `b n = c n n^{-σ}` and δ = 1 (using `T + 2^k ≤ 2(T+n)` for `n ∈ (2^{k-1},2^k]`), and Cauchy–Schwarz over the `≲ log(2N)` blocks. -/
theorem dirPolySepMeanSquareTN : ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (σ T : ℝ) (c : ℕ → ℂ) (S : Finset ℝ),
    1 ≤ N → 1 / 2 ≤ σ → 2 ≤ T →
    (∀ t ∈ S, |t| ≤ T) →
    (∀ t ∈ S, ∀ t' ∈ S, t ≠ t' → 1 ≤ |t - t'|) →
    (∑ t ∈ S, ‖∑ n ∈ Finset.Icc 1 N, c n * (n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))‖ ^ 2)
      ≤ C * (Real.log (2 * (N : ℝ))) ^ 5 *
          (∑ n ∈ Finset.Icc 1 N, ‖c n‖ ^ 2 * (n : ℝ) ^ (-(2 * σ)) * (T + (n : ℝ))) := by
  obtain ⟨C₀, hC₀pos, hMVT⟩ := dirPolySeparatedMVT
  refine ⟨200 * C₀, by positivity, ?_⟩
  intro N σ T c S hN _hσ hT hSb hSsep
  have hT0 : (0 : ℝ) ≤ T := by linarith
  have hNne : N ≠ 0 := by omega
  have hbd : ∀ t ∈ S, -T ≤ t ∧ t ≤ T := fun t ht => abs_le.mp (hSb t ht)
  have hperk : ∀ k ∈ Finset.range (Nat.log2 N + 1),
      (∑ t ∈ S, ‖blockPoly N σ c k t‖ ^ 2)
        ≤ C₀ * (1 + 2 * Real.log (2 * (N : ℝ))) * 2 *
            (∑ n ∈ (Finset.Icc 1 N).filter (fun n => Nat.log2 n = k),
              ‖c n‖ ^ 2 * (n : ℝ) ^ (-(2 * σ)) * (T + (n : ℝ))) := by
    intro k hk
    have hk_le : k ≤ Nat.log2 N := by
      have := Finset.mem_range.mp hk
      omega
    have hMk1 : 1 ≤ 2 ^ (k + 1) - 1 := by
      have h2 : (2 : ℕ) ≤ 2 ^ (k + 1) := by
        calc (2 : ℕ) = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have hMVTk := hMVT T 1 (by linarith) (by norm_num) (2 ^ (k + 1) - 1) hMk1
      (blockCoef N σ c k) S hbd (fun t ht t' ht' hne => hSsep t ht t' ht' hne)
    rw [dzNormSq N σ c k] at hMVTk
    set Fib : ℝ := ∑ n ∈ (Finset.Icc 1 N).filter (fun n => Nat.log2 n = k),
        ‖c n‖ ^ 2 * (n : ℝ) ^ (-(2 * σ)) with hFibdef
    set FibW : ℝ := ∑ n ∈ (Finset.Icc 1 N).filter (fun n => Nat.log2 n = k),
        ‖c n‖ ^ 2 * (n : ℝ) ^ (-(2 * σ)) * (T + (n : ℝ)) with hFibWdef
    have hFibnn : 0 ≤ Fib := by
      rw [hFibdef]
      apply Finset.sum_nonneg
      intro n hn
      have h1 : (0 : ℝ) ≤ (n : ℝ) ^ (-(2 * σ)) := Real.rpow_nonneg (by positivity) _
      positivity
    have hlogb : (1 : ℝ) / 1 + Real.log (2 * ((2 ^ (k + 1) - 1 : ℕ) : ℝ))
        ≤ 1 + 2 * Real.log (2 * (N : ℝ)) := by
      have h2N : ((2 ^ (k + 1) - 1 : ℕ) : ℝ) ≤ 2 * (N : ℝ) := by
        have h2n : 2 ^ (k + 1) ≤ 2 * N := by
          have h3 : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; ring
          have hpowk : 2 ^ k ≤ N := (Nat.le_log2 hNne).mp hk_le
          omega
        have hge1 : 1 ≤ 2 ^ (k + 1) := by
          calc (1 : ℕ) ≤ 2 ^ 1 := by norm_num
            _ ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
        calc ((2 ^ (k + 1) - 1 : ℕ) : ℝ) ≤ ((2 ^ (k + 1) : ℕ) : ℝ) := by
              rw [Nat.cast_sub hge1, Nat.cast_one]
              linarith
          _ ≤ 2 * (N : ℝ) := by exact_mod_cast h2n
      have hsplit : Real.log (2 * (2 * (N : ℝ))) = Real.log 2 + Real.log (2 * (N : ℝ)) := by
        rw [Real.log_mul (by norm_num) (by positivity)]
      have hlogm : Real.log (2 * ((2 ^ (k + 1) - 1 : ℕ) : ℝ))
          ≤ Real.log (2 * (2 * (N : ℝ))) := by
        apply Real.log_le_log (by positivity)
        linarith
      rw [hsplit] at hlogm
      have hN1R : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
      have hlog2le : Real.log 2 ≤ Real.log (2 * (N : ℝ)) :=
        Real.log_le_log (by norm_num) (by linarith)
      have h11 : (1 : ℝ) / 1 = 1 := by norm_num
      rw [h11]
      linarith
    have hW : (T + ((2 ^ (k + 1) - 1 : ℕ) : ℝ)) * Fib ≤ 2 * FibW := by
      rw [hFibdef, hFibWdef, Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro n hn
      have hn1 : n ∈ Finset.Icc 1 N := (Finset.mem_filter.mp hn).1
      have hlog : Nat.log2 n = k := (Finset.mem_filter.mp hn).2
      have hn0 : 0 < n := (Finset.mem_Icc.mp hn1).1
      have hw := dyadicWeightLe hT0 k n hn0 hlog
      have hfn : (0 : ℝ) ≤ ‖c n‖ ^ 2 * (n : ℝ) ^ (-(2 * σ)) := by
        have h1 : (0 : ℝ) ≤ (n : ℝ) ^ (-(2 * σ)) := Real.rpow_nonneg (by positivity) _
        positivity
      calc (T + ((2 ^ (k + 1) - 1 : ℕ) : ℝ)) * (‖c n‖ ^ 2 * (n : ℝ) ^ (-(2 * σ)))
          = (‖c n‖ ^ 2 * (n : ℝ) ^ (-(2 * σ))) * (T + ((2 ^ (k + 1) - 1 : ℕ) : ℝ)) := by
            ring
        _ ≤ (‖c n‖ ^ 2 * (n : ℝ) ^ (-(2 * σ))) * (2 * (T + (n : ℝ))) :=
            mul_le_mul_of_nonneg_left hw hfn
        _ = 2 * ((‖c n‖ ^ 2 * (n : ℝ) ^ (-(2 * σ))) * (T + (n : ℝ))) := by ring
    have hTnn : (0 : ℝ) ≤ T + ((2 ^ (k + 1) - 1 : ℕ) : ℝ) := by
      have h1 : (0 : ℝ) ≤ ((2 ^ (k + 1) - 1 : ℕ) : ℝ) := by positivity
      linarith
    refine hMVTk.trans ?_
    calc C₀ * (1 / 1 + Real.log (2 * ((2 ^ (k + 1) - 1 : ℕ) : ℝ)))
            * (T + ((2 ^ (k + 1) - 1 : ℕ) : ℝ)) * Fib
        ≤ C₀ * (1 + 2 * Real.log (2 * (N : ℝ)))
            * (T + ((2 ^ (k + 1) - 1 : ℕ) : ℝ)) * Fib := by
          apply mul_le_mul_of_nonneg_right _ hFibnn
          apply mul_le_mul_of_nonneg_right _ hTnn
          exact mul_le_mul_of_nonneg_left hlogb hC₀pos.le
      _ = C₀ * (1 + 2 * Real.log (2 * (N : ℝ))) *
            ((T + ((2 ^ (k + 1) - 1 : ℕ) : ℝ)) * Fib) := by ring
      _ ≤ C₀ * (1 + 2 * Real.log (2 * (N : ℝ))) * (2 * FibW) :=
          mul_le_mul_of_nonneg_left hW
            (mul_nonneg hC₀pos.le (by
              have h1 : (1 : ℝ) ≤ 2 * (N : ℝ) := by
                have hN1R : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
                linarith
              have h2 : (0 : ℝ) ≤ Real.log (2 * (N : ℝ)) := Real.log_nonneg h1
              linarith))
      _ = C₀ * (1 + 2 * Real.log (2 * (N : ℝ))) * 2 * FibW := by ring
  have hdecomp : ∀ t : ℝ,
      (∑ n ∈ Finset.Icc 1 N, c n * (n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I)))
        = ∑ k ∈ Finset.range (Nat.log2 N + 1), blockPoly N σ c k t := by
    intro t
    rw [Commons.Data.Finset.sum_Icc_eq_sum_log2_blocks 1 N
      (fun n => c n * (n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I)))]
    exact Finset.sum_congr rfl (fun k _ => dzPoly N σ t c k)
  have hcs_t : ∀ t ∈ S, ‖∑ k ∈ Finset.range (Nat.log2 N + 1), blockPoly N σ c k t‖ ^ 2
      ≤ ((Nat.log2 N : ℝ) + 1) * ∑ k ∈ Finset.range (Nat.log2 N + 1),
          ‖blockPoly N σ c k t‖ ^ 2 := by
    intro t ht
    have h := blocksCS (Nat.log2 N + 1) (fun k => blockPoly N σ c k t)
    simpa using h
  have hstep3 : (∑ k ∈ Finset.range (Nat.log2 N + 1), ∑ t ∈ S, ‖blockPoly N σ c k t‖ ^ 2)
      ≤ ∑ k ∈ Finset.range (Nat.log2 N + 1),
          C₀ * (1 + 2 * Real.log (2 * (N : ℝ))) * 2 *
            (∑ n ∈ (Finset.Icc 1 N).filter (fun n => Nat.log2 n = k),
              ‖c n‖ ^ 2 * (n : ℝ) ^ (-(2 * σ)) * (T + (n : ℝ))) :=
    Finset.sum_le_sum hperk
  have hfibR : (∑ n ∈ Finset.Icc 1 N, ‖c n‖ ^ 2 * (n : ℝ) ^ (-(2 * σ)) * (T + (n : ℝ)))
      = ∑ k ∈ Finset.range (Nat.log2 N + 1),
          ∑ n ∈ (Finset.Icc 1 N).filter (fun n => Nat.log2 n = k),
            ‖c n‖ ^ 2 * (n : ℝ) ^ (-(2 * σ)) * (T + (n : ℝ)) :=
    Commons.Data.Finset.sum_Icc_eq_sum_log2_blocks 1 N
      (fun n => ‖c n‖ ^ 2 * (n : ℝ) ^ (-(2 * σ)) * (T + (n : ℝ)))
  have hSnn : (0 : ℝ) ≤ ∑ n ∈ Finset.Icc 1 N, ‖c n‖ ^ 2 * (n : ℝ) ^ (-(2 * σ)) * (T + (n : ℝ)) := by
    rw [hfibR]
    apply Finset.sum_nonneg
    intro k hk
    apply Finset.sum_nonneg
    intro n hn
    have h1 : (0 : ℝ) ≤ (n : ℝ) ^ (-(2 * σ)) := Real.rpow_nonneg (by positivity) _
    have h2 : (0 : ℝ) ≤ T + (n : ℝ) := by positivity
    positivity
  calc (∑ t ∈ S, ‖∑ n ∈ Finset.Icc 1 N, c n * (n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))‖ ^ 2)
      = ∑ t ∈ S, ‖∑ k ∈ Finset.range (Nat.log2 N + 1), blockPoly N σ c k t‖ ^ 2 := by
        apply Finset.sum_congr rfl
        intro t ht
        rw [hdecomp t]
    _ ≤ ((Nat.log2 N : ℝ) + 1) * ∑ k ∈ Finset.range (Nat.log2 N + 1),
          ∑ t ∈ S, ‖blockPoly N σ c k t‖ ^ 2 := by
        calc (∑ t ∈ S, ‖∑ k ∈ Finset.range (Nat.log2 N + 1), blockPoly N σ c k t‖ ^ 2)
            ≤ ∑ t ∈ S, ((Nat.log2 N : ℝ) + 1) *
                ∑ k ∈ Finset.range (Nat.log2 N + 1), ‖blockPoly N σ c k t‖ ^ 2 :=
              Finset.sum_le_sum hcs_t
          _ = ((Nat.log2 N : ℝ) + 1) * ∑ t ∈ S,
                ∑ k ∈ Finset.range (Nat.log2 N + 1), ‖blockPoly N σ c k t‖ ^ 2 := by
              rw [Finset.mul_sum]
          _ = ((Nat.log2 N : ℝ) + 1) * ∑ k ∈ Finset.range (Nat.log2 N + 1),
                ∑ t ∈ S, ‖blockPoly N σ c k t‖ ^ 2 := by
              rw [Finset.sum_comm]
    _ ≤ ((Nat.log2 N : ℝ) + 1) * ∑ k ∈ Finset.range (Nat.log2 N + 1),
          C₀ * (1 + 2 * Real.log (2 * (N : ℝ))) * 2 *
            (∑ n ∈ (Finset.Icc 1 N).filter (fun n => Nat.log2 n = k),
              ‖c n‖ ^ 2 * (n : ℝ) ^ (-(2 * σ)) * (T + (n : ℝ))) :=
        mul_le_mul_of_nonneg_left hstep3 (by positivity)
    _ = ((Nat.log2 N : ℝ) + 1) * C₀ * (1 + 2 * Real.log (2 * (N : ℝ))) * 2 *
          (∑ n ∈ Finset.Icc 1 N, ‖c n‖ ^ 2 * (n : ℝ) ^ (-(2 * σ)) * (T + (n : ℝ))) := by
        rw [hfibR, ← Finset.mul_sum]
        ring
    _ ≤ (200 * C₀) * (Real.log (2 * (N : ℝ))) ^ 5 *
          (∑ n ∈ Finset.Icc 1 N, ‖c n‖ ^ 2 * (n : ℝ) ^ (-(2 * σ)) * (T + (n : ℝ))) := by
        have hb := log2BlocksLogBound N hN
        have hfac : ((Nat.log2 N : ℝ) + 1) * C₀ * (1 + 2 * Real.log (2 * (N : ℝ))) * 2
            = C₀ * (((Nat.log2 N : ℝ) + 1) * (1 + 2 * Real.log (2 * (N : ℝ))) * 2) := by
          ring
        rw [hfac]
        calc C₀ * (((Nat.log2 N : ℝ) + 1) * (1 + 2 * Real.log (2 * (N : ℝ))) * 2)
              * (∑ n ∈ Finset.Icc 1 N, ‖c n‖ ^ 2 * (n : ℝ) ^ (-(2 * σ)) * (T + (n : ℝ)))
            ≤ C₀ * (200 * (Real.log (2 * (N : ℝ))) ^ 5)
              * (∑ n ∈ Finset.Icc 1 N, ‖c n‖ ^ 2 * (n : ℝ) ^ (-(2 * σ)) * (T + (n : ℝ))) := by
              apply mul_le_mul_of_nonneg_right _ hSnn
              exact mul_le_mul_of_nonneg_left hb hC₀pos.le
          _ = (200 * C₀) * (Real.log (2 * (N : ℝ))) ^ 5 *
              (∑ n ∈ Finset.Icc 1 N, ‖c n‖ ^ 2 * (n : ℝ) ^ (-(2 * σ)) * (T + (n : ℝ))) := by ring

end

end Work.ZeroDensity.Ingham
