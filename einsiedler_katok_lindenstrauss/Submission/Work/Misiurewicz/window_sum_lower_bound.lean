import Mathlib
import Submission.Work.EKLComp.Core
import Submission.Work.EKLComp.Entropy
import Submission.Work.EKLComp.Misiurewicz.Defs
import Submission.Work.Misiurewicz.Hfam_winJoin_grid
import Submission.Work.Misiurewicz.Hfam_joinSets_add
import Submission.Work.Misiurewicz.Hfam_winJoin_mono_len
import Submission.Work.Misiurewicz.sum_range_ceilDiv_range
import Submission.Work.Misiurewicz.Hfam_joinSets_le_mul_log

/-!
# The Misiurewicz window sum: a lower bound for `∑_{k<N} H(winJoin T P k M)`

Let `T : X₃ → X₃` be measurable, `P` a finite measurable partition of `X₃` with `P.n` parts and
`μ` a probability measure.  Write

* `A_k := winJoin T P k M`, the partition into the atoms `⋂_{t<M} T^{-(t+k)} P.parts (w t)` —
  the information the orbit sees during the time window `[k, k+M)`;
* `H_N := Hfam μ (joinSets T P N)`, the entropy of the information over the whole time interval
  `[0, N)`.

The lemma proved here is the quantitative "sliding window" estimate

`M * (L - 2 (M-1) log P.n) ≤ ∑_{k<N} Hfam μ (winJoin T P k M)`  whenever  `L ≤ H_N`, `1 ≤ M` and
`2 M ≤ N`,

i.e. the `N` windows of length `M` (`N ≥ 2M` of them) contain, on average, at least `1/M` of the
information of the full window `[0,N)`, up to the correction `2(M-1) log P.n`.

## Proof

The only way to compare a *sum* of window entropies with the entropy of a large join is to split
the large join and to re-use each piece once per residue class.  Concretely, for every offset
`j < M` we cut `[0, N)` at time `j`:

`H_N ≤ H(joinSets T P j) + H(winJoin T P j (N-j))`   (`Hfam_joinSets_add`, no invariance needed).

* the first summand is at most `j log P.n ≤ (M-1) log P.n` (`Hfam_joinSets_le_mul_log` + Shannon);
* the window `[j, N)` is tiled by the blocks `[j + iM, j + (i+1)M)`, `i < ⌈(N-j)/M⌉`, so by
  monotonicity of `winJoin` in the window length (`Hfam_winJoin_mono_len`) and grid subadditivity
  (`Hfam_winJoin_grid`) the second summand is at most `∑_{i < ⌈(N-j)/M⌉} Hfam μ A_{j+iM}`.

Summing over the `M` offsets `j < M` and using that `(j, i) ↦ j + iM` is a bijection from
`{(j,i) : j < M, i < ⌈(N-j)/M⌉}` onto `{k : k < N}` (`sum_range_ceilDiv_range`) produces exactly

`M * H_N ≤ M (M-1) log P.n + ∑_{k<N} Hfam μ A_k`,

and `M (M-1) log P.n ∈ [0, 2 M (M-1) log P.n]` since `log P.n ≥ 0`, `M ≥ 1`.
-/

namespace Work.Misiurewicz

open MeasureTheory
open scoped BigOperators
open Work.EKLContract Work.EKLComp

/-- For an offset `j < M ≤ N`: the entropy of the join over the whole time interval `[0,N)` is
bounded by the Shannon bound `(M-1) log P.n` (for the initial segment `[0,j)`) plus the sum of the
entropies of the windows `[j + iM, j + (i+1)M)`, `i < ⌈(N-j)/M⌉`, which tile `[j, N)`.

This is one residue class of the sliding-window decomposition; summing it over the `M` offsets
`j < M` uses every window `[k, k+M)`, `k < N`, exactly once. -/
theorem Hfam_joinSets_le_window_blocks (μ : MeasureTheory.Measure Work.EKLContract.X3)
    [MeasureTheory.IsProbabilityMeasure μ]
    (T : Work.EKLContract.X3 → Work.EKLContract.X3) (hT : Measurable T)
    (P : Work.EKLContract.FinPart Work.EKLContract.X3) {M N j : ℕ}
    (hM : 1 ≤ M) (hMN : M ≤ N) (hj : j < M) :
    Hfam μ (joinSets T P N) ≤ ((M : ℝ) - 1) * Real.log (P.n : ℝ) +
      ∑ i ∈ Finset.range ((N - j) ⌈/⌉ M), Hfam μ (winJoin T P (j + i * M) M) := by
  have hjN : j ≤ N := by omega
  -- split the time interval `[0, N)` at the time `j`
  have hsplit := Hfam_joinSets_add μ T hT P j (N - j)
  rw [Nat.add_sub_cancel' hjN] at hsplit
  -- the initial segment `[0, j)` carries at most `j log P.n ≤ (M-1) log P.n`
  have hshannon : Hfam μ (joinSets T P j) ≤ ((M : ℝ) - 1) * Real.log (P.n : ℝ) := by
    have h1 := Hfam_joinSets_le_mul_log μ T hT P j
    have h3 : (j : ℝ) ≤ (M : ℝ) - 1 := by
      have h5 : (j : ℝ) + 1 ≤ (M : ℝ) := by exact_mod_cast (show j + 1 ≤ M by omega)
      linarith
    have h2 : (j : ℝ) * Real.log (P.n : ℝ) ≤ ((M : ℝ) - 1) * Real.log (P.n : ℝ) :=
      mul_le_mul_of_nonneg_right h3 (Real.log_natCast_nonneg P.n)
    linarith
  -- tile the window `[j, N)` by the `M`-blocks starting at `j`
  have hblocks : Hfam μ (winJoin T P j (N - j)) ≤
      ∑ i ∈ Finset.range ((N - j) ⌈/⌉ M), Hfam μ (winJoin T P (j + i * M) M) := by
    have hLM : N - j ≤ ((N - j) ⌈/⌉ M) * M := by
      have h : N - j ≤ M * ((N - j) ⌈/⌉ M) :=
        (gc_mul_ceilDiv (show 0 < M by omega)).le_u_l (N - j)
      rwa [Nat.mul_comm] at h
    calc Hfam μ (winJoin T P j (N - j))
        ≤ Hfam μ (winJoin T P j (((N - j) ⌈/⌉ M) * M)) :=
          Hfam_winJoin_mono_len μ T hT P j hLM
      _ ≤ ∑ i ∈ Finset.range ((N - j) ⌈/⌉ M), Hfam μ (winJoin T P (j + i * M) M) :=
          Hfam_winJoin_grid μ T hT P j ((N - j) ⌈/⌉ M) M
  linarith

theorem window_sum_lower_bound (μ : MeasureTheory.Measure Work.EKLContract.X3)
    [MeasureTheory.IsProbabilityMeasure μ]
    (T : Work.EKLContract.X3 → Work.EKLContract.X3) (hT : Measurable T)
    (P : Work.EKLContract.FinPart Work.EKLContract.X3) (M N : ℕ) (hM : 1 ≤ M) (hN : 2 * M ≤ N)
    (L : ℝ) (hL : L ≤ Work.EKLContract.Hfam μ (Work.EKLContract.joinSets T P N)) :
    (M : ℝ) * (L - 2 * ((M : ℝ) - 1) * Real.log (P.n : ℝ)) ≤
      ∑ k ∈ Finset.range N, Work.EKLContract.Hfam μ (Work.EKLComp.winJoin T P k M) := by
  have hMN : M ≤ N := by omega
  -- sum the residue-class decomposition over the `M` possible offsets
  have hkey : (M : ℝ) * Hfam μ (joinSets T P N) ≤
      (M : ℝ) * (((M : ℝ) - 1) * Real.log (P.n : ℝ)) +
        ∑ k ∈ Finset.range N, Hfam μ (winJoin T P k M) := by
    have h1 : (M : ℝ) * Hfam μ (joinSets T P N)
        = ∑ _j ∈ Finset.range M, Hfam μ (joinSets T P N) := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [h1]
    calc ∑ j ∈ Finset.range M, Hfam μ (joinSets T P N)
        ≤ ∑ j ∈ Finset.range M, (((M : ℝ) - 1) * Real.log (P.n : ℝ) +
            ∑ i ∈ Finset.range ((N - j) ⌈/⌉ M), Hfam μ (winJoin T P (j + i * M) M)) :=
          Finset.sum_le_sum
            (fun j hj => Hfam_joinSets_le_window_blocks μ T hT P hM hMN (Finset.mem_range.mp hj))
      _ = (M : ℝ) * (((M : ℝ) - 1) * Real.log (P.n : ℝ)) +
            ∑ j ∈ Finset.range M, ∑ i ∈ Finset.range ((N - j) ⌈/⌉ M),
              Hfam μ (winJoin T P (j + i * M) M) := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ = (M : ℝ) * (((M : ℝ) - 1) * Real.log (P.n : ℝ)) +
            ∑ k ∈ Finset.range N, Hfam μ (winJoin T P k M) := by
          rw [sum_range_ceilDiv_range (fun k => Hfam μ (winJoin T P k M)) hM hMN]
  have hML : (M : ℝ) * L ≤ (M : ℝ) * Hfam μ (joinSets T P N) :=
    mul_le_mul_of_nonneg_left hL (by positivity)
  have hmono : 0 ≤ (M : ℝ) * (((M : ℝ) - 1) * Real.log (P.n : ℝ)) := by
    have h1 : (0 : ℝ) ≤ (M : ℝ) - 1 := by
      have : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
      linarith
    positivity
  have h2 : (M : ℝ) * L ≤ (M : ℝ) * (((M : ℝ) - 1) * Real.log (P.n : ℝ)) +
      ∑ k ∈ Finset.range N, Hfam μ (winJoin T P k M) := le_trans hML hkey
  have h3 : (M : ℝ) * (L - 2 * ((M : ℝ) - 1) * Real.log (P.n : ℝ))
      = (M : ℝ) * L - 2 * ((M : ℝ) * (((M : ℝ) - 1) * Real.log (P.n : ℝ))) := by ring
  rw [h3]
  linarith

end Work.Misiurewicz
