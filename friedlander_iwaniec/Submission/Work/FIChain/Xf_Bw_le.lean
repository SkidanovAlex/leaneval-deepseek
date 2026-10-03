/-
# `Submission.Work.FIChain.Xf_Bw_le` — the trivial bound for the `τ⁶`-weighted `(B′)`-window

The `(B′)`-window ingredient of the chain is the pointwise bound

  `Bw x Pz u = Σ_{c ≤ x} τ(c)⁶ |Xf x Pz c u| ≤ C·Ã(x)·(log x)^{2^18}`,

uniform in `Pz` and `u`.  It is "trivial" in the sense that no cancellation is used anywhere:
`|Xf|` is dominated by the unsigned mass of the window, the condition `(n, Π) = 1` is dropped,
the truncation `cn ≤ x` is reindexed as `c ∣ m` with `m = cn`, and the divisor weight is absorbed
by the divisor function of `m`.

The two ingredients are

* `Work.FITop.AseqTauEightBound` (`Σ_{m ≤ x} ã_m τ(m)^8 ≤ C·Ã(x)·(log x)^{2^18}`), the only
  arithmetic input; and
* the standard double-counting reindexings
  `Commons.NumberTheory.Divisors.sum_filter_dvd_reindex` and
  `Commons.NumberTheory.Divisors.sum_divisors_filter_swap_of_pred`.

Explicitly, dropping the window conditions and the coprimality condition,
  `Bw ≤ Σ_{c ≤ x} τ(c)⁶ Σ_{n ≤ x/c} ã(cn) = Σ_{c ≤ x} Σ_{m ≤ x, c ∣ m} τ(c)⁶ ã(m)`,
and the inner mass of a fixed `m ≤ x` is
  `Σ_{c ∣ m} τ(c)⁶ ≤ τ(m)·τ(m)⁶ = τ(m)⁷ ≤ τ(m)⁸`.
-/
import Mathlib
import Submission.Work.FIChain.BpWinDefs
import Submission.Work.FITop.AseqTauEightBound
import Submission.Commons.NumberTheory.Divisors.sum_filter_dvd_reindex
import Submission.Commons.NumberTheory.Divisors.sum_divisors_filter_swap_of_pred

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.FIChain

open Finset

attribute [local instance] Classical.propDecidable

noncomputable section

/-- For `c > 0` the truncation `c·n ≤ x` is the range condition `n ≤ x/c`. -/
private lemma filter_mul_le_eq_Icc_div (x c : ℕ) (hc : 0 < c) :
    (Finset.Icc 1 x).filter (fun n => c * n ≤ x) = Finset.Icc 1 (x / c) := by
  ext n
  rw [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨h1, _⟩, h3⟩
    exact ⟨h1, (Nat.le_div_iff_mul_le hc).mpr (by rwa [mul_comm] at h3)⟩
  · rintro ⟨h1, h2⟩
    exact ⟨⟨h1, le_trans h2 (Nat.div_le_self x c)⟩,
      by rw [mul_comm]; exact (Nat.le_div_iff_mul_le hc).mp h2⟩

/-- The `τ⁶`-weighted divisor reindexing: the total `c`-weight landing on a fixed `m` is at most
`τ(m)⁶` per divisor of `m`, hence at most `τ(m)⁷`. -/
private lemma tau6_div_sum_le (x : ℕ) :
    (∑ c ∈ Finset.Icc 1 x, ((c.divisors.card : ℝ)) ^ 6 *
        ∑ n ∈ Finset.Icc 1 (x / c), atilc (c * n))
      ≤ ∑ m ∈ Finset.Icc 1 x, atilc m * ((m.divisors.card : ℝ)) ^ 7 := by
  have h1 : (∑ c ∈ Finset.Icc 1 x, ((c.divisors.card : ℝ)) ^ 6 *
        ∑ n ∈ Finset.Icc 1 (x / c), atilc (c * n))
      = ∑ c ∈ Finset.Icc 1 x, ∑ m ∈ (Finset.Icc 1 x).filter (fun m => c ∣ m),
            ((c.divisors.card : ℝ)) ^ 6 * atilc m := by
    refine Finset.sum_congr rfl (fun c hc => ?_)
    have hcpos : 0 < c := by
      have := (Finset.mem_Icc.mp hc).1
      omega
    rw [Finset.mul_sum]
    exact (Commons.NumberTheory.Divisors.sum_filter_dvd_reindex (N := x) (q := c) hcpos
      (fun m => ((c.divisors.card : ℝ)) ^ 6 * atilc m)).symm
  have h2 : (∑ c ∈ Finset.Icc 1 x, ∑ m ∈ (Finset.Icc 1 x).filter (fun m => c ∣ m),
            ((c.divisors.card : ℝ)) ^ 6 * atilc m)
      = ∑ m ∈ Finset.Icc 1 x, atilc m * ∑ b ∈ m.divisors, ((b.divisors.card : ℝ)) ^ 6 := by
    have hswap := Commons.NumberTheory.Divisors.sum_divisors_filter_swap_of_pred (N := x)
      (p := fun _ : ℕ => True) (F := fun m b => ((b.divisors.card : ℝ)) ^ 6 * atilc m)
    simp only [Finset.filter_true] at hswap
    calc (∑ c ∈ Finset.Icc 1 x, ∑ m ∈ (Finset.Icc 1 x).filter (fun m => c ∣ m),
            ((c.divisors.card : ℝ)) ^ 6 * atilc m)
        = ∑ m ∈ Finset.Icc 1 x, ∑ b ∈ m.divisors, ((b.divisors.card : ℝ)) ^ 6 * atilc m :=
          hswap.symm
      _ = ∑ m ∈ Finset.Icc 1 x, atilc m * ∑ b ∈ m.divisors, ((b.divisors.card : ℝ)) ^ 6 := by
          refine Finset.sum_congr rfl (fun m _ => ?_)
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun b _ => by ring)
  have h3 : (∑ m ∈ Finset.Icc 1 x, atilc m * ∑ b ∈ m.divisors, ((b.divisors.card : ℝ)) ^ 6)
      ≤ ∑ m ∈ Finset.Icc 1 x, atilc m * ((m.divisors.card : ℝ)) ^ 7 := by
    refine Finset.sum_le_sum (fun m hm => ?_)
    have hm0 : m ≠ 0 := by
      have := (Finset.mem_Icc.mp hm).1
      omega
    refine mul_le_mul_of_nonneg_left ?_ (Work.FITop.atilFIa_nonneg m)
    have hpoint : ∀ b ∈ m.divisors,
        ((b.divisors.card : ℝ)) ^ 6 ≤ ((m.divisors.card : ℝ)) ^ 6 := by
      intro b hb
      have hb' : b ∣ m := (Nat.mem_divisors.mp hb).1
      have hcard : b.divisors.card ≤ m.divisors.card :=
        Finset.card_le_card (Nat.divisors_subset_of_dvd hm0 hb')
      exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast hcard) 6
    calc ∑ b ∈ m.divisors, ((b.divisors.card : ℝ)) ^ 6
        ≤ ∑ _b ∈ m.divisors, ((m.divisors.card : ℝ)) ^ 6 := Finset.sum_le_sum hpoint
      _ = ((m.divisors.card : ℝ)) ^ 7 := by
          rw [Finset.sum_const, nsmul_eq_mul]
          ring
  exact h1.trans_le (h2.trans_le h3)

theorem Xf_Bw_le : ∃ C : ℝ, 0 < C ∧ ∃ X₀ : ℕ, ∀ x Pz : ℕ, X₀ ≤ x → ∀ u : ℝ,
    Work.FIChain.Bw x Pz u ≤ C * Work.FIChain.AcountAtilC x * (Real.log (x : ℝ)) ^ (262144 : ℕ) := by
  obtain ⟨C8, X8, hC8pos, hA8⟩ := Work.FITop.AseqTauEightBound
  refine ⟨(C8 : ℝ), by exact_mod_cast hC8pos, max X8 1, ?_⟩
  intro x Pz hx u
  have hxX8 : X8 ≤ x := le_trans (le_max_left _ _) hx
  have hstep1 : Bw x Pz u ≤ ∑ c ∈ Finset.Icc 1 x, ((c.divisors.card : ℝ)) ^ 6 *
      (∑ n ∈ (Finset.Icc 1 x).filter (fun n => c * n ≤ x), atilc (c * n)) := by
    rw [Bw]
    refine Finset.sum_le_sum (fun c hc => ?_)
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine (abs_Xf_le_sum x Pz c u).trans ?_
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_
      (fun n _ _ => Work.FITop.atilFIa_nonneg (c * n))
    intro n hn
    rw [Finset.mem_filter] at hn ⊢
    exact ⟨hn.1, hn.2.1⟩
  have hstep2 : (∑ c ∈ Finset.Icc 1 x, ((c.divisors.card : ℝ)) ^ 6 *
      (∑ n ∈ (Finset.Icc 1 x).filter (fun n => c * n ≤ x), atilc (c * n)))
      = ∑ c ∈ Finset.Icc 1 x, ((c.divisors.card : ℝ)) ^ 6 *
        (∑ n ∈ Finset.Icc 1 (x / c), atilc (c * n)) := by
    refine Finset.sum_congr rfl (fun c hc => ?_)
    have hcpos : 0 < c := by
      have := (Finset.mem_Icc.mp hc).1
      omega
    rw [filter_mul_le_eq_Icc_div x c hcpos]
  have hstep4 : (∑ m ∈ Finset.Icc 1 x, atilc m * ((m.divisors.card : ℝ)) ^ 7)
      ≤ ∑ m ∈ Finset.Icc 1 x, atilc m * ((m.divisors.card : ℝ)) ^ 8 := by
    refine Finset.sum_le_sum (fun m hm => ?_)
    have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
    have hge1 : (1 : ℝ) ≤ (m.divisors.card : ℝ) := by
      have h : 1 ≤ m.divisors.card :=
        Finset.card_pos.mpr ⟨1, by rw [Nat.mem_divisors]; exact ⟨one_dvd m, by omega⟩⟩
      exact_mod_cast h
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hge1 (by norm_num))
      (Work.FITop.atilFIa_nonneg m)
  calc Bw x Pz u
      ≤ ∑ c ∈ Finset.Icc 1 x, ((c.divisors.card : ℝ)) ^ 6 *
          (∑ n ∈ Finset.Icc 1 (x / c), atilc (c * n)) := hstep1.trans hstep2.le
    _ ≤ ∑ m ∈ Finset.Icc 1 x, atilc m * ((m.divisors.card : ℝ)) ^ 7 := tau6_div_sum_le x
    _ ≤ ∑ m ∈ Finset.Icc 1 x, atilc m * ((m.divisors.card : ℝ)) ^ 8 := hstep4
    _ ≤ (C8 : ℝ) * AcountAtilC x * (Real.log (x : ℝ)) ^ (262144 : ℕ) := hA8 x hxX8

end

end Work.FIChain
