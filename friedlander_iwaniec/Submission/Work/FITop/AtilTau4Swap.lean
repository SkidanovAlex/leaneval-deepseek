import Mathlib
import Submission.Work.FITop.Defs
import Submission.ASP.S7c
import Submission.ASP.S8b
import Submission.ASP.S20
import Submission.ASP.S21
import Submission.ASP.S22
import Submission.ASP.S23
import Submission.ASP.S24
import Submission.ASP.S25
import Submission.Work.FITop.WolkeSquarefreeTau

/-!
# `Work.FITop.AtilTau4Swap`

The `τ⁴`-weighted sum of the squarefree-supported sequence `ã = atilFIa` is bounded by a
swapped sum over squarefree `d ≤ x^{1/3}`, weighted by `(2 τ(d))^{12}`.

The point is Wolke's bound (`WolkeSquarefreeTau`): for squarefree `n` there is `d ∣ n` with
`d³ ≤ n` and `τ(n) ≤ (2 τ(d))³`, hence `τ(n)⁴ ≤ (2 τ(d))^{12}`, and `d` is itself squarefree
with `d³ ≤ x`.  Since only squarefree `n` have `ã(n) ≠ 0` (`ã = μ² a`), choosing such a `d = D(n)`
for every relevant `n` and grouping the sum by the value of `D` gives the claimed inequality.
-/

namespace Work.FITop

open Finset
open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable

/-- `ã n ≥ 0`. -/
private lemma atilFIa_nonneg (n : ℕ) : 0 ≤ atilFIa n := by
  rw [atilFIa, Submission.ASP.atil, Submission.ASP.FIa]
  positivity

/-- If `ã n ≠ 0` then `n` is squarefree, since `ã = μ²·a`. -/
private lemma squarefree_of_atilFIa_ne_zero {n : ℕ} (h : atilFIa n ≠ 0) : Squarefree n := by
  rw [atilFIa, Submission.ASP.atil] at h
  have h1 : ((ArithmeticFunction.moebius n : ℝ)) ^ 2 ≠ 0 := (mul_ne_zero_iff.mp h).1
  have h2 : (ArithmeticFunction.moebius n : ℝ) ≠ 0 := by
    intro h0; exact h1 (by rw [h0]; norm_num)
  have h3 : ArithmeticFunction.moebius n ≠ 0 := by
    intro h0; exact h2 (by rw [h0]; norm_num)
  exact ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp h3

/-- The `x^{1/3}` range check: `d ^ 3 ≤ x` puts the natural `d` into the index set
`[1, ⌊x^{1/3}⌋]`. -/
private lemma nat_le_floor_rpow_third {d x : ℕ} (hd : d ^ 3 ≤ x) :
    d ≤ ⌊(x : ℝ) ^ ((1 : ℝ) / 3)⌋₊ := by
  have hd3 : ((d : ℝ)) ^ 3 ≤ (x : ℝ) := by exact_mod_cast hd
  have hd0 : (0 : ℝ) ≤ (d : ℝ) := by positivity
  have hrpow : ((d : ℝ) ^ 3) ^ ((1 : ℝ) / 3) ≤ (x : ℝ) ^ ((1 : ℝ) / 3) :=
    Real.rpow_le_rpow (by positivity) hd3 (by norm_num)
  have heq : ((d : ℝ) ^ 3) ^ ((1 : ℝ) / 3) = (d : ℝ) := by
    rw [one_div]
    exact Real.pow_rpow_inv_natCast hd0 (by norm_num)
  exact Nat.le_floor (heq ▸ hrpow)

theorem AtilTau4Swap (x : ℕ) :
    (∑ n ∈ Finset.Icc 1 x, Work.FITop.atilFIa n * ((n.divisors.card : ℝ)) ^ 4)
      ≤ ∑ d ∈ (Finset.Icc 1 ⌊(x : ℝ) ^ ((1 : ℝ) / 3)⌋₊).filter Squarefree,
          (2 * ((d.divisors.card : ℝ))) ^ 12 *
            (∑ n ∈ (Finset.Icc 1 x).filter (fun n => d ∣ n), Work.FITop.atilFIa n) := by
  set T : Finset ℕ := (Finset.Icc 1 x).filter (fun n => atilFIa n ≠ 0) with hT
  set S : Finset ℕ := (Finset.Icc 1 ⌊(x : ℝ) ^ ((1 : ℝ) / 3)⌋₊).filter Squarefree with hS
  have hTsub : T ⊆ Finset.Icc 1 x := by rw [hT]; exact Finset.filter_subset _ _
  have hTmem : ∀ n ∈ T, 1 ≤ n ∧ Squarefree n := by
    intro n hn
    rw [hT] at hn
    obtain ⟨hnI, hn0⟩ := Finset.mem_filter.mp hn
    exact ⟨(Finset.mem_Icc.mp hnI).1, squarefree_of_atilFIa_ne_zero hn0⟩
  -- the Wolke witness at every relevant `n`
  have hW : ∀ n ∈ T, ∃ d, d ∈ S ∧ d ∣ n ∧
      ((n.divisors.card : ℝ)) ^ 4 ≤ (2 * ((d.divisors.card : ℝ))) ^ 12 := by
    intro n hn
    obtain ⟨hn1, hnsq⟩ := hTmem n hn
    have hnx : n ≤ x := (Finset.mem_Icc.mp (hTsub hn)).2
    obtain ⟨d, hdvd, hdcube, hdbound⟩ := WolkeSquarefreeTau n hn1 hnsq
    refine ⟨d, ?_, hdvd, ?_⟩
    · rw [hS, Finset.mem_filter]
      refine ⟨Finset.mem_Icc.mpr ⟨?_, nat_le_floor_rpow_third (le_trans hdcube hnx)⟩, ?_⟩
      · rcases Nat.eq_zero_or_pos d with h | h
        · exfalso
          rcases hdvd with ⟨k, hk⟩
          rw [h, zero_mul] at hk
          omega
        · exact h
      · exact Squarefree.squarefree_of_dvd hdvd hnsq
    · have hnτ : ((n.divisors.card : ℝ)) ≤ (2 * ((d.divisors.card : ℝ))) ^ 3 := by
        exact_mod_cast hdbound
      calc ((n.divisors.card : ℝ)) ^ 4
          ≤ ((2 * ((d.divisors.card : ℝ))) ^ 3) ^ 4 := pow_le_pow_left₀ (by positivity) hnτ 4
        _ = (2 * ((d.divisors.card : ℝ))) ^ 12 := by ring
  -- the choice of the witness
  set D : ℕ → ℕ := (fun n => if hn : n ∈ T then Classical.choose (hW n hn) else 0) with hDdef
  have hDmem : ∀ n ∈ T, D n ∈ S := by
    intro n hn
    rw [hDdef]
    simp only [dif_pos hn]
    exact (Classical.choose_spec (hW n hn)).1
  have hDdvd : ∀ n ∈ T, D n ∣ n := by
    intro n hn
    rw [hDdef]
    simp only [dif_pos hn]
    exact (Classical.choose_spec (hW n hn)).2.1
  have hDbnd : ∀ n ∈ T, ((n.divisors.card : ℝ)) ^ 4 ≤ (2 * ((D n).divisors.card : ℝ)) ^ 12 := by
    intro n hn
    rw [hDdef]
    simp only [dif_pos hn]
    exact (Classical.choose_spec (hW n hn)).2.2
  have hDimg : T.image D ⊆ S := by
    intro d hd
    rw [Finset.mem_image] at hd
    obtain ⟨n, hn, rfl⟩ := hd
    exact hDmem n hn
  -- Step 1: restrict to `n ∈ T`
  have hstep1 : (∑ n ∈ Finset.Icc 1 x, atilFIa n * ((n.divisors.card : ℝ)) ^ 4)
      = ∑ n ∈ T, atilFIa n * ((n.divisors.card : ℝ)) ^ 4 := by
    refine (Finset.sum_subset hTsub ?_).symm
    intro n hnI hnT
    have h0 : atilFIa n = 0 := by
      by_contra h
      exact hnT (by rw [hT]; exact Finset.mem_filter.mpr ⟨hnI, h⟩)
    rw [h0, zero_mul]
  -- Step 2: pointwise replacement of `τ(n)⁴` by the witness weight
  have hstep2 : ∑ n ∈ T, atilFIa n * ((n.divisors.card : ℝ)) ^ 4
      ≤ ∑ n ∈ T, atilFIa n * (2 * ((D n).divisors.card : ℝ)) ^ 12 := by
    refine Finset.sum_le_sum (fun n hn => ?_)
    exact mul_le_mul_of_nonneg_left (hDbnd n hn) (atilFIa_nonneg n)
  -- Step 3: group by the value of the witness
  have hmaps : ∀ n ∈ T, D n ∈ T.image D := fun n hn => Finset.mem_image.mpr ⟨n, hn, rfl⟩
  have hstep3 : ∑ n ∈ T, atilFIa n * (2 * ((D n).divisors.card : ℝ)) ^ 12
      = ∑ d ∈ T.image D, (2 * ((d).divisors.card : ℝ)) ^ 12 *
          ∑ n ∈ T.filter (fun n => D n = d), atilFIa n := by
    rw [← Finset.sum_fiberwise_of_maps_to hmaps
      (fun n => atilFIa n * (2 * ((D n).divisors.card : ℝ)) ^ 12)]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun n hn => ?_)
    have hDn : D n = d := (Finset.mem_filter.mp hn).2
    rw [hDn]
    ring
  -- Step 4: enlarge each inner range to all multiples of `d`
  have hstep4 : ∑ d ∈ T.image D, (2 * ((d).divisors.card : ℝ)) ^ 12 *
          ∑ n ∈ T.filter (fun n => D n = d), atilFIa n
      ≤ ∑ d ∈ T.image D, (2 * ((d).divisors.card : ℝ)) ^ 12 *
          ∑ n ∈ (Finset.Icc 1 x).filter (fun n => d ∣ n), atilFIa n := by
    refine Finset.sum_le_sum (fun d _ => ?_)
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
    · intro n hn
      rw [Finset.mem_filter] at hn ⊢
      obtain ⟨hnT, hDn⟩ := hn
      exact ⟨hTsub hnT, by rw [← hDn]; exact hDdvd n hnT⟩
    · intro n _ _
      exact atilFIa_nonneg n
  -- Step 5: enlarge the outer range from `T.image D` to `S`
  have hstep5 : ∑ d ∈ T.image D, (2 * ((d).divisors.card : ℝ)) ^ 12 *
          ∑ n ∈ (Finset.Icc 1 x).filter (fun n => d ∣ n), atilFIa n
      ≤ ∑ d ∈ S, (2 * ((d).divisors.card : ℝ)) ^ 12 *
          ∑ n ∈ (Finset.Icc 1 x).filter (fun n => d ∣ n), atilFIa n := by
    refine Finset.sum_le_sum_of_subset_of_nonneg hDimg (fun d _ _ => ?_)
    exact mul_nonneg (pow_nonneg (by positivity) 12)
      (Finset.sum_nonneg (fun n _ => atilFIa_nonneg n))
  exact hstep1.le.trans (hstep2.trans (hstep3.le.trans (hstep4.trans hstep5)))

end

end Work.FITop
