import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseK15.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseK15.sum_le_sum_annuli` — the dyadic annulus decomposition

The lattice decay sums of the chapter (`sum_inv_one_add_norm_le`,
`sum_inv_one_add_norm_tail`, `annulus_sum_bound`, …) are estimated annulus by
annulus: one writes a lattice set `S` of momenta `‖vec n‖ ∈ [R, 2^(K+1) R)` as
the union of the dyadic annuli

    `A_k = {n ∈ S | 2^k R ≤ ‖vec n‖ < 2^(k+1) R}`,  `k = 0, …, K`,

and then estimates each `A_k` by the size of the shell it occupies.

This file supplies the *trivial half* of that decomposition: the annuli cover
`S`, so with a nonnegative summand the sum over `S` is at most the sum over the
disjoint union, i.e. at most the sum of the annulus sums.  (No disjointness is
used: every `n ∈ S` occurs in some annulus, and the summand is nonnegative, so
counting each `n` with its multiplicity is an upper bound.)

The existence of the annulus index is the elementary "dyadic rounding" fact:
the set `{k ∈ {0,…,K} | 2^k R ≤ ‖vec n‖}` is nonempty (it contains `0` because
`R ≤ ‖vec n‖`) and its maximum `k` is the required index — `k + 1` cannot also
lie in the set, since either `k + 1 > K`, whence `2^(k+1) R ≥ 2^(K+1) R >
‖vec n‖`, or `k + 1 ≤ K` and the maximality of `k` is violated.
-/

namespace Work.BoseK15

theorem sum_le_sum_annuli (s K : ℕ) (R : ℝ) (S : Finset (Fin 3 → ℤ)) (hR : 1 ≤ R)
    (hlo : ∀ n ∈ S, R ≤ ‖Work.BoseB4.vec n‖)
    (hK : ∀ n ∈ S, ‖Work.BoseB4.vec n‖ < (2:ℝ)^(K+1) * R) :
    (∑ n ∈ S, (((1 : ℝ) + ‖Work.BoseB4.vec n‖ ^ 2) ^ s)⁻¹)
      ≤ ∑ k ∈ Finset.range (K+1),
          ∑ n ∈ (S.filter (fun n => (2:ℝ)^k * R ≤ ‖Work.BoseB4.vec n‖)).filter
            (fun n => ¬ ((2:ℝ)^(k+1) * R ≤ ‖Work.BoseB4.vec n‖)),
            (((1 : ℝ) + ‖Work.BoseB4.vec n‖ ^ 2) ^ s)⁻¹ := by
  have hRpos : 0 < R := lt_of_lt_of_le one_pos hR
  -- Every `n ∈ S` lies in one of the dyadic annuli `k = 0, …, K`.
  have hcover : ∀ n ∈ S, ∃ k ∈ Finset.range (K+1),
      (2:ℝ)^k * R ≤ ‖Work.BoseB4.vec n‖ ∧ ¬ ((2:ℝ)^(k+1) * R ≤ ‖Work.BoseB4.vec n‖) := by
    intro n hn
    let T : Finset ℕ := (Finset.range (K+1)).filter
        (fun k => (2:ℝ)^k * R ≤ ‖Work.BoseB4.vec n‖)
    have hne : T.Nonempty := ⟨0, by
      show (0 : ℕ) ∈ (Finset.range (K+1)).filter
        (fun k => (2:ℝ)^k * R ≤ ‖Work.BoseB4.vec n‖)
      rw [Finset.mem_filter, Finset.mem_range]
      exact ⟨Nat.succ_pos K, by simpa using hlo n hn⟩⟩
    have hmem : T.max' hne ∈ (Finset.range (K+1)).filter
        (fun k => (2:ℝ)^k * R ≤ ‖Work.BoseB4.vec n‖) := Finset.max'_mem T hne
    have hk : T.max' hne ∈ Finset.range (K+1) ∧
        (2:ℝ)^(T.max' hne) * R ≤ ‖Work.BoseB4.vec n‖ := Finset.mem_filter.mp hmem
    refine ⟨T.max' hne, hk.1, hk.2, ?_⟩
    intro hup
    by_cases hlt : T.max' hne + 1 < K + 1
    · -- `k + 1` would itself be in the annulus set, contradicting maximality.
      have hin : T.max' hne + 1 ∈ (Finset.range (K+1)).filter
          (fun k => (2:ℝ)^k * R ≤ ‖Work.BoseB4.vec n‖) :=
        Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hlt, hup⟩
      have hle : T.max' hne + 1 ≤ T.max' hne := Finset.le_max' T (T.max' hne + 1) hin
      omega
    · -- otherwise `2^(k+1) R ≥ 2^(K+1) R > ‖vec n‖`, contradicting the hypothesis.
      have hlt : K + 1 ≤ T.max' hne + 1 := by omega
      have hp : (2:ℝ)^(K+1) ≤ (2:ℝ)^(T.max' hne + 1) :=
        pow_le_pow_right₀ (by norm_num) hlt
      have hcontra : (2:ℝ)^(K+1) * R ≤ ‖Work.BoseB4.vec n‖ :=
        le_trans (mul_le_mul_of_nonneg_right hp (le_of_lt hRpos)) hup
      linarith [hK n hn]
  -- The summand, abbreviated.
  let g : (Fin 3 → ℤ) → ℝ := fun n => (((1 : ℝ) + ‖Work.BoseB4.vec n‖ ^ 2) ^ s)⁻¹
  have hgnn : ∀ n, 0 ≤ g n := fun n => inv_nonneg.mpr (pow_nonneg (by positivity) s)
  change (∑ n ∈ S, g n) ≤ ∑ k ∈ Finset.range (K+1),
      ∑ n ∈ (S.filter (fun n => (2:ℝ)^k * R ≤ ‖Work.BoseB4.vec n‖)).filter
        (fun n => ¬ ((2:ℝ)^(k+1) * R ≤ ‖Work.BoseB4.vec n‖)), g n
  calc (∑ n ∈ S, g n)
      ≤ ∑ n ∈ S, ∑ k ∈ Finset.range (K+1),
          (if (2:ℝ)^k * R ≤ ‖Work.BoseB4.vec n‖ ∧
             ¬ ((2:ℝ)^(k+1) * R ≤ ‖Work.BoseB4.vec n‖) then g n else 0) := by
        -- each `n` is counted at least once in the double sum, with `g n ≥ 0`
        refine Finset.sum_le_sum (fun n hn => ?_)
        obtain ⟨k0, hk0r, hk0q⟩ := hcover n hn
        have hsingle := Finset.single_le_sum (s := Finset.range (K+1))
          (f := fun k => if (2:ℝ)^k * R ≤ ‖Work.BoseB4.vec n‖ ∧
              ¬ ((2:ℝ)^(k+1) * R ≤ ‖Work.BoseB4.vec n‖) then g n else 0)
          (fun k _ => by
            by_cases h : (2:ℝ)^k * R ≤ ‖Work.BoseB4.vec n‖ ∧
                ¬ ((2:ℝ)^(k+1) * R ≤ ‖Work.BoseB4.vec n‖)
            · rw [if_pos h]; exact hgnn n
            · rw [if_neg h]) hk0r
        exact le_trans (le_of_eq (if_pos hk0q).symm) hsingle
    _ = ∑ k ∈ Finset.range (K+1), ∑ n ∈ S,
          (if (2:ℝ)^k * R ≤ ‖Work.BoseB4.vec n‖ ∧
             ¬ ((2:ℝ)^(k+1) * R ≤ ‖Work.BoseB4.vec n‖) then g n else 0) :=
        Finset.sum_comm
    _ = ∑ k ∈ Finset.range (K+1),
          ∑ n ∈ (S.filter (fun n => (2:ℝ)^k * R ≤ ‖Work.BoseB4.vec n‖)).filter
            (fun n => ¬ ((2:ℝ)^(k+1) * R ≤ ‖Work.BoseB4.vec n‖)), g n := by
        -- `∑_{S.filter (q ∧ r)} = ∑_{S} [q ∧ r]`
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [Finset.sum_filter, Finset.sum_filter]
        refine Finset.sum_congr rfl (fun n _ => ?_)
        by_cases hq : (2:ℝ)^k * R ≤ ‖Work.BoseB4.vec n‖
        · by_cases hr : (2:ℝ)^(k+1) * R ≤ ‖Work.BoseB4.vec n‖
          · rw [if_neg (fun h => h.2 hr), if_pos hq, if_neg (fun h => h hr)]
          · rw [if_pos ⟨hq, hr⟩, if_pos hq, if_pos hr]
        · rw [if_neg (fun h => hq h.1), if_neg hq]

end Work.BoseK15
