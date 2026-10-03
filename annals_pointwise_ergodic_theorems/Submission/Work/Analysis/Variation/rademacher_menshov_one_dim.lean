import Mathlib
import Submission.Work.Analysis.Variation.lp_variation_le_of_monotone_index
import Submission.Work.Analysis.Variation.rawLp_le_incLp

set_option autoImplicit false

open scoped BigOperators ENNReal
open Finset

namespace Work.Analysis.Variation

/-- **Core one-dimensional Rademacher--Menshov estimate.**  For `1 ≤ r`, `K < 2 ^ M`, a sequence
`a` with `a 0 = 0` and a monotone `u : Fin (J+1) → ℕ` with values `≤ K`, the `ℓ^r` norm of the
jumps of `a` along `u` is at most `2` times the sum of the increment norms `incLp r K (2 ^ m) a`
over the dyadic scales `2 ^ m`, `m < M`.

The proof is the dyadic telescope `a N = ∑_{m < M} (a (rnd N m) - a (rnd N (m+1)))`
(`telescope_rnd`), Minkowski's inequality over the `M` scales (`rpow_sum_sum_le`), and the
monotone-index `ℓ^r` variation bound `lp_variation_le_of_monotone_index` applied to the raw family
`rawH a m` at the monotone index `N ↦ N / 2 ^ m`, followed by `rawLp_le_incLp`. -/
lemma sum_jumps_le_incLp (r : ℝ) (hr : 1 ≤ r) (K M : ℕ) (hKM : K < 2 ^ M) (a : ℕ → ℂ)
    (ha0 : a 0 = 0) {J : ℕ} (u : Fin (J + 1) → ℕ) (hu : Monotone u) (huK : ∀ i, u i ≤ K) :
    (∑ j : Fin J, ‖a (u j.succ) - a (u j.castSucc)‖ₑ ^ r) ^ (1 / r)
      ≤ 2 * ∑ m ∈ Finset.range M, incLp r K (2 ^ m) a := by
  have hr0 : (0 : ℝ) < r := lt_of_lt_of_le zero_lt_one hr
  have h1r : (0 : ℝ) < 1 / r := one_div_pos.mpr hr0
  have huM : ∀ i : Fin (J + 1), u i < 2 ^ M := fun i => lt_of_le_of_lt (huK i) hKM
  -- Dyadic telescoping: `a N` is the sum of the increments `a (rnd N m) - a (rnd N (m+1))`.
  have hatel : ∀ N < 2 ^ M, a N = ∑ m ∈ Finset.range M, (a (rnd N m) - a (rnd N (m + 1))) := by
    intro N hN
    rw [telescope_rnd a hN, ha0, sub_zero]
  -- Each jump of `a` along `u` splits into the `M` scale contributions.
  have hjump : ∀ j : Fin J, a (u j.succ) - a (u j.castSucc)
      = ∑ m ∈ Finset.range M, ((a (rnd (u j.succ) m) - a (rnd (u j.succ) (m + 1)))
          - (a (rnd (u j.castSucc) m) - a (rnd (u j.castSucc) (m + 1)))) := by
    intro j
    rw [hatel (u j.succ) (huM j.succ), hatel (u j.castSucc) (huM j.castSucc)]
    exact (Finset.sum_sub_distrib (s := Finset.range M)
      (fun m => a (rnd (u j.succ) m) - a (rnd (u j.succ) (m + 1)))
      (fun m => a (rnd (u j.castSucc) m) - a (rnd (u j.castSucc) (m + 1)))).symm
  -- Per-scale estimate: the jumps at scale `2 ^ m` of `rawH a m` along the monotone index
  -- `i ↦ u i / 2 ^ m`.
  have hscale : ∀ m ∈ Finset.range M,
      (∑ j : Fin J, ‖(a (rnd (u j.succ) m) - a (rnd (u j.succ) (m + 1)))
          - (a (rnd (u j.castSucc) m) - a (rnd (u j.castSucc) (m + 1)))‖ₑ ^ r) ^ (1 / r)
        ≤ 2 * incLp r K (2 ^ m) a := by
    intro m _
    have hraw : ∀ N : ℕ, a (rnd N m) - a (rnd N (m + 1)) = rawH a m (N / 2 ^ m) :=
      fun N => (rawH_eq_rnd a m N).symm
    simp only [hraw]
    have hmon : Monotone (fun i : Fin (J + 1) => u i / 2 ^ m) :=
      fun i j hij => Nat.div_le_div_right (hu hij)
    have hn : ∀ i : Fin (J + 1), u i / 2 ^ m < K / 2 ^ m + 1 :=
      fun i => Nat.lt_succ_of_le (Nat.div_le_div_right (huK i))
    have hL := lp_variation_le_of_monotone_index hr (rawH a m)
      (fun i : Fin (J + 1) => u i / 2 ^ m) hmon hn
    calc (∑ j : Fin J, ‖rawH a m (u j.succ / 2 ^ m)
            - rawH a m (u j.castSucc / 2 ^ m)‖ₑ ^ r) ^ (1 / r)
        ≤ 2 * rawLp r K m a := by simpa only [rawLp] using hL
      _ ≤ 2 * incLp r K (2 ^ m) a := mul_le_mul' le_rfl (rawLp_le_incLp hr0 K m a)
  -- Assemble: triangle inequality, Minkowski over the `M` scales, then the per-scale bound.
  calc (∑ j : Fin J, ‖a (u j.succ) - a (u j.castSucc)‖ₑ ^ r) ^ (1 / r)
      = (∑ j : Fin J, ‖∑ m ∈ Finset.range M, ((a (rnd (u j.succ) m) - a (rnd (u j.succ) (m + 1)))
            - (a (rnd (u j.castSucc) m) - a (rnd (u j.castSucc) (m + 1))))‖ₑ ^ r) ^ (1 / r) := by
        simp only [hjump]
    _ ≤ (∑ j : Fin J, (∑ m ∈ Finset.range M, ‖(a (rnd (u j.succ) m) - a (rnd (u j.succ) (m + 1)))
            - (a (rnd (u j.castSucc) m) - a (rnd (u j.castSucc) (m + 1)))‖ₑ) ^ r) ^ (1 / r) := by
        refine ENNReal.rpow_le_rpow (Finset.sum_le_sum fun j _ => ?_) h1r.le
        exact ENNReal.rpow_le_rpow (enorm_sum_le (Finset.range M) _) hr0.le
    _ ≤ ∑ m ∈ Finset.range M, (∑ j : Fin J, ‖(a (rnd (u j.succ) m) - a (rnd (u j.succ) (m + 1)))
            - (a (rnd (u j.castSucc) m) - a (rnd (u j.castSucc) (m + 1)))‖ₑ ^ r) ^ (1 / r) :=
        rpow_sum_sum_le hr Finset.univ (Finset.range M) _
    _ ≤ ∑ m ∈ Finset.range M, 2 * incLp r K (2 ^ m) a := Finset.sum_le_sum hscale
    _ = 2 * ∑ m ∈ Finset.range M, incLp r K (2 ^ m) a := (Finset.mul_sum _ _ 2).symm

/-- **One-dimensional Rademacher--Menshov inequality** (Muckenhoupt--Stein--Zygmund, Lemma 2.5
pp. 534; the one-dimensional case of the paper's Lemma `2drm`): for `1 < r < ∞` there is
`C = C r > 0` such that for every `K` and every `a : ℕ → ℂ` with `a 0 = 0`,
`‖(a k)_{k ≤ K}‖_{V^r} ≤ C ∑_{m ≤ log₂ K} ‖(a (2^m (j+1)) - a (2^m j))_j‖_{ℓ^r}`,
where the right-hand side runs over the dyadic scales `2 ^ m ≤ K` (the sum over
`m ∈ Finset.range (Nat.log2 K + 1)`) and the `j`-sum runs over the blocks of size `2^m` tiling
`(0, K]` (the last block truncated at `K`).  `Vr r K a` (`Work.Analysis.Variation.Defs`) is the
truncated variation seminorm: the supremum over monotone `0 = u 0 ≤ … ≤ u J ≤ K` of the `ℓ^r` norm
of the jumps; `incLp r K M a` is the `ℓ^r` norm of the increments over the size-`M` tiling.

Proof strategy (all ingredients are in this directory):
* `Vr` is a supremum (`iSup_le`), so fix `J` and `0 = u 0 ≤ … ≤ u J ≤ K` and bound the `ℓ^r` norm
  of the jumps `a (u (j+1)) - a (u j)`.
* Put `M := Nat.log2 K + 1`, so that `2 ^ M > K ≥ N` for every `N ≤ K`
  (`Nat.log2_lt`); `telescope_rnd` (`Dyadic.lean`) gives
  `a N = ∑_{m < M} (a (rnd N m) - a (rnd N (m+1)))`, hence each jump is
  `∑_{m < M} (d m (u (j+1)) - d m (u j))` with `d m N = a (rnd N m) - a (rnd N (m+1))`.
* Minkowski over the `M` scales (`rpow_sum_sum_le`) reduces to bounding, for each `m < M`,
  `(∑_j ‖d m (u (j+1)) - d m (u j)‖^r)^{1/r}`.
* `rawH_eq_rnd` (`RawFamily.lean`): `d m N = rawH a m (N / 2 ^ m)`; as `N ↦ N / 2 ^ m` is monotone,
  `lp_variation_le_of_monotone_index` (with `n := K / 2 ^ m + 1`) gives
  `(∑_j ‖d m (u (j+1)) - d m (u j)‖^r)^{1/r} ≤ 2 * rawLp r K m a`.
* `rawLp_le_incLp` gives `rawLp r K m a ≤ incLp r K (2 ^ m) a`.
* Summing over `m < M` gives exactly the displayed right-hand side.
The constant is `C = 2` (any explicit constant `≥ 2` is acceptable). -/
theorem rademacher_menshov_one_dim (r : ℝ) (hr : 1 < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ (K : ℕ) (a : ℕ → ℂ), a 0 = 0 →
      Vr r K a ≤ ENNReal.ofReal C *
        ∑ m ∈ Finset.range (Nat.log2 K + 1), incLp r K (2 ^ m) a := by
  refine ⟨2, by norm_num, fun K a ha0 => ?_⟩
  have hr1 : 1 ≤ r := le_of_lt hr
  have hKM : K < 2 ^ (Nat.log2 K + 1) := by
    rcases Nat.eq_zero_or_pos K with hK0 | hK0
    · subst hK0
      rw [Nat.log2_zero]
      norm_num
    · exact (Nat.log2_lt (n := K) (k := Nat.log2 K + 1) hK0.ne').mp
        (Nat.lt_succ_self (Nat.log2 K))
  rw [show ENNReal.ofReal (2 : ℝ) = (2 : ℝ≥0∞) from by simp]
  unfold Vr
  apply iSup_le; intro J
  apply iSup_le; intro u
  apply iSup_le; intro hu
  apply iSup_le; intro hu0
  apply iSup_le; intro huK
  exact sum_jumps_le_incLp r hr1 K (Nat.log2 K + 1) hKM a ha0 u hu huK

end Work.Analysis.Variation
