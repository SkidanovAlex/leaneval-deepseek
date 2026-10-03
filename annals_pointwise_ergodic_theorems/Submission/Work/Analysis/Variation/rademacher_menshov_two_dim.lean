import Mathlib
import Submission.Work.Analysis.Variation.lp_variation_le_of_monotone_index_two
import Submission.Work.Analysis.Variation.rawLp2_le_incLp2
import Submission.Work.Analysis.Variation.telescope2_rnd

set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped BigOperators ENNReal
open Finset

namespace Work.Analysis.Variation

/-- **Core two-dimensional Rademacher--Menshov estimate.**  For `1 ≤ r`, `K < 2 ^ M`, a function
`a : ℕ → ℕ → ℂ` vanishing on the axes and a monotone `u : Fin (J+1) → ℕ` with values `≤ K`, the
`ℓ^r` norm of the diagonal jumps of `a` along `u` is at most `2` times the sum, over the `M²`
dyadic scale pairs `(m₁, m₂)`, of the second-difference increment norms
`incLp2 r K (2 ^ m₁) (2 ^ m₂) a`.

The proof is the two-dimensional dyadic telescope `telescope2_rnd`, the triangle inequality in
both coordinates, Minkowski over the scales `m₁` and then (for each `m₁`) over `m₂`
(`rpow_sum_sum_le`), and finally the monotone-index two-dimensional `ℓ^r` variation bound
`lp_variation_le_of_monotone_index_two` applied to the raw family `rawH2 a m₁ m₂` at the monotone
index pair `(N ↦ N / 2 ^ m₁, N ↦ N / 2 ^ m₂)`, followed by `rawLp2_le_incLp2`. -/
lemma sum_jumps2_le_incLp2 (r : ℝ) (hr : 1 ≤ r) (K M : ℕ) (hKM : K < 2 ^ M)
    (a : ℕ → ℕ → ℂ) (h1 : ∀ k, a k 0 = 0) (h2 : ∀ k, a 0 k = 0)
    {J : ℕ} (u : Fin (J + 1) → ℕ) (hu : Monotone u) (huK : ∀ i, u i ≤ K) :
    (∑ j : Fin J, ‖a (u j.succ) (u j.succ) - a (u j.castSucc) (u j.castSucc)‖ₑ ^ r) ^ (1 / r)
      ≤ 2 * ∑ m₁ ∈ Finset.range M, ∑ m₂ ∈ Finset.range M,
          incLp2 r K (2 ^ m₁) (2 ^ m₂) a := by
  have hr0 : (0 : ℝ) < r := lt_of_lt_of_le zero_lt_one hr
  have h1r : (0 : ℝ) < 1 / r := one_div_pos.mpr hr0
  have huM : ∀ i : Fin (J + 1), u i < 2 ^ M := fun i => lt_of_le_of_lt (huK i) hKM
  -- Two-dimensional dyadic telescoping, rewritten through the raw family.
  have hatel : ∀ N < 2 ^ M, a N N = ∑ m₁ ∈ Finset.range M, ∑ m₂ ∈ Finset.range M,
      rawH2 a m₁ m₂ (N / 2 ^ m₁) (N / 2 ^ m₂) := by
    intro N hN
    calc a N N = ∑ m₁ ∈ Finset.range M, ∑ m₂ ∈ Finset.range M,
          (a (rnd N m₁) (rnd N m₂) - a (rnd N (m₁ + 1)) (rnd N m₂)
            - a (rnd N m₁) (rnd N (m₂ + 1)) + a (rnd N (m₁ + 1)) (rnd N (m₂ + 1))) :=
          (telescope2_rnd a h1 h2 hN).symm
      _ = ∑ m₁ ∈ Finset.range M, ∑ m₂ ∈ Finset.range M,
            rawH2 a m₁ m₂ (N / 2 ^ m₁) (N / 2 ^ m₂) :=
          Finset.sum_congr rfl fun m₁ _ =>
            Finset.sum_congr rfl fun m₂ _ => (rawH2_eq_rnd a m₁ m₂ N).symm
  -- Each diagonal jump splits into the `M²` scale-pair contributions.
  have hjump : ∀ j : Fin J, a (u j.succ) (u j.succ) - a (u j.castSucc) (u j.castSucc)
      = ∑ m₁ ∈ Finset.range M, ∑ m₂ ∈ Finset.range M,
        (rawH2 a m₁ m₂ (u j.succ / 2 ^ m₁) (u j.succ / 2 ^ m₂)
          - rawH2 a m₁ m₂ (u j.castSucc / 2 ^ m₁) (u j.castSucc / 2 ^ m₂)) := by
    intro j
    calc a (u j.succ) (u j.succ) - a (u j.castSucc) (u j.castSucc)
        = (∑ m₁ ∈ Finset.range M, ∑ m₂ ∈ Finset.range M,
              rawH2 a m₁ m₂ (u j.succ / 2 ^ m₁) (u j.succ / 2 ^ m₂))
          - (∑ m₁ ∈ Finset.range M, ∑ m₂ ∈ Finset.range M,
              rawH2 a m₁ m₂ (u j.castSucc / 2 ^ m₁) (u j.castSucc / 2 ^ m₂)) := by
            rw [hatel (u j.succ) (huM j.succ), hatel (u j.castSucc) (huM j.castSucc)]
      _ = ∑ m₁ ∈ Finset.range M,
            ((∑ m₂ ∈ Finset.range M, rawH2 a m₁ m₂ (u j.succ / 2 ^ m₁) (u j.succ / 2 ^ m₂))
              - (∑ m₂ ∈ Finset.range M,
                  rawH2 a m₁ m₂ (u j.castSucc / 2 ^ m₁) (u j.castSucc / 2 ^ m₂))) :=
            (Finset.sum_sub_distrib
              (fun m₁ => ∑ m₂ ∈ Finset.range M,
                rawH2 a m₁ m₂ (u j.succ / 2 ^ m₁) (u j.succ / 2 ^ m₂))
              (fun m₁ => ∑ m₂ ∈ Finset.range M,
                rawH2 a m₁ m₂ (u j.castSucc / 2 ^ m₁) (u j.castSucc / 2 ^ m₂))).symm
      _ = ∑ m₁ ∈ Finset.range M, ∑ m₂ ∈ Finset.range M,
            (rawH2 a m₁ m₂ (u j.succ / 2 ^ m₁) (u j.succ / 2 ^ m₂)
              - rawH2 a m₁ m₂ (u j.castSucc / 2 ^ m₁) (u j.castSucc / 2 ^ m₂)) :=
            Finset.sum_congr rfl fun m₁ _ =>
              (Finset.sum_sub_distrib
                (fun m₂ => rawH2 a m₁ m₂ (u j.succ / 2 ^ m₁) (u j.succ / 2 ^ m₂))
                (fun m₂ => rawH2 a m₁ m₂ (u j.castSucc / 2 ^ m₁) (u j.castSucc / 2 ^ m₂))).symm
  -- Per-scale-pair estimate: the variation of `rawH2 a m₁ m₂` along the monotone index pair
  -- `(u / 2 ^ m₁, u / 2 ^ m₂)` is bounded by `2 * incLp2`.
  have hscale : ∀ m₁ ∈ Finset.range M, ∀ m₂ ∈ Finset.range M,
      (∑ j : Fin J, ‖rawH2 a m₁ m₂ (u j.succ / 2 ^ m₁) (u j.succ / 2 ^ m₂)
          - rawH2 a m₁ m₂ (u j.castSucc / 2 ^ m₁) (u j.castSucc / 2 ^ m₂)‖ₑ ^ r) ^ (1 / r)
        ≤ 2 * incLp2 r K (2 ^ m₁) (2 ^ m₂) a := by
    intro m₁ _ m₂ _
    have hL := lp_variation_le_of_monotone_index_two hr (rawH2 a m₁ m₂)
      (fun i : Fin (J + 1) => u i / 2 ^ m₁) (fun i : Fin (J + 1) => u i / 2 ^ m₂)
      (fun _ _ hij => Nat.div_le_div_right (hu hij))
      (fun _ _ hij => Nat.div_le_div_right (hu hij))
      (fun i => Nat.lt_succ_of_le (Nat.div_le_div_right (huK i)))
      (fun i => Nat.lt_succ_of_le (Nat.div_le_div_right (huK i)))
    calc (∑ j : Fin J, ‖rawH2 a m₁ m₂ (u j.succ / 2 ^ m₁) (u j.succ / 2 ^ m₂)
            - rawH2 a m₁ m₂ (u j.castSucc / 2 ^ m₁) (u j.castSucc / 2 ^ m₂)‖ₑ ^ r) ^ (1 / r)
        ≤ 2 * rawLp2 r K m₁ m₂ a := by simpa only [rawLp2] using hL
      _ ≤ 2 * incLp2 r K (2 ^ m₁) (2 ^ m₂) a :=
          mul_le_mul' le_rfl (rawLp2_le_incLp2 hr0 K m₁ m₂ a)
  -- Assembly: triangle inequality, then Minkowski over the two families of scales.
  calc (∑ j : Fin J, ‖a (u j.succ) (u j.succ) - a (u j.castSucc) (u j.castSucc)‖ₑ ^ r) ^ (1 / r)
      = (∑ j : Fin J, ‖∑ m₁ ∈ Finset.range M, ∑ m₂ ∈ Finset.range M,
            (rawH2 a m₁ m₂ (u j.succ / 2 ^ m₁) (u j.succ / 2 ^ m₂)
              - rawH2 a m₁ m₂ (u j.castSucc / 2 ^ m₁) (u j.castSucc / 2 ^ m₂))‖ₑ ^ r) ^ (1 / r) := by
          simp only [hjump]
    _ ≤ (∑ j : Fin J, (∑ m₁ ∈ Finset.range M, ∑ m₂ ∈ Finset.range M,
            ‖rawH2 a m₁ m₂ (u j.succ / 2 ^ m₁) (u j.succ / 2 ^ m₂)
              - rawH2 a m₁ m₂ (u j.castSucc / 2 ^ m₁) (u j.castSucc / 2 ^ m₂)‖ₑ) ^ r) ^ (1 / r) := by
          refine ENNReal.rpow_le_rpow (Finset.sum_le_sum fun j _ => ?_) h1r.le
          refine ENNReal.rpow_le_rpow ?_ hr0.le
          calc ‖∑ m₁ ∈ Finset.range M, ∑ m₂ ∈ Finset.range M,
                  (rawH2 a m₁ m₂ (u j.succ / 2 ^ m₁) (u j.succ / 2 ^ m₂)
                    - rawH2 a m₁ m₂ (u j.castSucc / 2 ^ m₁) (u j.castSucc / 2 ^ m₂))‖ₑ
              ≤ ∑ m₁ ∈ Finset.range M, ‖∑ m₂ ∈ Finset.range M,
                    (rawH2 a m₁ m₂ (u j.succ / 2 ^ m₁) (u j.succ / 2 ^ m₂)
                      - rawH2 a m₁ m₂ (u j.castSucc / 2 ^ m₁) (u j.castSucc / 2 ^ m₂))‖ₑ :=
                enorm_sum_le (Finset.range M) _
            _ ≤ ∑ m₁ ∈ Finset.range M, ∑ m₂ ∈ Finset.range M,
                    ‖rawH2 a m₁ m₂ (u j.succ / 2 ^ m₁) (u j.succ / 2 ^ m₂)
                      - rawH2 a m₁ m₂ (u j.castSucc / 2 ^ m₁) (u j.castSucc / 2 ^ m₂)‖ₑ :=
                Finset.sum_le_sum fun m₁ _ => enorm_sum_le (Finset.range M) _
    _ ≤ ∑ m₁ ∈ Finset.range M, (∑ j : Fin J, (∑ m₂ ∈ Finset.range M,
            ‖rawH2 a m₁ m₂ (u j.succ / 2 ^ m₁) (u j.succ / 2 ^ m₂)
              - rawH2 a m₁ m₂ (u j.castSucc / 2 ^ m₁) (u j.castSucc / 2 ^ m₂)‖ₑ) ^ r) ^ (1 / r) :=
          rpow_sum_sum_le (ι := Fin J) (κ := ℕ) hr Finset.univ (Finset.range M)
            (fun m₁ j => ∑ m₂ ∈ Finset.range M,
              ‖rawH2 a m₁ m₂ (u j.succ / 2 ^ m₁) (u j.succ / 2 ^ m₂)
                - rawH2 a m₁ m₂ (u j.castSucc / 2 ^ m₁) (u j.castSucc / 2 ^ m₂)‖ₑ)
    _ ≤ ∑ m₁ ∈ Finset.range M, ∑ m₂ ∈ Finset.range M,
          (∑ j : Fin J, ‖rawH2 a m₁ m₂ (u j.succ / 2 ^ m₁) (u j.succ / 2 ^ m₂)
              - rawH2 a m₁ m₂ (u j.castSucc / 2 ^ m₁) (u j.castSucc / 2 ^ m₂)‖ₑ ^ r) ^ (1 / r) := by
          refine Finset.sum_le_sum fun m₁ _ => ?_
          exact rpow_sum_sum_le (ι := Fin J) (κ := ℕ) hr Finset.univ (Finset.range M)
            (fun m₂ j => ‖rawH2 a m₁ m₂ (u j.succ / 2 ^ m₁) (u j.succ / 2 ^ m₂)
              - rawH2 a m₁ m₂ (u j.castSucc / 2 ^ m₁) (u j.castSucc / 2 ^ m₂)‖ₑ)
    _ ≤ ∑ m₁ ∈ Finset.range M, ∑ m₂ ∈ Finset.range M,
          2 * incLp2 r K (2 ^ m₁) (2 ^ m₂) a := by
          refine Finset.sum_le_sum fun m₁ hm₁ => Finset.sum_le_sum fun m₂ hm₂ => ?_
          exact hscale m₁ hm₁ m₂ hm₂
    _ = 2 * ∑ m₁ ∈ Finset.range M, ∑ m₂ ∈ Finset.range M,
          incLp2 r K (2 ^ m₁) (2 ^ m₂) a := by
          simp only [Finset.mul_sum]

/-- **Two-dimensional Rademacher--Menshov inequality** (Krause--Mirek--Tao, Lemma `2drm`):
for `1 < r < ∞` there is `C = C r > 0` such that for every `K` and every `a : ℕ → ℕ → ℂ` which
vanishes on the axes (`a k 0 = 0`, `a 0 k = 0`),
`‖(a k k)_{k ≤ K}‖_{V^r} ≤ C ∑_{m₁ ≤ log₂ K} ∑_{m₂ ≤ log₂ K} ‖(Δ²a)_{(j₁,j₂)}‖_{ℓ^r}`,
where the right-hand side runs over the dyadic scales `2^{m_i} ≤ K` (sums over
`Finset.range (Nat.log2 K + 1)`) and `Δ²a` over a rectangle with lower-left corner
`(2^m₁ j₁, 2^m₂ j₂)` and side lengths `2^m₁, 2^m₂` (right ends truncated at `K`) is
`blockDelta2`; `incLp2 r K M₁ M₂ a` is the corresponding `ℓ^r` norm over the tiling rectangles.
The left-hand side is `Vr r K` (`Work.Analysis.Variation.Defs`) applied to the diagonal sequence.

Proof strategy (all ingredients are in this directory):
* Fix a monotone `0 = u 0 ≤ … ≤ u J ≤ K` (`iSup_le`) and bound the `ℓ^r` norm of the diagonal
  jumps `a (u (j+1)) (u (j+1)) - a (u j) (u j)`.
* Put `M := Nat.log2 K + 1`, so `2 ^ M > K`; `telescope2_rnd` (`telescope2_rnd.lean`) gives
  `a N N = ∑_{m₁ < M} ∑_{m₂ < M} Δ²_{m₁,m₂}(N)` where `Δ²_{m₁,m₂}(N)` is the mixed second difference
  over `(rnd N (m₁+1), rnd N m₁] × (rnd N (m₂+1), rnd N m₂]`; subtract the expansions for
  `N = u (j+1)` and `N = u j`.
* Minkowski over the `M²` scale pairs (`rpow_sum_sum_le`), reducing to
  `(∑_j ‖Δ²_{m₁,m₂}(u (j+1)) - Δ²_{m₁,m₂}(u j)‖^r)^{1/r}` for each pair.
* `rawH2_eq_rnd` (`RawFamily.lean`): `Δ²_{m₁,m₂}(N) = rawH2 a m₁ m₂ (N / 2 ^ m₁) (N / 2 ^ m₂)`;
  both index maps are monotone, so `lp_variation_le_of_monotone_index_two` (with
  `n_i := K / 2 ^ m_i + 1`) gives the bound `2 * rawLp2 r K m₁ m₂ a`.
* `rawLp2_le_incLp2` converts the raw family into the tiling family.
The constant is `C = 2` (any explicit constant `≥ 2` is acceptable). -/
theorem rademacher_menshov_two_dim (r : ℝ) (hr : 1 < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ (K : ℕ) (a : ℕ → ℕ → ℂ),
      (∀ k, a k 0 = 0) → (∀ k, a 0 k = 0) →
      Vr r K (fun k => a k k) ≤ ENNReal.ofReal C *
        ∑ m₁ ∈ Finset.range (Nat.log2 K + 1), ∑ m₂ ∈ Finset.range (Nat.log2 K + 1),
          incLp2 r K (2 ^ m₁) (2 ^ m₂) a := by
  refine ⟨2, by norm_num, fun K a h1 h2 => ?_⟩
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
  exact sum_jumps2_le_incLp2 r hr1 K (Nat.log2 K + 1) hKM a h1 h2 u hu huK

end Work.Analysis.Variation
