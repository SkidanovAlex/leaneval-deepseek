import Mathlib
import Submission.Work.Analysis.Variation.dyadGridTelescope
import Submission.Work.Analysis.Variation.dyadicGridLevelBound
import Submission.Work.Analysis.Variation.dyadicGridTendsto

set_option autoImplicit false

open scoped BigOperators ENNReal Topology
open Finset Filter

namespace Work.Analysis.Variation

/-- **Dyadic decomposition of the `r`-variation of a continuous function on `[0,1]`.**

For a *continuous* `h : ℝ → ℂ` and a monotone chain `t` in `[0,1]`, the `ℓ^r` norm (`r ≥ 1`) of
the jumps of `h` along `t` is bounded by twice the sum over the dyadic scales `2^{-l}` of the
`ℓ^r` norm of the grid increments of `h` at scale `2^{-l}` (the grid on `[0,1]` being
`j / 2^l`, `j = 1, …, 2^l`).

Proof route (dyadic rounding down): put `σ_l(t) := ⌊2^l t⌋ / 2^l` and `σ_{-1} := 0`, so that
`σ_l(t) ↑ t` and `h(σ_L t) → h t` by continuity. For each `l` the difference
`h(σ_l t) - h(σ_{l-1} t)` is either `0` or a *single* grid increment `Φ_l(j)` at the unique
level-`l` cell with `j := ⌊2^l t⌋` (namely it is `Φ_l(j)` when `j` is odd — then
`σ_{l-1}(t) = (j-1)/2^l` and `σ_l(t) = j/2^l` — and `0` when `j` is even). Hence, writing
`G_l(j) := if Odd j then Φ_l(j) else 0` (with `G_0(1) := h 1 - h 0`), one has the *exact*
telescoping `h(t) - h(t') = ∑_l (G_l(⌊2^l t⌋) - G_l(⌊2^l t'⌋))`. Since `t ↦ ⌊2^l t⌋` is monotone
with values `< 2^l + 1` on `[0,1]`, the monotone-index variation bound
`Work.Analysis.Variation.lp_variation_le_of_monotone_index` gives
`(∑_i |G_l(⌊2^l t_{i+1}⌋) - G_l(⌊2^l t_i⌋)|^r)^{1/r} ≤ 2 (∑_{m < 2^l+1} |G_l m|^r)^{1/r}`, and
`|G_l m| ≤ |Φ_l m|` for `m ∈ Icc 1 (2^l)` with `G_l` vanishing elsewhere, giving the stated bound.
The infinite sum over `l` is handled by truncating at `L` (exact telescoping of `h (dyadPt L ·)`,
Minkowski's inequality in `ℓ^r` over the levels, then the level bounds) and letting `L → ∞` using
`h(σ_L t) → h t`.  The three ingredients are the lemmas `dyadGridTelescope` (the exact telescoping),
`dyadicGridLevelBound` (the single-level bound) and `dyadicGridTendsto` (the limit of the truncated
variations), with the dyadic vocabulary in `DyadicGrid.lean`. -/
theorem dyadicVariationLeGrid (r : ℝ) (hr : 1 ≤ r) (h : ℝ → ℂ) (hc : Continuous h)
    {J : ℕ} (t : Fin (J + 1) → ℝ) (ht : Monotone t) (ht0 : ∀ i, 0 ≤ t i)
    (ht1 : ∀ i, t i ≤ 1) :
    (∑ i : Fin J, ‖h (t i.succ) - h (t i.castSucc)‖ₑ ^ r) ^ (1 / r)
      ≤ 2 * ∑' (l : ℕ), (∑ j ∈ Finset.Icc (1:ℕ) (2 ^ l),
          ‖h ((j : ℝ) / 2 ^ l) - h (((j : ℝ) - 1) / 2 ^ l)‖ₑ ^ r) ^ (1 / r) := by
  classical
  have hr0 : (0 : ℝ) < r := lt_of_lt_of_le zero_lt_one hr
  have h1r : (0 : ℝ) < 1 / r := div_pos zero_lt_one hr0
  -- For each truncation level `L` the level-`L` dyadic variation is bounded by the full right hand
  -- side: the telescoping identity writes each jump of `h` along `t` as a sum of level jumps, the
  -- triangle inequality and Minkowski's inequality split that sum off the `ℓ^r` norm, and each
  -- level is controlled by `dyadicGridLevelBound`.
  have hmain : ∀ L : ℕ,
      (∑ i : Fin J, ‖h (dyadPt L (t i.succ)) - h (dyadPt L (t i.castSucc))‖ₑ ^ r) ^ (1 / r)
        ≤ 2 * ∑' (l : ℕ), dyadGridLp r h l := by
    intro L
    -- triangle inequality, after the exact telescoping of `h (dyadPt L ·)`
    have step1 : (∑ i : Fin J, ‖h (dyadPt L (t i.succ)) - h (dyadPt L (t i.castSucc))‖ₑ ^ r)
        ≤ ∑ i : Fin J, (∑ k ∈ Finset.range (L + 1),
            ‖dyadJump h k (dyadQ k (t i.succ)) - dyadJump h k (dyadQ k (t i.castSucc))‖ₑ) ^ r := by
      refine Finset.sum_le_sum (fun i _ => ?_)
      rw [dyadGridTelescope h L (ht0 i.castSucc) (ht1 i.castSucc) (ht0 i.succ) (ht1 i.succ)]
      exact ENNReal.rpow_le_rpow (enorm_sum_le _ _) hr0.le
    -- Minkowski's inequality in `ℓ^r` over the dyadic levels
    have step2 : (∑ i : Fin J, (∑ k ∈ Finset.range (L + 1),
            ‖dyadJump h k (dyadQ k (t i.succ)) - dyadJump h k (dyadQ k (t i.castSucc))‖ₑ) ^ r)
            ^ (1 / r)
        ≤ ∑ k ∈ Finset.range (L + 1),
            (∑ i : Fin J,
              ‖dyadJump h k (dyadQ k (t i.succ)) - dyadJump h k (dyadQ k (t i.castSucc))‖ₑ ^ r)
              ^ (1 / r) := by
      have hh := rpow_sum_sum_le hr (Finset.univ : Finset (Fin J)) (Finset.range (L + 1))
        (fun k (i : Fin J) =>
          ‖dyadJump h k (dyadQ k (t i.succ)) - dyadJump h k (dyadQ k (t i.castSucc))‖ₑ)
      simpa using hh
    -- the single-level bounds and the passage to the infinite sum
    have step3 : ∑ k ∈ Finset.range (L + 1),
            (∑ i : Fin J,
              ‖dyadJump h k (dyadQ k (t i.succ)) - dyadJump h k (dyadQ k (t i.castSucc))‖ₑ ^ r)
              ^ (1 / r)
        ≤ 2 * ∑' (l : ℕ), dyadGridLp r h l := by
      calc _ ≤ ∑ k ∈ Finset.range (L + 1), 2 * dyadGridLp r h k :=
              Finset.sum_le_sum (fun k _ => dyadicGridLevelBound r hr h t ht ht0 ht1 k)
        _ ≤ ∑' (l : ℕ), 2 * dyadGridLp r h l := by
              rw [ENNReal.tsum_eq_iSup_nat]
              exact le_iSup (fun i => ∑ a ∈ Finset.range i, 2 * dyadGridLp r h a) (L + 1)
        _ = 2 * ∑' (l : ℕ), dyadGridLp r h l := ENNReal.tsum_mul_left
    calc (∑ i : Fin J, ‖h (dyadPt L (t i.succ)) - h (dyadPt L (t i.castSucc))‖ₑ ^ r) ^ (1 / r)
        ≤ (∑ i : Fin J, (∑ k ∈ Finset.range (L + 1),
            ‖dyadJump h k (dyadQ k (t i.succ)) - dyadJump h k (dyadQ k (t i.castSucc))‖ₑ) ^ r)
            ^ (1 / r) := ENNReal.rpow_le_rpow step1 h1r.le
      _ ≤ ∑ k ∈ Finset.range (L + 1),
            (∑ i : Fin J,
              ‖dyadJump h k (dyadQ k (t i.succ)) - dyadJump h k (dyadQ k (t i.castSucc))‖ₑ ^ r)
              ^ (1 / r) := step2
      _ ≤ 2 * ∑' (l : ℕ), dyadGridLp r h l := step3
  -- passage to the limit `L → ∞`: the level-`L` variations converge to the exact variation.
  exact le_of_tendsto (dyadicGridTendsto r h hc t ht0 ht1) (Eventually.of_forall hmain)

end Work.Analysis.Variation
