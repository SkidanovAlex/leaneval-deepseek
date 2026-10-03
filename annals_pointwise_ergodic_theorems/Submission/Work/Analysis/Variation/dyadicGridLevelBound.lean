import Mathlib
import Submission.Work.Analysis.Variation.DyadicGrid
import Submission.Work.Analysis.Variation.lp_variation_le_of_monotone_index

namespace Work.Analysis.Variation

/-- **The `ℓ^r` variation of one dyadic level of `h`, controlled by the grid increments.**

For `h : ℝ → ℂ`, a monotone chain `t : Fin (J+1) → ℝ` with values in `[0,1]`, and `r ≥ 1`, the
`ℓ^r` norm of the successive differences of the signed grid increments `dyadJump h l (dyadQ l ·)`
along the chain `t` is at most `2` times the `ℓ^r` norm of the level-`l` grid increments of `h`:

`(∑_i ‖dyadJump h l (⌊2^l t_{i+1}⌋) - dyadJump h l (⌊2^l t_i⌋)‖^r)^{1/r} ≤ 2 dyadGridLp r h l`.

This is `Work.Analysis.Variation.lp_variation_le_of_monotone_index` applied to the monotone index map
`i ↦ dyadQ l (t i) < 2^l + 1`, combined with the fact that `‖dyadJump h l m‖ ≤ ‖h (m/2^l) - h ((m-1)/2^l)‖`
with `dyadJump h l m = 0` for even `m` (so only the indices `1 ≤ m ≤ 2^l` contribute).
The file should be in namespace `Work.Analysis.Variation`, importing both modules in `depends_on`. -/
theorem dyadicGridLevelBound (r : ℝ) (hr : 1 ≤ r) (h : ℝ → ℂ) {J : ℕ} (t : Fin (J + 1) → ℝ)
    (ht : Monotone t) (ht0 : ∀ i, 0 ≤ t i) (ht1 : ∀ i, t i ≤ 1) (l : ℕ) :
    (∑ i : Fin J, ‖dyadJump h l (dyadQ l (t i.succ)) - dyadJump h l (dyadQ l (t i.castSucc))‖ₑ ^ r)
        ^ (1 / r)
      ≤ 2 * dyadGridLp r h l := by
  classical
  have hr0 : (0 : ℝ) < r := lt_of_lt_of_le zero_lt_one hr
  have h1r : (0 : ℝ) < 1 / r := div_pos zero_lt_one hr0
  -- The index map `j ↦ dyadQ l (t j)` is monotone and takes values in `{0, …, 2^l}`.
  have hpmono : Monotone (fun j : Fin (J + 1) => dyadQ l (t j)) :=
    fun a b hab => dyadQ_mono l (ht hab)
  have hpn : ∀ j : Fin (J + 1), dyadQ l (t j) < 2 ^ l + 1 :=
    fun j => dyadQ_lt_two_pow_add_one (ht0 j) (ht1 j) l
  have hmain := lp_variation_le_of_monotone_index hr (fun m => dyadJump h l m)
    (fun j => dyadQ l (t j)) hpmono hpn
  -- The `ℓ^r` norm over `{0, …, 2^l}` of `dyadJump h l` is at most the grid increment norm:
  -- the `x = 0` term vanishes (being an even index) and the rest is bounded pointwise.
  have hstep : ∑ x ∈ Finset.range (2 ^ l + 1), ‖dyadJump h l x‖ₑ ^ r
      ≤ ∑ j ∈ Finset.Icc (1 : ℕ) (2 ^ l),
          ‖h ((j : ℝ) / 2 ^ l) - h (((j : ℝ) - 1) / 2 ^ l)‖ₑ ^ r := by
    have hsub : Finset.Icc (1 : ℕ) (2 ^ l) ⊆ Finset.range (2 ^ l + 1) := by
      intro x hx
      rw [Finset.mem_Icc] at hx
      exact Finset.mem_range.mpr (by omega)
    have hzero : ∀ x ∈ Finset.range (2 ^ l + 1), x ∉ Finset.Icc (1 : ℕ) (2 ^ l) →
        ‖dyadJump h l x‖ₑ ^ r = 0 := by
      intro x hx hxI
      rw [Finset.mem_range] at hx
      have hx0 : x = 0 := by
        by_contra hne
        exact hxI (by
          rw [Finset.mem_Icc]
          exact ⟨Nat.one_le_iff_ne_zero.mpr hne, by omega⟩)
      subst hx0
      rw [dyadJump_eq_zero_of_even h l 0 (⟨0, rfl⟩), enorm_zero,
        ENNReal.zero_rpow_of_pos hr0]
    rw [← Finset.sum_subset hsub hzero]
    exact Finset.sum_le_sum fun j _ => ENNReal.rpow_le_rpow (enorm_dyadJump_le h l j) hr0.le
  calc (∑ i : Fin J,
          ‖dyadJump h l (dyadQ l (t i.succ)) - dyadJump h l (dyadQ l (t i.castSucc))‖ₑ ^ r)
        ^ (1 / r)
      = (∑ j : Fin J,
          ‖(fun m => dyadJump h l m) ((fun j : Fin (J + 1) => dyadQ l (t j)) j.succ)
            - (fun m => dyadJump h l m) ((fun j : Fin (J + 1) => dyadQ l (t j)) j.castSucc)‖ₑ ^ r)
        ^ (1 / r) := rfl
    _ ≤ 2 * (∑ x ∈ Finset.range (2 ^ l + 1), ‖(fun m => dyadJump h l m) x‖ₑ ^ r)
        ^ (1 / r) := hmain
    _ ≤ 2 * dyadGridLp r h l := by
        rw [dyadGridLp]
        exact mul_le_mul_of_nonneg_left (ENNReal.rpow_le_rpow hstep h1r.le) (by norm_num)

end Work.Analysis.Variation
