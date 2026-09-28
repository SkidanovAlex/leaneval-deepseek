import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.lam_basic
import Submission.Work.HP.rk_le_card
import Submission.Work.HP.lam_prod_lower

/-!
# The Schmidt-type sum bound `Work.HP.sum_bound_rank2`

For a lattice `L ⊆ ℤ^ι` of rank `r = rk L ≥ 2`, with successive minima `λ_i = lam L i`, and a
parameter `Y` with `1 ≤ Y` and `λ_2 ≤ Y`, the sum

`∑_{i=0}^{r} Y^{r-i} / (λ_1 λ_2 ⋯ λ_{r-i})`

is at most `(card ι + 1) · Y^r / (λ_1 · λ_2^{r-1})`.

Indeed, the sum has `r + 1 ≤ card ι + 1` terms (`rk_le_card`), and every term corresponding to
`k = r - i ∈ [0,r]` is at most `T := Y^r/(λ_1 λ_2^{r-1})`:

* for `k ≥ 1`, `∏_{j<k} λ_{j+1} ≥ λ_1 λ_2^{k-1}` (`lam_prod_lower`, using monotonicity of the
  successive minima), and `Y^k/(λ_1 λ_2^{k-1}) ≤ Y^r/(λ_1 λ_2^{r-1})` because `Y ≥ λ_2`;
* for `k = 0` the term is `1`, and `1 ≤ T` because `λ_1 ≤ λ_2 ≤ Y`.
-/

set_option autoImplicit false

noncomputable section

open Finset

namespace Work.HP

/-- Real auxiliary.  For `0 < l1 ≤ l2 ≤ Y` with `1 ≤ Y`, the quantity `Y^n / (l1 * l2^(n-1))`
is nondecreasing in `n ≥ 1`.  Equivalently `Y / l2 ≥ 1`, the factor `l1` cancelling. -/
private lemma ratio_bound {l1 l2 Y : ℝ} (hl1 : 0 < l1) (hl12 : l1 ≤ l2) (hl2Y : l2 ≤ Y)
    (hY : 1 ≤ Y) {k r : ℕ} (hk1 : 1 ≤ k) (hkr : k ≤ r) :
    Y ^ k / (l1 * l2 ^ (k - 1)) ≤ Y ^ r / (l1 * l2 ^ (r - 1)) := by
  have hl2 : 0 < l2 := lt_of_lt_of_le hl1 hl12
  have hYpos : 0 < Y := lt_of_lt_of_le zero_lt_one hY
  have hdenk : 0 < l1 * l2 ^ (k - 1) := mul_pos hl1 (pow_pos hl2 _)
  have hdenr : 0 < l1 * l2 ^ (r - 1) := mul_pos hl1 (pow_pos hl2 _)
  rw [div_le_div_iff₀ hdenk hdenr]
  have key : Y ^ k * l2 ^ (r - 1) ≤ Y ^ r * l2 ^ (k - 1) := by
    have h1 : l2 ^ (r - 1) = l2 ^ (k - 1) * l2 ^ (r - k) := by
      rw [← pow_add]; congr 1; omega
    have h2 : Y ^ r = Y ^ k * Y ^ (r - k) := by
      rw [← pow_add]; congr 1; omega
    rw [h1, h2]
    have h3 : l2 ^ (r - k) ≤ Y ^ (r - k) := pow_le_pow_left₀ hl2.le hl2Y _
    have h4 : (0 : ℝ) ≤ Y ^ k * l2 ^ (k - 1) :=
      mul_nonneg (pow_nonneg hYpos.le k) (pow_nonneg hl2.le (k - 1))
    have h5 : Y ^ k * l2 ^ (k - 1) * l2 ^ (r - k) ≤ Y ^ k * l2 ^ (k - 1) * Y ^ (r - k) :=
      mul_le_mul_of_nonneg_left h3 h4
    nlinarith [h5]
  calc Y ^ k * (l1 * l2 ^ (r - 1)) = l1 * (Y ^ k * l2 ^ (r - 1)) := by ring
    _ ≤ l1 * (Y ^ r * l2 ^ (k - 1)) := mul_le_mul_of_nonneg_left key hl1.le
    _ = Y ^ r * (l1 * l2 ^ (k - 1)) := by ring

/-- Real auxiliary.  For `0 < l1 ≤ l2 ≤ Y` and `1 ≤ r`, one has `1 ≤ Y^r / (l1 * l2^(r-1))`,
i.e. the `k = 0` term of the sum is dominated by `Y^r/(l1 l2^{r-1})`. -/
private lemma one_le_ratio {l1 l2 Y : ℝ} (hl1 : 0 < l1) (hl12 : l1 ≤ l2) (hl2Y : l2 ≤ Y)
    (_hY : 1 ≤ Y) {r : ℕ} (hr : 1 ≤ r) : 1 ≤ Y ^ r / (l1 * l2 ^ (r - 1)) := by
  have hl2 : 0 < l2 := lt_of_lt_of_le hl1 hl12
  have hden : 0 < l1 * l2 ^ (r - 1) := mul_pos hl1 (pow_pos hl2 _)
  rw [le_div_iff₀ hden, one_mul]
  calc l1 * l2 ^ (r - 1) ≤ l2 * l2 ^ (r - 1) :=
        mul_le_mul_of_nonneg_right hl12 (pow_nonneg hl2.le _)
    _ = l2 ^ r := by rw [← pow_succ']; congr 1; omega
    _ ≤ Y ^ r := pow_le_pow_left₀ hl2.le hl2Y r

/-- The single-term bound: for `k ≤ rk L` the term `Y^k / (λ_1 ⋯ λ_k)` of the sum is bounded
by `Y^{rk L}/(λ_1 λ_2^{rk L - 1})`. -/
private lemma term_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : Submodule ℤ (ι → ℤ)) {Y : ℝ} (hY : 1 ≤ Y) (hr : 2 ≤ rk L) (hlam : lam L 2 ≤ Y)
    {k : ℕ} (hk : k ≤ rk L) :
    Y ^ k / (∏ j ∈ Finset.range k, lam L (j + 1))
      ≤ Y ^ rk L / (lam L 1 * lam L 2 ^ (rk L - 1)) := by
  have hYpos : 0 < Y := lt_of_lt_of_le zero_lt_one hY
  have hrk1 : 1 ≤ rk L := le_trans (by norm_num) hr
  have hl1 : 0 < lam L 1 := lam_pos L le_rfl hrk1
  have hl2 : 0 < lam L 2 := lam_pos L (by norm_num) hr
  have hl12 : lam L 1 ≤ lam L 2 := lam_mono L (by norm_num) hr
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · subst hk0
    have hL : Y ^ 0 / (∏ j ∈ Finset.range 0, lam L (j + 1)) = 1 := by simp
    rw [hL]
    exact one_le_ratio hl1 hl12 hlam hY hrk1
  · have hk1 : 1 ≤ k := Nat.succ_le_of_lt hkpos
    have hprod : lam L 1 * lam L 2 ^ (k - 1) ≤ ∏ j ∈ Finset.range k, lam L (j + 1) :=
      lam_prod_lower L hk1 hk
    have hden : 0 < lam L 1 * lam L 2 ^ (k - 1) := mul_pos hl1 (pow_pos hl2 _)
    calc Y ^ k / (∏ j ∈ Finset.range k, lam L (j + 1))
        ≤ Y ^ k / (lam L 1 * lam L 2 ^ (k - 1)) :=
          div_le_div_of_nonneg_left (pow_nonneg hYpos.le k) hden hprod
      _ ≤ Y ^ rk L / (lam L 1 * lam L 2 ^ (rk L - 1)) :=
          ratio_bound hl1 hl12 hlam hY hk1 hk

theorem sum_bound_rank2 {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : Submodule ℤ (ι → ℤ)) {Y : ℝ} (hY : 1 ≤ Y) (hr : 2 ≤ rk L) (hlam : lam L 2 ≤ Y) :
    (∑ i ∈ Finset.range (rk L + 1),
        Y ^ (rk L - i) / ∏ j ∈ Finset.range (rk L - i), lam L (j + 1))
      ≤ (Fintype.card ι + 1 : ℝ) *
          (Y ^ rk L / (lam L 1 * lam L 2 ^ (rk L - 1))) := by
  have hYpos : 0 < Y := lt_of_lt_of_le zero_lt_one hY
  have hrk1 : 1 ≤ rk L := le_trans (by norm_num) hr
  have hl1 : 0 < lam L 1 := lam_pos L le_rfl hrk1
  have hl2 : 0 < lam L 2 := lam_pos L (by norm_num) hr
  have hTnn : (0 : ℝ) ≤ Y ^ rk L / (lam L 1 * lam L 2 ^ (rk L - 1)) :=
    div_nonneg (pow_nonneg hYpos.le _) (mul_pos hl1 (pow_pos hl2 _)).le
  refine le_trans (Finset.sum_le_sum fun i _ => term_bound L hY hr hlam (Nat.sub_le (rk L) i)) ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  refine mul_le_mul_of_nonneg_right ?_ hTnn
  have hcard : (rk L : ℝ) ≤ (Fintype.card ι : ℝ) := by exact_mod_cast rk_le_card L
  push_cast
  linarith

end Work.HP
