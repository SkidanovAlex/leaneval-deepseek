/-
Copyright: the formalization team of the Vinogradov mean value theorem project.
-/
import Submission.Vinogradov.DescentLevel
import Submission.Commons.Combinatorics.LevelBlocks.card_filter_blkIdx_le
import Submission.Commons.Combinatorics.LevelBlocks.pow_step_reaches_half
import Submission.Commons.Analysis.Asymptotics.log_add_one_rpow_le_mul_rpow
import Submission.Commons.Analysis.Asymptotics.pow_const_le_mul_rpow

/-!
# The tower of the scale descent (GLYZ §3.3, Lemma 3.6)

This module chains the one-step `lvl2_step` of `DescentLevel.lean` along a tower of levels
`1 = n 0 | n 1 | ... | n K ≈ m`, giving GLYZ Lemma 3.6: `ℓ²`-decoupling for a general curve of
degree `l` with torsion, from the moment-curve theorem at degree `l`.

The step function is `lvlStep l n = 2 * max 1 ⌊n^{1/l}⌋`, which satisfies

* `n^{1/l} ≤ lvlStep l n`  (so the levels grow at least like `n_{j+1} ≥ n_j^{1+1/l}`, giving
  `K = O(log log m)` steps), and
* `(lvlStep l n)^l ≤ 2^l n ≤ (Ctube l)^l n`  (the numerical condition `hb` of `lvl2_step`).
-/

noncomputable section
open MeasureTheory Complex Classical Filter
open scoped Real BigOperators Topology RealInnerProductSpace ENNReal NNReal

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.style.emptyLine false
set_option linter.unusedVariables false
set_option maxHeartbeats 8000000

namespace Submission.Vinogradov

/-! ## 1. The step function of the tower -/

/-- The number of sub-blocks at level `n`: twice the integer part of `n^{1/l}` (at least `2`). -/
noncomputable def lvlStep (l n : ℕ) : ℕ := 2 * max 1 ⌊(n : ℝ) ^ (1 / (l : ℝ))⌋₊

lemma lvlStep_two_le (l n : ℕ) : 2 ≤ lvlStep l n := by
  rw [lvlStep]
  have h : 1 ≤ max 1 ⌊(n : ℝ) ^ (1 / (l : ℝ))⌋₊ := le_max_left _ _
  omega

lemma lvlStep_pos (l n : ℕ) : 0 < lvlStep l n := lt_of_lt_of_le (by norm_num) (lvlStep_two_le l n)

/-- The step function dominates `n^{1/l}`. -/
lemma le_lvlStep {l n : ℕ} (hn : 1 ≤ n) :
    (n : ℝ) ^ (1 / (l : ℝ)) ≤ (lvlStep l n : ℝ) := by
  have hx1 : (1 : ℝ) ≤ (n : ℝ) ^ (1 / (l : ℝ)) :=
    Real.one_le_rpow (by exact_mod_cast hn) (by positivity)
  have hfloor : (n : ℝ) ^ (1 / (l : ℝ)) / 2 ≤ (⌊(n : ℝ) ^ (1 / (l : ℝ))⌋₊ : ℝ) := by
    rcases lt_or_ge ((n : ℝ) ^ (1 / (l : ℝ))) 2 with h2 | h2
    · have h1 : (1 : ℝ) ≤ (⌊(n : ℝ) ^ (1 / (l : ℝ))⌋₊ : ℝ) := by
        have hh : (((1 : ℕ)) : ℝ) ≤ (n : ℝ) ^ (1 / (l : ℝ)) := by simpa using hx1
        exact_mod_cast (Nat.le_floor hh)
      linarith
    · have h3 : (n : ℝ) ^ (1 / (l : ℝ)) - 1 < (⌊(n : ℝ) ^ (1 / (l : ℝ))⌋₊ : ℝ) := by
        have := Nat.lt_floor_add_one ((n : ℝ) ^ (1 / (l : ℝ)))
        linarith
      linarith
  calc (n : ℝ) ^ (1 / (l : ℝ)) = 2 * ((n : ℝ) ^ (1 / (l : ℝ)) / 2) := by ring
    _ ≤ 2 * (⌊(n : ℝ) ^ (1 / (l : ℝ))⌋₊ : ℝ) := by linarith
    _ ≤ (lvlStep l n : ℝ) := by
        rw [lvlStep]
        push_cast
        exact mul_le_mul_of_nonneg_left
          (by exact_mod_cast le_max_right 1 ⌊(n : ℝ) ^ (1 / (l : ℝ))⌋₊) (by norm_num)

/-- The step function satisfies the numerical condition `hb` of `lvl2_step`. -/
lemma lvlStep_pow_le {l n : ℕ} (hl : 1 ≤ l) (hn : 1 ≤ n) :
    (lvlStep l n) ^ l ≤ 2 ^ l * n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hx1 : (1 : ℝ) ≤ (n : ℝ) ^ (1 / (l : ℝ)) :=
    Real.one_le_rpow (by exact_mod_cast hn) (by positivity)
  have hxle : ((max 1 ⌊(n : ℝ) ^ (1 / (l : ℝ))⌋₊ : ℕ) : ℝ) ≤ (n : ℝ) ^ (1 / (l : ℝ)) := by
    push_cast
    refine max_le hx1 ?_
    exact Nat.floor_le (by positivity)
  have hl0 : ((l : ℝ)) ≠ 0 := by positivity
  have hpow : ((max 1 ⌊(n : ℝ) ^ (1 / (l : ℝ))⌋₊ : ℕ) : ℝ) ^ l ≤ (n : ℝ) := by
    calc ((max 1 ⌊(n : ℝ) ^ (1 / (l : ℝ))⌋₊ : ℕ) : ℝ) ^ l
        ≤ ((n : ℝ) ^ (1 / (l : ℝ))) ^ l := pow_le_pow_left₀ (by positivity) hxle l
      _ = (n : ℝ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hn0.le]
          rw [show (1 / (l : ℝ)) * (l : ℝ) = 1 by field_simp]
          rw [Real.rpow_one]
  have hnat : (max 1 ⌊(n : ℝ) ^ (1 / (l : ℝ))⌋₊) ^ l ≤ n := by exact_mod_cast hpow
  calc (lvlStep l n) ^ l = 2 ^ l * (max 1 ⌊(n : ℝ) ^ (1 / (l : ℝ))⌋₊) ^ l := by
        rw [lvlStep, mul_pow]
    _ ≤ 2 ^ l * n := Nat.mul_le_mul_left _ hnat

/-! ## 2. The chain of levels -/

/-- **The `ℓ²`-chain.**  If each level is bounded by the next one with the constant `C j`, then the
level `0` is bounded by the level `K` with the product of the constants. -/
theorem lvl2_chain {l m : ℕ} (f : Fin m → E l → ℂ) {n : ℕ → ℕ} {C : ℕ → ℝ≥0∞}
    (h0 : n 0 = 1) (hbound : ∀ j, lvl2 l m (n j) f ≤ C j * lvl2 l m (n (j + 1)) f) :
    ∀ K, lvl2 l m 1 f ≤ (∏ j ∈ Finset.range K, C j) * lvl2 l m (n K) f := by
  intro K
  induction K with
  | zero => rw [Finset.prod_range_zero, one_mul, h0]
  | succ K ih =>
      rw [Finset.prod_range_succ]
      calc lvl2 l m 1 f ≤ (∏ j ∈ Finset.range K, C j) * lvl2 l m (n K) f := ih
        _ ≤ (∏ j ∈ Finset.range K, C j) * (C K * lvl2 l m (n (K + 1)) f) := by
              exact mul_le_mul_of_nonneg_left (hbound K) (by simp)
        _ = ((∏ j ∈ Finset.range K, C j) * C K) * lvl2 l m (n (K + 1)) f := by ring


/-! ## 3. The tower of levels -/

/-- The next level of the tower: from a level `n`, refine into `lvlStep l n` sub-blocks, unless
this would overshoot the fine level `m` (in which case use the largest number of sub-blocks that
stays below `m`); the tower stops once `2 n ≥ m`. -/
noncomputable def towerNext (l m : ℕ) (n : ℕ) : ℕ :=
  if 2 * n < m then (if n * lvlStep l n ≤ m then n * lvlStep l n else n * (m / n)) else n

/-- The tower of levels, starting at the level `1`. -/
noncomputable def towerN (l m : ℕ) : ℕ → ℕ := fun j => (towerNext l m)^[j] 1

lemma towerN_zero (l m : ℕ) : towerN l m 0 = 1 := rfl

lemma towerN_succ (l m j : ℕ) : towerN l m (j + 1) = towerNext l m (towerN l m j) :=
  Function.iterate_succ_apply' _ _ _

lemma le_towerNext (l m n : ℕ) : n ≤ towerNext l m n := by
  rw [towerNext]
  by_cases h : 2 * n < m
  · rw [if_pos h]
    by_cases h2 : n * lvlStep l n ≤ m
    · rw [if_pos h2]
      exact Nat.le_mul_of_pos_right _ (lvlStep_pos l n)
    · rw [if_neg h2]
      rcases Nat.eq_zero_or_pos n with hn | hn
      · subst hn
        simp
      · have hnm : n ≤ m := by omega
        exact Nat.le_mul_of_pos_right _ (Nat.div_pos hnm hn)
  · rw [if_neg h]

lemma le_towerN (l m j : ℕ) : towerN l m j ≤ towerN l m (j + 1) := by
  rw [towerN_succ]
  exact le_towerNext l m _

lemma towerN_le (l m j : ℕ) (hm : 1 ≤ m) : towerN l m j ≤ m := by
  induction j with
  | zero => rw [towerN_zero]; exact hm
  | succ j ih =>
      rw [towerN_succ, towerNext]
      by_cases h : 2 * towerN l m j < m
      · rw [if_pos h]
        by_cases h2 : towerN l m j * lvlStep l (towerN l m j) ≤ m
        · rw [if_pos h2]
          exact h2
        · rw [if_neg h2]
          rw [Nat.mul_comm]
          exact Nat.div_mul_le_self m _
      · rw [if_neg h]
        exact ih

lemma one_le_towerN (l m j : ℕ) : 1 ≤ towerN l m j := by
  induction j with
  | zero => simp [towerN_zero]
  | succ j ih => exact le_trans ih (le_towerN l m j)

/-- The tower is multiplicative: the level `j+1` is the level `j` times the number of sub-blocks. -/
lemma towerN_mul_div (l m j : ℕ) :
    towerN l m j * (towerN l m (j + 1) / towerN l m j) = towerN l m (j + 1) := by
  have hpos : 0 < towerN l m j := one_le_towerN l m j
  rw [towerN_succ, towerNext]
  by_cases h : 2 * towerN l m j < m
  · rw [if_pos h]
    by_cases h2 : towerN l m j * lvlStep l (towerN l m j) ≤ m
    · rw [if_pos h2]
      exact Nat.mul_div_cancel' (dvd_mul_right (towerN l m j) (lvlStep l (towerN l m j)))
    · rw [if_neg h2]
      exact Nat.mul_div_cancel' (dvd_mul_right (towerN l m j) (m / towerN l m j))
  · rw [if_neg h]
    rw [Nat.div_self hpos, mul_one]

/-- The hypothesis of `pow_step_reaches_half` for the tower. -/
lemma towerN_growth {l m : ℕ} (hl : 1 ≤ l) (hm : 4 ≤ m) (j : ℕ)
    (hj : towerN l m j < m) :
    m ≤ 2 * towerN l m (j + 1) ∨
      (towerN l m j : ℝ) ^ (1 + 1 / (l : ℝ)) ≤ (towerN l m (j + 1) : ℝ) := by
  have hn1 : 1 ≤ towerN l m j := one_le_towerN l m j
  have hpos : 0 < towerN l m j := hn1
  rw [towerN_succ, towerNext]
  by_cases h : 2 * towerN l m j < m
  · rw [if_pos h]
    by_cases h2 : towerN l m j * lvlStep l (towerN l m j) ≤ m
    · rw [if_pos h2]
      right
      have hspos : (0 : ℝ) < (towerN l m j : ℝ) := by exact_mod_cast hn1
      have hstep : (towerN l m j : ℝ) ^ (1 / (l : ℝ))
          ≤ (lvlStep l (towerN l m j) : ℝ) := le_lvlStep hn1
      have hsplit : (towerN l m j : ℝ) ^ (1 + 1 / (l : ℝ))
          = (towerN l m j : ℝ) * (towerN l m j : ℝ) ^ (1 / (l : ℝ)) := by
        rw [Real.rpow_add hspos, Real.rpow_one]
      rw [hsplit, Nat.cast_mul]
      exact mul_le_mul_of_nonneg_left hstep hspos.le
    · rw [if_neg h2]
      left
      have hmod : towerN l m j * (m / towerN l m j) + m % towerN l m j = m :=
        Nat.div_add_mod m _
      have hlt : m % towerN l m j < towerN l m j := Nat.mod_lt _ hpos
      omega
  · rw [if_neg h]
    left
    omega

/-! ## 4. The two end comparisons -/

/-- **The trivial bound** for the level-sum functional. -/
lemma lvl2_trivial {l m : ℕ} (hl : 1 ≤ l) (f : Fin m → E l → ℂ)
    (hf : ∀ i, AEStronglyMeasurable (f i) volume) :
    lvl2 l m 1 f ≤ (m : ℝ≥0∞) ^ (1 / 2 : ℝ) * lvl2 l m m f := by
  rw [lvl2_one, lvl2_self]
  simp only [l2Norm]
  have hp1 : 1 ≤ pE l := one_le_pE l hl
  have h1 : lpNorm l (pE l) (fun x => ∑ i, f i x) ≤ ∑ i : Fin m, lpNorm l (pE l) (f i) := by
    have hsum : (fun x => ∑ i : Fin m, f i x) = (∑ i : Fin m, f i) := by
      funext x
      simp only [Finset.sum_apply]
    rw [hsum]
    exact eLpNorm_sum_le (μ := volume) (p := pE l) (s := Finset.univ)
      (f := fun i => f i) (fun i _ => hf i) hp1
  refine h1.trans ?_
  have h2 : (∑ i : Fin m, lpNorm l (pE l) (f i)) ^ (2 : ℝ)
      ≤ (m : ℝ≥0∞) ^ ((2 : ℝ) - 1)
        * ∑ i : Fin m, (lpNorm l (pE l) (f i)) ^ (2 : ℝ) := by
    have h := Commons.Analysis.Inequalities.sum_rpow_le_card_rpow_mul_sum_rpow
      (Finset.univ : Finset (Fin m)) (fun i => lpNorm l (pE l) (f i)) (by norm_num : (1 : ℝ) ≤ 2)
    simpa [Finset.card_univ] using h
  have h3 := ENNReal.rpow_le_rpow h2 (by norm_num : (0 : ℝ) ≤ 1 / 2)
  rw [← ENNReal.rpow_mul, show (2 : ℝ) * (1 / 2) = 1 by norm_num, ENNReal.rpow_one,
    show (2 : ℝ) - 1 = 1 by norm_num, ENNReal.rpow_one,
    ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2)] at h3
  rw [show (1 : ℝ) / 2 = 1 / 2 by norm_num]
  exact h3

/-- **The final comparison of the tower.**  At a level `n` with `m ≤ 2 n`, each block contains at
most `3` fine pieces, so the `ℓ²`-norm of the level-`n` block sums is at most `√3` times the
`ℓ²`-norm of the individual pieces. -/
lemma lvl2_le_self {l m n : ℕ} (hl : 1 ≤ l) (hm : 0 < m) (hn : 0 < n) (h : m ≤ 2 * n)
    {f : Fin m → E l → ℂ} (hf : ∀ i, AEStronglyMeasurable (f i) volume) :
    lvl2 l m n f ≤ (3 : ℝ≥0∞) ^ (1 / 2 : ℝ) * lvl2 l m m f := by
  have hp1 : 1 ≤ pE l := one_le_pE l hl
  have hcard : ∀ I : Fin n,
      ((Finset.univ.filter (fun i : Fin m => blkIdx m n i = I.val)).card : ℝ≥0∞) ≤ 3 := by
    intro I
    have h1 : ((Finset.univ.filter (fun i : Fin m => blkIdx m n i = I.val)).card : ℕ)
        ≤ m / n + 1 := by
      have heq : (Finset.univ.filter (fun i : Fin m => blkIdx m n i = I.val))
          = (Finset.univ.filter (fun i : Fin m => (n * (2 * i.val + 1)) / (2 * m) = I.val)) := by
        apply Finset.filter_congr
        intro i _
        simp only [blkIdx]
      rw [heq]
      exact Commons.Combinatorics.LevelBlocks.card_filter_blkIdx_le (m := m) (n := n)
        (I := I.val) hm hn
    have h2 : m / n ≤ 2 := by
      rw [Nat.div_le_iff_le_mul_add_pred hn]
      omega
    have h3 : ((Finset.univ.filter (fun i : Fin m => blkIdx m n i = I.val)).card : ℕ) ≤ 3 := by
      omega
    exact_mod_cast h3
  have hmain : ∀ I : Fin n, lpNorm l (pE l) (blkSum l m n f I)
      ≤ (3 : ℝ≥0∞) ^ (1 / 2 : ℝ) * (∑ i ∈ (Finset.univ.filter
            (fun i : Fin m => blkIdx m n i = I.val)), (lpNorm l (pE l) (f i)) ^ (2 : ℝ))
          ^ (1 / 2 : ℝ) := by
    intro I
    have hsum_le : lpNorm l (pE l) (blkSum l m n f I)
        ≤ ∑ i ∈ (Finset.univ.filter (fun i : Fin m => blkIdx m n i = I.val)),
            lpNorm l (pE l) (f i) := by
      rw [show blkSum l m n f I = (fun x => ∑ i ∈ (Finset.univ.filter
          (fun i : Fin m => blkIdx m n i = I.val)), f i x) from rfl]
      have hsum : (fun x => ∑ i ∈ (Finset.univ.filter (fun i : Fin m => blkIdx m n i = I.val)),
          f i x) = (∑ i ∈ (Finset.univ.filter (fun i : Fin m => blkIdx m n i = I.val)), f i) := by
        funext x
        rw [Finset.sum_apply]
      simp only [lpNorm]
      rw [hsum]
      exact eLpNorm_sum_le (μ := volume) (p := pE l)
        (s := Finset.univ.filter (fun i : Fin m => blkIdx m n i = I.val))
        (f := fun i => f i) (fun i _ => hf i) hp1
    have hcs : (∑ i ∈ (Finset.univ.filter (fun i : Fin m => blkIdx m n i = I.val)),
          lpNorm l (pE l) (f i)) ^ (2 : ℝ)
        ≤ ((Finset.univ.filter (fun i : Fin m => blkIdx m n i = I.val)).card : ℝ≥0∞)
          ^ ((2 : ℝ) - 1)
          * ∑ i ∈ (Finset.univ.filter (fun i : Fin m => blkIdx m n i = I.val)),
              (lpNorm l (pE l) (f i)) ^ (2 : ℝ) :=
      Commons.Analysis.Inequalities.sum_rpow_le_card_rpow_mul_sum_rpow
        _ (fun i => lpNorm l (pE l) (f i)) (by norm_num : (1 : ℝ) ≤ 2)
    have h4 : (∑ i ∈ (Finset.univ.filter (fun i : Fin m => blkIdx m n i = I.val)),
          lpNorm l (pE l) (f i))
        ≤ (3 : ℝ≥0∞) ^ (1 / 2 : ℝ) * (∑ i ∈ (Finset.univ.filter
              (fun i : Fin m => blkIdx m n i = I.val)), (lpNorm l (pE l) (f i)) ^ (2 : ℝ))
            ^ (1 / 2 : ℝ) := by
      have hh := ENNReal.rpow_le_rpow hcs (by norm_num : (0 : ℝ) ≤ 1 / 2)
      rw [show (2 : ℝ) - 1 = 1 by norm_num, ENNReal.rpow_one] at hh
      rw [← ENNReal.rpow_mul, show (2 : ℝ) * (1 / 2) = 1 by norm_num,
        ENNReal.rpow_one] at hh
      refine hh.trans ?_
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      exact mul_le_mul_of_nonneg_right
        (ENNReal.rpow_le_rpow (hcard I) (by norm_num : (0 : ℝ) ≤ 1 / 2)) (by simp)
    exact hsum_le.trans h4
  have hkey : (∑ I : Fin n, ((3 : ℝ≥0∞) ^ (1 / 2 : ℝ) * (∑ i ∈ (Finset.univ.filter
        (fun i : Fin m => blkIdx m n i = I.val)), (lpNorm l (pE l) (f i)) ^ (2 : ℝ))
        ^ (1 / 2 : ℝ)) ^ (2 : ℝ))
      = (3 : ℝ≥0∞) * ∑ i : Fin m, (lpNorm l (pE l) (f i)) ^ (2 : ℝ) := by
    have h1fun : ∀ I : Fin n, ((3 : ℝ≥0∞) ^ (1 / 2 : ℝ) * (∑ i ∈ (Finset.univ.filter
          (fun i : Fin m => blkIdx m n i = I.val)), (lpNorm l (pE l) (f i)) ^ (2 : ℝ))
          ^ (1 / 2 : ℝ)) ^ (2 : ℝ)
        = (3 : ℝ≥0∞) * ∑ i ∈ (Finset.univ.filter (fun i : Fin m => blkIdx m n i = I.val)),
            (lpNorm l (pE l) (f i)) ^ (2 : ℝ) := by
      intro I
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2),
        ← ENNReal.rpow_mul, show (1 / 2 : ℝ) * 2 = 1 by norm_num, ENNReal.rpow_one,
        ← ENNReal.rpow_mul, show (1 / 2 : ℝ) * 2 = 1 by norm_num, ENNReal.rpow_one]
    have h1 : (∑ I : Fin n, ((3 : ℝ≥0∞) ^ (1 / 2 : ℝ) * (∑ i ∈ (Finset.univ.filter
          (fun i : Fin m => blkIdx m n i = I.val)), (lpNorm l (pE l) (f i)) ^ (2 : ℝ))
          ^ (1 / 2 : ℝ)) ^ (2 : ℝ))
        = ∑ I : Fin n, (3 : ℝ≥0∞) * ∑ i ∈ (Finset.univ.filter
            (fun i : Fin m => blkIdx m n i = I.val)), (lpNorm l (pE l) (f i)) ^ (2 : ℝ) :=
      Finset.sum_congr (rfl : (Finset.univ : Finset (Fin n)) = Finset.univ)
        (fun I (_ : I ∈ Finset.univ) => h1fun I)
    have h2 : (∑ I : Fin n, (3 : ℝ≥0∞) * ∑ i ∈ (Finset.univ.filter
            (fun i : Fin m => blkIdx m n i = I.val)), (lpNorm l (pE l) (f i)) ^ (2 : ℝ))
        = ∑ i : Fin m, (3 : ℝ≥0∞) * (lpNorm l (pE l) (f i)) ^ (2 : ℝ) := by
      rw [← Finset.sum_fiberwise (Finset.univ : Finset (Fin m))
        (fun i : Fin m => blkOf m n hn i)
        (fun i : Fin m => (3 : ℝ≥0∞) * (lpNorm l (pE l) (f i)) ^ (2 : ℝ))]
      refine Finset.sum_congr rfl fun I _ => ?_
      have hfilt : (Finset.univ.filter (fun i : Fin m => blkOf m n hn i = I))
          = (Finset.univ.filter (fun i : Fin m => blkIdx m n i = I.val)) := by
        apply Finset.filter_congr
        intro i _
        simp only [blkOf, Fin.ext_iff]
      rw [hfilt, Finset.mul_sum]
    rw [h1, h2, ← Finset.mul_sum]
  have hfin : lvl2 l m n f
      ≤ ((3 : ℝ≥0∞) * ∑ i : Fin m, (lpNorm l (pE l) (f i)) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
    rw [lvl2, l2Norm]
    refine (ENNReal.rpow_le_rpow (Finset.sum_le_sum fun I (_ : I ∈ Finset.univ) =>
      ENNReal.rpow_le_rpow (hmain I) (by norm_num : (0 : ℝ) ≤ 2)) (by norm_num)).trans ?_
    rw [hkey]
  refine hfin.trans ?_
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  rw [show (∑ i : Fin m, (lpNorm l (pE l) (f i)) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) = lvl2 l m m f by
    rw [lvl2_self, l2Norm]]


/-! ## 5. The number of sub-blocks of the tower -/

lemma towerN_div_le (l m j : ℕ) :
    towerN l m (j + 1) / towerN l m j ≤ max 1 (lvlStep l (towerN l m j)) := by
  have hpos : 0 < towerN l m j := one_le_towerN l m j
  rw [towerN_succ, towerNext]
  by_cases h : 2 * towerN l m j < m
  · rw [if_pos h]
    by_cases h2 : towerN l m j * lvlStep l (towerN l m j) ≤ m
    · rw [if_pos h2, Nat.mul_div_right _ hpos]
      exact le_max_right _ _
    · rw [if_neg h2, Nat.mul_div_right _ hpos]
      refine le_trans (le_of_lt ?_) (le_max_right _ _)
      rw [Nat.div_lt_iff_lt_mul hpos, Nat.mul_comm (lvlStep l (towerN l m j)) (towerN l m j)]
      omega
  · rw [if_neg h, Nat.div_self hpos]
    exact le_max_left _ _

/-! ## 6. GLYZ Lemma 3.6: decoupling for curves of degree `l` with torsion -/

/-- **GLYZ Lemma 3.6 (`ℓ²`-decoupling for a general curve with torsion).**  If the moment-curve
decoupling theorem of degree `l` is known at every scale with a constant `a * M^{εm}`, then the same
`ℓ²`-decoupling inequality (with an `m^{2 εm}` loss at scale `m`) holds for every curve `D` of
degree `l` with torsion, with plates of the fine scale `δ ≤ 1/(2m)`. -/
theorem curveDec_tower {l : ℕ} (hl : 1 ≤ l) (D : ℕ → ℝ → E l)
    {A cT R : ℝ} (hbd : CurveBounded l D A) (hA : 1 ≤ A) (htor : CurveTorsion l D cT)
    (hcT : 0 < cT) (htay : CurveTaylor l D R) (hR : 0 ≤ R)
    {Λ : ℝ} (hΛ : 1 ≤ Λ)
    {εt Λ₁ : ℝ} (hεt : 0 < εt) (hΛ₁ : Λ * (1 + εt) * Ctube l ≤ Λ₁)
    (ha : 2 * (2 ^ (l + 1) * R * ((l : ℝ) + 1) * Λ ^ (l + 1)) ≤ εt * tubeCG l A cT)
    {a : ℝ} (ha1 : 1 ≤ a) {εm : ℝ} (hεm : 0 < εm)
    (hmod : ∀ M : ℕ, 1 ≤ M → DecLinScale l M Λ₁ (ENNReal.ofReal (a * (M : ℝ) ^ εm)))
    {m : ℕ} (hm : 4 ≤ m) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hδΛ : δ ≤ Λ / (2 * (m : ℝ)))
    {f : Fin m → E l → ℂ}
    (hf : ∀ i, IsFourierRep l (curvePlate l D δ (pieceCenter m i)) (f i)) :
    ∃ C : ℝ, 0 < C ∧ lpNorm l (pE l) (fun x => ∑ i, f i x)
      ≤ ENNReal.ofReal C * (m : ℝ≥0∞) ^ (2 * εm) * l2Norm (fun i => lpNorm l (pE l) (f i)) := by
  classical
  have hm0 : 0 < m := by omega
  have hm1 : 1 ≤ m := by omega
  have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
  obtain ⟨Cabs, hCabs, habs⟩ := Commons.Analysis.Asymptotics.pow_const_le_mul_rpow
    (a := max 1 a) (b := εm) (le_max_left 1 a) hεm (L := 2 * (l : ℝ) + 1) (by positivity)
  refine ⟨3 * Cabs, by positivity, ?_⟩
  -- the curve constants
  have hCt2 : (2 : ℝ) ≤ Ctube l := by
    rw [Ctube]
    have h3 : (1 : ℝ) ≤ (l : ℝ) * (l.factorial : ℝ) := by
      have h4 : (1 : ℕ) ≤ l * l.factorial := by
        have h5 : 1 ≤ l := hl
        have h6 : 1 ≤ l.factorial := Nat.factorial_pos l
        nlinarith
      exact_mod_cast h4
    linarith
  -- the tower reaches the fine level
  have h0 : 2 ≤ towerN l m 1 := by
    rw [towerN_succ, towerN_zero, towerNext]
    rw [if_pos (by omega)]
    by_cases h2 : 1 * lvlStep l 1 ≤ m
    · rw [if_pos h2]
      simpa using lvlStep_two_le l 1
    · rw [if_neg h2]
      omega
  obtain ⟨K, hK, hmK⟩ := Commons.Combinatorics.LevelBlocks.pow_step_reaches_half (l := l) hl hm
    (n := fun j => towerN l m (j + 1)) h0 (fun j hj => towerN_growth hl hm (j + 1) hj)
  -- the per-step bound
  have hbound : ∀ j : ℕ, lvl2 l m (towerN l m j) f
      ≤ ENNReal.ofReal (a * ((towerN l m (j + 1) / towerN l m j : ℕ) : ℝ) ^ εm)
        * lvl2 l m (towerN l m (j + 1)) f := by
    intro j
    set M : ℕ := towerN l m (j + 1) / towerN l m j with hM
    have hn1 : 1 ≤ towerN l m j := one_le_towerN l m j
    have hMpos : 0 < M := by
      rcases Nat.eq_zero_or_pos M with h0M | h0M
      · exfalso
        have h1 := towerN_mul_div l m j
        rw [← hM, h0M, mul_zero] at h1
        have := one_le_towerN l m (j + 1)
        omega
      · exact h0M
    have hMtower : towerN l m j * M = towerN l m (j + 1) := by
      rw [hM]
      exact towerN_mul_div l m j
    have hδ1' : δ ≤ Λ / (2 * ((towerN l m j * M : ℕ) : ℝ)) := by
      rw [hMtower]
      have ht : (0 : ℝ) < (towerN l m (j + 1) : ℕ) := by
        exact_mod_cast one_le_towerN l m (j + 1)
      have hle : Λ / (2 * (m : ℝ)) ≤ Λ / (2 * ((towerN l m (j + 1) : ℕ) : ℝ)) := by
        apply div_le_div_of_nonneg_left (le_trans zero_le_one hΛ)
        · positivity
        · have h2 : (towerN l m (j + 1) : ℝ) ≤ (m : ℝ) := by
            exact_mod_cast towerN_le l m (j + 1) hm1
          linarith
      exact le_trans hδΛ hle
    have hb : (M : ℝ) ^ l ≤ (Ctube l) ^ l * ((towerN l m j : ℕ) : ℝ) := by
      have hMle : M ≤ max 1 (lvlStep l (towerN l m j)) := by
        rw [hM]
        exact towerN_div_le l m j
      rcases lt_or_ge 1 M with hM2 | hM1
      · have hMle' : M ≤ lvlStep l (towerN l m j) := by
          rcases le_max_iff.mp hMle with h | h
          · omega
          · exact h
        have hlvl : (lvlStep l (towerN l m j)) ^ l ≤ 2 ^ l * towerN l m j :=
          lvlStep_pow_le hl hn1
        have hreal : (M : ℝ) ^ l ≤ (2 : ℝ) ^ l * ((towerN l m j : ℕ) : ℝ) := by
          have h1 : (M : ℝ) ≤ ((lvlStep l (towerN l m j) : ℕ) : ℝ) := by exact_mod_cast hMle'
          have h2 : (M : ℝ) ^ l ≤ ((lvlStep l (towerN l m j) : ℕ) : ℝ) ^ l :=
            pow_le_pow_left₀ (by positivity) h1 l
          have h3 : (((lvlStep l (towerN l m j)) ^ l : ℕ) : ℝ)
              ≤ ((2 ^ l * towerN l m j : ℕ) : ℝ) := by exact_mod_cast hlvl
          calc (M : ℝ) ^ l ≤ ((lvlStep l (towerN l m j) : ℕ) : ℝ) ^ l := h2
            _ = (((lvlStep l (towerN l m j)) ^ l : ℕ) : ℝ) := by push_cast; ring
            _ ≤ ((2 ^ l * towerN l m j : ℕ) : ℝ) := h3
            _ = (2 : ℝ) ^ l * ((towerN l m j : ℕ) : ℝ) := by push_cast; ring
        exact hreal.trans (mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (by norm_num) hCt2 l) (by positivity))
      · have h1 : M = 1 := le_antisymm hM1 hMpos
        rw [h1, Nat.cast_one, one_pow]
        have hn1' : (1 : ℝ) ≤ (towerN l m j : ℕ) := by exact_mod_cast hn1
        have hCt1 : (1 : ℝ) ≤ (Ctube l) ^ l := one_le_pow₀ (le_trans (by norm_num) hCt2)
        nlinarith
    have hstep := lvl2_step (l := l) hl D hbd hA htor hcT htay hR hm0 hn1 hMpos
      hΛ hεt hΛ₁ (hmod M hMpos) hδ0 hδ1 hδ1' ha hb (fun i => hf i)
    rwa [hMtower] at hstep
  -- the telescoping of the product of constants
  have hprod : ∀ J : ℕ, (∏ j ∈ Finset.range J,
        ENNReal.ofReal (a * ((towerN l m (j + 1) / towerN l m j : ℕ) : ℝ) ^ εm))
      = ENNReal.ofReal (a ^ J * ((towerN l m J : ℕ) : ℝ) ^ εm) := by
    intro J
    induction J with
    | zero =>
        rw [Finset.prod_range_zero, towerN_zero]
        simp
    | succ J ih =>
        have hnn : (0 : ℝ) ≤ a ^ J * ((towerN l m J : ℕ) : ℝ) ^ εm :=
          mul_nonneg (pow_nonneg (by linarith [ha1]) J) (Real.rpow_nonneg (by positivity) εm)
        rw [Finset.prod_range_succ, ih, ← ENNReal.ofReal_mul hnn]
        congr 1
        have hM := towerN_mul_div l m J
        have hcast : ((towerN l m (J + 1) : ℕ) : ℝ)
            = (towerN l m J : ℝ) * ((towerN l m (J + 1) / towerN l m J : ℕ) : ℝ) := by
          rw [← Nat.cast_mul, towerN_mul_div]
        have htJ : (0 : ℝ) < (towerN l m J : ℕ) := by
          exact_mod_cast one_le_towerN l m J
        have htm : (0 : ℝ) < ((towerN l m (J + 1) / towerN l m J : ℕ) : ℝ) := by
          rcases Nat.eq_zero_or_pos (towerN l m (J + 1) / towerN l m J) with h0M | h0M
          · exfalso
            have h1 : towerN l m J * (towerN l m (J + 1) / towerN l m J) = towerN l m (J + 1) :=
              towerN_mul_div l m J
            rw [h0M, mul_zero] at h1
            have h2 := one_le_towerN l m (J + 1)
            omega
          · exact_mod_cast h0M
        rw [hcast, Real.mul_rpow htJ.le htm.le, pow_succ']
        ring
  -- the chain
  have hchain := lvl2_chain (l := l) (m := m) f (n := fun j => towerN l m j)
    (C := fun j => ENNReal.ofReal (a * ((towerN l m (j + 1) / towerN l m j : ℕ) : ℝ) ^ εm))
    (towerN_zero l m) hbound (K + 1)
  rw [hprod (K + 1)] at hchain
  -- the product bound
  have hpb : ENNReal.ofReal (a ^ (K + 1) * ((towerN l m (K + 1) : ℕ) : ℝ) ^ εm)
      ≤ ENNReal.ofReal (Cabs * (m : ℝ) ^ (2 * εm)) := by
    apply ENNReal.ofReal_le_ofReal
    have hlog1 : (1 : ℝ) ≤ Real.log (Real.log (m : ℝ) + 2) + 1 := by
      have h4 : (0 : ℝ) ≤ Real.log (m : ℝ) := Real.log_nonneg hmR
      have h5 : (1 : ℝ) ≤ Real.log (m : ℝ) + 2 := by linarith
      have h6 : (0 : ℝ) ≤ Real.log (Real.log (m : ℝ) + 2) := Real.log_nonneg h5
      linarith
    have hK' : ((K + 1 : ℕ) : ℝ)
        ≤ 2 + (2 * (l : ℝ) + 1) * (Real.log (Real.log (m : ℝ) + 2) + 1) := by
      have h1 : ((K : ℕ) : ℝ) ≤ 2 + 2 * (l : ℝ) * (Real.log (Real.log (m : ℝ) + 2) + 1) := hK
      have hL0 : (0 : ℝ) ≤ 2 * (l : ℝ) := by positivity
      push_cast
      nlinarith [h1, hL0, hlog1]
    have h1 : a ^ (K + 1) ≤ Cabs * (m : ℝ) ^ εm := by
      calc a ^ (K + 1) ≤ (max 1 a) ^ (K + 1) :=
            pow_le_pow_left₀ (by positivity) (le_max_right 1 a) _
        _ ≤ Cabs * (m : ℝ) ^ εm := habs (K + 1) m (by omega) hK'
    have h2 : ((towerN l m (K + 1) : ℕ) : ℝ) ^ εm ≤ (m : ℝ) ^ εm := by
      refine Real.rpow_le_rpow (by positivity) ?_ hεm.le
      exact_mod_cast towerN_le l m (K + 1) hm1
    have h3 : (m : ℝ) ^ εm * (m : ℝ) ^ εm = (m : ℝ) ^ (2 * εm) := by
      rw [← Real.rpow_add (by exact_mod_cast hm0)]
      ring_nf
    calc a ^ (K + 1) * ((towerN l m (K + 1) : ℕ) : ℝ) ^ εm
        ≤ (Cabs * (m : ℝ) ^ εm) * ((towerN l m (K + 1) : ℕ) : ℝ) ^ εm :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ ≤ (Cabs * (m : ℝ) ^ εm) * (m : ℝ) ^ εm :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = Cabs * (m : ℝ) ^ (2 * εm) := by rw [← h3]; ring
  -- the final comparison
  have hfin : lvl2 l m (towerN l m (K + 1)) f
      ≤ (3 : ℝ≥0∞) ^ (1 / 2 : ℝ) * lvl2 l m m f :=
    lvl2_le_self (l := l) hl hm0 (one_le_towerN l m (K + 1)) hmK
      (fun i => (hf i).aestronglyMeasurable)
  have hcomb : lvl2 l m 1 f
      ≤ (ENNReal.ofReal (Cabs * (m : ℝ) ^ (2 * εm)) * (3 : ℝ≥0∞) ^ (1 / 2 : ℝ))
        * lvl2 l m m f := by
    calc lvl2 l m 1 f
        ≤ ENNReal.ofReal (a ^ (K + 1) * ((towerN l m (K + 1) : ℕ) : ℝ) ^ εm)
            * lvl2 l m (towerN l m (K + 1)) f := hchain
      _ ≤ ENNReal.ofReal (Cabs * (m : ℝ) ^ (2 * εm)) * lvl2 l m (towerN l m (K + 1)) f :=
          mul_le_mul_of_nonneg_right hpb (by simp)
      _ ≤ ENNReal.ofReal (Cabs * (m : ℝ) ^ (2 * εm))
            * ((3 : ℝ≥0∞) ^ (1 / 2 : ℝ) * lvl2 l m m f) :=
          mul_le_mul_of_nonneg_left hfin (by simp)
      _ = (ENNReal.ofReal (Cabs * (m : ℝ) ^ (2 * εm)) * (3 : ℝ≥0∞) ^ (1 / 2 : ℝ))
            * lvl2 l m m f := by ring
  rw [lvl2_one] at hcomb
  refine hcomb.trans ?_
  have hob : (ENNReal.ofReal (Cabs * (m : ℝ) ^ (2 * εm)) * (3 : ℝ≥0∞) ^ (1 / 2 : ℝ))
      ≤ ENNReal.ofReal (3 * Cabs) * (m : ℝ≥0∞) ^ (2 * εm) := by
    have h3 : (3 : ℝ≥0∞) ^ (1 / 2 : ℝ) ≤ (3 : ℝ≥0∞) := by
      calc (3 : ℝ≥0∞) ^ (1 / 2 : ℝ) = ENNReal.ofReal (Real.sqrt 3) := by
            rw [Real.sqrt_eq_rpow, show (3 : ℝ≥0∞) = ENNReal.ofReal (3 : ℝ) by simp,
              ← ENNReal.ofReal_rpow_of_nonneg (by norm_num) (by norm_num)]
        _ ≤ ENNReal.ofReal (3 : ℝ) := ENNReal.ofReal_le_ofReal (by
            nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_nonneg 3])
        _ = (3 : ℝ≥0∞) := by simp
    calc (ENNReal.ofReal (Cabs * (m : ℝ) ^ (2 * εm)) * (3 : ℝ≥0∞) ^ (1 / 2 : ℝ))
        = (ENNReal.ofReal Cabs * (m : ℝ≥0∞) ^ (2 * εm)) * (3 : ℝ≥0∞) ^ (1 / 2 : ℝ) := by
          rw [ENNReal.ofReal_mul (by positivity),
            ← ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity)]
          norm_num
      _ ≤ (ENNReal.ofReal Cabs * (m : ℝ≥0∞) ^ (2 * εm)) * 3 :=
          mul_le_mul_of_nonneg_left h3 (by simp)
      _ = ENNReal.ofReal (3 * Cabs) * (m : ℝ≥0∞) ^ (2 * εm) := by
          have h3e : ENNReal.ofReal (3 : ℝ) = (3 : ℝ≥0∞) := by simp
          rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3), h3e]
          ring
  calc (ENNReal.ofReal (Cabs * (m : ℝ) ^ (2 * εm)) * (3 : ℝ≥0∞) ^ (1 / 2 : ℝ))
        * lvl2 l m m f
      ≤ (ENNReal.ofReal (3 * Cabs) * (m : ℝ≥0∞) ^ (2 * εm)) * lvl2 l m m f :=
        mul_le_mul_of_nonneg_right hob (by simp)
    _ = ENNReal.ofReal (3 * Cabs) * (m : ℝ≥0∞) ^ (2 * εm)
          * l2Norm (fun i => lpNorm l (pE l) (f i)) := by rw [lvl2_self]


end Submission.Vinogradov
