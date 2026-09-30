import Mathlib
import Submission.Work.BMF.HL.prime_block_inv_log_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.HL

open Finset Real

/-- The dyadic tower `11, 11², 11⁴, …` along which the block estimate
`Σ_{a<p≤a²} 1/(p log p) ≤ C/log a` is telescoped. -/
private def tower : ℕ → ℕ
  | 0 => 11
  | (k + 1) => tower k ^ 2

private lemma tower_eq (k : ℕ) : tower k = 11 ^ 2 ^ k := by
  induction k with
  | zero => norm_num [tower]
  | succ k ih =>
    simp only [tower]
    rw [ih, ← pow_mul, pow_succ]

private lemma tower_cast (k : ℕ) : (tower k : ℝ) = (11 : ℝ) ^ (2 ^ k) := by
  rw [tower_eq]
  push_cast
  norm_num

private lemma log_tower (k : ℕ) : Real.log (tower k : ℝ) = (2 : ℝ) ^ k * Real.log 11 := by
  rw [tower_cast, Real.log_pow]
  norm_num

private lemma eleven_le_tower (k : ℕ) : 11 ≤ tower k := by
  rw [tower_eq]
  exact Nat.pow_le_pow_right (n := 11) (by norm_num) Nat.one_le_two_pow

private lemma self_le_tower (n : ℕ) : n ≤ tower n := by
  calc n ≤ 2 ^ n := le_of_lt Nat.lt_two_pow_self
    _ ≤ 2 ^ (2 ^ n) := Nat.pow_le_pow_right (by norm_num) (le_of_lt Nat.lt_two_pow_self)
    _ ≤ 11 ^ (2 ^ n) := Nat.pow_le_pow_left (by norm_num) (2 ^ n)
    _ = tower n := (tower_eq n).symm

/-- `g n = Σ_{p ≤ n} 1/(p log p)`. -/
private noncomputable def g (n : ℕ) : ℝ := ∑ p ∈ n.primesLE, 1 / ((p : ℝ) * Real.log p)

private lemma g_le_three : g 11 ≤ 3 := by
  unfold g
  have hset : (11).primesLE = ({2, 3, 5, 7, 11} : Finset ℕ) := by decide
  have hlog2 : (1 : ℝ) / 2 < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlog3 : (1 : ℝ) < Real.log 3 := by
    have h : Real.exp 1 < 3 := by linarith [Real.exp_one_lt_d9]
    have := Real.log_lt_log (Real.exp_pos 1) h
    rwa [Real.log_exp] at this
  have hterm : ∀ p : ℝ, 3 ≤ p → 1 / (p * Real.log p) ≤ 1 / 3 := by
    intro p hp
    have h3 : (3 : ℝ) ≤ p * Real.log p := by
      have h1 : (1 : ℝ) ≤ Real.log p := le_trans hlog3.le (Real.log_le_log (by norm_num) hp)
      nlinarith [hp]
    exact one_div_le_one_div_of_le (by norm_num) h3
  rw [hset]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  have h2 : 1 / ((2 : ℝ) * Real.log 2) ≤ 1 := by
    rw [div_le_one (by positivity)]
    nlinarith [hlog2]
  have e3 : 1 / ((3 : ℝ) * Real.log 3) ≤ 1 / 3 := hterm 3 (by norm_num)
  have e5 : 1 / ((5 : ℝ) * Real.log 5) ≤ 1 / 3 := hterm 5 (by norm_num)
  have e7 : 1 / ((7 : ℝ) * Real.log 7) ≤ 1 / 3 := hterm 7 (by norm_num)
  have e11 : 1 / ((11 : ℝ) * Real.log 11) ≤ 1 / 3 := hterm 11 (by norm_num)
  linarith

/-- `Σ_{p ≤ x} 1/(p log p)` is bounded by an absolute constant for every `x ≥ 2` (i.e.
`Σ_p 1/(p log p) < ∞`).  Proof route: the block bound `prime_block_inv_log_le` says
`Σ_{a<p≤a²} 1/(p log p) ≤ (log 2 + C)/log a` for `a ≥ 11`; iterate it along the dyadic tower
`a, a², a⁴, …` starting at `a = 11` (block `k` contributes at most `2^{-k}(log 2 + C)/log 11`,
summing to `2(log 2 + C)/log 11`), and absorb the finitely many primes `p ≤ 11` into the
constant. -/
theorem sum_inv_p_log_p_le_const :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 2 ≤ x →
      (∑ p ∈ (⌊x⌋₊).primesLE, (1 : ℝ) / ((p : ℝ) * Real.log p)) ≤ C := by
  obtain ⟨Cb, _hCbpos, hCb⟩ := prime_block_inv_log_le
  have hlog11pos : 0 < Real.log 11 := Real.log_pos (by norm_num)
  have hC'pos : 0 < Real.log 2 + Cb := by
    have := Real.log_pos (show (1 : ℝ) < 2 by norm_num)
    linarith
  -- The block estimate, re-expressed along consecutive tower levels.
  have hblock : ∀ k, (∑ p ∈ (tower (k + 1)).primesLE \ (tower k).primesLE,
        1 / ((p : ℝ) * Real.log p)) ≤ (Real.log 2 + Cb) / Real.log (tower k) := by
    intro k
    have h11 : (11 : ℝ) ≤ (tower k : ℝ) := by exact_mod_cast eleven_le_tower k
    have h := hCb (tower k : ℝ) h11
    have hfl : ⌊(tower k : ℝ)⌋₊ = tower k := Nat.floor_natCast _
    have hfl2 : ⌊(tower k : ℝ) ^ 2⌋₊ = tower (k + 1) := by
      have hcast : (tower k : ℝ) ^ 2 = ((tower k ^ 2 : ℕ) : ℝ) := by push_cast; ring
      rw [hcast, Nat.floor_natCast]
      rfl
    rw [hfl, hfl2] at h
    exact h
  -- Consecutive tower levels are nested.
  have hmono : ∀ k, (tower k).primesLE ⊆ (tower (k + 1)).primesLE := by
    intro k
    apply Nat.primesLE_mono
    show tower k ≤ tower (k + 1)
    calc tower k ≤ tower k * tower k := Nat.le_mul_self _
      _ = tower k ^ 2 := (pow_two _).symm
  -- Exact one-step telescoping.
  have hsplit : ∀ k, g (tower (k + 1)) = g (tower k) +
      ∑ p ∈ (tower (k + 1)).primesLE \ (tower k).primesLE, 1 / ((p : ℝ) * Real.log p) := by
    intro k
    unfold g
    have := Finset.sum_sdiff (hmono k) (f := fun p : ℕ => 1 / ((p : ℝ) * Real.log p))
    linarith
  -- Telescoped bound over the first `N` levels.
  have htel : ∀ N, g (tower N) ≤
      3 + ∑ k ∈ Finset.range N, (Real.log 2 + Cb) / Real.log (tower k) := by
    intro N
    induction N with
    | zero =>
      simp only [Finset.range_zero, Finset.sum_empty, add_zero]
      exact g_le_three
    | succ N ih =>
      rw [hsplit N, Finset.sum_range_succ]
      linarith [ih, hblock N]
  -- The geometric collapse of the tower contribution.
  have hgeom : ∀ N, (∑ k ∈ Finset.range N, (Real.log 2 + Cb) / Real.log (tower k))
      ≤ 2 * (Real.log 2 + Cb) / Real.log 11 := by
    intro N
    have hkey : (∑ k ∈ Finset.range N, (Real.log 2 + Cb) / Real.log (tower k))
        = (Real.log 2 + Cb) / Real.log 11 * (∑ k ∈ Finset.range N, (1 / 2 : ℝ) ^ k) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      rw [log_tower]
      have h2k : ((2 : ℝ) ^ k) ≠ 0 := by positivity
      have hL : Real.log 11 ≠ 0 := ne_of_gt hlog11pos
      rw [show (1 / 2 : ℝ) ^ k = ((2 : ℝ) ^ k)⁻¹ by rw [one_div, inv_pow]]
      field_simp
    rw [hkey]
    have hgeomsum : (∑ k ∈ Finset.range N, (1 / 2 : ℝ) ^ k) ≤ 2 := by
      rw [geom_sum_eq (by norm_num : (1 / 2 : ℝ) ≠ 1),
        div_le_iff_of_neg (by norm_num : (1 : ℝ) / 2 - 1 < 0)]
      nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) N]
    have hle : (0 : ℝ) ≤ (Real.log 2 + Cb) / Real.log 11 :=
      le_of_lt (div_pos hC'pos hlog11pos)
    calc (Real.log 2 + Cb) / Real.log 11 * (∑ k ∈ Finset.range N, (1 / 2 : ℝ) ^ k)
        ≤ (Real.log 2 + Cb) / Real.log 11 * 2 := by nlinarith
      _ = 2 * (Real.log 2 + Cb) / Real.log 11 := by ring
  refine ⟨3 + 2 * (Real.log 2 + Cb) / Real.log 11 + 1, ?_, ?_⟩
  · have hpos : 0 < (Real.log 2 + Cb) / Real.log 11 := div_pos hC'pos hlog11pos
    have h2 : 0 < 2 * ((Real.log 2 + Cb) / Real.log 11) := by linarith
    have heq : 2 * (Real.log 2 + Cb) / Real.log 11 = 2 * ((Real.log 2 + Cb) / Real.log 11) := by
      ring
    rw [heq]
    linarith
  · intro x _
    have hsub : (⌊x⌋₊).primesLE ⊆ (tower ⌊x⌋₊).primesLE := Nat.primesLE_mono (self_le_tower ⌊x⌋₊)
    have hmonosum : g ⌊x⌋₊ ≤ g (tower ⌊x⌋₊) := by
      unfold g
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro p hp _
      have hpp : Nat.Prime p := Nat.prime_of_mem_primesLE hp
      have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
      have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
      have hlogp : 0 < Real.log (p : ℝ) := Real.log_pos (by linarith)
      exact div_nonneg zero_le_one (le_of_lt (mul_pos hp0 hlogp))
    have h1 := htel ⌊x⌋₊
    have h2 := hgeom ⌊x⌋₊
    have hfinal : g ⌊x⌋₊ ≤ 3 + 2 * (Real.log 2 + Cb) / Real.log 11 + 1 := by linarith
    simpa only [g] using hfinal

end Work.BMF.HL
