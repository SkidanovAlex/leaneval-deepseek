import Mathlib
import Submission.Section5DCount
import Submission.CorPerm5D
import Submission.Commons.Analysis.Real.factorial_lower_exp

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

noncomputable section

open scoped BigOperators ENNReal

namespace Submission.Section5D

attribute [local instance] Classical.propDecidable

open Submission.Admissible
open Commons.LinearAlgebra.Net

/-!
# Product bound for the coordinate family `Acoord`

This is the last counting-layer piece of Section 5d: the product of the
window cardinalities of `Acoord n δ ν T` is bounded by `(K_A · N)^n` with
`N = holeN ν T`, uniformly in `n ≥ n₀(δ,ν)` and `T ∈ (0, ν/2]`.
-/

/-- `√(x^k) = (√x)^k` for `x ≥ 0`. -/
lemma sqrt_pow_eq (x : ℝ) (hx : 0 ≤ x) (k : ℕ) :
    Real.sqrt (x ^ k) = (Real.sqrt x) ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, Real.sqrt_mul (pow_nonneg hx k) x, ih, pow_succ]

/-- Constant for the small-coordinate factor. -/
noncomputable def KS (δ ν : ℝ) : ℝ := 64 * Real.sqrt (2 * Real.exp 1 / δ) / ν

/-- Constant for the large-coordinate factor. -/
noncomputable def KL (δ ν : ℝ) : ℝ := 12 * Real.sqrt 8 / (Real.sqrt δ * ν) + 6

/-- Per-coordinate bound at a small index. -/
lemma Acoord_small_card_le {n : ℕ} {δ ν T : ℝ} {i : Fin n}
    (hi : smallIndex n δ (i.val)) (hν0 : 0 < ν) (hν1 : ν ≤ 1) (hT0 : 0 < T)
    (hTν : T ≤ ν / 2) :
    ((Acoord n δ ν T i).card : ℝ)
      ≤ 16 * Real.sqrt (n : ℝ) / (T * Real.sqrt (posOf i : ℝ)) := by
  have hpos1 : 1 ≤ posOf i := posOf_pos i
  have hposn : posOf i ≤ n := posOf_le i
  have hposR : (0 : ℝ) < (posOf i : ℝ) :=
    by exact_mod_cast (lt_of_lt_of_le (by norm_num) hpos1)
  set x : ℝ := Real.sqrt (n : ℝ) / (T * Real.sqrt (posOf i : ℝ)) with hxdef
  have hxhalf : (1 / 2 : ℝ) ≤ x := by
    rw [hxdef, le_div_iff₀ (by positivity : (0:ℝ) < T * Real.sqrt (posOf i : ℝ))]
    have h1 : Real.sqrt (posOf i : ℝ) ≤ Real.sqrt (n : ℝ) := by
      apply Real.sqrt_le_sqrt
      exact_mod_cast hposn
    have hT12 : T ≤ 1 / 2 := by nlinarith [hTν, hν1]
    have hsp : (0 : ℝ) ≤ Real.sqrt (posOf i : ℝ) := Real.sqrt_nonneg _
    have h2 : T * Real.sqrt (posOf i : ℝ) ≤ Real.sqrt (n : ℝ) / 2 := by
      calc T * Real.sqrt (posOf i : ℝ)
          ≤ (1/2) * Real.sqrt (n : ℝ) :=
            mul_le_mul hT12 h1 hsp (by norm_num)
        _ = Real.sqrt (n : ℝ) / 2 := by ring
    linarith [Real.sqrt_nonneg (n : ℝ)]
  have hcard := Acoord_small_card_le_two_smallRad (n := n) (δ := δ) (ν := ν) (T := T)
    (i := i) hi hν0 hν1 hT0 hTν
  have hrad := smallRad_upper_pos (n := n) T (posOf i) hposR hT0
  have hx4 : 4 * Real.sqrt (n : ℝ) / (T * Real.sqrt (posOf i : ℝ)) = 4 * x := by
    rw [hxdef]; ring
  have hmain : ((Acoord n δ ν T i).card : ℝ) ≤ 16 * x := by
    have h1 : ((Acoord n δ ν T i).card : ℝ)
        ≤ 2 * (4 * Real.sqrt (n : ℝ) / (T * Real.sqrt (posOf i : ℝ)) + 2) := by linarith
    rw [hx4] at h1
    linarith
  have hgoal : 16 * Real.sqrt (n : ℝ) / (T * Real.sqrt (posOf i : ℝ)) = 16 * x := by
    rw [hxdef]; ring
  rw [hgoal]
  exact hmain

/-- Per-coordinate bound at a large index. -/
lemma Acoord_large_card_le {n : ℕ} {δ ν T : ℝ} {i : Fin n}
    (hi : ¬ smallIndex n δ (i.val)) (hδ0 : 0 < δ) (hν0 : 0 < ν) (hT0 : 0 < T)
    (hTν : T ≤ ν / 2) :
    ((Acoord n δ ν T i).card : ℝ) ≤ KL δ ν * (holeN ν T : ℝ) := by
  have h1 := Acoord_large_card_le_three_largeRad (n := n) (δ := δ) (ν := ν) (T := T) (i := i) hi
  have h2 := largeRad_upper (δ := δ) (T := T) hδ0 hT0
  have hN1 : (1 : ℝ) ≤ (holeN ν T : ℝ) := by
    exact_mod_cast holeN_ge_one (ν := ν) (T := T) hT0 hν0 hTν
  have hNT : (ν / 4 : ℝ) ≤ (holeN ν T : ℝ) * T :=
    holeN_mul_T_ge_quarter (ν := ν) (T := T) hT0 hν0 hTν
  have hinv : 1 / T ≤ 4 * (holeN ν T : ℝ) / ν := by
    rw [div_le_iff₀ hT0, div_mul_eq_mul_div, le_div_iff₀ hν0]
    linarith
  have hsqrtδ : (0 : ℝ) < Real.sqrt δ := Real.sqrt_pos.2 hδ0
  have hlarge : (largeRad δ T : ℝ) ≤ Real.sqrt 8 / (Real.sqrt δ * T) + 2 := h2
  have hstep : 3 * (Real.sqrt 8 / (Real.sqrt δ * T) + 2)
      ≤ KL δ ν * (holeN ν T : ℝ) := by
    have hA : 3 * (Real.sqrt 8 / (Real.sqrt δ * T))
        ≤ 12 * Real.sqrt 8 / (Real.sqrt δ * ν) * (holeN ν T : ℝ) := by
      have h3 : 3 * (Real.sqrt 8 / (Real.sqrt δ * T))
          = 3 * Real.sqrt 8 / Real.sqrt δ * (1 / T) := by
        first | ring | (field_simp; ring)
      rw [h3]
      calc 3 * Real.sqrt 8 / Real.sqrt δ * (1 / T)
          ≤ 3 * Real.sqrt 8 / Real.sqrt δ * (4 * (holeN ν T : ℝ) / ν) :=
            mul_le_mul_of_nonneg_left hinv (by positivity)
        _ = 12 * Real.sqrt 8 / (Real.sqrt δ * ν) * (holeN ν T : ℝ) := by
            first | ring | (field_simp; ring) | (field_simp; norm_num)
    have hB : 3 * 2 ≤ 6 * (holeN ν T : ℝ) := by linarith
    have hsum : 3 * (Real.sqrt 8 / (Real.sqrt δ * T) + 2)
        = 3 * (Real.sqrt 8 / (Real.sqrt δ * T)) + 6 := by ring
    rw [hsum, KL]
    nlinarith [hA, hB]
  linarith [h1, hlarge, hstep]


/-- The small-coordinate factor is bounded by `KS δ ν · holeN ν T`. -/
lemma small_factor_le {n k : ℕ} {δ ν T : ℝ} (hδ0 : 0 < δ) (hν0 : 0 < ν)
    (hδn2 : 2 ≤ δ * (n : ℝ)) (hk : δ * (n : ℝ) / 2 ≤ (k : ℝ)) (hk1 : 1 ≤ k)
    (hT0 : 0 < T) (hTν : T ≤ ν / 2) :
    16 * Real.sqrt (Real.exp 1 * (n : ℝ) / (k : ℝ)) / T ≤ KS δ ν * (holeN ν T : ℝ) := by
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk1
  have hkR2 : δ * (n : ℝ) ≤ 2 * (k : ℝ) := by linarith
  have hnk : (n : ℝ) / (k : ℝ) ≤ 2 / δ := by
    rw [div_le_iff₀ hkR, div_mul_eq_mul_div, le_div_iff₀ hδ0]
    linarith
  have h1 : Real.sqrt ((n : ℝ) / (k : ℝ)) ≤ Real.sqrt (2 / δ) := Real.sqrt_le_sqrt hnk
  have hNT : (ν / 4 : ℝ) ≤ (holeN ν T : ℝ) * T :=
    holeN_mul_T_ge_quarter (ν := ν) (T := T) hT0 hν0 hTν
  have hinv : 1 / T ≤ 4 * (holeN ν T : ℝ) / ν := by
    rw [div_le_iff₀ hT0, div_mul_eq_mul_div, le_div_iff₀ hν0]
    linarith
  have hprod : Real.sqrt ((n : ℝ) / (k : ℝ)) * (1 / T)
      ≤ Real.sqrt (2 / δ) * (4 * (holeN ν T : ℝ) / ν) :=
    mul_le_mul h1 hinv (by positivity) (Real.sqrt_nonneg _)
  have h16 : (0 : ℝ) ≤ 16 * Real.sqrt (Real.exp 1) := by positivity
  have hstep : 16 * (Real.sqrt (Real.exp 1) * Real.sqrt ((n : ℝ) / (k : ℝ))) * (1 / T)
      ≤ 16 * (Real.sqrt (Real.exp 1) * Real.sqrt (2 / δ)) * (4 * (holeN ν T : ℝ) / ν) := by
    calc 16 * (Real.sqrt (Real.exp 1) * Real.sqrt ((n : ℝ) / (k : ℝ))) * (1 / T)
        = 16 * Real.sqrt (Real.exp 1) * (Real.sqrt ((n : ℝ) / (k : ℝ)) * (1 / T)) := by ring
      _ ≤ 16 * Real.sqrt (Real.exp 1) * (Real.sqrt (2 / δ) * (4 * (holeN ν T : ℝ) / ν)) :=
          mul_le_mul_of_nonneg_left hprod h16
      _ = 16 * (Real.sqrt (Real.exp 1) * Real.sqrt (2 / δ)) * (4 * (holeN ν T : ℝ) / ν) := by
          ring
  have he : Real.sqrt (Real.exp 1 * (n : ℝ) / (k : ℝ))
      = Real.sqrt (Real.exp 1) * Real.sqrt ((n : ℝ) / (k : ℝ)) := by
    rw [show Real.exp 1 * (n : ℝ) / (k : ℝ) = Real.exp 1 * ((n : ℝ) / (k : ℝ)) by ring]
    rw [Real.sqrt_mul (Real.exp_nonneg 1)]
  have hKS : KS δ ν = 64 * Real.sqrt (Real.exp 1) * Real.sqrt (2 / δ) / ν := by
    rw [KS, show (2 * Real.exp 1 / δ) = Real.exp 1 * (2 / δ) by ring]
    rw [Real.sqrt_mul (Real.exp_nonneg 1)]
    ring
  calc 16 * Real.sqrt (Real.exp 1 * (n : ℝ) / (k : ℝ)) / T
      = 16 * (Real.sqrt (Real.exp 1) * Real.sqrt ((n : ℝ) / (k : ℝ))) * (1 / T) := by
        rw [he]; ring
    _ ≤ 16 * (Real.sqrt (Real.exp 1) * Real.sqrt (2 / δ)) * (4 * (holeN ν T : ℝ) / ν) := hstep
    _ = KS δ ν * (holeN ν T : ℝ) := by rw [hKS]; ring

/-- Product bound over the small coordinates. -/
lemma prod_small_le {n k : ℕ} {δ ν T : ℝ} (hδ0 : 0 < δ) (hν0 : 0 < ν)
    (hδn2 : 2 ≤ δ * (n : ℝ)) (hk : δ * (n : ℝ) / 2 ≤ (k : ℝ)) (hk1 : 1 ≤ k)
    (hT0 : 0 < T) (hTν : T ≤ ν / 2) :
    (∏ j : Fin k, 16 * Real.sqrt (n : ℝ) / (T * Real.sqrt (((j : ℕ) : ℝ) + 1)))
      ≤ (KS δ ν * (holeN ν T : ℝ)) ^ k := by
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk1
  have hkne : (k : ℝ) ≠ 0 := ne_of_gt hkR
  -- (1) exact product formula
  have hden : (∏ j : Fin k, Real.sqrt (((j : ℕ) : ℝ) + 1)) = Real.sqrt (k.factorial : ℝ) := by
    rw [← Real.sqrt_prod (s := Finset.univ)
      (x := fun j : Fin k => (((j : ℕ) : ℝ) + 1)) (by intro j _; positivity)]
    congr 1
    rw [← Finset.prod_range (n := k) (f := fun i : ℕ => ((i : ℝ) + 1))]
    rw [← Finset.prod_range_add_one_eq_factorial k]
    rw [Nat.cast_prod]
    apply Finset.prod_congr rfl
    intro i _
    push_cast
    ring
  have h1 : (∏ j : Fin k, 16 * Real.sqrt (n : ℝ) / (T * Real.sqrt (((j : ℕ) : ℝ) + 1)))
      = (16 * Real.sqrt (n : ℝ) / T) ^ k / Real.sqrt (k.factorial : ℝ) := by
    rw [show (∏ j : Fin k, 16 * Real.sqrt (n : ℝ) / (T * Real.sqrt (((j : ℕ) : ℝ) + 1)))
        = ∏ j : Fin k, (16 * Real.sqrt (n : ℝ) / T) / Real.sqrt (((j : ℕ) : ℝ) + 1) by
      apply Finset.prod_congr rfl
      intro j _
      first | ring | (field_simp; ring)]
    rw [Finset.prod_div_distrib, Finset.prod_const]
    simp only [Finset.card_univ, Fintype.card_fin]
    rw [hden]
  -- (2) factorial bound
  have hfact : 1 / Real.sqrt (k.factorial : ℝ) ≤ (Real.sqrt (Real.exp 1 / (k : ℝ))) ^ k := by
    have hke := Commons.Analysis.Real.factorial_lower_exp hk1
    have hnonneg : (0 : ℝ) ≤ (Real.exp 1 / (k : ℝ)) ^ k := by positivity
    have hmul := mul_le_mul_of_nonneg_left hke hnonneg
    have hone : (Real.exp 1 / (k : ℝ)) ^ k * ((k : ℝ) / Real.exp 1) ^ k = 1 := by
      rw [← mul_pow]
      have h2 : Real.exp 1 / (k : ℝ) * ((k : ℝ) / Real.exp 1) = 1 := by
        field_simp [hkne, Real.exp_ne_zero 1]
      rw [h2, one_pow]
    have h1' : 1 ≤ (Real.exp 1 / (k : ℝ)) ^ k * (k.factorial : ℝ) := by
      have h := hmul
      rwa [hone] at h
    have hfacpos : (0 : ℝ) < (k.factorial : ℝ) := by
      exact_mod_cast Nat.factorial_pos k
    rw [div_le_iff₀ (Real.sqrt_pos.2 hfacpos)]
    rw [← sqrt_pow_eq (Real.exp 1 / (k : ℝ)) (by positivity) k]
    rw [← Real.sqrt_mul hnonneg (k.factorial : ℝ)]
    simpa using Real.sqrt_le_sqrt h1'
  -- (3) rewrite and combine
  have hsqrtn : Real.sqrt (n : ℝ) * Real.sqrt (Real.exp 1 / (k : ℝ))
      = Real.sqrt (Real.exp 1 * (n : ℝ) / (k : ℝ)) := by
    rw [← Real.sqrt_mul (Nat.cast_nonneg n)]
    congr 1
    ring
  have hbase : 16 * Real.sqrt (n : ℝ) * Real.sqrt (Real.exp 1 / (k : ℝ))
      = 16 * Real.sqrt (Real.exp 1 * (n : ℝ) / (k : ℝ)) := by
    rw [← hsqrtn]; ring
  calc (∏ j : Fin k, 16 * Real.sqrt (n : ℝ) / (T * Real.sqrt (((j : ℕ) : ℝ) + 1)))
      = (16 * Real.sqrt (n : ℝ) / T) ^ k / Real.sqrt (k.factorial : ℝ) := h1
    _ = (16 * Real.sqrt (n : ℝ) / T) ^ k * (1 / Real.sqrt (k.factorial : ℝ)) := by ring
    _ ≤ (16 * Real.sqrt (n : ℝ) / T) ^ k * (Real.sqrt (Real.exp 1 / (k : ℝ))) ^ k :=
        mul_le_mul_of_nonneg_left hfact (by positivity)
    _ = (16 * Real.sqrt (n : ℝ) * Real.sqrt (Real.exp 1 / (k : ℝ)) / T) ^ k := by
        rw [← mul_pow]; ring
    _ = (16 * Real.sqrt (Real.exp 1 * (n : ℝ) / (k : ℝ)) / T) ^ k := by rw [hbase]
    _ ≤ (KS δ ν * (holeN ν T : ℝ)) ^ k :=
        pow_le_pow_left₀ (by positivity) (small_factor_le hδ0 hν0 hδn2 hk hk1 hT0 hTν) k

/-- **Product bound**: the product of the window cardinalities of the family
`Acoord n δ ν T` is at most `(K_A · holeN ν T)^n` for all large `n` and all
`T ∈ (0, ν/2]`. -/
theorem Acoord_prod_bound {δ ν : ℝ} (hδ0 : 0 < δ) (hδ12 : δ ≤ 1 / 2) (hν0 : 0 < ν)
    (hν1 : ν ≤ 1) :
    ∃ K_A : ℝ, 1 ≤ K_A ∧ ∃ n₀ : ℕ, 1 ≤ n₀ ∧
      ∀ n : ℕ, n₀ ≤ n → ∀ T : ℝ, 0 < T → T ≤ ν / 2 →
        (∏ i : Fin n, (((Acoord n δ ν T i).card : ℕ) : ℝ))
          ≤ (K_A * (holeN ν T : ℝ)) ^ n := by
  refine ⟨max 1 (max (KS δ ν) (KL δ ν)), le_max_left _ _, max 1 (⌈2 / δ⌉₊ + 1),
    le_max_left _ _, ?_⟩
  intro n hn T hT0 hTν
  set k : ℕ := ⌊δ * (n : ℝ)⌋₊ with hkdef
  have hn1 : 1 ≤ n := by
    have h : 1 ≤ max 1 (⌈2 / δ⌉₊ + 1) := le_max_left _ _
    omega
  have hceil_le : ⌈2 / δ⌉₊ ≤ n := by
    have h : max 1 (⌈2 / δ⌉₊ + 1) ≤ n := hn
    omega
  have hn_ge : (⌈2 / δ⌉₊ : ℝ) ≤ (n : ℝ) := by exact_mod_cast hceil_le
  have hδn2 : 2 ≤ δ * (n : ℝ) := by
    have hc : 2 / δ ≤ (⌈2 / δ⌉₊ : ℝ) := Nat.le_ceil (2 / δ)
    have hc2 : 2 / δ ≤ (n : ℝ) := le_trans hc hn_ge
    have h := (div_le_iff₀ hδ0).mp hc2
    linarith
  have hk_le_n : k ≤ n := by
    have h1 : (k : ℝ) ≤ δ * (n : ℝ) := by
      rw [hkdef]
      exact Nat.floor_le (by positivity)
    have h2 : δ * (n : ℝ) ≤ (n : ℝ) := by
      have := mul_le_mul_of_nonneg_right hδ12 (Nat.cast_nonneg n)
      linarith
    exact_mod_cast (le_trans h1 h2)
  have hk_half : δ * (n : ℝ) / 2 ≤ (k : ℝ) := by
    have hfl : δ * (n : ℝ) < (k : ℝ) + 1 := by
      rw [hkdef]
      exact Nat.lt_floor_add_one _
    linarith
  have hk1 : 1 ≤ k := by
    have : (1 : ℝ) ≤ (k : ℝ) := by linarith
    exact_mod_cast this
  -- index bookkeeping
  have hsmall_iff : ∀ i : Fin n, (smallIndex n δ (i.val) ↔ i.val < k) := by
    intro i
    rw [smallIndex_iff_pos_le]
    simp only [posOf, Nat.cast_add, Nat.cast_one]
    constructor
    · intro h
      have h' : ((i.val + 1 : ℕ) : ℝ) ≤ δ * (n : ℝ) := by
        rw [Nat.cast_add, Nat.cast_one]
        exact h
      have hle := Nat.le_floor h'
      rwa [hkdef]
    · intro h
      have hk_le : (k : ℝ) ≤ δ * (n : ℝ) := by
        rw [hkdef]
        exact Nat.floor_le (by positivity)
      have h1 : i.val + 1 ≤ k := by omega
      have h2 : ((i.val + 1 : ℕ) : ℝ) ≤ δ * (n : ℝ) := by
        rw [Nat.cast_add, Nat.cast_one]
        exact le_trans (by exact_mod_cast h1) hk_le
      rw [Nat.cast_add, Nat.cast_one] at h2
      exact h2
  set S : Finset (Fin n) := Finset.univ.filter (fun i : Fin n => smallIndex n δ (i.val))
    with hSdef
  set L : Finset (Fin n) := Finset.univ.filter (fun i : Fin n => ¬ smallIndex n δ (i.val))
    with hLdef
  have hsplit : (∏ i ∈ S, (((Acoord n δ ν T i).card : ℕ) : ℝ))
        * (∏ i ∈ L, (((Acoord n δ ν T i).card : ℕ) : ℝ))
      = ∏ i : Fin n, (((Acoord n δ ν T i).card : ℕ) : ℝ) := by
    rw [hSdef, hLdef]
    exact Finset.prod_filter_mul_prod_filter_not (Finset.univ : Finset (Fin n))
      (fun i : Fin n => smallIndex n δ (i.val))
      (fun i : Fin n => (((Acoord n δ ν T i).card : ℕ) : ℝ))
  let emb : Fin k → Fin n := fun j => ⟨j.val, lt_of_lt_of_le j.isLt hk_le_n⟩
  have hemb_inj : Function.Injective emb := by
    intro a b hab
    apply Fin.ext
    have h := congrArg Fin.val hab
    simpa [emb] using h
  have hS_eq_image : S = (Finset.univ : Finset (Fin k)).image emb := by
    rw [hSdef]
    ext i
    constructor
    · intro hi
      have hilt : i.val < k := (hsmall_iff i).1 (Finset.mem_filter.mp hi).2
      exact Finset.mem_image.mpr ⟨⟨i.val, hilt⟩, Finset.mem_univ _, Fin.ext rfl⟩
    · intro hi
      rcases Finset.mem_image.mp hi with ⟨j, _, hj⟩
      rw [← hj]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hsmall_iff (emb j)).2 j.isLt⟩
  have hcardS : S.card = k := by
    rw [hS_eq_image, Finset.card_image_of_injective _ hemb_inj]
    simp
  have hcardL : L.card = n - k := by
    have h2 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
      (p := fun i : Fin n => smallIndex n δ (i.val))
    rw [← hSdef, ← hLdef] at h2
    simp only [Finset.card_univ, Fintype.card_fin] at h2
    omega
  -- small product
  have hsmall : (∏ i ∈ S, (((Acoord n δ ν T i).card : ℕ) : ℝ))
      ≤ (KS δ ν * (holeN ν T : ℝ)) ^ k := by
    have hstep1 : (∏ i ∈ S, (((Acoord n δ ν T i).card : ℕ) : ℝ))
        ≤ ∏ i ∈ S, (16 * Real.sqrt (n : ℝ) / (T * Real.sqrt (posOf i : ℝ))) := by
      apply Finset.prod_le_prod
      · intro i _
        exact Nat.cast_nonneg _
      · intro i hi
        rw [hSdef] at hi
        exact Acoord_small_card_le (Finset.mem_filter.mp hi).2 hν0 hν1 hT0 hTν
    have hstep2 : (∏ i ∈ S, (16 * Real.sqrt (n : ℝ) / (T * Real.sqrt (posOf i : ℝ))))
        = ∏ j : Fin k, (16 * Real.sqrt (n : ℝ) / (T * Real.sqrt (((j : ℕ) : ℝ) + 1))) := by
      rw [hS_eq_image, Finset.prod_image (s := Finset.univ) (g := emb)
        (f := fun i : Fin n => 16 * Real.sqrt (n : ℝ) / (T * Real.sqrt (posOf i : ℝ)))
        hemb_inj.injOn]
      apply Finset.prod_congr rfl
      intro j _
      simp [posOf, emb]
    calc (∏ i ∈ S, (((Acoord n δ ν T i).card : ℕ) : ℝ))
        ≤ ∏ i ∈ S, (16 * Real.sqrt (n : ℝ) / (T * Real.sqrt (posOf i : ℝ))) := hstep1
      _ = ∏ j : Fin k, (16 * Real.sqrt (n : ℝ) / (T * Real.sqrt (((j : ℕ) : ℝ) + 1))) :=
          hstep2
      _ ≤ (KS δ ν * (holeN ν T : ℝ)) ^ k :=
          prod_small_le hδ0 hν0 hδn2 hk_half hk1 hT0 hTν
  -- large product
  have hlarge : (∏ i ∈ L, (((Acoord n δ ν T i).card : ℕ) : ℝ))
      ≤ (KL δ ν * (holeN ν T : ℝ)) ^ (n - k) := by
    have hstep1 : (∏ i ∈ L, (((Acoord n δ ν T i).card : ℕ) : ℝ))
        ≤ ∏ i ∈ L, (KL δ ν * (holeN ν T : ℝ)) := by
      apply Finset.prod_le_prod
      · intro i _
        exact Nat.cast_nonneg _
      · intro i hi
        rw [hLdef] at hi
        exact Acoord_large_card_le (Finset.mem_filter.mp hi).2 hδ0 hν0 hT0 hTν
    rw [Finset.prod_const] at hstep1
    rwa [hcardL] at hstep1
  -- assembly
  have hNpos : (0 : ℝ) ≤ (holeN ν T : ℝ) := by
    have := holeN_ge_one (ν := ν) (T := T) hT0 hν0 hTν
    exact_mod_cast (by omega : 0 ≤ holeN ν T)
  have hKs0 : 0 ≤ KS δ ν := by rw [KS]; positivity
  have hKl0 : 0 ≤ KL δ ν := by rw [KL]; positivity
  have hKA1 : KS δ ν ≤ max 1 (max (KS δ ν) (KL δ ν)) :=
    le_trans (le_max_left _ _) (le_max_right _ _)
  have hKA2 : KL δ ν ≤ max 1 (max (KS δ ν) (KL δ ν)) :=
    le_trans (le_max_right _ _) (le_max_right _ _)
  have hKA0 : (0 : ℝ) ≤ max 1 (max (KS δ ν) (KL δ ν)) :=
    le_trans zero_le_one (le_max_left _ _)
  calc ∏ i : Fin n, (((Acoord n δ ν T i).card : ℕ) : ℝ)
      = (∏ i ∈ S, (((Acoord n δ ν T i).card : ℕ) : ℝ))
          * (∏ i ∈ L, (((Acoord n δ ν T i).card : ℕ) : ℝ)) := hsplit.symm
    _ ≤ (KS δ ν * (holeN ν T : ℝ)) ^ k * (KL δ ν * (holeN ν T : ℝ)) ^ (n - k) :=
        mul_le_mul hsmall hlarge (Finset.prod_nonneg (fun i _ => Nat.cast_nonneg _))
          (pow_nonneg (mul_nonneg hKs0 hNpos) k)
    _ ≤ (max 1 (max (KS δ ν) (KL δ ν)) * (holeN ν T : ℝ)) ^ k
          * (max 1 (max (KS δ ν) (KL δ ν)) * (holeN ν T : ℝ)) ^ (n - k) := by
        apply mul_le_mul
        · exact pow_le_pow_left₀ (mul_nonneg hKs0 hNpos)
            (mul_le_mul_of_nonneg_right hKA1 hNpos) k
        · exact pow_le_pow_left₀ (mul_nonneg hKl0 hNpos)
            (mul_le_mul_of_nonneg_right hKA2 hNpos) (n - k)
        · exact pow_nonneg (mul_nonneg hKl0 hNpos) (n - k)
        · exact pow_nonneg (mul_nonneg hKA0 hNpos) k
    _ = (max 1 (max (KS δ ν) (KL δ ν)) * (holeN ν T : ℝ)) ^ (k + (n - k)) := by
        rw [pow_add]
    _ = (max 1 (max (KS δ ν) (KL δ ν)) * (holeN ν T : ℝ)) ^ n := by
        rw [Nat.add_sub_of_le hk_le_n]

end Submission.Section5D
