/-
Copyright (c) 2026 The AnnalsChallenge team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AnnalsChallenge team
-/
import Mathlib
import Submission.Work.Peluse.Basic

/-!
# The one-dimensional counting bound for `Work.Peluse.Ulower.boxNormPow_le_one_sub`

For the arithmetic-progression direction set `arithIcc c D = {c, 2c, …, Dc}` (`c ≠ 0`, `D ≥ 2`) and
any `W ≥ 0` we prove

`∑_{a,b ∈ c[D]} min (|a - b|, W) ≥ min (|c| D³/8) (W D²/2)`.

The proof uses the difference-distribution identity `pairSum_dist`, the sharp discrete bound
`sum_Icc_posPart_le` (`∑_{d ∈ [1,M]} (θ-d)₊ ≤ θ²/2 - θ/2 + 1/8`), and the resulting case analysis
in `two_sum_le` (`Ψ(θ) ≥ min (D³/8) (θD²/2)` for `Ψ(θ) = 2∑_{d} (D-d) min(d,θ)`).
-/

set_option autoImplicit false

open scoped BigOperators

namespace Work.Peluse.Ulower

noncomputable section

open Work.Peluse

/-! ## Cardinalities -/

lemma card_symIcc (L : ℕ) : (symIcc L).card = 2 * L + 1 := by
  rw [symIcc, Int.card_Icc]
  have h : (L : ℤ) + 1 - (-(L : ℤ)) = ((2 * L + 1 : ℕ) : ℤ) := by push_cast; ring
  rw [h, Int.toNat_natCast]

lemma card_arithIcc {c : ℤ} (hc : c ≠ 0) (D : ℕ) : (arithIcc c D).card = D := by
  rw [arithIcc, Finset.card_image_of_injOn]
  · simp
  · intro a _ b _ hab
    have h : (a : ℤ) = (b : ℤ) := mul_left_cancel₀ hc hab
    exact_mod_cast h

/-! ## Elementary sums over `[1,m]` -/

lemma sum_Icc_one_id (m : ℕ) :
    (∑ d ∈ Finset.Icc 1 m, (d : ℝ)) = (m : ℝ) * ((m : ℝ) + 1) / 2 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_Icc_succ_top (Nat.le_add_left 1 m)]
    rw [ih]
    push_cast
    ring

lemma sum_Icc_one_const (m : ℕ) (a : ℝ) :
    (∑ _d ∈ Finset.Icc 1 m, a) = (m : ℝ) * a := by
  rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel]
  simp [nsmul_eq_mul]

lemma sum_Icc_sub_id (m : ℕ) (A : ℝ) :
    (∑ d ∈ Finset.Icc 1 m, (A - (d : ℝ))) = (m : ℝ) * A - (m : ℝ) * ((m : ℝ) + 1) / 2 := by
  rw [Finset.sum_sub_distrib, sum_Icc_one_const, sum_Icc_one_id]

/-- Reflection of a sum over `[1,N]`. -/
lemma sum_Icc_reflect (N : ℕ) (φ : ℕ → ℝ) :
    (∑ m ∈ Finset.Icc 1 N, φ (N + 1 - m)) = ∑ j ∈ Finset.Icc 1 N, φ j := by
  refine Finset.sum_bij (fun m _ => N + 1 - m) ?_ ?_ ?_ ?_
  · intro m hm
    simp only [Finset.mem_Icc] at hm ⊢
    omega
  · intro m hm m' hm' h
    simp only [Finset.mem_Icc] at hm hm'
    omega
  · intro j hj
    simp only [Finset.mem_Icc] at hj
    exact ⟨N + 1 - j, by simp only [Finset.mem_Icc]; omega, by omega⟩
  · intro m _
    rfl

/-! ## Pointwise facts -/

lemma min_eq_sub_max (x θ : ℝ) : min x θ = θ - max 0 (θ - x) := by
  rcases le_total x θ with h | h
  · rw [min_eq_left h, max_eq_right (by linarith)]; ring
  · rw [min_eq_right h, max_eq_left (by linarith)]; ring

lemma mul_min_eq (c : ℝ) (hc : 0 ≤ c) (a b : ℝ) : c * min a b = min (c * a) (c * b) := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, min_eq_left (mul_le_mul_of_nonneg_left h hc)]
  · rw [min_eq_right h, min_eq_right (mul_le_mul_of_nonneg_left h hc)]

/-! ## The sharp discrete `(θ - ·)₊` bound -/

lemma sum_Icc_posPart_le (θ : ℝ) (hθ : 0 ≤ θ) (M : ℕ) :
    (∑ d ∈ Finset.Icc 1 M, max 0 (θ - (d : ℝ))) ≤ θ ^ 2 / 2 - θ / 2 + 1 / 8 := by
  classical
  set K : ℕ := ⌈θ⌉₊ with hK
  have hKθ : θ ≤ (K : ℝ) := by rw [hK]; exact Nat.le_ceil θ
  rcases Nat.eq_zero_or_pos K with hK0 | hKpos
  · -- `⌈θ⌉₊ = 0`, hence `θ = 0` and the sum vanishes
    have hθzero : θ = 0 := by
      have h1 : θ ≤ 0 := by
        have h2 : ⌈θ⌉₊ ≤ 0 := by rw [← hK]; exact hK0.le
        simpa using (Nat.ceil_le (a := θ) (n := 0)).mp h2
      linarith
    have hzero : (∑ d ∈ Finset.Icc 1 M, max 0 (θ - (d : ℝ))) = 0 := by
      refine Finset.sum_eq_zero (fun d _ => ?_)
      rw [hθzero, zero_sub, max_eq_left]
      exact neg_nonpos.mpr (Nat.cast_nonneg d)
    rw [hzero, hθzero]
    norm_num
  · have hlt : K - 1 < K := by
      simpa using Nat.pred_lt hKpos.ne'
    have hterm : ∀ d ∈ Finset.Icc 1 M,
        max 0 (θ - (d : ℝ)) ≤ if d ≤ K - 1 then (θ - (d : ℝ)) else 0 := by
      intro d _
      by_cases h : d ≤ K - 1
      · rw [if_pos h]
        have hd : (d : ℝ) < θ := by
          by_contra hcon
          have hcon' : θ ≤ (d : ℝ) := not_lt.mp hcon
          have hKd : K ≤ d := Nat.ceil_le.mpr hcon'
          have hle : K ≤ K - 1 := le_trans hKd h
          exact (Nat.not_le.mpr hlt) hle
        rw [max_eq_right (by linarith)]
      · rw [if_neg h]
        have h1 : K - 1 < d := not_le.mp h
        have hKd : K ≤ d := Nat.le_of_pred_lt h1
        have hKd' : (K : ℝ) ≤ (d : ℝ) := by exact_mod_cast hKd
        rw [max_eq_left (by linarith)]
    have hbd : ∀ d : ℕ, d ≤ K - 1 → (d : ℝ) < θ := by
      intro d hd
      by_contra hcon
      have hcon' : θ ≤ (d : ℝ) := not_lt.mp hcon
      have hKd : K ≤ d := Nat.ceil_le.mpr hcon'
      have hle : K ≤ K - 1 := le_trans hKd hd
      exact (Nat.not_le.mpr hlt) hle
    calc (∑ d ∈ Finset.Icc 1 M, max 0 (θ - (d : ℝ)))
        ≤ ∑ d ∈ Finset.Icc 1 M, (if d ≤ K - 1 then (θ - (d : ℝ)) else 0) :=
          Finset.sum_le_sum hterm
      _ = ∑ d ∈ (Finset.Icc 1 M).filter (fun d => d ≤ K - 1), (θ - (d : ℝ)) := by
          rw [Finset.sum_filter]
      _ ≤ ∑ d ∈ Finset.Icc 1 (K - 1), (θ - (d : ℝ)) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
          · intro d hd
            simp only [Finset.mem_filter, Finset.mem_Icc] at hd
            exact Finset.mem_Icc.mpr ⟨hd.1.1, hd.2⟩
          · intro d hd _
            simp only [Finset.mem_Icc] at hd
            have := hbd d hd.2
            linarith
      _ = ((K - 1 : ℕ) : ℝ) * θ - ((K - 1 : ℕ) : ℝ) * (((K - 1 : ℕ) : ℝ) + 1) / 2 :=
          sum_Icc_sub_id (K - 1) θ
      _ ≤ θ ^ 2 / 2 - θ / 2 + 1 / 8 := by
          have hsq : 0 ≤ (θ - ((K - 1 : ℕ) : ℝ) - 1 / 2) ^ 2 := sq_nonneg _
          nlinarith [hsq]

/-! ## The distribution of the difference -/

lemma pairSum_dist (D : ℕ) (g : ℝ → ℝ) :
    (∑ n ∈ Finset.Icc 1 D, ∑ m ∈ Finset.Icc 1 D, g |(n : ℝ) - (m : ℝ)|)
      = (D : ℝ) * g 0
        + 2 * ∑ d ∈ Finset.Icc 1 D, ((D : ℝ) - (d : ℝ)) * g (d : ℝ) := by
  induction D with
  | zero => simp
  | succ D ih =>
    have hcast : ∀ n ∈ Finset.Icc 1 D,
        |(n : ℝ) - ((D + 1 : ℕ) : ℝ)| = ((D + 1 - n : ℕ) : ℝ) := by
      intro n hn
      simp only [Finset.mem_Icc] at hn
      have hle : (n : ℝ) ≤ ((D + 1 : ℕ) : ℝ) := by
        have : n ≤ D + 1 := by omega
        exact_mod_cast this
      rw [abs_of_nonpos (by linarith), Nat.cast_sub (by omega : n ≤ D + 1)]
      push_cast
      ring
    rw [Finset.sum_Icc_succ_top (show (1 : ℕ) ≤ D + 1 by omega)]
    have hinner : ∀ n ∈ Finset.Icc 1 D,
        (∑ m ∈ Finset.Icc 1 (D + 1), g |(n : ℝ) - (m : ℝ)|)
          = (∑ m ∈ Finset.Icc 1 D, g |(n : ℝ) - (m : ℝ)|) + g (((D + 1 - n : ℕ)) : ℝ) := by
      intro n hn
      rw [Finset.sum_Icc_succ_top (show (1 : ℕ) ≤ D + 1 by omega)]
      rw [hcast n hn]
    rw [Finset.sum_congr rfl hinner, Finset.sum_add_distrib]
    rw [Finset.sum_Icc_succ_top (show (1 : ℕ) ≤ D + 1 by omega)]
    have hlast : g |((D + 1 : ℕ) : ℝ) - ((D + 1 : ℕ) : ℝ)| = g 0 := by norm_num
    rw [hlast]
    have hrefl : ∀ m ∈ Finset.Icc 1 D,
        g |((D + 1 : ℕ) : ℝ) - (m : ℝ)| = g (((D + 1 - m : ℕ)) : ℝ) := by
      intro m hm
      rw [abs_sub_comm]
      exact congrArg g (hcast m hm)
    rw [Finset.sum_congr rfl hrefl]
    rw [sum_Icc_reflect D (fun j => g (j : ℝ))]
    rw [ih]
    have hstep : (((D + 1 : ℕ)) : ℝ) * g 0
          + 2 * ∑ d ∈ Finset.Icc 1 (D + 1), ((((D + 1 : ℕ)) : ℝ) - (d : ℝ)) * g (d : ℝ)
        = ((D : ℝ) * g 0 + 2 * ∑ d ∈ Finset.Icc 1 D, ((D : ℝ) - (d : ℝ)) * g (d : ℝ))
          + (2 * ∑ j ∈ Finset.Icc 1 D, g (j : ℝ) + g 0) := by
      rw [show (((D + 1 : ℕ)) : ℝ) = (D : ℝ) + 1 by push_cast; ring]
      rw [Finset.sum_Icc_succ_top (show (1 : ℕ) ≤ D + 1 by omega)]
      have hlastd : (((D : ℝ) + 1) - (((D + 1 : ℕ)) : ℝ)) * g (((D + 1 : ℕ)) : ℝ) = 0 := by
        rw [show (((D + 1 : ℕ)) : ℝ) = (D : ℝ) + 1 by push_cast; ring]; ring
      rw [hlastd, add_zero]
      have hsplit : ∀ d ∈ Finset.Icc 1 D,
          (((D : ℝ) + 1) - (d : ℝ)) * g (d : ℝ)
            = ((D : ℝ) - (d : ℝ)) * g (d : ℝ) + g (d : ℝ) := by
        intro d _; ring
      rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib]
      ring
    rw [hstep]
    ring

/-! ## The `Ψ` bound -/

lemma psi_bound (D : ℕ) (hD : 2 ≤ D) {θ : ℝ} (hθ : 0 ≤ θ) :
    min ((D : ℝ) ^ 3 / 8) (θ * (D : ℝ) ^ 2 / 2)
      ≤ 2 * ∑ d ∈ Finset.Icc 1 D, ((D : ℝ) - (d : ℝ)) * min (d : ℝ) θ := by
  have hD2 : (2 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD
  have hD0 : (0 : ℝ) ≤ (D : ℝ) := le_trans (by norm_num) hD2
  have hsumD : (∑ d ∈ Finset.Icc 1 D, ((D : ℝ) - (d : ℝ))) = (D : ℝ) * ((D : ℝ) - 1) / 2 := by
    rw [sum_Icc_sub_id D (D : ℝ)]; ring
  have hnonneg : ∀ d ∈ Finset.Icc 1 D, 0 ≤ (D : ℝ) - (d : ℝ) := by
    intro d hd
    simp only [Finset.mem_Icc] at hd
    have : (d : ℝ) ≤ (D : ℝ) := by exact_mod_cast hd.2
    linarith
  -- the exact value: Ψ(θ') = θ' D(D-1) - 2Σ (D-d) (θ'-d)₊
  have hkey : ∀ θ' : ℝ, 2 * (∑ d ∈ Finset.Icc 1 D, ((D : ℝ) - (d : ℝ)) * min (d : ℝ) θ')
      = θ' * ((D : ℝ) * ((D : ℝ) - 1))
        - 2 * ∑ d ∈ Finset.Icc 1 D, ((D : ℝ) - (d : ℝ)) * max 0 (θ' - (d : ℝ)) := by
    intro θ'
    have h1 : ∀ d ∈ Finset.Icc 1 D, ((D : ℝ) - (d : ℝ)) * min (d : ℝ) θ'
        = θ' * ((D : ℝ) - (d : ℝ)) - ((D : ℝ) - (d : ℝ)) * max 0 (θ' - (d : ℝ)) := by
      intro d _
      rw [min_eq_sub_max]
      ring
    rw [show (∑ d ∈ Finset.Icc 1 D, ((D : ℝ) - (d : ℝ)) * min (d : ℝ) θ')
          = ∑ d ∈ Finset.Icc 1 D,
              (θ' * ((D : ℝ) - (d : ℝ)) - ((D : ℝ) - (d : ℝ)) * max 0 (θ' - (d : ℝ)))
          from Finset.sum_congr rfl h1,
      Finset.sum_sub_distrib,
      show (∑ d ∈ Finset.Icc 1 D, θ' * ((D : ℝ) - (d : ℝ)))
          = θ' * ∑ d ∈ Finset.Icc 1 D, ((D : ℝ) - (d : ℝ)) from (Finset.mul_sum _ _ _).symm,
      hsumD]
    ring
  -- the subtracted sum
  have hbd : ∀ θ' : ℝ, 0 ≤ θ' →
      (∑ d ∈ Finset.Icc 1 D, ((D : ℝ) - (d : ℝ)) * max 0 (θ' - (d : ℝ)))
        ≤ (D : ℝ) * (θ' ^ 2 / 2 - θ' / 2 + 1 / 8) := by
    intro θ' hθ'
    have h1 : ∀ d ∈ Finset.Icc 1 D, ((D : ℝ) - (d : ℝ)) * max 0 (θ' - (d : ℝ))
        ≤ (D : ℝ) * max 0 (θ' - (d : ℝ)) := by
      intro d hd
      have hx : 0 ≤ max 0 (θ' - (d : ℝ)) := le_max_left _ _
      have hle : ((D : ℝ) - (d : ℝ)) ≤ (D : ℝ) := by
        have : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg _
        linarith
      exact mul_le_mul_of_nonneg_right hle hx
    refine le_trans (Finset.sum_le_sum h1) ?_
    rw [show (∑ d ∈ Finset.Icc 1 D, (D : ℝ) * max 0 (θ' - (d : ℝ)))
        = (D : ℝ) * ∑ d ∈ Finset.Icc 1 D, max 0 (θ' - (d : ℝ)) from (Finset.mul_sum _ _ _).symm]
    exact mul_le_mul_of_nonneg_left (sum_Icc_posPart_le θ' hθ' D) hD0
  -- value at θ' ≤ 1
  have hval1 : ∀ θ' : ℝ, θ' ≤ 1 →
      2 * (∑ d ∈ Finset.Icc 1 D, ((D : ℝ) - (d : ℝ)) * min (d : ℝ) θ')
        = θ' * ((D : ℝ) * ((D : ℝ) - 1)) := by
    intro θ' hθ'1
    have hmin : ∀ d ∈ Finset.Icc 1 D, min (d : ℝ) θ' = θ' := by
      intro d hd
      simp only [Finset.mem_Icc] at hd
      have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd.1
      exact min_eq_right (by linarith)
    rw [show (∑ d ∈ Finset.Icc 1 D, ((D : ℝ) - (d : ℝ)) * min (d : ℝ) θ')
          = ∑ d ∈ Finset.Icc 1 D, ((D : ℝ) - (d : ℝ)) * θ'
          from Finset.sum_congr rfl (fun d hd => by rw [hmin d hd]),
      show (∑ d ∈ Finset.Icc 1 D, ((D : ℝ) - (d : ℝ)) * θ')
          = (∑ d ∈ Finset.Icc 1 D, ((D : ℝ) - (d : ℝ))) * θ' from (Finset.sum_mul _ _ _).symm,
      hsumD]
    ring
  -- monotonicity
  have hmono : ∀ a b : ℝ, a ≤ b →
      2 * (∑ d ∈ Finset.Icc 1 D, ((D : ℝ) - (d : ℝ)) * min (d : ℝ) a)
        ≤ 2 * ∑ d ∈ Finset.Icc 1 D, ((D : ℝ) - (d : ℝ)) * min (d : ℝ) b := by
    intro a b hab
    have h1 : ∀ d ∈ Finset.Icc 1 D, ((D : ℝ) - (d : ℝ)) * min (d : ℝ) a
        ≤ ((D : ℝ) - (d : ℝ)) * min (d : ℝ) b :=
      fun d hd => mul_le_mul_of_nonneg_left (min_le_min le_rfl hab) (hnonneg d hd)
    linarith [Finset.sum_le_sum h1]
  rcases le_total θ 1 with h1 | h1
  · rcases le_total θ ((D : ℝ) / 4) with h2 | h2
    · rw [min_eq_right (by nlinarith), hval1 θ h1]
      have hA : (0 : ℝ) ≤ θ * (D : ℝ) := mul_nonneg hθ hD0
      have hB : (D : ℝ) / 2 ≤ (D : ℝ) - 1 := by linarith
      have hC := mul_le_mul_of_nonneg_left hB hA
      nlinarith [hC]
    · rw [min_eq_left (by nlinarith), hval1 θ h1]
      have hstep : ((D : ℝ) / 4) * ((D : ℝ) * ((D : ℝ) - 1))
          ≤ θ * ((D : ℝ) * ((D : ℝ) - 1)) :=
        mul_le_mul_of_nonneg_right h2 (by nlinarith)
      have hprod : (0 : ℝ) ≤ (D : ℝ) ^ 2 * ((D : ℝ) - 2) :=
        mul_nonneg (by positivity) (by linarith)
      nlinarith [hstep, hprod]
  · rcases le_total θ ((D : ℝ) / 4) with h2 | h2
    · rw [min_eq_right (by nlinarith)]
      have hkey' : θ * ((D : ℝ) * ((D : ℝ) - 1)) - 2 * (D : ℝ) * (θ ^ 2 / 2 - θ / 2 + 1 / 8)
          ≤ 2 * ∑ d ∈ Finset.Icc 1 D, ((D : ℝ) - (d : ℝ)) * min (d : ℝ) θ := by
        rw [hkey θ]
        linarith [hbd θ hθ]
      have hchain : (1 : ℝ) / 4 ≤ θ * ((D : ℝ) / 2 - θ) := by
        have he : θ * ((D : ℝ) / 2 - θ)
            = (θ - 1) * ((D : ℝ) / 2 - θ) + ((D : ℝ) / 2 - θ) := by ring
        rw [he]
        have h2' : 0 ≤ (D : ℝ) / 2 - θ := by linarith
        have hsq : 0 ≤ (θ - 1) * ((D : ℝ) / 2 - θ) := mul_nonneg (by linarith) h2'
        have h5 : (D : ℝ) / 4 ≤ (D : ℝ) / 2 - θ := by linarith
        have h6 : (1 : ℝ) / 4 ≤ (D : ℝ) / 4 := by linarith
        linarith
      nlinarith [hkey', hchain, hD2]
    · rw [min_eq_left (by nlinarith)]
      rcases le_total ((D : ℝ) / 4) 1 with h3 | h3
      · have hmono1 := hmono 1 θ h1
        rw [hval1 1 le_rfl] at hmono1
        have h4 : (D : ℝ) ^ 2 ≤ 8 * ((D : ℝ) - 1) := by nlinarith [h3, hD2]
        have hprod : (D : ℝ) ^ 3 / 8 ≤ (D : ℝ) * ((D : ℝ) - 1) := by
          have := mul_le_mul_of_nonneg_left h4 hD0
          nlinarith [this]
        nlinarith [hmono1, hprod]
      · have hmono1 := hmono ((D : ℝ) / 4) θ h2
        have hkey4 : ((D : ℝ) / 4) * ((D : ℝ) * ((D : ℝ) - 1))
            - 2 * (D : ℝ) * (((D : ℝ) / 4) ^ 2 / 2 - ((D : ℝ) / 4) / 2 + 1 / 8)
            ≤ 2 * ∑ d ∈ Finset.Icc 1 D, ((D : ℝ) - (d : ℝ)) * min (d : ℝ) ((D : ℝ) / 4) := by
          rw [hkey ((D : ℝ) / 4)]
          linarith [hbd ((D : ℝ) / 4) (by linarith)]
        have hchain := le_trans hkey4 hmono1
        have hprod : (0 : ℝ) ≤ (D : ℝ) ^ 3 * ((D : ℝ) - 2) :=
          mul_nonneg (by positivity) (by linarith)
        nlinarith [hchain, hprod]

/-! ## The `c, W` form -/

lemma two_sum_le (D : ℕ) (hD : 2 ≤ D) {c W : ℝ} (hc : 0 ≤ c) (hW : 0 ≤ W) :
    min (c * (D : ℝ) ^ 3 / 8) (W * (D : ℝ) ^ 2 / 2)
      ≤ 2 * ∑ d ∈ Finset.Icc 1 D, ((D : ℝ) - (d : ℝ)) * min (c * (d : ℝ)) W := by
  rcases eq_or_lt_of_le hc with hc0 | hcpos
  · subst hc0
    have hL : min ((0 : ℝ) * (D : ℝ) ^ 3 / 8) (W * (D : ℝ) ^ 2 / 2) = 0 := by
      rw [zero_mul, zero_div]
      exact min_eq_left (by positivity)
    have hR : 2 * ∑ d ∈ Finset.Icc 1 D, ((D : ℝ) - (d : ℝ)) * min ((0 : ℝ) * (d : ℝ)) W = 0 := by
      have hterm : ∀ d ∈ Finset.Icc 1 D,
          ((D : ℝ) - (d : ℝ)) * min ((0 : ℝ) * (d : ℝ)) W = 0 := by
        intro d _
        rw [zero_mul, min_eq_left hW, mul_zero]
      rw [Finset.sum_congr rfl hterm]
      simp
    rw [hL, hR]
  · set θ : ℝ := W / c with hθ
    have hθ0 : 0 ≤ θ := by rw [hθ]; positivity
    have hWc : W = c * θ := by rw [hθ]; field_simp
    have h1 := psi_bound D hD hθ0
    have e1 : min (c * (D : ℝ) ^ 3 / 8) (W * (D : ℝ) ^ 2 / 2)
        = c * min ((D : ℝ) ^ 3 / 8) (θ * (D : ℝ) ^ 2 / 2) := by
      rw [hWc]
      have h2 : c * θ * (D : ℝ) ^ 2 / 2 = c * (θ * (D : ℝ) ^ 2 / 2) := by ring
      have h3 : c * (D : ℝ) ^ 3 / 8 = c * ((D : ℝ) ^ 3 / 8) := by ring
      rw [h2, h3, mul_min_eq c hc]
    have e2 : 2 * ∑ d ∈ Finset.Icc 1 D, ((D : ℝ) - (d : ℝ)) * min (c * (d : ℝ)) W
        = c * (2 * ∑ d ∈ Finset.Icc 1 D, ((D : ℝ) - (d : ℝ)) * min (d : ℝ) θ) := by
      rw [hWc]
      have hterm : ∀ d ∈ Finset.Icc 1 D,
          ((D : ℝ) - (d : ℝ)) * min (c * (d : ℝ)) (c * θ)
            = c * (((D : ℝ) - (d : ℝ)) * min (d : ℝ) θ) := by
        intro d _
        rw [show min (c * (d : ℝ)) (c * θ) = c * min (d : ℝ) θ
          from (mul_min_eq c hc (d : ℝ) θ).symm]
        ring
      rw [Finset.sum_congr rfl hterm,
        show (∑ d ∈ Finset.Icc 1 D, c * (((D : ℝ) - (d : ℝ)) * min (d : ℝ) θ))
          = c * ∑ d ∈ Finset.Icc 1 D, ((D : ℝ) - (d : ℝ)) * min (d : ℝ) θ
          from (Finset.mul_sum _ _ _).symm]
      ring
    rw [e1, e2]
    exact mul_le_mul_of_nonneg_left h1 hc

/-! ## The Pi-factorisation -/

/-- The equivalence `(Fin (n+1) → α) ≃ α × (Fin n → α)` splitting off the first coordinate. -/
def finSuccArrowEquiv (n : ℕ) (α : Type*) : (Fin (n + 1) → α) ≃ α × (Fin n → α) where
  toFun f := (f 0, fun i => f i.succ)
  invFun p := Fin.cons p.1 p.2
  left_inv f := by
    have h : Fin.cons (f 0) (fun i : Fin n => f i.succ) = f := Fin.cons_self_tail f
    simpa using h
  right_inv p := by
    obtain ⟨a, u⟩ := p
    simp [Fin.cons_zero, Fin.cons_succ]

lemma sum_pi_apply_zero {n : ℕ} {α : Type*} [Fintype α] {φ : α → ℝ} :
    (∑ f : Fin (n + 1) → α, φ (f 0)) = (Fintype.card α : ℝ) ^ n * ∑ a, φ a := by
  classical
  rw [Fintype.sum_equiv (finSuccArrowEquiv n α) (fun f => φ (f 0))
      (fun p : α × (Fin n → α) => φ p.1) (by intro f; rfl)]
  rw [Fintype.sum_prod_type]
  have h1 : ∀ a : α, (∑ _u : Fin n → α, φ a) = (Fintype.card (Fin n → α) : ℝ) * φ a := by
    intro a
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [Finset.sum_congr rfl (fun a _ => h1 a), ← Finset.mul_sum]
  have hcard : ((Fintype.card (Fin n → α) : ℕ) : ℝ) = (Fintype.card α : ℝ) ^ n := by
    rw [Fintype.card_fun, Fintype.card_fin]
    push_cast
    ring
  rw [hcard]

/-! ## The main bound -/

theorem arithIcc_pairMin_bound {c₀ : ℤ} (hc₀ : c₀ ≠ 0) {D : ℕ} (hD : 2 ≤ D) {W : ℝ}
    (hW : 0 ≤ W) :
    min ((|(c₀ : ℝ)| * (D : ℝ) ^ 3) / 8) (W * (D : ℝ) ^ 2 / 2)
      ≤ ∑ a : {x : ℤ // x ∈ arithIcc c₀ D}, ∑ b : {x : ℤ // x ∈ arithIcc c₀ D},
          min (|((a : ℤ) : ℝ) - ((b : ℤ) : ℝ)|) W := by
  have h1 : (∑ a : {x : ℤ // x ∈ arithIcc c₀ D}, ∑ b : {x : ℤ // x ∈ arithIcc c₀ D},
        min (|((a : ℤ) : ℝ) - ((b : ℤ) : ℝ)|) W)
      = ∑ a ∈ arithIcc c₀ D, ∑ b ∈ arithIcc c₀ D, min (|(a : ℝ) - (b : ℝ)|) W := by
    rw [Finset.sum_coe_sort (arithIcc c₀ D)
      (fun a => ∑ b : {x : ℤ // x ∈ arithIcc c₀ D}, min (|(a : ℝ) - ((b : ℤ) : ℝ)|) W)]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    exact Finset.sum_coe_sort (arithIcc c₀ D) (fun b => min (|(a : ℝ) - (b : ℝ)|) W)
  rw [h1]
  have hinj : Set.InjOn (fun n : ℕ => c₀ * (n : ℤ)) ↑(Finset.Icc 1 D) := by
    intro x hx y hy h
    simp only [Finset.mem_coe, Finset.mem_Icc] at hx hy
    have h' : (x : ℤ) = (y : ℤ) := mul_left_cancel₀ hc₀ h
    exact_mod_cast h'
  have h2 : (∑ a ∈ arithIcc c₀ D, ∑ b ∈ arithIcc c₀ D, min (|(a : ℝ) - (b : ℝ)|) W)
      = ∑ x ∈ Finset.Icc 1 D, ∑ y ∈ Finset.Icc 1 D,
          min ((|(c₀ : ℝ)|) * |(x : ℝ) - (y : ℝ)|) W := by
    simp only [arithIcc]
    rw [Finset.sum_image hinj]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [Finset.sum_image hinj]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    have hc : (((c₀ * (x : ℤ) : ℤ)) : ℝ) = (c₀ : ℝ) * (x : ℝ) := by push_cast; ring
    have hd : (((c₀ * (y : ℤ) : ℤ)) : ℝ) = (c₀ : ℝ) * (y : ℝ) := by push_cast; ring
    rw [hc, hd, ← abs_mul]
    ring_nf
  rw [h2, pairSum_dist D (fun x => min ((|(c₀ : ℝ)|) * x) W)]
  have hg0 : min ((|(c₀ : ℝ)|) * 0) W = 0 := by rw [mul_zero]; exact min_eq_left hW
  rw [show (D : ℝ) * min ((|(c₀ : ℝ)|) * 0) W = 0 by rw [hg0, mul_zero]]
  rw [zero_add]
  exact two_sum_le D hD (abs_nonneg _) hW

end

end Work.Peluse.Ulower
