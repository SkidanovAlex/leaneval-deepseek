import Mathlib
import Submission.Commons.NumberTheory.Sieve.LambdaR_prime
import Submission.Commons.NumberTheory.Sieve.nu_majorant_lower

/-!
# The Goldston–Yıldırım majorant on `ZMod p` (Green–Tao Definition 8.1)

Green–Tao define, for `R = N^{k^{-1}2^{-k-4}}` and `ε_k = 1/(2^k (k+4)!)`, the function
`ν : Z_N → ℝ⁺` by

* `ν(n) = (φ(W)/W) · Λ_R(Wn+1)² / log R` for `ε_k N ≤ n ≤ 2 ε_k N`,
* `ν(n) = 1` otherwise,

where `Λ_R(m) = ∑_{d | m, d ≤ R} μ(d) log(R/d)` is the Goldston–Yıldırım truncated divisor sum
(commons: `Commons.NumberTheory.Sieve.LambdaR`).

This file provides the `ZMod p` version of `ν`, the W-tricked von Mangoldt `Λ̃` restricted to the
window, and their elementary properties: non-negativity, the support condition, the pointwise
majorisation `Λ̃ ≤ k 2^{k+5} ν` (Green–Tao Lemma 8.2, from the commons lemma
`nu_majorant_lower`), and a uniform upper bound.
-/

namespace GYMaj

open Commons.NumberTheory.Sieve

/-- The Goldston–Yıldırım weight `(φ(W)/W)·Λ_R(Wn+1)²/log R`. -/
noncomputable def nuBulk (R W p : ℕ) (x : ZMod p) : ℝ :=
  (Nat.totient W : ℝ) / (W : ℝ) * ((LambdaR R (W * x.val + 1)) ^ 2 / Real.log (R : ℝ))

/-- Green–Tao's majorant `ν` on `ZMod p` (Definition 8.1): the bulk value in the window
`[εN, 2εN]` and `1` outside. -/
noncomputable def nuGT (R W p : ℕ) (ε : ℝ) (x : ZMod p) : ℝ :=
  if ε * (p : ℝ) ≤ (x.val : ℝ) ∧ (x.val : ℝ) ≤ 2 * ε * (p : ℝ)
    then nuBulk R W p x else 1

/-- The W-tricked von Mangoldt `Λ̃`, restricted to the window `[εN, 2εN]` and to primes. -/
noncomputable def fGT (W p : ℕ) (ε : ℝ) (x : ZMod p) : ℝ :=
  if ε * (p : ℝ) ≤ (x.val : ℝ) ∧ (x.val : ℝ) ≤ 2 * ε * (p : ℝ) ∧ Nat.Prime (W * x.val + 1)
    then (Nat.totient W : ℝ) / (W : ℝ) * Real.log ((W * x.val + 1 : ℕ) : ℝ) else 0

/-- Uniform upper bound for `fGT`. -/
noncomputable def bndGT (W p : ℕ) (ε : ℝ) : ℝ :=
  (Nat.totient W : ℝ) / (W : ℝ) * Real.log (2 * ε * (W : ℝ) * (p : ℝ) + 1)

section Basic

variable {R W p : ℕ} {ε : ℝ} {x : ZMod p}

lemma log_pos_of_one_lt {R : ℕ} (hR : 1 < R) : 0 < Real.log (R : ℝ) :=
  Real.log_pos (by exact_mod_cast hR)

lemma nuBulk_nonneg (hR : 1 < R) (x : ZMod p) : 0 ≤ nuBulk R W p x := by
  unfold nuBulk
  exact mul_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    (div_nonneg (sq_nonneg _) (log_pos_of_one_lt hR).le)

lemma fGT_nonneg (W p : ℕ) (ε : ℝ) (x : ZMod p) : 0 ≤ fGT W p ε x := by
  unfold fGT
  split_ifs with h
  · exact mul_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (Real.log_nonneg (by
      have h1 : (1:ℕ) ≤ W * x.val + 1 := by omega
      exact_mod_cast h1))
  · exact le_refl 0

lemma nuGT_nonneg (hR : 1 < R) (x : ZMod p) : 0 ≤ nuGT R W p ε x := by
  unfold nuGT
  split_ifs
  · exact nuBulk_nonneg hR x
  · exact zero_le_one

/-- On the window and on primes, `Λ̃(x) ≤ k·2^{k+5}·ν(x)` (Green–Tao Lemma 8.2). -/
lemma fGT_le_const_mul_nuGT {k : ℕ} (hk : 0 < k) (hR : 1 < R) (hRW : R < W * x.val + 1)
    (hprime : Nat.Prime (W * x.val + 1))
    (hbound : Real.log ((W * x.val + 1 : ℕ) : ℝ)
      ≤ (k : ℝ) * (2 : ℝ) ^ (k + 5) * Real.log (R : ℝ)) :
    fGT W p ε x ≤ (k : ℝ) * (2 : ℝ) ^ (k + 5) * nuGT R W p ε x := by
  by_cases hwin : ε * (p : ℝ) ≤ (x.val : ℝ) ∧ (x.val : ℝ) ≤ 2 * ε * (p : ℝ)
  · have hf : fGT W p ε x = (Nat.totient W : ℝ) / (W : ℝ) * Real.log ((W * x.val + 1 : ℕ) : ℝ) := by
      unfold fGT; rw [if_pos ⟨hwin.1, hwin.2, hprime⟩]
    have hn : nuGT R W p ε x = nuBulk R W p x := by unfold nuGT; rw [if_pos hwin]
    rw [hf, hn]
    unfold nuBulk
    have h1 : (1:ℕ) ≤ W * x.val + 1 := by omega
    have hlow := nu_majorant_lower (R := R) (W := W) (n := x.val) (k := k)
      (by omega) hk (log_pos_of_one_lt hR)
      (Real.log_nonneg (by exact_mod_cast h1))
      hRW hprime hbound
    -- hlow : (φ/W)(1/k)2^{-(k+5)} log(Wn+1) ≤ (φ/W) Λ_R(Wn+1)²/log R
    have hφ : 0 ≤ (Nat.totient W : ℝ) / (W : ℝ) := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    have hkpos : (0:ℝ) < (k : ℝ) := by exact_mod_cast hk
    have h2 : (0:ℝ) < (2:ℝ) ^ (k+5) := by positivity
    have hshift : (Nat.totient W : ℝ) / (W : ℝ) * Real.log ((W * x.val + 1 : ℕ) : ℝ)
        = (k : ℝ) * (2:ℝ) ^ (k+5) *
          ((Nat.totient W : ℝ) / (W : ℝ) * (k:ℝ)⁻¹ * (2:ℝ) ^ (-(k:ℤ) - 5)
            * Real.log ((W * x.val + 1 : ℕ) : ℝ)) := by
      have hz : (2:ℝ) ^ (-(k:ℤ) - 5) = ((2:ℝ) ^ (k+5))⁻¹ := by
        have h : (-(k : ℤ) - 5) = -((k + 5 : ℕ) : ℤ) := by push_cast; ring
        rw [h, zpow_neg, zpow_natCast]
      rw [hz]
      field_simp
    rw [hshift]
    exact mul_le_mul_of_nonneg_left hlow (by positivity)
  · have hf : fGT W p ε x = 0 := by unfold fGT; rw [if_neg (fun h => hwin ⟨h.1, h.2.1⟩)]
    rw [hf]
    have hR2 : (0:ℝ) < (2:ℝ) ^ (k+5) := by positivity
    have : (0:ℝ) ≤ (k : ℝ) * (2:ℝ) ^ (k+5) * nuGT R W p ε x :=
      mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hR2.le) (nuGT_nonneg hR x)
    linarith

/-- The support condition: `fGT W p ε x ≠ 0` forces the window and primality. -/
lemma fGT_ne_zero_imp {W p : ℕ} {ε : ℝ} {x : ZMod p}
    (h : fGT W p ε x ≠ 0) :
    ε * (p : ℝ) ≤ (x.val : ℝ) ∧ (x.val : ℝ) ≤ 2 * ε * (p : ℝ) ∧
      Nat.Prime (W * x.val + 1) := by
  by_contra hc
  push Not at hc
  apply h
  unfold fGT
  rw [if_neg]
  intro hh
  exact hc hh.1 hh.2.1 hh.2.2

/-- The uniform upper bound `fGT x ≤ bndGT`. -/
lemma fGT_le_bnd {W p : ℕ} {ε : ℝ} (hε : 0 ≤ ε) {x : ZMod p}
    (hx : (x.val : ℝ) ≤ 2 * ε * (p : ℝ)) :
    fGT W p ε x ≤ bndGT W p ε := by
  have hφ : 0 ≤ (Nat.totient W : ℝ) / (W : ℝ) := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  unfold fGT bndGT
  split_ifs with h
  · have hW : (0:ℝ) ≤ (W:ℝ) := Nat.cast_nonneg W
    have h1 : (W:ℝ) * (x.val:ℝ) ≤ (W:ℝ) * (2 * ε * (p:ℝ)) := mul_le_mul_of_nonneg_left hx hW
    have h2 : (W:ℝ) * (2 * ε * (p:ℝ)) = 2 * ε * (W:ℝ) * (p:ℝ) := by ring
    have hle : ((W * x.val + 1 : ℕ) : ℝ) ≤ 2 * ε * (W:ℝ) * (p:ℝ) + 1 := by
      push_cast; linarith [h1, h2]
    have hpos : (0:ℝ) < ((W * x.val + 1 : ℕ) : ℝ) := by positivity
    exact mul_le_mul_of_nonneg_left (Real.log_le_log hpos hle) hφ
  · have hlog : 0 ≤ Real.log (2 * ε * (W:ℝ) * (p:ℝ) + 1) := by
      apply Real.log_nonneg
      have hW0 : (0:ℝ) ≤ (W:ℝ) := Nat.cast_nonneg W
      have hp0 : (0:ℝ) ≤ (p:ℝ) := Nat.cast_nonneg p
      nlinarith [hW0, hp0]
    linarith [mul_nonneg hφ hlog]

/-- Green–Tao Lemma 8.2 in the form needed by the transference theorem: after dividing by
`k·2^{k+5}`, the W-tricked von Mangoldt is pointwise dominated by the majorant `ν`. -/
lemma fGT_div_const_le_nuGT {k : ℕ} (hk : 0 < k) (hR : 1 < R) (hRW : R < W * x.val + 1)
    (hprime : Nat.Prime (W * x.val + 1)) {ε : ℝ}
    (hbound : Real.log ((W * x.val + 1 : ℕ) : ℝ)
      ≤ (k : ℝ) * (2 : ℝ) ^ (k + 5) * Real.log (R : ℝ)) :
    ((k : ℝ) * (2 : ℝ) ^ (k + 5))⁻¹ * fGT W p ε x ≤ nuGT R W p ε x := by
  have hk2 : (0:ℝ) < (k : ℝ) * (2 : ℝ) ^ (k + 5) := by positivity
  have hmain := fGT_le_const_mul_nuGT (p := p) (ε := ε) hk hR hRW hprime hbound
  rw [inv_mul_le_iff₀ hk2]
  linarith [hmain]

end Basic

end GYMaj
