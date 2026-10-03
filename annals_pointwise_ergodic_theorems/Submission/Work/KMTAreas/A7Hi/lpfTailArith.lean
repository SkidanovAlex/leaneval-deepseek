import Mathlib
import Submission.Work.Analysis.IonescuWainger.iwQl_le
import Submission.Work.BourgainPlan.Maximal.kmsz_major_defs

/-!
# The tail arithmetic of the low-pass Ionescu–Wainger walk

The Ionescu–Wainger common denominator `Q_{≤l} = lc(P_{≤l})` satisfies the sharp growth bound
`iwQl ρ l ≤ 2^{C_ρ 2^l}` (`Work.Analysis.IonescuWainger.iwQl_le`, Appendix A of
Krause–Mirek–Tao).  The tail estimates of the low-pass walk in the area `A7Hi` are applied at a
*lacunary* sample scale `2^κ`, and therefore need the following exact form of that growth bound:
there is a constant `Cκ` (depending only on `ρ`) such that for every `l₁` and every level `m₀`
there is a `κ` with

* `κ + 1 ≤ Cκ · (1 + l₁)²` — the sample scale `2^κ` is *polynomial* in the height `l₁` (so that
  it stays inside the `(1+l₁)²` budget of the sampling principle), and
* `6 · iwQl ρ l₁ ≤ 2^{m₀ + 2^κ}` — the sample scale `2^κ` already dominates the denominator, with
  room to spare for the arbitrarily large level `m₀`.

## The proof

Let `C > 0` with `iwQl ρ l ≤ 2^{C 2^l}`, and pick `K` with `C + 1 ≤ 2^K` (so `K ≥ 1`).  For
`l₁ ∈ ℕ` put `A = 2^{l₁}`.  Since `K ≥ 1` we have `A ≥ 1`, hence
`C · A ≤ (2^K - 1) · A = A · 2^K - A ≤ A · 2^K - 1`, so

`iwQl ρ l₁ ≤ 2^{A · 2^K - 1} = 2^{A·2^K} / 2`,

i.e. `2 · iwQl ρ l₁ ≤ 2^{2^{l₁+K}}` as natural numbers (because `(2^{l₁+K} : ℝ) = A · 2^K`).
Taking `κ := l₁ + K + 1`, so that `2^κ = 2 · 2^{l₁+K} ≥ 2^{l₁+K} + 2`, we get

`6 · iwQl ρ l₁ ≤ 3 · 2^{2^{l₁+K}} ≤ 2^{2^{l₁+K} + 2} ≤ 2^{m₀ + 2^κ}`.

Finally `κ + 1 = l₁ + K + 2 ≤ (K+2)(1 + l₁) ≤ (K+2)(1 + l₁)²`, so `Cκ := K + 2` works.

This mirrors `Work.KMTAreas.A7Hi.exists_shift_narrow`, which extracts the closely related shift
form `2 · iwQl ρ l₁ ≤ 2^{m₀ + n + 2^{l₁+K}}` from the same growth bound.
-/

namespace Work.KMTAreas.A7Hi

open Work.Analysis.IonescuWainger

/-- **Tail arithmetic for the low-pass Ionescu–Wainger walk.**  There is a constant `Cκ > 0`
(depending only on `ρ ∈ (0,1]`) such that for every height `l₁` and every level `m₀` one can pick a
lacunary scale `2^κ` which is `≤ Cκ (1+l₁)²` in size and dominates the IW denominator
`6 · iwQl ρ l₁` up to the level `m₀`. -/
theorem lpfTailArith (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    ∃ Cκ : ℝ, 0 < Cκ ∧ ∀ (l₁ m₀ : ℕ), ∃ κ : ℕ,
      (κ : ℝ) + 1 ≤ Cκ * (1 + (l₁ : ℝ)) ^ 2 ∧
        6 * Work.Analysis.IonescuWainger.iwQl ρ l₁ ≤ 2 ^ (m₀ + 2 ^ κ) := by
  obtain ⟨C, hCpos, hC⟩ := Work.Analysis.IonescuWainger.iwQl_le hρ hρ1
  -- a natural `K` with `C + 1 ≤ 2^K`
  obtain ⟨K, hK⟩ := exists_nat_gt (C + 1)
  have hKpow : C + 1 ≤ (2 : ℝ) ^ K := by
    have h1 : (K : ℝ) ≤ (2 : ℝ) ^ K := by
      exact_mod_cast (Nat.lt_two_pow_self (n := K)).le
    linarith
  have hKne : K ≠ 0 := by
    intro h0
    rw [h0, pow_zero] at hKpow
    linarith
  have hK1 : 1 ≤ K := Nat.one_le_iff_ne_zero.mpr hKne
  refine ⟨(K : ℝ) + 2, by positivity, ?_⟩
  intro l₁ m₀
  refine ⟨l₁ + K + 1, ?_, ?_⟩
  · -- the size constraint `κ + 1 ≤ Cκ (1+l₁)²`
    have hl : (0 : ℝ) ≤ (l₁ : ℝ) := Nat.cast_nonneg l₁
    have hcast : (((l₁ + K + 1 : ℕ) : ℝ) + 1) = (l₁ : ℝ) + K + 2 := by push_cast; ring
    rw [hcast]
    have h1 : (l₁ : ℝ) + K + 2 ≤ ((K : ℝ) + 2) * (1 + (l₁ : ℝ)) := by
      have hle : (0 : ℝ) ≤ (l₁ : ℝ) * ((K : ℝ) + 1) := by positivity
      nlinarith [hle]
    have h2 : (1 + (l₁ : ℝ)) ≤ (1 + (l₁ : ℝ)) ^ 2 := by
      have ht : (1 : ℝ) ≤ 1 + (l₁ : ℝ) := by linarith
      calc (1 + (l₁ : ℝ)) = 1 * (1 + (l₁ : ℝ)) := by ring
        _ ≤ (1 + (l₁ : ℝ)) * (1 + (l₁ : ℝ)) :=
            mul_le_mul_of_nonneg_right ht (by linarith)
        _ = (1 + (l₁ : ℝ)) ^ 2 := by ring
    exact le_trans h1 (mul_le_mul_of_nonneg_left h2 (by positivity))
  · -- the growth constraint `6 · iwQl ρ l₁ ≤ 2^{m₀ + 2^κ}`
    set A : ℝ := (2 : ℝ) ^ l₁ with hA
    have hA1 : 1 ≤ A := by rw [hA]; exact one_le_pow₀ (by norm_num)
    have hArp : A = (2 : ℝ) ^ ((l₁ : ℕ) : ℝ) := by rw [hA, Real.rpow_natCast]
    have hcast2 : ((2 ^ (l₁ + K) : ℕ) : ℝ) = A * (2 : ℝ) ^ K := by
      rw [Nat.cast_pow, pow_add, hA, Nat.cast_ofNat]
    have hCb : C * (2 : ℝ) ^ ((l₁ : ℕ) : ℝ) ≤ A * (2 : ℝ) ^ K - 1 := by
      rw [← hArp]
      nlinarith [hA1, hKpow]
    have hiwQl : ((Work.Analysis.IonescuWainger.iwQl ρ l₁ : ℕ) : ℝ) ≤
        (2 : ℝ) ^ (A * (2 : ℝ) ^ K - 1) := by
      calc ((Work.Analysis.IonescuWainger.iwQl ρ l₁ : ℕ) : ℝ)
          ≤ (2 : ℝ) ^ (C * (2 : ℝ) ^ ((l₁ : ℕ) : ℝ)) := hC l₁
        _ ≤ (2 : ℝ) ^ (A * (2 : ℝ) ^ K - 1) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) hCb
    have hsplit : (2 : ℝ) ^ (A * (2 : ℝ) ^ K - 1) = (2 : ℝ) ^ (A * (2 : ℝ) ^ K) / 2 := by
      rw [Real.rpow_sub (by norm_num : (0 : ℝ) < 2), Real.rpow_one]
    have hkey : (2 : ℝ) ^ (A * (2 : ℝ) ^ K) = ((2 ^ (2 ^ (l₁ + K)) : ℕ) : ℝ) := by
      rw [← hcast2, Real.rpow_natCast, Nat.cast_pow, Nat.cast_ofNat]
    have hgoalR : ((2 * Work.Analysis.IonescuWainger.iwQl ρ l₁ : ℕ) : ℝ)
        ≤ ((2 ^ (2 ^ (l₁ + K)) : ℕ) : ℝ) := by
      have h2 : ((2 * Work.Analysis.IonescuWainger.iwQl ρ l₁ : ℕ) : ℝ)
          = 2 * ((Work.Analysis.IonescuWainger.iwQl ρ l₁ : ℕ) : ℝ) := by push_cast; ring
      rw [h2]
      calc 2 * ((Work.Analysis.IonescuWainger.iwQl ρ l₁ : ℕ) : ℝ)
          ≤ 2 * (2 : ℝ) ^ (A * (2 : ℝ) ^ K - 1) := by linarith
        _ = (2 : ℝ) ^ (A * (2 : ℝ) ^ K) := by rw [hsplit]; ring
        _ = ((2 ^ (2 ^ (l₁ + K)) : ℕ) : ℝ) := hkey
    -- the natural-number form of the crucial bound
    have h2Q : 2 * Work.Analysis.IonescuWainger.iwQl ρ l₁ ≤ 2 ^ (2 ^ (l₁ + K)) :=
      by exact_mod_cast hgoalR
    have hY : 0 < 2 ^ (2 ^ (l₁ + K)) := pow_pos (by norm_num) _
    have h6 : 6 * Work.Analysis.IonescuWainger.iwQl ρ l₁ ≤ 2 ^ (2 ^ (l₁ + K) + 2) := by
      calc 6 * Work.Analysis.IonescuWainger.iwQl ρ l₁
          = 3 * (2 * Work.Analysis.IonescuWainger.iwQl ρ l₁) := by ring
        _ ≤ 3 * 2 ^ (2 ^ (l₁ + K)) := Nat.mul_le_mul_left 3 h2Q
        _ ≤ 2 ^ 2 * 2 ^ (2 ^ (l₁ + K)) := by nlinarith [hY]
        _ = 2 ^ (2 ^ (l₁ + K) + 2) := by rw [pow_add]; ring
    have hexp : 2 ^ (l₁ + K) + 2 ≤ m₀ + 2 ^ (l₁ + K + 1) := by
      have h2base : 2 ≤ 2 ^ (l₁ + K) := by
        calc (2 : ℕ) = 2 ^ 1 := rfl
          _ ≤ 2 ^ (l₁ + K) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have hpow : 2 ^ (l₁ + K + 1) = 2 ^ (l₁ + K) * 2 := by rw [pow_succ]
      omega
    calc 6 * Work.Analysis.IonescuWainger.iwQl ρ l₁ ≤ 2 ^ (2 ^ (l₁ + K) + 2) := h6
      _ ≤ 2 ^ (m₀ + 2 ^ (l₁ + K + 1)) := Nat.pow_le_pow_right (by norm_num) hexp

end Work.KMTAreas.A7Hi
