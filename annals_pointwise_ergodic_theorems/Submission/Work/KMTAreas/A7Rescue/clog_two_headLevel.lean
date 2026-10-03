import Mathlib
import Submission.Work.Analysis.IonescuWainger.iwQl_le

/-!
# The `log₂`-level of the *head* window is linear in `l`

The head (short-window) analysis of the low-pass Ionescu--Wainger family at level `l` has to
measure the size of a dyadic level

`⌈D · 2^{ρ l}⌉₊ + log₂ (3 · Q_{≤l}) + 4`,

where `Q_{≤l} = iwQl ρ l` is the common denominator of the IW frequency set `(ℚ/ℤ)_{≤l}` and `D`
is an arbitrary positive constant (the window length).  This file proves that its
`Nat.clog 2` (the number of dyadic digits) grows *linearly* in `l`,

`Nat.clog 2 (2 * (⌈D · 2^{ρ l}⌉₊ + Nat.log 2 (3 * iwQl ρ l) + 4) + 1) ≤ K * (l + 1)`,

with a constant `K` depending only on `ρ` and `D`.

The two inputs are elementary: `⌈D · 2^{ρ l}⌉₊ ≤ ⌈D⌉₊ · 2^l` (because `ρ ≤ 1`), and
`iwQl ρ l ≤ 2^{C · 2^l}` for some `C = C(ρ)` (`Work.Analysis.IonescuWainger.iwQl_le`), so that
`Nat.log 2 (3 * iwQl ρ l) ≤ ⌈C⌉₊ · 2^l + 2`.  Both terms are therefore `O(2^l)`, and a number of
size `O(2^l)` has at most `O(l)` dyadic digits.
-/

namespace Work.KMTAreas.A7Rescue

/-- A number `m ≤ Q · 2^l` (`Q ≥ 1`) has at most `Q · (l + 1)` dyadic digits: `m ≤ 2^{Q(l+1)}`.
Indeed `Q · 2^l ≤ 2^Q · 2^l = 2^{Q+l}` and `Q + l ≤ Q · (l+1)`. -/
private lemma clog_two_le_of_le_mul_pow {m Q l : ℕ} (hQ : 1 ≤ Q) (hm : m ≤ Q * 2 ^ l) :
    Nat.clog 2 m ≤ Q * (l + 1) := by
  refine Nat.clog_le_of_le_pow ?_
  have h1 : Q * 2 ^ l ≤ 2 ^ Q * 2 ^ l :=
    Nat.mul_le_mul_right _ (le_of_lt (Nat.lt_two_pow_self (n := Q)))
  have h2 : 2 ^ Q * 2 ^ l = 2 ^ (Q + l) := (Nat.pow_add 2 Q l).symm
  have h3 : Q + l ≤ Q * (l + 1) := by
    have hl : l ≤ Q * l := Nat.le_mul_of_pos_left l (by omega)
    have : Q * (l + 1) = Q * l + Q := by rw [Nat.mul_add, Nat.mul_one]
    omega
  calc m ≤ Q * 2 ^ l := hm
    _ ≤ 2 ^ Q * 2 ^ l := h1
    _ = 2 ^ (Q + l) := h2
    _ ≤ 2 ^ (Q * (l + 1)) := Nat.pow_le_pow_right (by norm_num) h3

/-- The head window level `⌈D · 2^{ρ l}⌉₊ + log₂ (3 Q_{≤l}) + 4` is `≤ Q · 2^l` with
`Q = 2(⌈D⌉₊ + ⌈C⌉₊) + 13`, `C` the IW denominator constant. -/
private lemma headLevel_le_mul_pow {ρ : ℝ} (hρ1 : ρ ≤ 1) {D : ℝ}
    (C : ℝ)
    (hC : ∀ l, (Work.Analysis.IonescuWainger.iwQl ρ l : ℝ) ≤ (2 : ℝ) ^ (C * (2 : ℝ) ^ (l : ℝ)))
    (l : ℕ) :
    2 * (⌈D * (2 : ℝ) ^ (ρ * (l : ℝ))⌉₊
          + Nat.log 2 (3 * Work.Analysis.IonescuWainger.iwQl ρ l) + 4) + 1
      ≤ (2 * (⌈D⌉₊ + ⌈C⌉₊) + 13) * 2 ^ l := by
  -- the window term
  have hA : ⌈D * (2 : ℝ) ^ (ρ * (l : ℝ))⌉₊ ≤ ⌈D⌉₊ * 2 ^ l := by
    have hDle : D ≤ (⌈D⌉₊ : ℝ) := Nat.le_ceil D
    have hDnn : (0 : ℝ) ≤ (⌈D⌉₊ : ℝ) := by positivity
    have hexp : (2 : ℝ) ^ (ρ * (l : ℝ)) ≤ (2 : ℝ) ^ (l : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by
        have : (0 : ℝ) ≤ (l : ℝ) := Nat.cast_nonneg l
        nlinarith [hρ1, this])
    have hmain : D * (2 : ℝ) ^ (ρ * (l : ℝ)) ≤ ((⌈D⌉₊ * 2 ^ l : ℕ) : ℝ) := by
      have h1 : D * (2 : ℝ) ^ (ρ * (l : ℝ)) ≤ (⌈D⌉₊ : ℝ) * (2 : ℝ) ^ (l : ℝ) := by
        have hpos2 : (0 : ℝ) ≤ (2 : ℝ) ^ (ρ * (l : ℝ)) := Real.rpow_nonneg (by norm_num) _
        calc D * (2 : ℝ) ^ (ρ * (l : ℝ)) ≤ (⌈D⌉₊ : ℝ) * (2 : ℝ) ^ (ρ * (l : ℝ)) :=
              mul_le_mul_of_nonneg_right hDle hpos2
          _ ≤ (⌈D⌉₊ : ℝ) * (2 : ℝ) ^ (l : ℝ) := mul_le_mul_of_nonneg_left hexp hDnn
      have hcast : ((⌈D⌉₊ * 2 ^ l : ℕ) : ℝ) = (⌈D⌉₊ : ℝ) * (2 : ℝ) ^ (l : ℝ) := by
        push_cast
        rw [Real.rpow_natCast]
      rw [hcast]; exact h1
    exact Nat.ceil_le.mpr hmain
  -- the IW denominator term
  have hB : Nat.log 2 (3 * Work.Analysis.IonescuWainger.iwQl ρ l) ≤ ⌈C⌉₊ * 2 ^ l + 2 := by
    have hcast : ((2 : ℕ) ^ (⌈C⌉₊ * 2 ^ l) : ℝ)
        = (2 : ℝ) ^ ((⌈C⌉₊ : ℝ) * (2 : ℝ) ^ (l : ℝ)) := by
      rw [← Real.rpow_natCast]
      congr 1
      push_cast
      rw [Real.rpow_natCast]
    have hQle : Work.Analysis.IonescuWainger.iwQl ρ l ≤ 2 ^ (⌈C⌉₊ * 2 ^ l) := by
      have h1 : (Work.Analysis.IonescuWainger.iwQl ρ l : ℝ)
          ≤ ((2 : ℕ) ^ (⌈C⌉₊ * 2 ^ l) : ℝ) := by
        rw [hcast]
        exact le_trans (hC l) (Real.rpow_le_rpow_of_exponent_le (by norm_num)
          (mul_le_mul_of_nonneg_right (Nat.le_ceil C) (Real.rpow_nonneg (by norm_num) _)))
      exact_mod_cast h1
    have h3 : 3 * Work.Analysis.IonescuWainger.iwQl ρ l ≤ 2 ^ (⌈C⌉₊ * 2 ^ l + 2) := by
      calc 3 * Work.Analysis.IonescuWainger.iwQl ρ l
            ≤ 3 * 2 ^ (⌈C⌉₊ * 2 ^ l) := Nat.mul_le_mul_left 3 hQle
        _ ≤ 4 * 2 ^ (⌈C⌉₊ * 2 ^ l) := Nat.mul_le_mul_right _ (by norm_num)
        _ = 2 ^ (⌈C⌉₊ * 2 ^ l + 2) := by rw [Nat.pow_add]; ring
    exact le_trans (Nat.log_le_clog 2 _) (Nat.clog_le_of_le_pow h3)
  -- combine
  have hsum : ⌈D * (2 : ℝ) ^ (ρ * (l : ℝ))⌉₊
        + Nat.log 2 (3 * Work.Analysis.IonescuWainger.iwQl ρ l) + 4
      ≤ (⌈D⌉₊ + ⌈C⌉₊) * 2 ^ l + 6 := by
    rw [Nat.add_mul]
    omega
  have h13 : 13 ≤ 13 * 2 ^ l := Nat.le_mul_of_pos_right _ (Nat.one_le_two_pow)
  have h2 : (2 * (⌈D⌉₊ + ⌈C⌉₊) + 13) * 2 ^ l
      = 2 * ((⌈D⌉₊ + ⌈C⌉₊) * 2 ^ l) + 13 * 2 ^ l := by
    rw [Nat.add_mul, Nat.mul_assoc]
  rw [h2]
  omega

theorem clog_two_headLevel (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (D : ℝ) (hD : 0 < D) :
    ∃ K : ℕ, ∀ l : ℕ,
      Nat.clog 2 (2 * (⌈D * (2 : ℝ) ^ (ρ * (l : ℝ))⌉₊ + Nat.log 2 (3 * Work.Analysis.IonescuWainger.iwQl ρ l) + 4) + 1)
        ≤ K * (l + 1) := by
  obtain ⟨C, _, hC⟩ := Work.Analysis.IonescuWainger.iwQl_le hρ hρ1
  refine ⟨2 * (⌈D⌉₊ + ⌈C⌉₊) + 13, fun l => ?_⟩
  exact clog_two_le_of_le_mul_pow (by omega) (headLevel_le_mul_pow hρ1 C hC l)

end Work.KMTAreas.A7Rescue
