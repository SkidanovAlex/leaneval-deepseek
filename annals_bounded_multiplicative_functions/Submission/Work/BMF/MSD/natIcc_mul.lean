import Mathlib
import Submission.Work.BMF.MSD.basic
import Submission.Work.BMF.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.MSD

open Polynomial Finset Real Complex
open BoundedMultiplicativeFunctions
open Work.BMF
open Work.BMF.MSD

/-- For a natural number `n` and a real `b`, the inequality `n ≤ ⌊b⌋₊` holds exactly when
either `n ≤ b` (the "honest" case) or `n = 0` (in which case it is automatic, even for
negative `b`, where `⌊b⌋₊ = 0`). This is the form of `Nat.le_floor` that remains valid for
negative arguments and is used to push the upper endpoint of `natIcc` through a division. -/
theorem natIcc_le_floor_iff (n : ℕ) (b : ℝ) : n ≤ ⌊b⌋₊ ↔ (n : ℝ) ≤ b ∨ n = 0 := by
  constructor
  · intro h
    rcases eq_or_ne n 0 with hn | hn
    · exact Or.inr hn
    · left
      have hb : 0 ≤ b := by
        by_contra hb
        simp only [not_le] at hb
        have h0 : ⌊b⌋₊ = 0 := Nat.floor_eq_zero.mpr (by linarith)
        omega
      exact le_trans (by exact_mod_cast h) (Nat.floor_le hb)
  · rintro (h | rfl)
    · exact Nat.le_floor h
    · exact Nat.zero_le _

/-- The multiples of `p` in `ℕ ∩ [x, x+H]` are exactly `p*m` with `m ∈ ℕ ∩ [x/p, (x+H)/p]`. -/
theorem natIcc_mul (x H : ℝ) (p : ℕ) (hp : 1 ≤ p) (f : ℕ → ℂ) :
    (∑ m ∈ natIcc (x / p) ((x + H) / p), f (p * m))
      = ∑ n ∈ (natIcc x (x + H)).filter (fun n => p ∣ n), f n := by
  have hpN : 0 < p := by omega
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hpN
  -- `⌈x⌉₊ ≤ p*m` is equivalent to `x/p ≤ m` (anchored at the real inequality `x ≤ p*m`).
  have hpq1 : ∀ m : ℕ, x ≤ (p : ℝ) * m ↔ x / p ≤ (m : ℝ) := by
    intro m
    rw [div_le_iff₀ hp0]
    constructor <;> intro h <;> linarith
  -- `p*m ≤ x+H` is equivalent to `m ≤ (x+H)/p`.
  have hpq2 : ∀ m : ℕ, (p : ℝ) * m ≤ x + H ↔ (m : ℝ) ≤ (x + H) / p := by
    intro m
    rw [le_div_iff₀ hp0]
    constructor <;> intro h <;> linarith
  have hpq3 : ∀ m : ℕ, (p * m = 0) ↔ (m = 0) := by
    intro m
    rw [Nat.mul_eq_zero]
    constructor
    · rintro (h | h)
      · omega
      · exact h
    · intro h; exact Or.inr h
  have hmem : ∀ m : ℕ, p * m ∈ natIcc x (x + H) ↔ m ∈ natIcc (x / p) ((x + H) / p) := by
    intro m
    rw [natIcc, natIcc, Finset.mem_Icc, Finset.mem_Icc, Nat.ceil_le, Nat.ceil_le,
      natIcc_le_floor_iff, natIcc_le_floor_iff]
    push_cast
    constructor
    · rintro ⟨a, b | b⟩
      · exact ⟨hpq1 m |>.mp a, Or.inl (hpq2 m |>.mp b)⟩
      · exact ⟨hpq1 m |>.mp a, Or.inr (hpq3 m |>.mp b)⟩
    · rintro ⟨a, b | b⟩
      · exact ⟨hpq1 m |>.mpr a, Or.inl (hpq2 m |>.mpr b)⟩
      · exact ⟨hpq1 m |>.mpr a, Or.inr (hpq3 m |>.mpr b)⟩
  -- The multiples of `p` in `natIcc x (x+H)` are precisely the image of `natIcc (x/p) ((x+H)/p)`
  -- under `m ↦ p*m`.
  have hset : (natIcc x (x + H)).filter (fun n => p ∣ n)
      = (natIcc (x / p) ((x + H) / p)).image (fun m => p * m) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨hn, k, rfl⟩
      exact ⟨k, (hmem k).mp hn, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨(hmem k).mpr hk, dvd_mul_right p k⟩
  rw [hset, Finset.sum_image]
  intro a _ b _ hab
  exact Nat.mul_left_cancel hpN hab

end Work.BMF.MSD
