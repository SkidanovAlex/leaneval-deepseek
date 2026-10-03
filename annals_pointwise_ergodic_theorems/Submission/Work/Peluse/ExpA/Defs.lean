/-
Copyright (c) 2026 The AnnalsChallenge team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Submission.Work.Peluse.Holds.ExpPET.Defs

/-!
# The vocabulary of the corrected first half of Peluse's Theorem 3.5 (`ExpansionPETShortA`)

This module fixes the notation of the expansion + Lemma 4.10 step at the *short* direction scale,
in the corrected ("A") form `Work.Peluse.C46.ExpansionPETShortA`.

## The expansion

For a datum `(c, a, b, n, n')` with `κ i = c·a + b i` and integer label vectors `n, n' : Fin s → ℤ`
the cube term of the box sum is (see `Holds.ExpPET.petExpansion.expCube_eq_multilinear`)

`expCube (c·a + b) n n' f (x - ∑ i, n' i·(c·a + b i)) = f x · ∏_{ω ≠ 0} (star^[|ω|]) (f (x + c·a·D_ω + S_ω))`

with the corner coefficients

* `dotU ω u = D_ω = ∑_{j : ω j} u j`,   `u j = n j - n' j`,
* `dotB ω b u = S_ω = ∑_{j : ω j} u j · b j`.

Thus the `a`-average of `Λ_{n,n'} = ∑_{a} ∑'_x expCube (c·a+b) n n' f x` is the multilinear
average `∑'_x F 0 x · ∑_{a ∈ [M₂]} ∏_{i : Fin (2^s-1)} F (i.succ) (x + cSlot (i.succ)·a)` of Peluse's
Lemma 4.10, where `F j` is the slot function of the `j`-th sign pattern:

* `slotIdx s : Fin (2^s - 1 + 1) → (Fin s → Bool)` is the binary-value enumeration of the sign
  patterns; it is injective, sends `0` to the all-false pattern and the last index to the all-ones
  pattern (`slotIdx_zero`, `slotIdx_last`);
* `slotFn b u f j = (star^[|slotIdx j|]) ∘ T_{dotB (slotIdx j) b u} f`;
* `cSlot c u j = c · dotU (slotIdx j) u`.

The conclusion of Lemma 4.10 is the box-norm power at the direction family
`fun i : Fin (2^s-1) => arithIcc (cSlot (last) - cSlot (i.castSucc)) D`, and by
`cSlot_last_sub` this is `arithIcc (c · dotU (ωOfA s i) u) D` with

* `ωOfA s i = comp (slotIdx s i.castSucc)` — an injection of `Fin (2^s-1)` into the **nonzero**
  sign patterns, which is exactly the enumeration required by `ExpansionPETShortA`.

## The window

`winN s C₀ N = (s·(C₀+1)+1)·N` is the enlarged window at which Lemma 4.10 is invoked: it dominates
`N + s·C₀·N` (the support of the translated slot functions), `s·N` (the largest shift
`|cSlot j · a|`) and `2N+1 = |symIcc N|` (so that the normalised level `|Λ|/(winN·M₂)` is `≤ 1`).
-/

set_option autoImplicit false
open scoped BigOperators

namespace Work.Peluse.ExpA

open Work.Peluse
open Work.Peluse.Holds.ExpPET (comp comp_involutive comp_injective ones zeros)

noncomputable section

/-! ## The enumeration of the sign patterns -/

/-- The bijection `(Fin s → Bool) ≃ Fin (2^s)` given by the binary expansion (the `i`-th bit is
`ω i`). -/
def patEquiv (s : ℕ) : (Fin s → Bool) ≃ Fin (2 ^ s) :=
  (Equiv.piCongrRight (fun _ : Fin s => finTwoEquiv.symm)).trans finFunctionFinEquiv

/-- The binary value of a sign pattern. -/
lemma patEquiv_apply (s : ℕ) (ω : Fin s → Bool) :
    ((patEquiv s ω : Fin (2 ^ s)) : ℕ) = ∑ i : Fin s, (if ω i then 1 else 0) * 2 ^ (i : ℕ) := by
  rw [patEquiv, Equiv.trans_apply, finFunctionFinEquiv_apply]
  congr 1
  funext i
  rw [Equiv.piCongrRight_apply, Pi.map_apply]
  cases ω i <;> rfl

/-- `∑_{i < s} 2^i = 2^s - 1`. -/
lemma sum_fin_pow_two (s : ℕ) : (∑ i : Fin s, 2 ^ (i : ℕ)) = 2 ^ s - 1 := by
  induction s with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_castSucc]
    rw [Finset.sum_congr rfl (fun i _ => by rw [Fin.val_castSucc]), ih]
    simp [pow_succ]
    omega

/-- `2 ^ s - 1 < 2 ^ s`. -/
lemma two_pow_sub_one_lt (s : ℕ) : 2 ^ s - 1 < 2 ^ s :=
  Nat.sub_one_lt (pow_ne_zero s (by norm_num))

/-- The enumeration `Fin (2^s) → (Fin s → Bool)` of the sign patterns by binary value. -/
def slotEnum (s : ℕ) : Fin (2 ^ s) → (Fin s → Bool) := (patEquiv s).symm

lemma patEquiv_zero (s : ℕ) : patEquiv s (0 : Fin s → Bool) = 0 := by
  apply Fin.ext
  rw [patEquiv_apply]
  simp

lemma patEquiv_ones (s : ℕ) :
    patEquiv s (fun _ : Fin s => true) = ⟨2 ^ s - 1, two_pow_sub_one_lt s⟩ := by
  apply Fin.ext
  rw [patEquiv_apply]
  simp only [if_true, one_mul]
  exact sum_fin_pow_two s

lemma slotEnum_injective (s : ℕ) : Function.Injective (slotEnum s) := (patEquiv s).symm.injective

lemma slotEnum_zero (s : ℕ) : slotEnum s 0 = (0 : Fin s → Bool) := by
  rw [slotEnum, Equiv.symm_apply_eq]
  exact (patEquiv_zero s).symm

lemma slotEnum_last (s : ℕ) :
    slotEnum s ⟨2 ^ s - 1, two_pow_sub_one_lt s⟩ = (fun _ : Fin s => true) := by
  rw [slotEnum, Equiv.symm_apply_eq]
  exact (patEquiv_ones s).symm

/-- The enumeration of the sign patterns on the slot index type `Fin (2^s - 1 + 1)` of
Lemma 4.10 (slot `0` is the phase-free one, slot `j.succ` the `j`-th nonzero pattern). -/
def slotIdx (s : ℕ) : Fin (2 ^ s - 1 + 1) → (Fin s → Bool) :=
  fun j => slotEnum s (Fin.cast (Nat.sub_one_add_one (pow_ne_zero s (by norm_num))) j)

lemma slotIdx_injective (s : ℕ) : Function.Injective (slotIdx s) := fun i j h =>
  Fin.cast_injective _ (slotEnum_injective s h)

lemma slotIdx_zero (s : ℕ) : slotIdx s 0 = (0 : Fin s → Bool) := by
  simp [slotIdx, slotEnum_zero]

lemma slotIdx_last (s : ℕ) : slotIdx s (Fin.last (2 ^ s - 1)) = (fun _ : Fin s => true) := by
  have h : Fin.cast (Nat.sub_one_add_one (pow_ne_zero s (by norm_num))) (Fin.last (2 ^ s - 1))
      = ⟨2 ^ s - 1, two_pow_sub_one_lt s⟩ := by
    apply Fin.ext
    simp
  simp only [slotIdx, h, slotEnum_last]

lemma slotIdx_ne_last {s : ℕ} (i : Fin (2 ^ s - 1)) : slotIdx s i.castSucc ≠ (fun _ : Fin s => true) := by
  intro h
  have h1 : i.castSucc = Fin.last (2 ^ s - 1) := slotIdx_injective s (by rw [h, slotIdx_last])
  exact Fin.castSucc_ne_last i h1

/-! ## The corner coefficients -/

/-- The `ω`-corner coefficient `D_ω = ∑_{j : ω j} u j`. -/
def dotU {s : ℕ} (ω : Fin s → Bool) (u : Fin s → ℤ) : ℤ := ∑ j : Fin s, if ω j then u j else 0

/-- The `ω`-corner constant `S_ω = ∑_{j : ω j} u j · b j`. -/
def dotB {s : ℕ} (ω : Fin s → Bool) (b u : Fin s → ℤ) : ℤ :=
  ∑ j : Fin s, (if ω j then u j else 0) * b j

lemma comp_zero {s : ℕ} : comp (0 : Fin s → Bool) = (fun _ : Fin s => true) := by
  funext i; rfl

lemma dotU_zero {s : ℕ} (u : Fin s → ℤ) : dotU (0 : Fin s → Bool) u = 0 := by
  simp [dotU]

lemma dotB_zero {s : ℕ} (b u : Fin s → ℤ) : dotB (0 : Fin s → Bool) b u = 0 := by
  simp [dotB]

/-- Complementing a pattern: `D_{comp ω} = D_{all} - D_ω`. -/
lemma dotU_comp {s : ℕ} (ω : Fin s → Bool) (u : Fin s → ℤ) :
    dotU (comp ω) u = dotU (fun _ : Fin s => true) u - dotU ω u := by
  rw [dotU, dotU, dotU, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases h : ω j <;> simp [Work.Peluse.Holds.ExpPET.comp, h]

/-! ## The slot family of Lemma 4.10 -/

/-- The phase coefficients `c_slot j = c · D_{slot j}` (with `c_slot 0 = 0`). -/
def cSlot (s : ℕ) (c : ℤ) (u : Fin s → ℤ) : Fin (2 ^ s - 1 + 1) → ℤ :=
  fun j => c * dotU (slotIdx s j) u

/-- The slot functions of Lemma 4.10: the translated, conjugated copies of `f`. -/
def slotFn (s : ℕ) (b u : Fin s → ℤ) (f : ℤ → ℂ) : Fin (2 ^ s - 1 + 1) → ℤ → ℂ :=
  fun j => (star^[weight (slotIdx s j)]) ∘ shift (dotB (slotIdx s j) b u) f

lemma cSlot_zero (s : ℕ) (c : ℤ) (u : Fin s → ℤ) : cSlot s c u 0 = 0 := by
  simp [cSlot, slotIdx_zero, dotU_zero]

lemma slotFn_zero (s : ℕ) (b u : Fin s → ℤ) (f : ℤ → ℂ) (x : ℤ) :
    slotFn s b u f 0 x = f x := by
  simp only [slotFn, slotIdx_zero, dotB_zero, Function.comp_apply, Work.Peluse.shift, zero_add]
  rw [show weight (0 : Fin s → Bool) = 0 from by simp [weight, Pi.zero_apply]]
  simp

/-- The direction family produced by Lemma 4.10, in the form consumed by the conclusion: the
`i`-th direction is `c · D_{ωOfA i}`. -/
lemma cSlot_last_sub (s : ℕ) (c : ℤ) (u : Fin s → ℤ) (i : Fin (2 ^ s - 1)) :
    cSlot s c u (Fin.last (2 ^ s - 1)) - cSlot s c u i.castSucc
      = c * dotU (comp (slotIdx s i.castSucc)) u := by
  have h : cSlot s c u (Fin.last (2 ^ s - 1)) = c * dotU (fun _ : Fin s => true) u := by
    simp [cSlot, slotIdx_last]
  rw [h, cSlot, dotU_comp]
  ring

/-- The enumeration of the *nonzero* sign patterns required by `ExpansionPETShortA`. -/
def ωOfA (s : ℕ) : Fin (2 ^ s - 1) → (Fin s → Bool) := fun i => comp (slotIdx s i.castSucc)

lemma ωOfA_injective (s : ℕ) : Function.Injective (ωOfA s) := by
  intro i j h
  have h' : slotIdx s i.castSucc = slotIdx s j.castSucc := by
    have := congrArg comp h
    simpa [ωOfA, comp_involutive] using this
  exact Fin.castSucc_injective _ (slotIdx_injective s h')

lemma ωOfA_ne_zero (s : ℕ) (i : Fin (2 ^ s - 1)) : ωOfA s i ≠ 0 := by
  intro h
  have hc : comp (ωOfA s i) = comp 0 := congrArg comp h
  rw [ωOfA, comp_involutive, comp_zero] at hc
  exact slotIdx_ne_last i hc

/-! ## The enlarged window -/

/-- The window at which Lemma 4.10 is invoked.  It dominates `N + s·C₀·N` (support of the slot
functions), `s·N` (the largest shift `|cSlot j · a|`) and `|symIcc N| = 2N+1`. -/
def winN (s C₀ N : ℕ) : ℕ := (s * (C₀ + 1) + 3) * N

lemma le_winN (s C₀ N : ℕ) : N ≤ winN s C₀ N := by
  rw [winN]
  calc N = 1 * N := (one_mul N).symm
    _ ≤ (s * (C₀ + 1) + 3) * N := Nat.mul_le_mul_right N (by omega)

lemma add_mul_le_winN (s C₀ N : ℕ) : N + s * C₀ * N ≤ winN s C₀ N := by
  have h1 : N + s * C₀ * N = (1 + s * C₀) * N := by ring
  rw [h1, winN]
  refine Nat.mul_le_mul_right N ?_
  have h2 : s * (C₀ + 1) + 3 = (1 + s * C₀) + (s + 2) := by ring
  rw [h2]
  exact Nat.le_add_right _ _

lemma s_mul_le_winN (s C₀ N : ℕ) : s * N ≤ winN s C₀ N := by
  rw [winN]
  refine Nat.mul_le_mul_right N ?_
  calc s = s * 1 := (mul_one s).symm
    _ ≤ s * (C₀ + 1) := Nat.mul_le_mul_left s (Nat.le_add_left 1 C₀)
    _ ≤ s * (C₀ + 1) + 3 := Nat.le_add_right _ _

lemma three_mul_le_winN (s C₀ N : ℕ) : 3 * N ≤ winN s C₀ N := by
  rw [winN]
  exact Nat.mul_le_mul_right N (by omega)

lemma card_symIcc_le_winN {s C₀ N : ℕ} (hN : 1 ≤ N) : (symIcc N).card ≤ winN s C₀ N := by
  have hcard : (symIcc N).card = 2 * N + 1 := by
    rw [symIcc, Int.card_Icc]
    omega
  rw [hcard]
  exact le_trans (by omega : 2 * N + 1 ≤ 3 * N) (three_mul_le_winN s C₀ N)

end

end Work.Peluse.ExpA
