/-
# Narrowness of the modulated bump on the index set of the low case

This module proves the *threshold comparison* that turns the height bound contained in the index
set `I^{max(l₁,l₂),k₁,k₂}` of the model tuple into the **narrowness** of the symbol
`varphiNt N k₁ t`: on the index set, a nonzero value of the bump forces `|ξ|` to be as small as
`2^{⌊-Cρ·2^{ρl₁}⌋}`, i.e. the bump is `GoodMajorArcs ρ Cρ l₁ ·`-narrow.

It is the *index-set* version of `Work.KMTAreas.A7.narrow_of_core`: the latter uses the full
`core` of the model tuple (`inIndexSet` ∧ `splitCut` ∧ `mainRegime`), while here only the
`inIndexSet` conjunct is assumed, and the scale `L = max(max l₁ l₂)(max k₁ k₂)` of the threshold
is written in the low case's notation `lcL l₁ l₂ k₁ k₂` (definitionally the same natural number).
Only the first conjunct of `core` played any role in `narrow_of_core`, so this is strictly more
general.

The two inputs are

* the support of the bump, `varphiNt_support_le_all` (valid for *all* heights `k₁`, the case
  `k₁ = 0` included): `varphiNt N k₁ t ξ ≠ 0 → |ξ| ≤ 2^{k₁ - Log N}`;
* the height bound of the index set, `inIndexSet C₀ (max l₁ l₂) k₁ k₂ N`, i.e.
  `L ≤ heightScale C₀ N = C₀ · LogLog N` with `L = max (max l₁ l₂) (max k₁ k₂)`, which gives

      `2 ^ (L / C₀ - 2) ≤ Log N + 2`     (`two_rpow_div_sub_two_le`)

  (because `2 ^ (L/C₀) ≤ 2 ^ LogLog N ≤ Log N + 2`).

Combining these with the explicit threshold hypothesis

      `k₁ + Cρ · 2^{ρ l₁} + 2 ≤ 2 ^ (L / C₀ - 2)`

yields `k₁ + Cρ · 2^{ρ l₁} ≤ Log N`, whence `k₁ - Log N ≤ ⌊-Cρ · 2^{ρ l₁}⌋` (an integer
comparison), and the support bound gives the claim with the floor exponent.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.narrow_of_core
import Submission.Work.KMTPlan.A6.LowSmallDefs

set_option autoImplicit false

namespace Work.KMTPlan.A6

open Work.Analysis.EndVar

theorem narrow_of_index (ρ : ℝ) (Cρ : ℝ) (C₀ : ℕ) (hC₀ : 1 ≤ C₀)
    {l₁ l₂ k₁ k₂ : ℕ} {a : ℕ → NNReal} {n : ℕ} {t : ℝ}
    (hindex : Work.Analysis.EndVar.inIndexSet C₀ (max (l₁ : ℤ) (l₂ : ℤ)) (k₁ : ℤ) (k₂ : ℤ)
      (Nat.floor (a n)))
    (hthr : (k₁ : ℝ) + Cρ * (2 : ℝ) ^ (ρ * (l₁ : ℝ)) + 2 ≤
      (2 : ℝ) ^ (((Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂ : ℕ) : ℝ) / (C₀ : ℝ) - 2)) :
    ∀ ξ : ℝ, Work.KMTAreas.A7.varphiNt (Nat.floor (a n)) k₁ t ξ ≠ 0 →
      |ξ| ≤ (2 : ℝ) ^ (⌊-Cρ * (2 : ℝ) ^ (ρ * (l₁ : ℝ))⌋ : ℤ) := by
  -- the height bound `L = lcL l₁ l₂ k₁ k₂ ≤ heightScale C₀ N` of the index set
  have hLh : lcL l₁ l₂ k₁ k₂ ≤ heightScale C₀ (Nat.floor (a n)) := by
    have h1 : max (l₁ : ℤ) (l₂ : ℤ) ≤ (heightScale C₀ (Nat.floor (a n)) : ℤ) := hindex.1
    have h2 : (k₁ : ℤ) ≤ (heightScale C₀ (Nat.floor (a n)) : ℤ) := hindex.2.1
    have h3 : (k₂ : ℤ) ≤ (heightScale C₀ (Nat.floor (a n)) : ℤ) := hindex.2.2
    have h1' : (max l₁ l₂ : ℤ) ≤ (heightScale C₀ (Nat.floor (a n)) : ℤ) := h1
    rw [lcL]
    omega
  -- the threshold comparison `k₁ + Cρ 2^{ρl₁} ≤ Log N`
  have hkey : (k₁ : ℝ) + Cρ * (2 : ℝ) ^ (ρ * (l₁ : ℝ)) ≤ (logN (Nat.floor (a n)) : ℝ) := by
    have h := Work.KMTAreas.A7.two_rpow_div_sub_two_le C₀ (lcL l₁ l₂ k₁ k₂)
      (Nat.floor (a n)) hC₀ hLh
    linarith
  -- the integer form of the comparison, with the floor
  have hfloor : (k₁ : ℤ) - logN (Nat.floor (a n)) ≤ ⌊-Cρ * (2 : ℝ) ^ (ρ * (l₁ : ℝ))⌋ := by
    have h := Work.KMTAreas.A7.int_sub_le_floor_neg (N := Nat.floor (a n)) (k := k₁)
      (x := Cρ * (2 : ℝ) ^ (ρ * (l₁ : ℝ))) hkey
    have hx : -(Cρ * (2 : ℝ) ^ (ρ * (l₁ : ℝ))) =
        -Cρ * (2 : ℝ) ^ (ρ * (l₁ : ℝ)) := by ring
    rwa [hx] at h
  intro ξ hξ
  -- the support bound at the height `k₁` and the monotonicity of the integer power
  calc |ξ| ≤ (2 : ℝ) ^ ((k₁ : ℝ) - (logN (Nat.floor (a n)) : ℝ)) :=
        Work.KMTAreas.A7.varphiNt_support_le_all k₁ (Nat.floor (a n)) t ξ hξ
    _ = (2 : ℝ) ^ ((k₁ : ℤ) - logN (Nat.floor (a n))) := by
        rw [← Real.rpow_intCast]
        congr 1
        simp only [logN, Int.cast_sub, Int.cast_natCast]
    _ ≤ (2 : ℝ) ^ (⌊-Cρ * (2 : ℝ) ^ (ρ * (l₁ : ℝ))⌋ : ℤ) :=
        zpow_le_zpow_right₀ (by norm_num) hfloor

end Work.KMTPlan.A6
