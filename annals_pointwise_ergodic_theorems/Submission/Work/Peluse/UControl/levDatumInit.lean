import Mathlib
import Submission.Work.Peluse.UControl.levDatum
import Submission.Work.Peluse.UControl.phase1TerminalLevCube

/-!
# The level-chain invariant at the start of the level chain (level `1`)

The phase-1 terminal state `Phase1Terminal d n lc Y` of the PET chapter is the level-`1` state of the
level chain: its live slots are the `P`-tagged histories `h ≠ 0` of `Fin n → Bool` (the punctured
Boolean cube), all of degree `d - 1`, with leading coefficients `C d · C lc · shift h`.

This file identifies it with `LevDInv` at level `1`: the level sizes are `initN` (level `0` has one
dummy slot, level `1` has `n`), the coordinates are `initC` (`c 1 s = s`), the attachments are
`initP` (`P 0 k = {0}`), and the frozen vector is `0` on the level-`1` slots.
-/

set_option autoImplicit false
open scoped BigOperators

namespace Work.Peluse.UControl

noncomputable section

open Polynomial

attribute [local instance] Classical.propDecidable

/-! ## The initial data -/

/-- The level sizes of the initial level state: the dummy level `0` and the level `1` with `n` slots
(the other levels are empty). -/
def initN (n : ℕ) : ℕ → ℕ := fun i => if i = 0 then 1 else if i = 1 then n else 0

/-- The coordinates: the level-`1` slot `s` has coordinate `s`. -/
def initC (n : ℕ) : ℕ → ℕ → ℕ := fun i s => if i = 1 then s else 0

/-- The attachments: every level-`1` slot is attached to the single level-`0` slot. -/
def initP (n : ℕ) : ℕ → ℕ → Finset ℕ := fun i _ => if i = 0 then {0} else ∅

@[simp] lemma initN_zero (n : ℕ) : initN n 0 = 1 := by simp [initN]
@[simp] lemma initN_one (n : ℕ) : initN n 1 = n := by simp [initN]
lemma initN_of_lt_one {n i : ℕ} (hi : 1 < i) : initN n i = 0 := by
  simp only [initN]
  rw [if_neg (by omega), if_neg (by omega)]
@[simp] lemma initC_one (n s : ℕ) : initC n 1 s = s := by simp [initC]
@[simp] lemma initP_zero (n k : ℕ) : initP n 0 k = {0} := by simp [initP]
lemma initP_ne_zero {n i : ℕ} (hi : i ≠ 0) (k : ℕ) : initP n i k = ∅ := by
  simp only [initP]; rw [if_neg hi]

/-- The level-`1` coordinate set of the initial data is everything. -/
lemma lvlSet_init (n : ℕ) (hL : 1 ≤ n) :
    lvlSet (initN n) (initC n) n 1 hL = Finset.univ := by
  ext x
  rw [mem_lvlSet]
  constructor
  · rintro ⟨s, -, rfl⟩
    exact Finset.mem_univ _
  · intro _
    refine ⟨x.1, by simpa using x.2, ?_⟩
    apply Fin.ext
    rw [ptFin_val_of_lt hL (by simpa using x.2), initC_one]

/-- The `Fin n`-point of the initial level-`1` coordinate map. -/
lemma ptFin_init (n : ℕ) (hL : 1 ≤ n) {s : ℕ} (hs : s < n) :
    ptFin (initC n) n 1 s hL = ⟨s, hs⟩ := by
  apply Fin.ext
  rw [ptFin_val_of_lt hL (by simpa using hs), initC_one]

/-- The direction family of the initial data at level `1` is `(d·lc)·Σ_{s ∈ v} X s`. -/
lemma dirPoly_init_one (d : ℕ) (lc : ℤ) (n : ℕ) (v : Finset ℕ) :
    dirPoly d lc (initP n) (initC n) 1 v
      = ∑ s ∈ v, MvPolynomial.C ((d : ℤ) * lc) * MvPolynomial.X s := by
  rw [dirPoly_succ]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  rw [dirPoly_zero, initC_one]
  have h1 : ((d : ℤ) - ((0 : ℕ) : ℤ)) = (d : ℤ) := by simp
  rw [h1, ← map_mul]

/-- The index set of a history, for the initial data. -/
lemma idxSet_init_eq (n : ℕ) (hL : 1 ≤ n) (h : Fin n → Bool) :
    idxSet (initN n) (initC n) n 1 hL h
      = ((Finset.univ : Finset (Fin n)).filter (fun i => h i = true)).image Fin.val := by
  ext s
  rw [mem_idxSet, Finset.mem_image]
  constructor
  · rintro ⟨hs, hh⟩
    rw [ptFin_init n hL hs] at hh
    exact ⟨⟨s, hs⟩, by simp [hh], rfl⟩
  · rintro ⟨i, hi, rfl⟩
    refine ⟨i.2, ?_⟩
    rw [ptFin_init n hL i.2, (Finset.mem_filter.mp hi).2]

/-- The sum of the `X s` over the initial index set of a history, as a sum over `Fin n`. -/
lemma sum_idxSet_init (n : ℕ) (hL : 1 ≤ n) (h : Fin n → Bool) :
    (∑ s ∈ idxSet (initN n) (initC n) n 1 hL h, (MvPolynomial.X s : MvPolynomial ℕ ℤ))
      = ∑ i : Fin n, (if h i = true then MvPolynomial.X (i : ℕ) else 0 : MvPolynomial ℕ ℤ) := by
  rw [show (∑ i : Fin n, (if h i = true then (MvPolynomial.X (i : ℕ) : MvPolynomial ℕ ℤ) else 0))
      = ∑ i ∈ (Finset.univ : Finset (Fin n)).filter (fun i => h i = true),
          (MvPolynomial.X (i : ℕ) : MvPolynomial ℕ ℤ) from by simp [Finset.sum_filter]]
  rw [idxSet_init_eq n hL h, Finset.sum_image]
  exact fun a _ b _ hab => Fin.val_injective hab

/-! ## The initial invariant -/

/-- **The phase-1 terminal state is the level-`1` state of the level chain.** -/
theorem levDInv_init {d n : ℕ} (hL : 1 ≤ n) {lc : ℤ} {Y : HistData d n}
    (hT : Phase1Terminal d n lc Y) :
    LevDInv d lc 1 n hL (initN n) (initP n) (initC n) Y (0 : Fin n → Bool) := by
  classical
  refine ⟨le_refl 1, initN_zero n, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    exact initN_of_lt_one hi
  · intro i hi k hk
    rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
    · rw [initP_zero, initN_zero]
      intro x hx
      rw [Finset.mem_singleton] at hx
      rw [hx]
      exact Finset.mem_singleton_self 0
    · exact absurd hk (by rw [initN_of_lt_one (by omega)]; omega)
  · intro i hi k hk
    rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
    · rw [initP_zero]; exact ⟨0, Finset.mem_singleton_self 0⟩
    · exact absurd hk (by rw [initN_of_lt_one (by omega)]; omega)
  · intro i hi1 hi2 s hs
    have hi : i = 1 := by omega
    subst hi
    rw [initN_one] at hs
    rwa [initC_one]
  · intro k hk
    exact ⟨1, le_refl 1, le_refl 1, k, by simpa using hk, by simp⟩
  · intro i i' s s' hi1 hi2 hi1' hi2' hs hs' heq
    have hii : i = 1 := by omega
    have hii' : i' = 1 := by omega
    subst hii
    subst hii'
    rw [initC_one, initC_one] at heq
    exact ⟨rfl, heq⟩
  · intro s hs
    rfl
  · rw [lvlSet_init n hL, LevH_univ]
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hx
      obtain ⟨hx1, hx2, -, -⟩ := hT.1 x hx
      exact ⟨hx1, hx2⟩
    · rintro ⟨hx1, hx2⟩
      have hmem := hT.2 x.2 hx2
      have h2 : ((Sum.inr 0 : InitIdx d), x.2) = x := by rw [← hx1]
      rwa [h2] at hmem
  · intro h hh hne
    rw [lvlSet_init n hL] at hh
    obtain ⟨-, -, hdeg, -⟩ := hT.1 ((Sum.inr 0 : InitIdx d), h) (hT.2 h hne)
    exact hdeg
  · intro h hh hne
    rw [lvlSet_init n hL] at hh
    obtain ⟨-, -, -, hlc⟩ := hT.1 ((Sum.inr 0 : InitIdx d), h) (hT.2 h hne)
    rw [hlc, dirPoly_init_one]
    have hmul : MvPolynomial.C ((d : ℤ) * lc) *
          (∑ i : Fin n, (if h i = true then MvPolynomial.X (i : ℕ) else 0 : MvPolynomial ℕ ℤ))
        = ∑ i : Fin n, MvPolynomial.C ((d : ℤ) * lc) *
            (if h i = true then MvPolynomial.X (i : ℕ) else 0 : MvPolynomial ℕ ℤ) :=
      Finset.mul_sum (Finset.univ : Finset (Fin n))
        (fun i : Fin n => (if h i = true then MvPolynomial.X (i : ℕ) else 0 : MvPolynomial ℕ ℤ))
        (MvPolynomial.C ((d : ℤ) * lc))
    have hmul2 : (∑ s ∈ idxSet (initN n) (initC n) n 1 hL h,
          MvPolynomial.C ((d : ℤ) * lc) * (MvPolynomial.X s : MvPolynomial ℕ ℤ))
        = MvPolynomial.C ((d : ℤ) * lc) *
            (∑ s ∈ idxSet (initN n) (initC n) n 1 hL h,
              (MvPolynomial.X s : MvPolynomial ℕ ℤ)) :=
      (Finset.mul_sum (idxSet (initN n) (initC n) n 1 hL h)
        (fun s : ℕ => (MvPolynomial.X s : MvPolynomial ℕ ℤ))
        (MvPolynomial.C ((d : ℤ) * lc))).symm
    calc MvPolynomial.rename Fin.val
          (MvPolynomial.C (d : ℤ) * MvPolynomial.C lc * HistData.shift h : MvPolynomial (Fin n) ℤ)
        = MvPolynomial.C ((d : ℤ) * lc) *
            (∑ i : Fin n, (if h i = true then MvPolynomial.X (i : ℕ) else 0
              : MvPolynomial ℕ ℤ)) := by
          rw [map_mul, map_mul, MvPolynomial.rename_C, MvPolynomial.rename_C, HistData.shift,
            map_sum, show ((MvPolynomial.C (d : ℤ) : MvPolynomial ℕ ℤ) * MvPolynomial.C lc)
              = MvPolynomial.C ((d : ℤ) * lc)
              from (MvPolynomial.C_mul (σ := ℕ) (R := ℤ) (a := (d : ℤ)) (a' := lc)).symm]
          congr 1
          refine Finset.sum_congr rfl (fun i _ => ?_)
          by_cases hi : h i <;> simp [hi, MvPolynomial.rename_X]
        _ = ∑ s ∈ idxSet (initN n) (initC n) n 1 hL h,
              MvPolynomial.C ((d : ℤ) * lc) * (MvPolynomial.X s : MvPolynomial ℕ ℤ) := by
          rw [hmul2]
          exact congrArg (fun z => MvPolynomial.C ((d : ℤ) * lc) * z)
            (sum_idxSet_init n hL h).symm
end

end Work.Peluse.UControl
