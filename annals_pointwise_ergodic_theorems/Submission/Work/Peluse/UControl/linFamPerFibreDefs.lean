/-
Copyright (c) 2026 The AnnalsChallenge team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AnnalsChallenge team
-/
import Mathlib
import Submission.Work.Peluse.UControl.peluseProp34Defs

/-!
# The combinatorial core of `Work.Peluse.UControl.linFamPerFibre`

This module collects the *vocabulary* of the last step of the proof of Peluse's Proposition 3.4 in
the form needed by the per-fibre estimate `Work.Peluse.UControl.linFamPerFibre`: the direction family
produced by Peluse's Lemma 4.10 is `{c_m - c_i}`, while the datum's own family (used by `petDir`) is
`{dir w : w ∈ I_{l-1}}`.  The identification of the two is the paper's "recalling our choice of
enumeration of `A_{\ell-1}`", and it rests on the **complement identity** `dir(univ) - dir(w) =
dir(univ \ w)` for a nonempty proper `w ⊆ univ`.

The construction (all on the index type `Fin (Fintype.card (D.I (l-1)))` of the enumeration
`Ienum D l = (Fintype.equivFin (D.I (l-1))).symm` used by `petDir`):

* `dirSet` — the plain subset sum of `IdxDatum.dir`, extended to arbitrary finite sets (so that
  `∅` and set differences are allowed);
* `fullSetIdx` — the index of the full set `univ : Finset (D.S (l-1))`;
* `pairIdx` — the transposition of `fullSetIdx` and the last index `lastIdx`;
* `complIdx` — the complement involution `I ↦ univ \ I`, an involutive bijection of
  `{i // i ≠ fullSetIdx}` fixing `fullSetIdx`;
* `idxPerm` — the bijection `Fin m → Fin m` with `idxPerm i = fullSetIdx` when `i.val = 0` and
  `idxPerm i = complIdx (pairIdx (i - 1))` otherwise; it relates the direction family `{c_m - c_i}`
  of Lemma 4.10 to the datum's family `{petDir i}`;
* `cc` — the coefficient vector `c` of Lemma 4.10 attached to the datum (`c 0 = 0`,
  `c (i+1) = petDir (pairIdx i)`);
* `slotFun` — the functions `F` of Lemma 4.10 attached to the datum (`F 0 = f` and, for `i ≥ 1`,
  the slot function `f (· + β)` or its conjugate according to `b`).

The main results are `idxPerm_bijective`, `cc_dir` (the direction identity
`c m - c i.castSucc = petDir (idxPerm i)`), `slotFun_zero`, `slotFun_succ_apply` and `prod_slot_eq`
(the product of the slot functions of `linFib` reindexed along `pairIdx`).
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped BigOperators
open Polynomial

namespace Work.Peluse.UControl

noncomputable section

open Work.Peluse

/-- The positivity of the number of level-`(l-1)` indices. -/
lemma card_I_pos (D : IdxDatum) (l : ℕ)
    (hne : (Finset.univ : Finset (D.S (l - 1))).Nonempty) :
    0 < Fintype.card (D.I (l - 1)) :=
  Fintype.card_pos_iff.mpr ⟨⟨Finset.univ, hne⟩⟩

/-! ## 1. `dir` on arbitrary finite slot sets -/

/-- The level-`j` direction of an arbitrary finite set of level-`j` slots (the same formula as
`IdxDatum.dir`, but on plain `Finset`s, so that `∅` and set differences are allowed).  This is a copy
of `Work.Peluse.UControl.dirOf` of `peluseProp34.lean`. -/
def dirSet (D : IdxDatum) (l : ℕ) (c : ℤ) (j : ℕ) (a : (i : ℕ) → D.S i → ℤ)
    (w : Finset (D.S j)) : ℤ :=
  match j with
  | 0 => c
  | (k + 1) => ∑ s ∈ w, (((l : ℤ) - (k : ℤ)) * D.dir l c k (D.par k s) a) * a (k + 1) s

lemma dirSet_succ (D : IdxDatum) (l : ℕ) (c : ℤ) (k : ℕ)
    (a : (i : ℕ) → D.S i → ℤ) (w : Finset (D.S (k + 1))) :
    dirSet D l c (k + 1) a w
      = ∑ s ∈ w, (((l : ℤ) - (k : ℤ)) * D.dir l c k (D.par k s) a) * a (k + 1) s := rfl

lemma dirSet_eq_dir (D : IdxDatum) (l : ℕ) (c : ℤ) :
    ∀ (j : ℕ) (w : D.I j) (a : (i : ℕ) → D.S i → ℤ),
      dirSet D l c j a w.1 = D.dir l c j w a := by
  intro j
  induction j with
  | zero => intro w a; rfl
  | succ k ih => intro w a; rw [dirSet_succ]; rfl

/-- **The additivity of the level-`j` direction over disjoint slot sets**, for every `j ≥ 1`. -/
lemma dirSet_union (D : IdxDatum) (l : ℕ) (c : ℤ) :
    ∀ (j : ℕ) (a : (i : ℕ) → D.S i → ℤ) {w₁ w₂ : Finset (D.S j)}, 1 ≤ j →
      Disjoint w₁ w₂ →
      dirSet D l c j a (w₁ ∪ w₂) = dirSet D l c j a w₁ + dirSet D l c j a w₂ := by
  intro j
  induction j with
  | zero => intro a w₁ w₂ hj _; omega
  | succ k ih =>
      intro a w₁ w₂ _ h
      rw [dirSet_succ, dirSet_succ, dirSet_succ, Finset.sum_union h]

/-- **The complement identity** `dir w' - dir w = dir (w' \ w)` for `w ⊆ w'` and `1 ≤ j`. -/
lemma dirSet_sdiff (D : IdxDatum) (l : ℕ) (c : ℤ) (j : ℕ) (a : (i : ℕ) → D.S i → ℤ)
    (hj : 1 ≤ j) {w w' : Finset (D.S j)} (hw : w ⊆ w') :
    dirSet D l c j a w' - dirSet D l c j a w = dirSet D l c j a (w' \ w) := by
  have hdisj : Disjoint w (w' \ w) := Finset.disjoint_sdiff
  have hunion : w ∪ (w' \ w) = w' := Finset.union_sdiff_of_subset hw
  have h1 := dirSet_union D l c j a hj hdisj
  rw [hunion] at h1
  linarith

/-! ## 2. The enumeration of `D.I (l-1)`, the complement involution and the permutation -/

/-- The enumeration `Fin (card (D.I (l-1))) ≃ D.I (l-1)` used by `petDir`. -/
abbrev Ienum (D : IdxDatum) (l : ℕ) : Fin (Fintype.card (D.I (l - 1))) ≃ D.I (l - 1) :=
  (Fintype.equivFin (D.I (l - 1))).symm

lemma Ienum_injective (D : IdxDatum) (l : ℕ) : Function.Injective (Ienum D l) :=
  Equiv.injective _

/-- `petDir` is the datum's `dir` at the corresponding level-`(l-1)` slot set. -/
lemma petDir_eq_dirSet (D : IdxDatum) (l : ℕ) (c : ℤ) (a : D.Idx l)
    (i : Fin (Fintype.card (D.I (l - 1)))) :
    petDir D l c a i = dirSet D l c (l - 1) (D.pad l a) (Ienum D l i).1 := by
  rw [petDir, dirSet_eq_dir]

/-- The index of the full set `univ : Finset (D.S (l-1))`. -/
abbrev fullSetIdx (D : IdxDatum) (l : ℕ)
    (hne : (Finset.univ : Finset (D.S (l - 1))).Nonempty) :
    Fin (Fintype.card (D.I (l - 1))) :=
  Fintype.equivFin (D.I (l - 1)) ⟨Finset.univ, hne⟩

lemma Ienum_fullSetIdx (D : IdxDatum) (l : ℕ)
    (hne : (Finset.univ : Finset (D.S (l - 1))).Nonempty) :
    (Ienum D l (fullSetIdx D l hne)).1 = (Finset.univ : Finset (D.S (l - 1))) :=
  congrArg Subtype.val (Equiv.symm_apply_apply (Fintype.equivFin (D.I (l - 1)))
    ⟨Finset.univ, hne⟩)

/-- The last index `card - 1`. -/
abbrev lastIdx (D : IdxDatum) (l : ℕ)
    (hne : (Finset.univ : Finset (D.S (l - 1))).Nonempty) :
    Fin (Fintype.card (D.I (l - 1))) :=
  ⟨Fintype.card (D.I (l - 1)) - 1, by have := card_I_pos D l hne; omega⟩

/-- The transposition of `fullSetIdx` and the last index. -/
abbrev pairIdx (D : IdxDatum) (l : ℕ)
    (hne : (Finset.univ : Finset (D.S (l - 1))).Nonempty) :
    Fin (Fintype.card (D.I (l - 1))) ≃ Fin (Fintype.card (D.I (l - 1))) :=
  Equiv.swap (fullSetIdx D l hne) (lastIdx D l hne)

lemma pairIdx_apply_fullSet (D : IdxDatum) (l : ℕ)
    (hne : (Finset.univ : Finset (D.S (l - 1))).Nonempty) :
    pairIdx D l hne (fullSetIdx D l hne) = lastIdx D l hne :=
  Equiv.swap_apply_left _ _

lemma pairIdx_apply_last (D : IdxDatum) (l : ℕ)
    (hne : (Finset.univ : Finset (D.S (l - 1))).Nonempty) :
    pairIdx D l hne (lastIdx D l hne) = fullSetIdx D l hne :=
  Equiv.swap_apply_right _ _

lemma pairIdx_apply_apply (D : IdxDatum) (l : ℕ)
    (hne : (Finset.univ : Finset (D.S (l - 1))).Nonempty)
    (x : Fin (Fintype.card (D.I (l - 1)))) :
    pairIdx D l hne (pairIdx D l hne x) = x :=
  Equiv.swap_apply_self _ _ _

lemma pairIdx_eq_fullSet_iff (D : IdxDatum) (l : ℕ)
    (hne : (Finset.univ : Finset (D.S (l - 1))).Nonempty)
    (x : Fin (Fintype.card (D.I (l - 1)))) :
    pairIdx D l hne x = fullSetIdx D l hne ↔ x = lastIdx D l hne := by
  constructor
  · intro hx
    have h1 : x = pairIdx D l hne (pairIdx D l hne x) := (pairIdx_apply_apply D l hne x).symm
    rw [hx, pairIdx_apply_fullSet] at h1
    exact h1
  · intro hx
    rw [hx, pairIdx_apply_last]

/-- A nonempty complement in the full set `univ : Finset (D.S (l-1))`. -/
lemma complIdx_aux (D : IdxDatum) (l : ℕ)
    (hne : (Finset.univ : Finset (D.S (l - 1))).Nonempty)
    (i : Fin (Fintype.card (D.I (l - 1)))) (hi : i ≠ fullSetIdx D l hne) :
    (Finset.univ \ (Ienum D l i).1).Nonempty := by
  have hne1 : (Ienum D l i).1 ≠ Finset.univ := by
    intro hc
    refine hi ?_
    have h2 : (Ienum D l i).1 = (Ienum D l (fullSetIdx D l hne)).1 := by
      rw [Ienum_fullSetIdx D l hne]; exact hc
    exact Ienum_injective D l (Subtype.ext h2)
  have : ∃ x, x ∉ (Ienum D l i).1 := by
    by_contra hcon
    push Not at hcon
    exact hne1 (Finset.eq_univ_of_forall hcon)
  obtain ⟨x, hx⟩ := this
  exact ⟨x, Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, hx⟩⟩

/-- The complement involution on the indices of `D.I (l-1)`: `i ↦ (univ \ I_i)`, with `fullSetIdx`
fixed. -/
def complIdx (D : IdxDatum) (l : ℕ) (hne : (Finset.univ : Finset (D.S (l - 1))).Nonempty)
    (i : Fin (Fintype.card (D.I (l - 1)))) : Fin (Fintype.card (D.I (l - 1))) :=
  if h : i = fullSetIdx D l hne then fullSetIdx D l hne
  else Fintype.equivFin (D.I (l - 1))
    ⟨Finset.univ \ (Ienum D l i).1, complIdx_aux D l hne i h⟩

lemma complIdx_fullSet (D : IdxDatum) (l : ℕ)
    (hne : (Finset.univ : Finset (D.S (l - 1))).Nonempty) :
    complIdx D l hne (fullSetIdx D l hne) = fullSetIdx D l hne := by
  rw [complIdx]
  simp

lemma Ienum_complIdx (D : IdxDatum) (l : ℕ)
    (hne : (Finset.univ : Finset (D.S (l - 1))).Nonempty)
    (i : Fin (Fintype.card (D.I (l - 1)))) (hi : i ≠ fullSetIdx D l hne) :
    (Ienum D l (complIdx D l hne i)).1 = Finset.univ \ (Ienum D l i).1 := by
  rw [complIdx]
  simp only [dif_neg hi]
  exact congrArg Subtype.val (Equiv.symm_apply_apply (Fintype.equivFin (D.I (l - 1)))
    ⟨Finset.univ \ (Ienum D l i).1, complIdx_aux D l hne i hi⟩)

lemma complIdx_ne_fullSet (D : IdxDatum) (l : ℕ)
    (hne : (Finset.univ : Finset (D.S (l - 1))).Nonempty)
    (i : Fin (Fintype.card (D.I (l - 1)))) (hi : i ≠ fullSetIdx D l hne) :
    complIdx D l hne i ≠ fullSetIdx D l hne := by
  intro hc
  have h1 : (Ienum D l (complIdx D l hne i)).1 = (Ienum D l (fullSetIdx D l hne)).1 := by
    rw [hc]
  rw [Ienum_complIdx D l hne i hi, Ienum_fullSetIdx D l hne] at h1
  obtain ⟨x, hx⟩ := (Ienum D l i).2
  have h2 : x ∈ (Finset.univ \ (Ienum D l i).1 : Finset (D.S (l - 1))) := by
    rw [h1]; exact Finset.mem_univ x
  rw [Finset.mem_sdiff] at h2
  exact h2.2 hx

lemma complIdx_invol (D : IdxDatum) (l : ℕ)
    (hne : (Finset.univ : Finset (D.S (l - 1))).Nonempty)
    (i : Fin (Fintype.card (D.I (l - 1)))) :
    complIdx D l hne (complIdx D l hne i) = i := by
  rcases eq_or_ne i (fullSetIdx D l hne) with h | hi
  · rw [h, complIdx_fullSet, complIdx_fullSet]
  · have hne1 : complIdx D l hne i ≠ fullSetIdx D l hne :=
      complIdx_ne_fullSet D l hne i hi
    apply Ienum_injective D l
    apply Subtype.ext
    rw [Ienum_complIdx D l hne (complIdx D l hne i) hne1,
      Ienum_complIdx D l hne i hi,
      Finset.sdiff_sdiff_eq_self (Finset.subset_univ (Ienum D l i).1)]

lemma complIdx_injective (D : IdxDatum) (l : ℕ)
    (hne : (Finset.univ : Finset (D.S (l - 1))).Nonempty) :
    Function.Injective (complIdx D l hne) := by
  intro x y hxy
  rw [← complIdx_invol D l hne x, ← complIdx_invol D l hne y, hxy]

/-- **The complement identity in the datum's own coordinates**: for `i ≠ fullSetIdx`,
`petDir fullSetIdx - petDir i = petDir (complIdx i)`. -/
lemma petDir_complIdx (D : IdxDatum) (l : ℕ) (hl : 2 ≤ l) (c : ℤ) (a : D.Idx l)
    (hne : (Finset.univ : Finset (D.S (l - 1))).Nonempty)
    (i : Fin (Fintype.card (D.I (l - 1)))) (hi : i ≠ fullSetIdx D l hne) :
    petDir D l c a (fullSetIdx D l hne) - petDir D l c a i
      = petDir D l c a (complIdx D l hne i) := by
  rw [petDir_eq_dirSet D l c a, petDir_eq_dirSet D l c a, petDir_eq_dirSet D l c a,
    Ienum_fullSetIdx D l hne, Ienum_complIdx D l hne i hi]
  exact dirSet_sdiff D l c (l - 1) (D.pad l a) (by omega) (Finset.subset_univ _)

/-! ## 3. The predecessor indices -/

/-- The predecessor index `i - 1` of `i : Fin n`, for `i ≠ 0`. -/
def predFin (n : ℕ) (i : Fin n) (h : i.val ≠ 0) : Fin n :=
  ⟨i.val - 1, by have h1 : i.val < n := i.isLt; omega⟩

/-- The predecessor index `i - 1` of `i : Fin (n+1)`, for `i ≠ 0`, as an element of `Fin n`. -/
def predFinSucc (n : ℕ) (i : Fin (n + 1)) (h : i.val ≠ 0) : Fin n :=
  ⟨i.val - 1, by have h1 : i.val < n + 1 := i.isLt; omega⟩

lemma predFinSucc_succ (n : ℕ) (i : Fin n) :
    predFinSucc n i.succ (by simp) = i :=
  Fin.ext (by simp [predFinSucc])

/-- **The permutation relating the two direction families.** -/
def idxPerm (D : IdxDatum) (l : ℕ) (hne : (Finset.univ : Finset (D.S (l - 1))).Nonempty) :
    Fin (Fintype.card (D.I (l - 1))) → Fin (Fintype.card (D.I (l - 1))) :=
  fun i => if h : i.val = 0 then fullSetIdx D l hne
    else complIdx D l hne (pairIdx D l hne (predFin _ i h))

lemma idxPerm_of_val_zero (D : IdxDatum) (l : ℕ)
    (hne : (Finset.univ : Finset (D.S (l - 1))).Nonempty)
    (i : Fin (Fintype.card (D.I (l - 1)))) (hi : i.val = 0) :
    idxPerm D l hne i = fullSetIdx D l hne := by
  rw [idxPerm]
  simp only [dif_pos hi]

lemma idxPerm_eq (D : IdxDatum) (l : ℕ)
    (hne : (Finset.univ : Finset (D.S (l - 1))).Nonempty)
    (i : Fin (Fintype.card (D.I (l - 1)))) (hi : i.val ≠ 0) :
    idxPerm D l hne i = complIdx D l hne (pairIdx D l hne (predFin _ i hi)) := by
  rw [idxPerm]
  simp only [dif_neg hi]

lemma predFin_ne_last (D : IdxDatum) (l : ℕ)
    (hne : (Finset.univ : Finset (D.S (l - 1))).Nonempty)
    (i : Fin (Fintype.card (D.I (l - 1)))) (h : i.val ≠ 0) :
    predFin _ i h ≠ lastIdx D l hne := by
  intro hc
  have h1 : (predFin _ i h).val = (lastIdx D l hne).val := congrArg Fin.val hc
  simp only [predFin, Fin.val_mk] at h1
  have h3 : i.val < Fintype.card (D.I (l - 1)) := i.isLt
  omega

lemma idxPerm_injective (D : IdxDatum) (l : ℕ)
    (hne : (Finset.univ : Finset (D.S (l - 1))).Nonempty) :
    Function.Injective (idxPerm D l hne) := by
  intro i₁ i₂ hij
  rcases eq_or_ne i₁.val 0 with h₁ | h₁
  · rw [idxPerm_of_val_zero D l hne i₁ h₁] at hij
    rcases eq_or_ne i₂.val 0 with h₂ | h₂
    · exact Fin.ext (by rw [h₁, h₂])
    · exfalso
      rw [idxPerm_eq D l hne i₂ h₂] at hij
      have hk : pairIdx D l hne (predFin _ i₂ h₂) = fullSetIdx D l hne := by
        have h3 := complIdx_invol D l hne (pairIdx D l hne (predFin _ i₂ h₂))
        exact (h3 ▸ congrArg (complIdx D l hne) hij.symm).trans (complIdx_fullSet D l hne)
      exact predFin_ne_last D l hne i₂ h₂ ((pairIdx_eq_fullSet_iff D l hne _).mp hk)
  · rcases eq_or_ne i₂.val 0 with h₂ | h₂
    · exfalso
      rw [idxPerm_of_val_zero D l hne i₂ h₂, idxPerm_eq D l hne i₁ h₁] at hij
      have hk : pairIdx D l hne (predFin _ i₁ h₁) = fullSetIdx D l hne := by
        have h3 := complIdx_invol D l hne (pairIdx D l hne (predFin _ i₁ h₁))
        exact (h3 ▸ congrArg (complIdx D l hne) hij).trans (complIdx_fullSet D l hne)
      exact predFin_ne_last D l hne i₁ h₁ ((pairIdx_eq_fullSet_iff D l hne _).mp hk)
    · rw [idxPerm_eq D l hne i₁ h₁, idxPerm_eq D l hne i₂ h₂] at hij
      have hx : pairIdx D l hne (predFin _ i₁ h₁) = pairIdx D l hne (predFin _ i₂ h₂) :=
        complIdx_injective D l hne hij
      have hk : predFin _ i₁ h₁ = predFin _ i₂ h₂ := (pairIdx D l hne).injective hx
      refine Fin.ext ?_
      have h5 : (predFin _ i₁ h₁).val = (predFin _ i₂ h₂).val := congrArg Fin.val hk
      simp only [predFin, Fin.val_mk] at h5
      omega

lemma idxPerm_bijective (D : IdxDatum) (l : ℕ)
    (hne : (Finset.univ : Finset (D.S (l - 1))).Nonempty) :
    Function.Bijective (idxPerm D l hne) :=
  Finite.injective_iff_bijective.mp (idxPerm_injective D l hne)

/-! ## 4. The coefficient vector `c` of Lemma 4.10 attached to the datum -/

/-- The coefficient vector `c : Fin (m+1) → ℤ` of Peluse's Lemma 4.10 attached to the datum:
`c 0 = 0` and `c (i+1) = petDir (pairIdx i)`, so that `c m = dir(univ)`. -/
def cc (D : IdxDatum) (l : ℕ) (c : ℤ)
    (hne : (Finset.univ : Finset (D.S (l - 1))).Nonempty)
    (a : D.Idx l) : Fin (Fintype.card (D.I (l - 1)) + 1) → ℤ :=
  fun i => if h : i.val = 0 then 0
    else petDir D l c a (pairIdx D l hne (predFinSucc _ i h))

lemma cc_zero (D : IdxDatum) (l : ℕ) (c : ℤ)
    (hne : (Finset.univ : Finset (D.S (l - 1))).Nonempty) (a : D.Idx l) :
    cc D l c hne a 0 = 0 := by
  rw [cc]
  simp

lemma cc_pos (D : IdxDatum) (l : ℕ) (c : ℤ)
    (hne : (Finset.univ : Finset (D.S (l - 1))).Nonempty) (a : D.Idx l)
    (j : Fin (Fintype.card (D.I (l - 1)) + 1)) (hj : j.val ≠ 0) :
    cc D l c hne a j = petDir D l c a (pairIdx D l hne (predFinSucc _ j hj)) := by
  rw [cc]
  simp only [dif_neg hj]

lemma cc_succ (D : IdxDatum) (l : ℕ) (c : ℤ)
    (hne : (Finset.univ : Finset (D.S (l - 1))).Nonempty) (a : D.Idx l)
    (i : Fin (Fintype.card (D.I (l - 1)))) :
    cc D l c hne a i.succ = petDir D l c a (pairIdx D l hne i) := by
  rw [cc_pos D l c hne a i.succ (by simp), predFinSucc_succ]

lemma cc_last (D : IdxDatum) (l : ℕ) (c : ℤ)
    (hne : (Finset.univ : Finset (D.S (l - 1))).Nonempty) (a : D.Idx l) :
    cc D l c hne a ⟨Fintype.card (D.I (l - 1)), Nat.lt_succ_self _⟩
      = petDir D l c a (fullSetIdx D l hne) := by
  have hcard : 0 < Fintype.card (D.I (l - 1)) := card_I_pos D l hne
  rw [cc_pos D l c hne a _ (by simp only [Fin.val_mk]; omega),
    show predFinSucc _ ⟨Fintype.card (D.I (l - 1)), Nat.lt_succ_self _⟩ _ = lastIdx D l hne
      from Fin.ext (by simp [predFinSucc, lastIdx]),
    pairIdx_apply_last]

lemma castSucc_eq_predSucc (D : IdxDatum) (l : ℕ)
    (i : Fin (Fintype.card (D.I (l - 1)))) (h : i.val ≠ 0) :
    i.castSucc = (predFin _ i h).succ :=
  Fin.ext (by simp only [Fin.val_castSucc, Fin.val_succ, predFin, Fin.val_mk]; omega)

/-- **The direction identity**: the direction family `{c m - c i}` of Lemma 4.10 is the datum's own
family reindexed by `idxPerm`. -/
lemma cc_dir (D : IdxDatum) (l : ℕ) (hl : 2 ≤ l) (c : ℤ)
    (hne : (Finset.univ : Finset (D.S (l - 1))).Nonempty) (a : D.Idx l)
    (i : Fin (Fintype.card (D.I (l - 1)))) :
    cc D l c hne a ⟨Fintype.card (D.I (l - 1)), Nat.lt_succ_self _⟩ - cc D l c hne a i.castSucc
      = petDir D l c a (idxPerm D l hne i) := by
  rcases eq_or_ne i.val 0 with h | h
  · rw [idxPerm_of_val_zero D l hne i h,
      show i.castSucc = (0 : Fin (Fintype.card (D.I (l - 1)) + 1)) from Fin.ext (by simpa using h),
      cc_zero, sub_zero, cc_last]
  · rw [idxPerm_eq D l hne i h, cc_last, castSucc_eq_predSucc D l i h, cc_succ]
    exact petDir_complIdx D l hl c a hne _
      (fun hc => predFin_ne_last D l hne i h ((pairIdx_eq_fullSet_iff D l hne _).mp hc))

/-! ## 5. The slot functions `F` of Lemma 4.10 attached to the datum -/

/-- The functions `F : Fin (m+1) → ℤ → ℂ` of Peluse's Lemma 4.10 attached to the datum:
`F 0 = f` and, for `i ≥ 1`, `F i` is the translate `f (· + β)` or its conjugate according to `b`. -/
def slotFun (D : IdxDatum) (l : ℕ)
    (hne : (Finset.univ : Finset (D.S (l - 1))).Nonempty) (f : ℤ → ℂ)
    (b : Fin (Fintype.card (D.I (l - 1))) → Bool)
    (β : D.Idx l → Fin (Fintype.card (D.I (l - 1))) → ℤ) (a : D.Idx l) :
    Fin (Fintype.card (D.I (l - 1)) + 1) → ℤ → ℂ :=
  fun i x => if h : i.val = 0 then f x
    else if b (pairIdx D l hne (predFinSucc _ i h))
      then star (f (x + β a (pairIdx D l hne (predFinSucc _ i h))))
      else f (x + β a (pairIdx D l hne (predFinSucc _ i h)))

lemma slotFun_zero (D : IdxDatum) (l : ℕ)
    (hne : (Finset.univ : Finset (D.S (l - 1))).Nonempty) (f : ℤ → ℂ)
    (b : Fin (Fintype.card (D.I (l - 1))) → Bool)
    (β : D.Idx l → Fin (Fintype.card (D.I (l - 1))) → ℤ) (a : D.Idx l) :
    slotFun D l hne f b β a 0 = f := by
  funext x
  rw [slotFun]
  simp

lemma slotFun_pos_apply (D : IdxDatum) (l : ℕ)
    (hne : (Finset.univ : Finset (D.S (l - 1))).Nonempty) (f : ℤ → ℂ)
    (b : Fin (Fintype.card (D.I (l - 1))) → Bool)
    (β : D.Idx l → Fin (Fintype.card (D.I (l - 1))) → ℤ) (a : D.Idx l)
    (j : Fin (Fintype.card (D.I (l - 1)) + 1)) (hj : j.val ≠ 0) (x : ℤ) :
    slotFun D l hne f b β a j x
      = if b (pairIdx D l hne (predFinSucc _ j hj))
          then star (f (x + β a (pairIdx D l hne (predFinSucc _ j hj))))
          else f (x + β a (pairIdx D l hne (predFinSucc _ j hj))) := by
  rw [slotFun]
  simp only [dif_neg hj]

lemma slotFun_succ_apply (D : IdxDatum) (l : ℕ)
    (hne : (Finset.univ : Finset (D.S (l - 1))).Nonempty) (f : ℤ → ℂ)
    (b : Fin (Fintype.card (D.I (l - 1))) → Bool)
    (β : D.Idx l → Fin (Fintype.card (D.I (l - 1))) → ℤ) (a : D.Idx l)
    (i : Fin (Fintype.card (D.I (l - 1)))) (x : ℤ) :
    slotFun D l hne f b β a i.succ x
      = if b (pairIdx D l hne i) then star (f (x + β a (pairIdx D l hne i)))
        else f (x + β a (pairIdx D l hne i)) := by
  rw [slotFun_pos_apply D l hne f b β a i.succ (by simp) x, predFinSucc_succ]

lemma slotFun_norm_le_one (D : IdxDatum) (l : ℕ)
    (hne : (Finset.univ : Finset (D.S (l - 1))).Nonempty) {f : ℤ → ℂ}
    (b : Fin (Fintype.card (D.I (l - 1))) → Bool)
    (β : D.Idx l → Fin (Fintype.card (D.I (l - 1))) → ℤ) (a : D.Idx l)
    (hf : ∀ x : ℤ, ‖f x‖ ≤ 1) (i : Fin (Fintype.card (D.I (l - 1)) + 1)) (x : ℤ) :
    ‖slotFun D l hne f b β a i x‖ ≤ 1 := by
  by_cases hi : i.val = 0
  · rw [show i = 0 from Fin.ext hi, slotFun_zero]
    exact hf x
  · rw [slotFun_pos_apply D l hne f b β a i hi x]
    by_cases hb : b (pairIdx D l hne (predFinSucc _ i hi))
    · rw [if_pos hb, norm_star]; exact hf _
    · rw [if_neg hb]; exact hf _

/-- The product of the slot functions of `linFib` (with the shifts `petDir i·y + β i`), reindexed
along the transposition `pairIdx`. -/
lemma prod_slot_eq (D : IdxDatum) (l : ℕ) (c : ℤ)
    (hne : (Finset.univ : Finset (D.S (l - 1))).Nonempty) (f : ℤ → ℂ)
    (b : Fin (Fintype.card (D.I (l - 1))) → Bool)
    (β : D.Idx l → Fin (Fintype.card (D.I (l - 1))) → ℤ) (a : D.Idx l) (x y : ℤ) :
    ∏ i : Fin (Fintype.card (D.I (l - 1))),
        slotFun D l hne f b β a i.succ (x + cc D l c hne a i.succ * y)
      = ∏ i : Fin (Fintype.card (D.I (l - 1))),
          (if b i then star (f (x + (petDir D l c a i * y + β a i)))
            else f (x + (petDir D l c a i * y + β a i))) := by
  refine Finset.prod_equiv (pairIdx D l hne) (fun i => by simp) (fun i _ => ?_)
  rw [slotFun_succ_apply, cc_succ]
  by_cases hb : b (pairIdx D l hne i)
  · rw [if_pos hb, if_pos hb]
    congr 1
    ring
  · rw [if_neg hb, if_neg hb]
    congr 1
    ring

end

end Work.Peluse.UControl
