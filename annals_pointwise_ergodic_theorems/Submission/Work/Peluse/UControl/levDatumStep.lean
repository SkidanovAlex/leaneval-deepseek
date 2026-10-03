import Mathlib
import Submission.Work.Peluse.UControl.levDatumInit

/-!
# The level-chain invariant survives a round of Peluse's Lemma 4.8

`levDInv_step` is the induction step of the level chain: from a `LevDInv`-state at level `j` and the
output of a round (`LevRoundU`), produce a `LevDInv`-state at level `j + 1`.

The new data is

* `N' i = if i = j+1 then Nnew else N i` (the round's step count),
* `c' i s = if i = j+1 then L + s else c i s` (the fresh coordinates are the round's new ones),
* `P' j k = { raw indices of the elements of Pround k }` (the round's attachment, transported to the
  raw index sets of the old level).

The identity clause is the recursion `dir_{j+1}(v) = Σ_{s∈v} (d-j)·dir_j(P j s)·X_{c(j+1)s}`: the new
leading coefficients are `atomSum A' atoms' h` with
`atoms' k = C (d-j) · (Σ_{s' ∈ Pround k} rename (castLE) (atoms s')) · X k`, so the `atomSum` of a
history rewrites through the round's factorisation into `dirPoly (j+1)` of its index set, each
cofactor being `dirPoly j` of the corresponding raw index set by the inductive hypothesis.
-/

set_option autoImplicit false
open scoped BigOperators

namespace Work.Peluse.UControl

noncomputable section

open Polynomial

attribute [local instance] Classical.propDecidable

variable {d : ℕ}

/-! ## The raw index of a level-`j` slot -/

/-- The raw index of a slot of the level-`j` slot set of a `LevDInv`-state. -/
def rawOf {lc : ℤ} {j L : ℕ} {hL : 1 ≤ L} {N : ℕ → ℕ} {P : ℕ → ℕ → Finset ℕ}
    {c : ℕ → ℕ → ℕ} {X : HistData d L} {f₀ : Fin L → Bool}
    (h : LevDInv d lc j L hL N P c X f₀) (x : {x // x ∈ lvlSet N c L j hL}) : ℕ :=
  Classical.choose (mem_lvlSet.mp x.2)

lemma rawOf_lt {lc : ℤ} {j L : ℕ} {hL : 1 ≤ L} {N : ℕ → ℕ} {P : ℕ → ℕ → Finset ℕ}
    {c : ℕ → ℕ → ℕ} {X : HistData d L} {f₀ : Fin L → Bool}
    (h : LevDInv d lc j L hL N P c X f₀) (x : {x // x ∈ lvlSet N c L j hL}) :
    rawOf h x < N j := (Classical.choose_spec (mem_lvlSet.mp x.2)).1

lemma rawOf_spec {lc : ℤ} {j L : ℕ} {hL : 1 ≤ L} {N : ℕ → ℕ} {P : ℕ → ℕ → Finset ℕ}
    {c : ℕ → ℕ → ℕ} {X : HistData d L} {f₀ : Fin L → Bool}
    (h : LevDInv d lc j L hL N P c X f₀) (x : {x // x ∈ lvlSet N c L j hL}) :
    ptFin c L j (rawOf h x) hL = x.1 :=
  (Classical.choose_spec (mem_lvlSet.mp x.2)).2

/-- The level-`j` coordinate map is injective on the valid range. -/
lemma ptFin_injective {lc : ℤ} {j L : ℕ} {hL : 1 ≤ L} {N : ℕ → ℕ} {P : ℕ → ℕ → Finset ℕ}
    {c : ℕ → ℕ → ℕ} {X : HistData d L} {f₀ : Fin L → Bool}
    (h : LevDInv d lc j L hL N P c X f₀) {s s' : ℕ} (hs : s < N j) (hs' : s' < N j)
    (he : ptFin c L j s hL = ptFin c L j s' hL) : s = s' := by
  have h2 := congrArg Fin.val he
  rw [ptFin_val_of_lt hL (h.cbound j h.hj (le_refl j) s hs),
    ptFin_val_of_lt hL (h.cbound j h.hj (le_refl j) s' hs')] at h2
  exact (h.cinj j j s s' h.hj (le_refl j) h.hj (le_refl j) hs hs' h2).2

lemma rawOf_ptFin {lc : ℤ} {j L : ℕ} {hL : 1 ≤ L} {N : ℕ → ℕ} {P : ℕ → ℕ → Finset ℕ}
    {c : ℕ → ℕ → ℕ} {X : HistData d L} {f₀ : Fin L → Bool}
    (h : LevDInv d lc j L hL N P c X f₀) {s : ℕ} (hs : s < N j) :
    rawOf h ⟨ptFin c L j s hL, mem_lvlSet.mpr ⟨s, hs, rfl⟩⟩ = s :=
  ptFin_injective h (rawOf_lt h _) hs (rawOf_spec h _)

/-! ## The extended data of one step -/

/-- The level sizes after a round whose step count is `Nnew`. -/
def stepN (N : ℕ → ℕ) (Nnew j : ℕ) : ℕ → ℕ := fun i => if i = j + 1 then Nnew else N i

/-- The coordinates after a round: the new level's slots get the fresh coordinates. -/
def stepC (c : ℕ → ℕ → ℕ) (L j : ℕ) : ℕ → ℕ → ℕ :=
  fun i s => if i = j + 1 then L + s else c i s

/-- The attachments after a round: at level `j` the raw index sets of the round's attachments. -/
def stepP {lc : ℤ} {j L : ℕ} {hL : 1 ≤ L} {N : ℕ → ℕ} {P : ℕ → ℕ → Finset ℕ}
    {c : ℕ → ℕ → ℕ} {X : HistData d L} {f₀ : Fin L → Bool}
    (h : LevDInv d lc j L hL N P c X f₀) {Nnew : ℕ} {A' : Finset (Fin (L + Nnew))}
    (hA' : A' = freshFin L Nnew)
    (Pround : {s // s ∈ A'} → Finset {s' // s' ∈ lvlSet N c L j hL}) (k : ℕ) : Finset ℕ :=
  if hk : k < Nnew then
    (Pround ⟨⟨L + k, by omega⟩, by rw [hA']; exact mem_freshFin.mpr (Nat.le_add_right L k)⟩).image
      (fun s' => rawOf h s')
  else ∅

lemma mem_stepP {lc : ℤ} {j L : ℕ} {hL : 1 ≤ L} {N : ℕ → ℕ} {P : ℕ → ℕ → Finset ℕ}
    {c : ℕ → ℕ → ℕ} {X : HistData d L} {f₀ : Fin L → Bool}
    (h : LevDInv d lc j L hL N P c X f₀) {Nnew : ℕ} {A' : Finset (Fin (L + Nnew))}
    (hA' : A' = freshFin L Nnew)
    (Pround : {s // s ∈ A'} → Finset {s' // s' ∈ lvlSet N c L j hL}) {k s : ℕ}
    (hk : k < Nnew) :
    s ∈ stepP h hA' Pround k ↔ ∃ s' ∈ Pround ⟨⟨L + k, by omega⟩,
      by rw [hA']; exact mem_freshFin.mpr (Nat.le_add_right L k)⟩, rawOf h s' = s := by
  rw [stepP, dif_pos hk, Finset.mem_image]

lemma stepP_subset {lc : ℤ} {j L : ℕ} {hL : 1 ≤ L} {N : ℕ → ℕ} {P : ℕ → ℕ → Finset ℕ}
    {c : ℕ → ℕ → ℕ} {X : HistData d L} {f₀ : Fin L → Bool}
    (h : LevDInv d lc j L hL N P c X f₀) {Nnew : ℕ} {A' : Finset (Fin (L + Nnew))}
    (hA' : A' = freshFin L Nnew)
    (Pround : {s // s ∈ A'} → Finset {s' // s' ∈ lvlSet N c L j hL}) (k : ℕ) :
    stepP h hA' Pround k ⊆ Finset.range (N j) := by
  intro s hs
  rw [stepP] at hs
  split_ifs at hs with hk
  · rw [Finset.mem_image] at hs
    obtain ⟨s', -, rfl⟩ := hs
    exact Finset.mem_range.mpr (rawOf_lt h s')
  · exact absurd hs (Finset.notMem_empty s)

lemma stepP_nonempty {lc : ℤ} {j L : ℕ} {hL : 1 ≤ L} {N : ℕ → ℕ} {P : ℕ → ℕ → Finset ℕ}
    {c : ℕ → ℕ → ℕ} {X : HistData d L} {f₀ : Fin L → Bool}
    (h : LevDInv d lc j L hL N P c X f₀) {Nnew : ℕ} {A' : Finset (Fin (L + Nnew))}
    (hA' : A' = freshFin L Nnew)
    (Pround : {s // s ∈ A'} → Finset {s' // s' ∈ lvlSet N c L j hL})
    (hPne : ∀ s, (Pround s).Nonempty) {k : ℕ} (hk : k < Nnew) :
    (stepP h hA' Pround k).Nonempty := by
  obtain ⟨s', hs'⟩ := hPne ⟨⟨L + k, by omega⟩,
    by rw [hA']; exact mem_freshFin.mpr (Nat.le_add_right L k)⟩
  exact ⟨rawOf h s', (mem_stepP h hA' Pround hk).mpr ⟨s', hs', rfl⟩⟩

@[simp] lemma stepN_self (N : ℕ → ℕ) (Nnew j : ℕ) : stepN N Nnew j (j + 1) = Nnew := by
  simp [stepN]

lemma stepN_of_ne {N : ℕ → ℕ} {Nnew j i : ℕ} (hi : i ≠ j + 1) : stepN N Nnew j i = N i := by
  simp [stepN, hi]

@[simp] lemma stepC_self (c : ℕ → ℕ → ℕ) (L j s : ℕ) : stepC c L j (j + 1) s = L + s := by
  simp [stepC]

lemma stepC_of_ne {c : ℕ → ℕ → ℕ} {L j i : ℕ} (hi : i ≠ j + 1) (s : ℕ) :
    stepC c L j i s = c i s := by
  simp [stepC, hi]

/-- The attachment function after a round. -/
def stepPAll {lc : ℤ} {j L : ℕ} {hL : 1 ≤ L} {N : ℕ → ℕ} {P : ℕ → ℕ → Finset ℕ}
    {c : ℕ → ℕ → ℕ} {X : HistData d L} {f₀ : Fin L → Bool}
    (h : LevDInv d lc j L hL N P c X f₀) {Nnew : ℕ} {A' : Finset (Fin (L + Nnew))}
    (hA' : A' = freshFin L Nnew)
    (Pround : {s // s ∈ A'} → Finset {s' // s' ∈ lvlSet N c L j hL}) : ℕ → ℕ → Finset ℕ :=
  fun i k => if i = j then stepP h hA' Pround k else P i k

lemma stepPAll_self {lc : ℤ} {j L : ℕ} {hL : 1 ≤ L} {N : ℕ → ℕ} {P : ℕ → ℕ → Finset ℕ}
    {c : ℕ → ℕ → ℕ} {X : HistData d L} {f₀ : Fin L → Bool}
    (h : LevDInv d lc j L hL N P c X f₀) {Nnew : ℕ} {A' : Finset (Fin (L + Nnew))}
    (hA' : A' = freshFin L Nnew)
    (Pround : {s // s ∈ A'} → Finset {s' // s' ∈ lvlSet N c L j hL}) (k : ℕ) :
    stepPAll h hA' Pround j k = stepP h hA' Pround k := by
  simp [stepPAll]

lemma stepPAll_of_ne {lc : ℤ} {j L : ℕ} {hL : 1 ≤ L} {N : ℕ → ℕ} {P : ℕ → ℕ → Finset ℕ}
    {c : ℕ → ℕ → ℕ} {X : HistData d L} {f₀ : Fin L → Bool}
    (h : LevDInv d lc j L hL N P c X f₀) {Nnew : ℕ} {A' : Finset (Fin (L + Nnew))}
    (hA' : A' = freshFin L Nnew)
    (Pround : {s // s ∈ A'} → Finset {s' // s' ∈ lvlSet N c L j hL}) {i : ℕ} (hi : i ≠ j)
    (k : ℕ) : stepPAll h hA' Pround i k = P i k := by
  simp [stepPAll, hi]

/-! ## The level-`(j+1)` slot set and index set after the step -/

/-- The level-`(j+1)` coordinate of the fresh index `s`. -/
lemma ptFin_step {j L Nnew : ℕ} {c : ℕ → ℕ → ℕ} (hL' : 1 ≤ L + Nnew) {s : ℕ}
    (hs : s < Nnew) :
    ptFin (stepC c L j) (L + Nnew) (j + 1) s hL' = ⟨L + s, by omega⟩ := by
  apply Fin.ext
  rw [ptFin_val_of_lt hL' (by rw [stepC_self]; omega), stepC_self]

/-- The fresh coordinate of a `Fin Nnew`-index. -/
def freshPt (L Nnew : ℕ) (k : Fin Nnew) : Fin (L + Nnew) :=
  ⟨L + k.1, by have := k.2; omega⟩

@[simp] lemma freshPt_val (L Nnew : ℕ) (k : Fin Nnew) : (freshPt L Nnew k).1 = L + k.1 := rfl

lemma ptFin_eq_freshPt {j L Nnew : ℕ} {c : ℕ → ℕ → ℕ} (hL' : 1 ≤ L + Nnew) {s : ℕ}
    (hs : s < Nnew) :
    ptFin (stepC c L j) (L + Nnew) (j + 1) s hL' = freshPt L Nnew ⟨s, hs⟩ := by
  rw [ptFin_step hL' hs]
  exact Fin.ext rfl

/-- The fresh coordinates are the level-`(j+1)` coordinates after the step. -/
lemma lvlSet_step {j L Nnew : ℕ} {N : ℕ → ℕ} {c : ℕ → ℕ → ℕ} {A' : Finset (Fin (L + Nnew))}
    (hA' : A' = freshFin L Nnew) (hL' : 1 ≤ L + Nnew) :
    lvlSet (stepN N Nnew j) (stepC c L j) (L + Nnew) (j + 1) hL' = A' := by
  rw [hA', freshFin]
  ext x
  rw [mem_lvlSet]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨s, hs, rfl⟩
    rw [ptFin_step hL' (by simpa using hs)]
    exact Nat.le_add_right L s
  · intro hx
    have hlt : x.1 - L < Nnew := by
      have h1 : x.1 - L + L = x.1 := Nat.sub_add_cancel hx
      have h2 : x.1 - L + L < Nnew + L := by
        rw [h1]
        exact lt_of_lt_of_eq x.2 (Nat.add_comm L Nnew)
      exact Nat.lt_of_add_lt_add_right h2
    refine ⟨x.1 - L, by simpa using hlt, ?_⟩
    rw [ptFin_step hL' hlt]
    apply Fin.ext
    simp only [freshPt_val]
    omega

/-- The fresh index set of a history: the fresh indices at which it is `true`. -/
def freshIdxSet (L Nnew : ℕ) (h' : Fin (L + Nnew) → Bool) : Finset ℕ :=
  ((Finset.univ : Finset (Fin Nnew)).filter (fun k => h' (freshPt L Nnew k) = true)).image Fin.val

lemma mem_freshIdxSet {L Nnew : ℕ} {h' : Fin (L + Nnew) → Bool} {s : ℕ} :
    s ∈ freshIdxSet L Nnew h' ↔ ∃ k : Fin Nnew, k.1 = s ∧ h' (freshPt L Nnew k) = true := by
  rw [freshIdxSet, Finset.mem_image]
  constructor
  · rintro ⟨k, hk, hks⟩
    exact ⟨k, hks, (Finset.mem_filter.mp hk).2⟩
  · rintro ⟨k, hks, hh⟩
    exact ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hh⟩, hks⟩

/-- The index set of a history after the step is its fresh index set. -/
lemma idxSet_step {j L Nnew : ℕ} {N : ℕ → ℕ} {c : ℕ → ℕ → ℕ}
    (hL' : 1 ≤ L + Nnew) (h' : Fin (L + Nnew) → Bool) :
    idxSet (stepN N Nnew j) (stepC c L j) (L + Nnew) (j + 1) hL' h'
      = freshIdxSet L Nnew h' := by
  ext s
  rw [mem_idxSet, mem_freshIdxSet]
  constructor
  · rintro ⟨hs, hh⟩
    have hs' : s < Nnew := by simpa using hs
    refine ⟨⟨s, hs'⟩, rfl, ?_⟩
    rw [ptFin_eq_freshPt hL' hs'] at hh
    exact hh
  · rintro ⟨k, hk, hh⟩
    rw [← hk]
    refine ⟨by simpa using k.2, ?_⟩
    rw [ptFin_eq_freshPt hL' k.2]
    exact hh


end

end Work.Peluse.UControl
