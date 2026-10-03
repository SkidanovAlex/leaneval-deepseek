import Mathlib
import Submission.Work.Peluse.UControl.slotHist_natAdd

/-!
# The round of Peluse's Lemma 4.8 with a *pinned* closing class

`Work.Peluse.UControl.LevInv` (in `levRoundDefs.lean`) describes a state of one round of Peluse's
Lemma 4.8 with the surviving class pinned to the *whole* parameter set `A`
(`memA : A ∈ K`, and the `(D-1)`-coefficient recursion `coeff_diff` is stated for the class `A`).
That is enough for the level chain's application (where `f₀ = 0` and the punctured history of `A` is
`f₀`), but not for the statement `LevRoundT` with an arbitrary frozen vector `f₀`: the class that
survives the round is the class of the punctured-out history `f₀` only when the class of `f₀` is
`A`; in general the round must be run with an arbitrary closing class `ω`.

This file defines the invariant with such a parameter closing class, together with the elementary
dictionary (`histCls`, `slotCls`, `histOf`, `slotHist`) that the round's bookkeeping uses.

* `histCls A h = A.filter (fun i => h i)` — the class of a history: the parameter subset it selects;
* `slotCls A r h = A.filter (fun i => h (Fin.castAdd r i))` — the class of a slot at a state with `r`
  new coordinates (the old coordinates of its history);
* `LevInv2 d D A f₀ atoms ω r K σ X` — the state of one round after `r` steps, with closing class
  `ω` (`K` the alive class set, `σ` the reference of the class reduction at each time);
* `mem_cubeSet_new` — the new coordinates' sub-cube, identified with the `ε`-histories of the
  closing class (the shape of the round's output at the level of the slot set).
-/

set_option autoImplicit false
open scoped BigOperators

namespace Work.Peluse.UControl

noncomputable section

open Polynomial

attribute [local instance] Classical.propDecidable

variable {d D L : ℕ}

/-! ## The class of a history -/

/-- The class of a history `h`: the set of the current parameters at which `h` is true. -/
def histCls {n : ℕ} (A : Finset (Fin n)) (h : Fin n → Bool) : Finset (Fin n) :=
  A.filter (fun i => h i)

lemma histCls_subset {n : ℕ} (A : Finset (Fin n)) (h : Fin n → Bool) : histCls A h ⊆ A :=
  Finset.filter_subset _ _

lemma mem_histCls {n : ℕ} {A : Finset (Fin n)} {h : Fin n → Bool} {i : Fin n} :
    i ∈ histCls A h ↔ i ∈ A ∧ h i = true := by
  rw [histCls, Finset.mem_filter]

lemma histCls_histOf {L : ℕ} {A : Finset (Fin L)} {f₀ : Fin L → Bool} {ω : Finset (Fin L)}
    (hω : ω ⊆ A) : histCls A (histOf A f₀ ω) = ω := by
  ext i
  rw [mem_histCls]
  constructor
  · rintro ⟨hiA, hd⟩
    rw [histOf_apply hiA] at hd
    exact of_decide_eq_true hd
  · intro hi
    exact ⟨hω hi, by rw [histOf_apply (hω hi), decide_eq_true hi]⟩

lemma histOf_histCls {L : ℕ} {A : Finset (Fin L)} {f₀ : Fin L → Bool} {h : Fin L → Bool}
    (hh : h ∈ cubeSet L A f₀) : histOf A f₀ (histCls A h) = h := by
  funext i
  rw [cubeSet, Finset.mem_filter] at hh
  by_cases hi : i ∈ A
  · rw [histOf_apply hi]
    by_cases hmem : i ∈ histCls A h
    · rw [decide_eq_true hmem]
      exact (mem_histCls.mp hmem).2.symm
    · rw [decide_eq_false hmem]
      have hf : h i = false := by
        cases hb : h i with
        | false => rfl
        | true => exact absurd (mem_histCls.mpr ⟨hi, hb⟩) hmem
      rw [hf]
  · rw [histOf, if_neg hi]
    exact (hh.2 i hi).symm

/-- The class of a slot of a state with `r` new coordinates: the parameters at which its history is
true (the new coordinates are ignored). -/
def slotCls {L : ℕ} (A : Finset (Fin L)) (r : ℕ) (h : Fin (L + r) → Bool) : Finset (Fin L) :=
  A.filter (fun i => h (Fin.castAdd r i))

lemma mem_slotCls {L r : ℕ} {A : Finset (Fin L)} {h : Fin (L + r) → Bool} {i : Fin L} :
    i ∈ slotCls A r h ↔ i ∈ A ∧ h (Fin.castAdd r i) = true := by
  rw [slotCls, Finset.mem_filter]

lemma slotCls_slotHist {L r : ℕ} (A : Finset (Fin L)) (h₀ : Fin L → Bool) (w : Fin r → Bool) :
    slotCls A r (slotHist h₀ r w) = histCls A h₀ := by
  ext i
  rw [mem_slotCls, mem_histCls, slotHist_castAdd]

lemma slotCls_histOf {L r : ℕ} {A : Finset (Fin L)} {f₀ : Fin L → Bool} {ω : Finset (Fin L)}
    (hω : ω ⊆ A) (w : Fin r → Bool) :
    slotCls A r (slotHist (histOf A f₀ ω) r w) = ω := by
  rw [slotCls_slotHist, histCls_histOf hω]

/-! ## The invariant of a round with a pinned closing class -/

/-- **The invariant of one round of Peluse's Lemma 4.8, with closing class `ω`.**

* `K` is the set of *alive classes* (subsets of `A`, described by their histories
  `histOf A f₀ ω'`), `ω ∈ K` is the class that will be closed;
* `σ j` is the reference of the class reduction performed at time `j` (the atom sum of the class
  killed then), so that the top-degree slots of a class `ω'` at time `r` have leading coefficient
  `subSum ω' - subSum (σ (last r))`;
* the top-degree slots are exactly `(inr 0, slotHist (histOf A f₀ ω') r w)` for `ω' ∈ K` and
  `w : Fin r → Bool`, all of degree `D`;
* `coeff_diff` is the `ε`-recursion of the degree-`(D-1)` coefficients of the closing class `ω`,
  which the closing step turns into the new leading coefficients. -/
structure LevInv2 (d D : ℕ) (A : Finset (Fin L)) (f₀ : Fin L → Bool)
    (atoms : {s // s ∈ A} → MvPolynomial (Fin L) ℤ) (ω : Finset (Fin L))
    (r : ℕ) (K : Finset (Finset (Fin L))) (σ : Fin (r + 1) → Finset (Fin L))
    (X : HistData d (L + r)) : Prop where
  subK : ∀ ω' ∈ K, ω' ⊆ A
  memK : ω ∈ K
  sigma_sub : ∀ j, σ j ⊆ A
  sigma_ne : ∀ j, σ j ≠ ω
  degLe : ∀ x ∈ X.H, (X.Q x.1 x.2).natDegree ≤ D
  top_mem : ∀ ω' ∈ K, ∀ w : Fin r → Bool,
    ((Sum.inr 0 : InitIdx d), slotHist (histOf A f₀ ω') r w) ∈ X.H ∧
    (X.Q (Sum.inr 0) (slotHist (histOf A f₀ ω') r w)).natDegree = D ∧
    (X.Q (Sum.inr 0) (slotHist (histOf A f₀ ω') r w)).leadingCoeff
      = liftSub A atoms r ω' - liftSub A atoms r (σ (Fin.last r))
  top_only : ∀ x ∈ X.H, D ≤ (X.Q x.1 x.2).natDegree →
    x.1 = (Sum.inr 0 : InitIdx d) ∧ ∃ ω' ∈ K, ∃ w : Fin r → Bool,
      x.2 = slotHist (histOf A f₀ ω') r w
  coeff_diff : ∀ w : Fin r → Bool,
    (X.Q (Sum.inr 0) (slotHist (histOf A f₀ ω) r w)).coeff (D - 1)
      - (X.Q (Sum.inr 0) (slotHist (histOf A f₀ ω) r 0)).coeff (D - 1)
    = ∑ j : Fin r, D • ((liftSub A atoms r ω - liftSub A atoms r (σ (Fin.castSucc j)))
        * MvPolynomial.X (Fin.natAdd L j)
        * (if w j then (1 : MvPolynomial (Fin (L + r)) ℤ) else 0))

/-- The round has run to completion at `X`: every live slot has degree `D` and one class is left. -/
def LevStop (D : ℕ) {d L r : ℕ} (X : HistData d (L + r)) (K : Finset (Finset (Fin L))) : Prop :=
  (∀ x ∈ X.H, D ≤ (X.Q x.1 x.2).natDegree) ∧ K.card = 1

/-! ## The closing class's sub-cube

The output of the round is the punctured sub-cube of the *new* coordinates: the histories agreeing
with the closing class's history off the new coordinates.  The lemma below identifies it with the
`ε`-histories of the closing class. -/

/-- The new coordinates of a state obtained by `N` steps from a state at length `L`. -/
def newCoords (L N : ℕ) : Finset (Fin (L + N)) :=
  Finset.univ.filter (fun i : Fin (L + N) => L ≤ i.1)

lemma mem_newCoords {L N : ℕ} {i : Fin (L + N)} : i ∈ newCoords L N ↔ L ≤ i.1 := by
  simp [newCoords]

lemma natAdd_mem_newCoords {L N : ℕ} (j : Fin N) : Fin.natAdd L j ∈ newCoords L N := by
  rw [mem_newCoords, Fin.val_natAdd]
  omega

lemma eq_castAdd_of_not_mem_newCoords {L N : ℕ} {i : Fin (L + N)}
    (h : i ∉ newCoords L N) : ∃ i' : Fin L, i = Fin.castAdd N i' := by
  rw [mem_newCoords] at h
  have hv : i.1 < L := by omega
  exact ⟨⟨i.1, hv⟩, Fin.ext rfl⟩

/-- **The sub-cube of the new coordinates is the set of the `ε`-histories of the closing class.** -/
lemma mem_cubeSet_new {L N : ℕ} (h₀ : Fin L → Bool) (h' : Fin (L + N) → Bool) :
    h' ∈ cubeSet (L + N) (newCoords L N) (slotHist h₀ N 0) ↔
      ∃ w : Fin N → Bool, h' = slotHist h₀ N w := by
  constructor
  · intro hh
    refine ⟨fun j => h' (Fin.natAdd L j), ?_⟩
    funext i
    refine Fin.addCases (motive := fun i =>
      h' i = slotHist h₀ N (fun j => h' (Fin.natAdd L j)) i) ?_ ?_ i
    · intro i'
      have hmem : Fin.castAdd N i' ∉ newCoords L N := by
        rw [mem_newCoords, Fin.val_castAdd]; omega
      have h1 : h' (Fin.castAdd N i') = slotHist h₀ N 0 (Fin.castAdd N i') :=
        (Finset.mem_filter.mp hh).2 _ hmem
      rw [h1, slotHist_castAdd, slotHist_castAdd]
    · intro j
      rw [slotHist_natAdd]
  · rintro ⟨w, rfl⟩
    rw [cubeSet, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, fun i hi => ?_⟩
    obtain ⟨i', rfl⟩ := eq_castAdd_of_not_mem_newCoords hi
    rw [slotHist_castAdd, slotHist_castAdd]

/-- The closing class's own `ε`-history of all `false` is the `0` of the new sub-cube. -/
lemma slotHist_zero_eq (L N : ℕ) (h₀ : Fin L → Bool) :
    slotHist h₀ N (0 : Fin N → Bool) = slotHist h₀ N 0 := rfl

/-! ## The index of a new coordinate, and the class parameters in subtype form -/

/-- The `ε`-coordinate index of a new coordinate of a state with `N` new parameters. -/
def newIdx {L N : ℕ} (i : Fin (L + N)) (hi : L ≤ i.1) : Fin N :=
  ⟨i.1 - L, by have h := i.2; omega⟩

lemma newIdx_natAdd {L N : ℕ} (j : Fin N) (h : L ≤ (Fin.natAdd L j).1) :
    newIdx (Fin.natAdd L j) h = j := by
  apply Fin.ext
  have h2 : (newIdx (Fin.natAdd L j) h).1 = (Fin.natAdd L j).1 - L := rfl
  rw [h2, Fin.val_natAdd]
  omega

lemma natAdd_newIdx {L N : ℕ} {i : Fin (L + N)} (hi : L ≤ i.1) :
    Fin.natAdd L (newIdx i hi) = i := by
  apply Fin.ext
  rw [Fin.val_natAdd, newIdx]
  simp
  omega

/-- The parameters of a class `P`, as a subset of the input parameters `A` in the subtype form used
by the round's output (`P : {s // s ∈ A'} → Finset {s' // s' ∈ A}`). -/
def clsPar {L : ℕ} (A : Finset (Fin L)) (P : Finset (Fin L)) : Finset {s // s ∈ A} :=
  (P ∩ A).attach.map ⟨fun s => (⟨s.1, (Finset.mem_inter.mp s.2).2⟩ : {s // s ∈ A}), by
    intro a b h
    refine Subtype.ext ?_
    have h1 := congrArg (fun x : {s // s ∈ A} => (x : Fin L)) h
    simpa using h1⟩

lemma mem_clsPar {L : ℕ} {A P : Finset (Fin L)} {s : {s // s ∈ A}} :
    s ∈ clsPar A P ↔ s.1 ∈ P := by
  constructor
  · intro hs
    rw [clsPar, Finset.mem_map] at hs
    obtain ⟨t, _, ht'⟩ := hs
    have h1 : (t : Fin L) = (s : Fin L) := by
      have h2 : ((⟨t.1, (Finset.mem_inter.mp t.2).2⟩ : {x // x ∈ A}) : Fin L) = (s : Fin L) :=
        congrArg (fun x : {x // x ∈ A} => (x : Fin L)) ht'
      exact h2
    rw [← h1]
    exact (Finset.mem_inter.mp t.2).1
  · intro hs
    rw [clsPar, Finset.mem_map]
    exact ⟨⟨s.1, Finset.mem_inter.mpr ⟨hs, s.2⟩⟩, Finset.mem_attach _ _, rfl⟩

/-- A sum over the class parameters of `P` is the corresponding filtered sum over the subtype. -/
lemma sum_clsPar {L n : ℕ} (A P : Finset (Fin L)) (f : {s // s ∈ A} → MvPolynomial (Fin n) ℤ) :
    (∑ s ∈ clsPar A P, f s) = ∑ s : {s // s ∈ A}, if s.1 ∈ P then f s else 0 := by
  rw [← Finset.sum_filter]
  congr 1
  ext s
  rw [Finset.mem_filter, mem_clsPar]
  simp

end

end Work.Peluse.UControl
