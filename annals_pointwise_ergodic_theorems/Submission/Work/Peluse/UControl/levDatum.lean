import Mathlib
import Submission.Work.Peluse.UControl.levRoundUHolds

/-!
# The nested PET datum carried by the level chain (`d ≥ 3` part of `PetLevelChain`)

The remaining obligation of `Work.Peluse.UControl.petChapter5Holds` is `PetLevelChain P` for
`P.natDegree ≥ 3`, whose content is Peluse's Lemma 4.8 iterated `d - 2` times.  The last round
produces a `LevCube`-state of degree `1` whose live slots are the punctured cube of the round's
fresh coordinates, and the *terminal comparison* with `linFamAvg` needs that state's leading
coefficients to be the *directions* `dir D d lc (d-1)` of the nested PET datum `D` (`IdxDatum`).

This file fixes the vocabulary in which the datum is carried along the chain.  Two design points
make the bookkeeping type-stable (the naive datum `S j = Fin (m j)` with `m` growing by
`Function.update` forces `Fin.cast`-transports at every level):

* the **level sizes** are a *raw* function `N : ℕ → ℕ` (level `i` has `N i` slots; `N i = 0` above
  the current level), the **attachments** are *raw* sets of natural numbers
  `P : ℕ → ℕ → Finset ℕ` (`P i k` is the set of level-`i` indices attached to the level-`(i+1)`
  index `k`), and the **coordinates** are a *raw* function `c : ℕ → ℕ → ℕ` (`c i s` is the
  coordinate of the level-`i` slot `s` inside the state's `Fin L`);
* the **direction polynomial** `dirPoly d lc P c j v` is built in the free polynomial ring
  `MvPolynomial ℕ ℤ` (so no `Fin L` and no casts appear in it): it is the polynomial analogue of
  `IdxDatum.dir`, with `dirPoly d lc P c 0 = C lc` and
  `dirPoly d lc P c (j+1) v = Σ_{s ∈ v} C (d - j) · dirPoly d lc P c j (P j s) · X (c (j+1) s)`.

`LevDInv d lc j L hL N P c X f₀` is the level-chain invariant at level `j`: the state `X` is the
`LevCube`-state of degree `d - j` on the level-`j` slot set, and the (image under `Fin.val` of the)
leading coefficients of its slots are the values of `dirPoly` at the raw index sets.
-/

set_option autoImplicit false
open scoped BigOperators

namespace Work.Peluse.UControl

noncomputable section

open Polynomial

attribute [local instance] Classical.propDecidable

variable {d L : ℕ}

/-! ## The coordinate map -/

/-- The `Fin L`-point with raw coordinate `c j s` (the default `⟨0, _⟩` is used when the value is
out of range; the invariant always calls it on coordinates `< L`). -/
def ptFin (c : ℕ → ℕ → ℕ) (L j s : ℕ) (hL : 1 ≤ L) : Fin L :=
  if h : c j s < L then ⟨c j s, h⟩ else ⟨0, hL⟩

lemma ptFin_of_lt {c : ℕ → ℕ → ℕ} {L j s : ℕ} (hL : 1 ≤ L) (h : c j s < L) :
    ptFin c L j s hL = ⟨c j s, h⟩ := dif_pos h

@[simp] lemma ptFin_val_of_lt {c : ℕ → ℕ → ℕ} {L j s : ℕ} (hL : 1 ≤ L) (h : c j s < L) :
    (ptFin c L j s hL).1 = c j s := by
  rw [ptFin_of_lt hL h]

/-- The level-`j` slot set, as a subset of the state's coordinates. -/
def lvlSet (N : ℕ → ℕ) (c : ℕ → ℕ → ℕ) (L j : ℕ) (hL : 1 ≤ L) : Finset (Fin L) :=
  ((Finset.range (N j)).attach).image (fun s => ptFin c L j s.1 hL)

lemma mem_lvlSet {N : ℕ → ℕ} {c : ℕ → ℕ → ℕ} {L j : ℕ} {hL : 1 ≤ L} {x : Fin L} :
    x ∈ lvlSet N c L j hL ↔ ∃ s, s < N j ∧ ptFin c L j s hL = x := by
  rw [lvlSet, Finset.mem_image]
  constructor
  · rintro ⟨s, -, rfl⟩
    exact ⟨s.1, Finset.mem_range.mp s.2, rfl⟩
  · rintro ⟨s, hs, rfl⟩
    exact ⟨⟨s, Finset.mem_range.mpr hs⟩, Finset.mem_univ _, rfl⟩

/-- The raw index set of a history at level `j`: the indices `s < N j` at which `h` is `true`. -/
def idxSet (N : ℕ → ℕ) (c : ℕ → ℕ → ℕ) (L j : ℕ) (hL : 1 ≤ L) (h : Fin L → Bool) : Finset ℕ :=
  (Finset.range (N j)).filter (fun s => h (ptFin c L j s hL) = true)

lemma mem_idxSet {N : ℕ → ℕ} {c : ℕ → ℕ → ℕ} {L j : ℕ} {hL : 1 ≤ L} {h : Fin L → Bool} {s : ℕ} :
    s ∈ idxSet N c L j hL h ↔ s < N j ∧ h (ptFin c L j s hL) = true := by
  rw [idxSet, Finset.mem_filter, Finset.mem_range]

lemma idxSet_subset (N : ℕ → ℕ) (c : ℕ → ℕ → ℕ) (L j : ℕ) (hL : 1 ≤ L) (h : Fin L → Bool) :
    idxSet N c L j hL h ⊆ Finset.range (N j) := fun _ hs => Finset.mem_range.mpr (mem_idxSet.mp hs).1

/-! ## The direction polynomial -/

/-- **The direction polynomial of the nested PET datum.**  `dirPoly d lc P c 0 = C lc` is the base
direction and `dirPoly d lc P c (j+1) v = Σ_{s ∈ v} C (d - j)·dirPoly d lc P c j (P j s)·X (c (j+1) s)`
is the recursion `dir_{j+1}(v) = Σ_{s∈v} (ℓ - j)·dir_j(par j s)·a_{j+1}(s)` of `IdxDatum.dir`. -/
def dirPoly (d : ℕ) (lc : ℤ) (P : ℕ → ℕ → Finset ℕ) (c : ℕ → ℕ → ℕ) :
    ℕ → Finset ℕ → MvPolynomial ℕ ℤ
  | 0, _ => MvPolynomial.C lc
  | (j + 1), v => ∑ s ∈ v, (MvPolynomial.C ((d : ℤ) - (j : ℤ)) *
      dirPoly d lc P c j (P j s)) * MvPolynomial.X (c (j + 1) s)

@[simp] lemma dirPoly_zero (d : ℕ) (lc : ℤ) (P : ℕ → ℕ → Finset ℕ) (c : ℕ → ℕ → ℕ)
    (v : Finset ℕ) :
    dirPoly d lc P c 0 v = MvPolynomial.C lc := rfl

lemma dirPoly_succ (d : ℕ) (lc : ℤ) (P : ℕ → ℕ → Finset ℕ) (c : ℕ → ℕ → ℕ)
    (j : ℕ) (v : Finset ℕ) :
    dirPoly d lc P c (j + 1) v = ∑ s ∈ v, (MvPolynomial.C ((d : ℤ) - (j : ℤ)) *
      dirPoly d lc P c j (P j s)) * MvPolynomial.X (c (j + 1) s) := rfl

/-- `dirPoly` at level `j+1` on a singleton. -/
lemma dirPoly_succ_singleton (d : ℕ) (lc : ℤ) (P : ℕ → ℕ → Finset ℕ) (c : ℕ → ℕ → ℕ)
    (j s : ℕ) :
    dirPoly d lc P c (j + 1) {s} = (MvPolynomial.C ((d : ℤ) - (j : ℤ)) *
      dirPoly d lc P c j (P j s)) * MvPolynomial.X (c (j + 1) s) := by
  rw [dirPoly_succ, Finset.sum_singleton]

/-- `dirPoly` at level `j+1` is the sum of its values on the singletons. -/
lemma dirPoly_succ_sum_singleton (d : ℕ) (lc : ℤ) (P : ℕ → ℕ → Finset ℕ)
    (c : ℕ → ℕ → ℕ) (j : ℕ) (v : Finset ℕ) :
    dirPoly d lc P c (j + 1) v = ∑ s ∈ v, dirPoly d lc P c (j + 1) {s} := by
  rw [dirPoly_succ]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  rw [dirPoly_succ_singleton]

/-- `dirPoly` only depends on the data at the levels `≤ j`. -/
lemma dirPoly_congr {d : ℕ} {lc : ℤ} {P P' : ℕ → ℕ → Finset ℕ} {c c' : ℕ → ℕ → ℕ} {j : ℕ}
    (hP : ∀ i < j, ∀ s, P i s = P' i s) (hc : ∀ i ≤ j, ∀ s, c i s = c' i s) :
    ∀ v : Finset ℕ, dirPoly d lc P c j v = dirPoly d lc P' c' j v := by
  induction j with
  | zero => intro v; simp
  | succ j ih =>
    intro v
    rw [dirPoly_succ, dirPoly_succ]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    rw [ih (fun i hi => hP i (by omega)) (fun i hi => hc i (by omega)) (P j s), hP j (by omega) s,
      hc (j + 1) (by omega) s]

/-- `dirPoly` at level `j` does not involve the data above level `j`. -/
lemma dirPoly_congr_le {d : ℕ} {lc : ℤ} {P P' : ℕ → ℕ → Finset ℕ} {c c' : ℕ → ℕ → ℕ} {j : ℕ}
    (hP : ∀ i < j, ∀ s, P i s = P' i s) (hc : ∀ i ≤ j, ∀ s, c i s = c' i s)
    (v : Finset ℕ) : dirPoly d lc P c j v = dirPoly d lc P' c' j v :=
  dirPoly_congr hP hc v

/-! ## The invariant -/

/-- **The level-chain invariant.**  `X : HistData d L` is the state of the level chain at level `j`
(the level sizes are `N`, the attachments `P`, the coordinates `c`): its live slots are the punctured
cube of the level-`j` slot set `lvlSet N c L j hL`, they all have degree `d - j`, and the image under
`Fin.val` of their leading coefficients is `dirPoly d lc P c j` at the raw index set of the history.
The hypothesis `1 ≤ L` only makes the default branch of `ptFin` total. -/
structure LevDInv (d : ℕ) (lc : ℤ) (j L : ℕ) (hL : 1 ≤ L) (N : ℕ → ℕ)
    (P : ℕ → ℕ → Finset ℕ) (c : ℕ → ℕ → ℕ) (X : HistData d L) (f₀ : Fin L → Bool) : Prop where
  hj : 1 ≤ j
  N0 : N 0 = 1
  Ntop : ∀ i, j < i → N i = 0
  Psub : ∀ i, i ≤ j → ∀ k, k < N (i + 1) → P i k ⊆ Finset.range (N i)
  Pne : ∀ i, i ≤ j → ∀ k, k < N (i + 1) → (P i k).Nonempty
  cbound : ∀ i, 1 ≤ i → i ≤ j → ∀ s, s < N i → c i s < L
  ccover : ∀ k, k < L → ∃ i, 1 ≤ i ∧ i ≤ j ∧ ∃ s, s < N i ∧ c i s = k
  cinj : ∀ i i' s s', 1 ≤ i → i ≤ j → 1 ≤ i' → i' ≤ j → s < N i → s' < N i' →
    c i s = c i' s' → i = i' ∧ s = s'
  f0false : ∀ s, s < N j → f₀ (ptFin c L j s hL) = false
  H_eq : X.H = LevH d L (lvlSet N c L j hL) f₀
  deg : ∀ h ∈ cubeSet L (lvlSet N c L j hL) f₀, h ≠ f₀ →
    (X.Q (Sum.inr 0 : InitIdx d) h).natDegree = d - j
  lc_eq : ∀ h ∈ cubeSet L (lvlSet N c L j hL) f₀, h ≠ f₀ →
    MvPolynomial.rename Fin.val ((X.Q (Sum.inr 0 : InitIdx d) h).leadingCoeff)
      = dirPoly d lc P c j (idxSet N c L j hL h)

end

end Work.Peluse.UControl
