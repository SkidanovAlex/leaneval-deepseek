import Mathlib
import Submission.Work.Drive.cutTransport
import Submission.Work.Surf.Neutral.ChordCrossingParity
import Submission.Work.Drive.cutDictionary
import Submission.Work.Drive.parityCore_of_functional

/-!
# The transport without the family-transversality package `ChordPair`

`Submission/Work/Drive/cutTransport.lean` proves the multiplicativity of Hugelmeyer's Lemma 2,
`n_P ≡ ε_Q · ε_R`, in two forms: the general one
(`Work.Drive.odd_ncard_cutBaseBox_iff_arcParity`, whose input is the base case
`hcross : ∀ i j, Odd #(chordMeet (A i) (B j))`) and the *packaged* one
(`Work.Drive.odd_ncard_cutBaseBox_iff_arcParity_of_chordPair` and
`Work.Drive.Capping.odd_ncard_topBdryMeet_zero_iff_arcParity*`), whose input is `Work.Drive.ChordPair`
for every pair of chords.

`ChordPair` contains, besides the position hypotheses, the **transversality of the straightening
family** of the two chords — a *family* transversality, i.e. a Sard-type statement about the concrete
cuts that is not available in the workspace (`CUT_TRANSPORT_STATUS.md` §4 item 5).  The strict base
case `Work.Surf.chord_crossing_parity` needs only the *pointwise* transversality

> `det2 (deriv a s) (deriv b t) ≠ 0` at every crossing `(s, t)`,

which is what the geometry of two transverse cuts actually provides.  Until now, that theorem could
not be used in the transport because its import closure contained
`Submission/Work/Drive/winding_eq_crossing_sum.lean`, which declares `Work.Drive.toC` — the same name
as `Submission/Work/Drive/UmlaufSetup.lean`, which the capping world needs
(`WindingEqCrossingSum`'s `toC` enters through an *unused* import of that file into the `GRB`
chapter).  The neutral copies under `Submission/Work/Surf/Neutral/` remove exactly that obstruction:
`Work.Surf.ChordN.chord_crossing_parity` imports together with `Work.Drive.CappingSpace` and hence
with `Work.Drive.cutTransport` (verified).

This file is therefore the *strict* transport: the same conclusions as
`cutTransport.lean`'s packaged forms, with `ChordPair` replaced by

* `hchord` — every arc is a chord (`Work.Drive.IsChord`);
* `hintN` — the crossings of the two systems lie strictly inside the disk (this is the "arcs are
  strictly interior off their endpoints" clause of an arc system, and it is also available in the
  packaged form `hint` with the norm conjunct);
* `htrans` — the pointwise transversality above.

Nothing else changes, and no new mathematics is needed: the base case is
`Work.Surf.ChordN.chord_crossing_parity`, transported by the already proved
`Work.Drive.odd_ncard_cutBaseBox_iff_arcParity`.
-/

namespace Work.Drive

open scoped Topology Manifold ContDiff
open Set

noncomputable section

/-- **The strict base case, in the transport's own hypothesis shape.**  For two systems of chords of
the disk model whose crossings are strictly interior and in the disk, and at which the two chords are
transverse, the pair count of `Work.Drive.odd_ncard_cutBaseBox_iff_arcParity` is odd.

This is `Work.Surf.ChordN.chord_crossing_parity` with the transport's (`Icc`-form) hypotheses. -/
theorem odd_ncard_chordMeet_of_strict {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : ι → ℝ → EuclideanSpace ℝ (Fin 2)) (B : κ → ℝ → EuclideanSpace ℝ (Fin 2))
    (hchordA : ∀ i, IsChord (A i)) (hchordB : ∀ j, IsChord (B j))
    (hint : ∀ (i : ι) (j : κ) (t s : ℝ), t ∈ Set.Icc (0 : ℝ) 1 → s ∈ Set.Icc (0 : ℝ) 1 →
      A i t = B j s → t ∈ Set.Ioo (0 : ℝ) 1 ∧ s ∈ Set.Ioo (0 : ℝ) 1 ∧ ‖A i t‖ < 1)
    (htrans : ∀ (i : ι) (j : κ) (t s : ℝ), t ∈ Set.Ioo (0 : ℝ) 1 → s ∈ Set.Ioo (0 : ℝ) 1 →
      A i t = B j s → det2 (deriv (A i) t) (deriv (B j) s) ≠ 0) :
    ∀ i j, Odd (chordMeet (A i) (B j)).ncard :=
  fun i j => Work.Surf.ChordN.chord_crossing_parity (hchordA i) (hchordB j)
    (fun s t hs ht h => hint i j s t hs ht h)
    (fun s t hs ht h => htrans i j s t hs ht h)

/-- **THE STRICT TRANSPORT.**  `Work.Drive.odd_ncard_cutBaseBox_iff_arcParity_of_chordPair` with the
family-transversality package `ChordPair` replaced by the pointwise transversality `htrans` (plus the
`IsChord` and interiority clauses, which are part of the arc-system structure of a cut). -/
theorem odd_ncard_cutBaseBox_iff_arcParity_of_strict {ι κ : Type*} [Fintype ι] [Fintype κ]
    (Q : ℂ → CappingSpace)
    (V W : EuclideanSpace ℝ (Fin 3) → CappingSpace)
    (A : ι → ℝ → EuclideanSpace ℝ (Fin 2)) (B : κ → ℝ → EuclideanSpace ℝ (Fin 2))
    (hVcut : diskCut Q V = arcCycle A) (hWcut : diskCut Q W = arcCycle B)
    (hchordA : ∀ i, IsChord (A i)) (hchordB : ∀ j, IsChord (B j))
    (hAinj : ∀ i, Set.InjOn (A i) (Set.Icc (0 : ℝ) 1))
    (hBinj : ∀ j, Set.InjOn (B j) (Set.Icc (0 : ℝ) 1))
    (hAdisj : ∀ i i' : ι, i ≠ i' →
      Disjoint (A i '' Set.Icc (0 : ℝ) 1) (A i' '' Set.Icc (0 : ℝ) 1))
    (hBdisj : ∀ j j' : κ, j ≠ j' →
      Disjoint (B j '' Set.Icc (0 : ℝ) 1) (B j' '' Set.Icc (0 : ℝ) 1))
    (hint : ∀ (i : ι) (j : κ) (t s : ℝ), t ∈ Set.Icc (0 : ℝ) 1 → s ∈ Set.Icc (0 : ℝ) 1 →
      A i t = B j s → t ∈ Set.Ioo (0 : ℝ) 1 ∧ s ∈ Set.Ioo (0 : ℝ) 1 ∧ ‖A i t‖ < 1)
    (hendsA : ∀ i k : ι, A i 0 = A k 0 ∨ A i 0 = antipode (A k 0) → i = k)
    (hendsB : ∀ j l : κ, B j 0 = B l 0 ∨ B j 0 = antipode (B l 0) → j = l)
    (htrans : ∀ (i : ι) (j : κ) (t s : ℝ), t ∈ Set.Ioo (0 : ℝ) 1 → s ∈ Set.Ioo (0 : ℝ) 1 →
      A i t = B j s → det2 (deriv (A i) t) (deriv (B j) s) ≠ 0) :
    Odd (cutBaseBox (diskPlane Q) V W).ncard ↔
      (Odd (chainMeetsLine A).ncard ∧ Odd (chainMeetsLine B).ncard) :=
  odd_ncard_cutBaseBox_iff_arcParity Q V W A B hVcut hWcut hAinj hBinj hAdisj hBdisj
    (fun i j t s ht hs h => ⟨(hint i j t s ht hs h).1, (hint i j t s ht hs h).2.1⟩)
    hendsA hendsB (odd_ncard_chordMeet_of_strict A B hchordA hchordB hint htrans)

/-- The strict transport in the multiplicative form (the shape `(SURF)` consumes directly). -/
theorem odd_ncard_cutBaseBox_iff_mul_of_strict {ι κ : Type*} [Fintype ι] [Fintype κ]
    (Q : ℂ → CappingSpace)
    (V W : EuclideanSpace ℝ (Fin 3) → CappingSpace)
    (A : ι → ℝ → EuclideanSpace ℝ (Fin 2)) (B : κ → ℝ → EuclideanSpace ℝ (Fin 2))
    (hVcut : diskCut Q V = arcCycle A) (hWcut : diskCut Q W = arcCycle B)
    (hchordA : ∀ i, IsChord (A i)) (hchordB : ∀ j, IsChord (B j))
    (hAinj : ∀ i, Set.InjOn (A i) (Set.Icc (0 : ℝ) 1))
    (hBinj : ∀ j, Set.InjOn (B j) (Set.Icc (0 : ℝ) 1))
    (hAdisj : ∀ i i' : ι, i ≠ i' →
      Disjoint (A i '' Set.Icc (0 : ℝ) 1) (A i' '' Set.Icc (0 : ℝ) 1))
    (hBdisj : ∀ j j' : κ, j ≠ j' →
      Disjoint (B j '' Set.Icc (0 : ℝ) 1) (B j' '' Set.Icc (0 : ℝ) 1))
    (hint : ∀ (i : ι) (j : κ) (t s : ℝ), t ∈ Set.Icc (0 : ℝ) 1 → s ∈ Set.Icc (0 : ℝ) 1 →
      A i t = B j s → t ∈ Set.Ioo (0 : ℝ) 1 ∧ s ∈ Set.Ioo (0 : ℝ) 1 ∧ ‖A i t‖ < 1)
    (hendsA : ∀ i k : ι, A i 0 = A k 0 ∨ A i 0 = antipode (A k 0) → i = k)
    (hendsB : ∀ j l : κ, B j 0 = B l 0 ∨ B j 0 = antipode (B l 0) → j = l)
    (htrans : ∀ (i : ι) (j : κ) (t s : ℝ), t ∈ Set.Ioo (0 : ℝ) 1 → s ∈ Set.Ioo (0 : ℝ) 1 →
      A i t = B j s → det2 (deriv (A i) t) (deriv (B j) s) ≠ 0) :
    Odd (cutBaseBox (diskPlane Q) V W).ncard ↔
      Odd ((chainMeetsLine A).ncard * (chainMeetsLine B).ncard) := by
  rw [odd_ncard_cutBaseBox_iff_arcParity_of_strict Q V W A B hVcut hWcut hchordA hchordB hAinj hBinj
    hAdisj hBdisj hint hendsA hendsB htrans, Nat.odd_mul]

/-- **The strict transport in the engine's own count.**  `Work.Drive.Capping.odd_ncard_topBdryMeet_zero_iff_arcParity`
with `ChordPair` replaced by the strict hypotheses (see `odd_ncard_cutBaseBox_iff_arcParity_of_strict`). -/
theorem Capping.odd_ncard_topBdryMeet_zero_iff_arcParity_of_strict
    (Q : ℂ → CappingSpace) (P : Fin 3 → EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (hQ : P 0 = diskPlane Q)
    (c : Fin 3 → ℝ) (ψ : ℝ → ℝ) (hψ : ψ 1 = 0)
    (hfibV : ∀ u ∈ cutBaseBox (P 0) (clampedSweep (c 1) ψ (P 1)) (clampedSweep (c 2) ψ (P 2)),
      (cutFibreBox (P 0) (clampedSweep (c 1) ψ (P 1)) u).ncard = 1)
    (hfibW : ∀ u ∈ cutBaseBox (P 0) (clampedSweep (c 1) ψ (P 1)) (clampedSweep (c 2) ψ (P 2)),
      (cutFibreBox (P 0) (clampedSweep (c 2) ψ (P 2)) u).ncard = 1)
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : ι → ℝ → EuclideanSpace ℝ (Fin 2)) (B : κ → ℝ → EuclideanSpace ℝ (Fin 2))
    (hVcut : diskCut Q (clampedSweep (c 1) ψ (P 1)) = arcCycle A)
    (hWcut : diskCut Q (clampedSweep (c 2) ψ (P 2)) = arcCycle B)
    (hchordA : ∀ i, IsChord (A i)) (hchordB : ∀ j, IsChord (B j))
    (hAinj : ∀ i, Set.InjOn (A i) (Set.Icc (0 : ℝ) 1))
    (hBinj : ∀ j, Set.InjOn (B j) (Set.Icc (0 : ℝ) 1))
    (hAdisj : ∀ i i' : ι, i ≠ i' →
      Disjoint (A i '' Set.Icc (0 : ℝ) 1) (A i' '' Set.Icc (0 : ℝ) 1))
    (hBdisj : ∀ j j' : κ, j ≠ j' →
      Disjoint (B j '' Set.Icc (0 : ℝ) 1) (B j' '' Set.Icc (0 : ℝ) 1))
    (hint : ∀ (i : ι) (j : κ) (t s : ℝ), t ∈ Set.Icc (0 : ℝ) 1 → s ∈ Set.Icc (0 : ℝ) 1 →
      A i t = B j s → t ∈ Set.Ioo (0 : ℝ) 1 ∧ s ∈ Set.Ioo (0 : ℝ) 1 ∧ ‖A i t‖ < 1)
    (hendsA : ∀ i k : ι, A i 0 = A k 0 ∨ A i 0 = antipode (A k 0) → i = k)
    (hendsB : ∀ j l : κ, B j 0 = B l 0 ∨ B j 0 = antipode (B l 0) → j = l)
    (htrans : ∀ (i : ι) (j : κ) (t s : ℝ), t ∈ Set.Ioo (0 : ℝ) 1 → s ∈ Set.Ioo (0 : ℝ) 1 →
      A i t = B j s → det2 (deriv (A i) t) (deriv (B j) s) ≠ 0) :
    Odd (topBdryMeet CappingSpace (fun k => clampedSweep (c k) ψ (P k)) 0).ncard ↔
      (Odd (chainMeetsLine A).ncard ∧ Odd (chainMeetsLine B).ncard) := by
  rw [Capping.ncard_topBdryMeet_zero_eq_ncard_cutBaseBox P c ψ hψ hfibV hfibW, hQ]
  exact odd_ncard_cutBaseBox_iff_arcParity_of_strict Q _ _ A B hVcut hWcut hchordA hchordB hAinj hBinj
    hAdisj hBdisj hint hendsA hendsB htrans

/-- **The strict transport for the radial sweeps** (the odd-multiplicity case, which is the geometric
one): the strict form of `Work.Drive.Capping.odd_ncard_topBdryMeet_zero_iff_arcParity_of_odd_fibres`. -/
theorem Capping.odd_ncard_topBdryMeet_zero_iff_arcParity_of_odd_fibres_strict
    (Q : ℂ → CappingSpace) (P : Fin 3 → EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (hQ : P 0 = diskPlane Q)
    (c : Fin 3 → ℝ) (ψ : ℝ → ℝ) (hψ : ψ 1 = 0)
    (hfinV : (cutRelBox (P 0) (clampedSweep (c 1) ψ (P 1))).Finite)
    (hfinW : (cutRelBox (P 0) (clampedSweep (c 2) ψ (P 2))).Finite)
    (hfibV : ∀ u ∈ cutBaseBox (P 0) (clampedSweep (c 1) ψ (P 1)) (clampedSweep (c 2) ψ (P 2)),
      Odd (cutFibreBox (P 0) (clampedSweep (c 1) ψ (P 1)) u).ncard)
    (hfibW : ∀ u ∈ cutBaseBox (P 0) (clampedSweep (c 1) ψ (P 1)) (clampedSweep (c 2) ψ (P 2)),
      Odd (cutFibreBox (P 0) (clampedSweep (c 2) ψ (P 2)) u).ncard)
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : ι → ℝ → EuclideanSpace ℝ (Fin 2)) (B : κ → ℝ → EuclideanSpace ℝ (Fin 2))
    (hVcut : diskCut Q (clampedSweep (c 1) ψ (P 1)) = arcCycle A)
    (hWcut : diskCut Q (clampedSweep (c 2) ψ (P 2)) = arcCycle B)
    (hchordA : ∀ i, IsChord (A i)) (hchordB : ∀ j, IsChord (B j))
    (hAinj : ∀ i, Set.InjOn (A i) (Set.Icc (0 : ℝ) 1))
    (hBinj : ∀ j, Set.InjOn (B j) (Set.Icc (0 : ℝ) 1))
    (hAdisj : ∀ i i' : ι, i ≠ i' →
      Disjoint (A i '' Set.Icc (0 : ℝ) 1) (A i' '' Set.Icc (0 : ℝ) 1))
    (hBdisj : ∀ j j' : κ, j ≠ j' →
      Disjoint (B j '' Set.Icc (0 : ℝ) 1) (B j' '' Set.Icc (0 : ℝ) 1))
    (hint : ∀ (i : ι) (j : κ) (t s : ℝ), t ∈ Set.Icc (0 : ℝ) 1 → s ∈ Set.Icc (0 : ℝ) 1 →
      A i t = B j s → t ∈ Set.Ioo (0 : ℝ) 1 ∧ s ∈ Set.Ioo (0 : ℝ) 1 ∧ ‖A i t‖ < 1)
    (hendsA : ∀ i k : ι, A i 0 = A k 0 ∨ A i 0 = antipode (A k 0) → i = k)
    (hendsB : ∀ j l : κ, B j 0 = B l 0 ∨ B j 0 = antipode (B l 0) → j = l)
    (htrans : ∀ (i : ι) (j : κ) (t s : ℝ), t ∈ Set.Ioo (0 : ℝ) 1 → s ∈ Set.Ioo (0 : ℝ) 1 →
      A i t = B j s → det2 (deriv (A i) t) (deriv (B j) s) ≠ 0) :
    Odd (topBdryMeet CappingSpace (fun k => clampedSweep (c k) ψ (P k)) 0).ncard ↔
      (Odd (chainMeetsLine A).ncard ∧ Odd (chainMeetsLine B).ncard) := by
  have hbase : Odd (cutBaseBox (P 0) (clampedSweep (c 1) ψ (P 1))
        (clampedSweep (c 2) ψ (P 2))).ncard ↔
      (Odd (chainMeetsLine A).ncard ∧ Odd (chainMeetsLine B).ncard) := by
    rw [hQ]
    exact odd_ncard_cutBaseBox_iff_arcParity_of_strict Q _ _ A B hVcut hWcut hchordA hchordB hAinj
      hBinj hAdisj hBdisj hint hendsA hendsB htrans
  have hev := even_ncard_cutTriples_add_ncard_cutBaseBox_of_odd_fibres (P 0)
    (clampedSweep (c 1) ψ (P 1)) (clampedSweep (c 2) ψ (P 2)) hfinV hfinW hfibV hfibW
  rw [Nat.even_add] at hev
  have hiff : Odd (cutTriples (P 0) (clampedSweep (c 1) ψ (P 1))
        (clampedSweep (c 2) ψ (P 2))).ncard ↔
      Odd (cutBaseBox (P 0) (clampedSweep (c 1) ψ (P 1))
        (clampedSweep (c 2) ψ (P 2))).ncard := by
    have hmod : (cutTriples (P 0) (clampedSweep (c 1) ψ (P 1))
          (clampedSweep (c 2) ψ (P 2))).ncard % 2
        = (cutBaseBox (P 0) (clampedSweep (c 1) ψ (P 1))
          (clampedSweep (c 2) ψ (P 2))).ncard % 2 := by
      have h1 : (cutTriples (P 0) (clampedSweep (c 1) ψ (P 1))
            (clampedSweep (c 2) ψ (P 2))).ncard % 2 = 0 ↔
          (cutBaseBox (P 0) (clampedSweep (c 1) ψ (P 1))
            (clampedSweep (c 2) ψ (P 2))).ncard % 2 = 0 := by
        simpa [Nat.even_iff] using hev
      omega
    rw [Nat.odd_iff, Nat.odd_iff, hmod]
  rw [ncard_topBdryMeet_zero_eq_ncard_cutTriples P c ψ hψ]
  exact hiff.trans hbase

/-- **The strict transport with the transport's own `hint`.**  The packaged forms of
`cutTransport.lean` take `hint` in the `Icc`-form without the norm conjunct; here that conjunct is
replaced by the two hypotheses that every arc of the system is strictly inside the disk off its
endpoints (`hArcA`, `hArcB`) — which is a clause of the arc-system structure of a cut. -/
theorem odd_ncard_cutBaseBox_iff_arcParity_of_strict'
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (Q : ℂ → CappingSpace)
    (V W : EuclideanSpace ℝ (Fin 3) → CappingSpace)
    (A : ι → ℝ → EuclideanSpace ℝ (Fin 2)) (B : κ → ℝ → EuclideanSpace ℝ (Fin 2))
    (hVcut : diskCut Q V = arcCycle A) (hWcut : diskCut Q W = arcCycle B)
    (hchordA : ∀ i, IsChord (A i)) (hchordB : ∀ j, IsChord (B j))
    (hAinj : ∀ i, Set.InjOn (A i) (Set.Icc (0 : ℝ) 1))
    (hBinj : ∀ j, Set.InjOn (B j) (Set.Icc (0 : ℝ) 1))
    (hAdisj : ∀ i i' : ι, i ≠ i' →
      Disjoint (A i '' Set.Icc (0 : ℝ) 1) (A i' '' Set.Icc (0 : ℝ) 1))
    (hBdisj : ∀ j j' : κ, j ≠ j' →
      Disjoint (B j '' Set.Icc (0 : ℝ) 1) (B j' '' Set.Icc (0 : ℝ) 1))
    (hint : ∀ (i : ι) (j : κ) (t s : ℝ), t ∈ Set.Icc (0 : ℝ) 1 → s ∈ Set.Icc (0 : ℝ) 1 →
      A i t = B j s → t ∈ Set.Ioo (0 : ℝ) 1 ∧ s ∈ Set.Ioo (0 : ℝ) 1)
    (hArcA : ∀ (i : ι) (t : ℝ), t ∈ Set.Ioo (0 : ℝ) 1 → ‖A i t‖ < 1)
    (hArcB : ∀ (j : κ) (s : ℝ), s ∈ Set.Ioo (0 : ℝ) 1 → ‖B j s‖ < 1)
    (hendsA : ∀ i k : ι, A i 0 = A k 0 ∨ A i 0 = antipode (A k 0) → i = k)
    (hendsB : ∀ j l : κ, B j 0 = B l 0 ∨ B j 0 = antipode (B l 0) → j = l)
    (htrans : ∀ (i : ι) (j : κ) (t s : ℝ), t ∈ Set.Ioo (0 : ℝ) 1 → s ∈ Set.Ioo (0 : ℝ) 1 →
      A i t = B j s → det2 (deriv (A i) t) (deriv (B j) s) ≠ 0) :
    Odd (cutBaseBox (diskPlane Q) V W).ncard ↔
      (Odd (chainMeetsLine A).ncard ∧ Odd (chainMeetsLine B).ncard) :=
  odd_ncard_cutBaseBox_iff_arcParity_of_strict Q V W A B hVcut hWcut hchordA hchordB hAinj hBinj
    hAdisj hBdisj
    (fun i j t s ht hs h => ⟨(hint i j t s ht hs h).1, (hint i j t s ht hs h).2,
      hArcA i t (hint i j t s ht hs h).1⟩)
    hendsA hendsB htrans

/-- **`(SURF)` in the cut's own vocabulary, with the strict base case.**  This is
`Work.Drive.surf_arcCycle` (`cutDictionary.lean`) with the pair counts `hcross` discharged from the
*strict* hypotheses — the `ChordPair`-free form of `Work.Drive.surf_arcCycle_chords`, and the statement
the multiplicativity of the transport consumes once the cuts are known to be chord systems. -/
theorem surf_arcCycle_strict {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : ι → ℝ → EuclideanSpace ℝ (Fin 2)) (B : κ → ℝ → EuclideanSpace ℝ (Fin 2))
    (hchordA : ∀ i, IsChord (A i)) (hchordB : ∀ j, IsChord (B j))
    (hAinj : ∀ i, Set.InjOn (A i) (Set.Icc (0 : ℝ) 1))
    (hBinj : ∀ j, Set.InjOn (B j) (Set.Icc (0 : ℝ) 1))
    (hAdisj : ∀ i i' : ι, i ≠ i' →
      Disjoint (A i '' Set.Icc (0 : ℝ) 1) (A i' '' Set.Icc (0 : ℝ) 1))
    (hBdisj : ∀ j j' : κ, j ≠ j' →
      Disjoint (B j '' Set.Icc (0 : ℝ) 1) (B j' '' Set.Icc (0 : ℝ) 1))
    (hint : ∀ (i : ι) (j : κ) (t s : ℝ), t ∈ Set.Icc (0 : ℝ) 1 → s ∈ Set.Icc (0 : ℝ) 1 →
      A i t = B j s → t ∈ Set.Ioo (0 : ℝ) 1 ∧ s ∈ Set.Ioo (0 : ℝ) 1 ∧ ‖A i t‖ < 1)
    (hendsA : ∀ i k : ι, A i 0 = A k 0 ∨ A i 0 = antipode (A k 0) → i = k)
    (hendsB : ∀ j l : κ, B j 0 = B l 0 ∨ B j 0 = antipode (B l 0) → j = l)
    (htrans : ∀ (i : ι) (j : κ) (t s : ℝ), t ∈ Set.Ioo (0 : ℝ) 1 → s ∈ Set.Ioo (0 : ℝ) 1 →
      A i t = B j s → det2 (deriv (A i) t) (deriv (B j) s) ≠ 0) :
    Odd (arcCycle A ∩ arcCycle B).ncard ↔
      (Odd (chainMeetsLine A).ncard ∧ Odd (chainMeetsLine B).ncard) :=
  surf_arcCycle A B hAinj hBinj hAdisj hBdisj
    (fun i j t s ht hs h => ⟨(hint i j t s ht hs h).1, (hint i j t s ht hs h).2.1⟩)
    hendsA hendsB (odd_ncard_chordMeet_of_strict A B hchordA hchordB hint htrans)

/-- **The strict transport in the `ZMod 2` form.**  `Work.Drive.parityCore_of_oddThreeCount`'s
multiplicativity clause needs the cast identity
`((n : ℕ) : ZMod 2) = e · e'`; this is `Work.Drive.cast_eq_mul_of_iff_odd` applied to the strict
transport. -/
theorem cast_ncard_cutBaseBox_eq_mul_of_strict {ι κ : Type*} [Fintype ι] [Fintype κ]
    (Q : ℂ → CappingSpace)
    (V W : EuclideanSpace ℝ (Fin 3) → CappingSpace)
    (A : ι → ℝ → EuclideanSpace ℝ (Fin 2)) (B : κ → ℝ → EuclideanSpace ℝ (Fin 2))
    (hVcut : diskCut Q V = arcCycle A) (hWcut : diskCut Q W = arcCycle B)
    (hchordA : ∀ i, IsChord (A i)) (hchordB : ∀ j, IsChord (B j))
    (hAinj : ∀ i, Set.InjOn (A i) (Set.Icc (0 : ℝ) 1))
    (hBinj : ∀ j, Set.InjOn (B j) (Set.Icc (0 : ℝ) 1))
    (hAdisj : ∀ i i' : ι, i ≠ i' →
      Disjoint (A i '' Set.Icc (0 : ℝ) 1) (A i' '' Set.Icc (0 : ℝ) 1))
    (hBdisj : ∀ j j' : κ, j ≠ j' →
      Disjoint (B j '' Set.Icc (0 : ℝ) 1) (B j' '' Set.Icc (0 : ℝ) 1))
    (hint : ∀ (i : ι) (j : κ) (t s : ℝ), t ∈ Set.Icc (0 : ℝ) 1 → s ∈ Set.Icc (0 : ℝ) 1 →
      A i t = B j s → t ∈ Set.Ioo (0 : ℝ) 1 ∧ s ∈ Set.Ioo (0 : ℝ) 1 ∧ ‖A i t‖ < 1)
    (hendsA : ∀ i k : ι, A i 0 = A k 0 ∨ A i 0 = antipode (A k 0) → i = k)
    (hendsB : ∀ j l : κ, B j 0 = B l 0 ∨ B j 0 = antipode (B l 0) → j = l)
    (htrans : ∀ (i : ι) (j : κ) (t s : ℝ), t ∈ Set.Ioo (0 : ℝ) 1 → s ∈ Set.Ioo (0 : ℝ) 1 →
      A i t = B j s → det2 (deriv (A i) t) (deriv (B j) s) ≠ 0) :
    ((cutBaseBox (diskPlane Q) V W).ncard : ZMod 2)
      = ((chainMeetsLine A).ncard : ZMod 2) * ((chainMeetsLine B).ncard : ZMod 2) :=
  cast_eq_mul_of_iff_odd _ _ _
    (odd_ncard_cutBaseBox_iff_arcParity_of_strict Q V W A B hVcut hWcut hchordA hchordB
      hAinj hBinj hAdisj hBdisj hint hendsA hendsB htrans)

/-- **The strict transport in the engine's own count, in the `ZMod 2` form.** -/
theorem zmod2_ncard_topBdryMeet_zero_eq_mul_of_odd_fibres_strict
    (Q : ℂ → CappingSpace) (P : Fin 3 → EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (hQ : P 0 = diskPlane Q)
    (c : Fin 3 → ℝ) (ψ : ℝ → ℝ) (hψ : ψ 1 = 0)
    (hfinV : (cutRelBox (P 0) (clampedSweep (c 1) ψ (P 1))).Finite)
    (hfinW : (cutRelBox (P 0) (clampedSweep (c 2) ψ (P 2))).Finite)
    (hfibV : ∀ u ∈ cutBaseBox (P 0) (clampedSweep (c 1) ψ (P 1)) (clampedSweep (c 2) ψ (P 2)),
      Odd (cutFibreBox (P 0) (clampedSweep (c 1) ψ (P 1)) u).ncard)
    (hfibW : ∀ u ∈ cutBaseBox (P 0) (clampedSweep (c 1) ψ (P 1)) (clampedSweep (c 2) ψ (P 2)),
      Odd (cutFibreBox (P 0) (clampedSweep (c 2) ψ (P 2)) u).ncard)
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : ι → ℝ → EuclideanSpace ℝ (Fin 2)) (B : κ → ℝ → EuclideanSpace ℝ (Fin 2))
    (hVcut : diskCut Q (clampedSweep (c 1) ψ (P 1)) = arcCycle A)
    (hWcut : diskCut Q (clampedSweep (c 2) ψ (P 2)) = arcCycle B)
    (hchordA : ∀ i, IsChord (A i)) (hchordB : ∀ j, IsChord (B j))
    (hAinj : ∀ i, Set.InjOn (A i) (Set.Icc (0 : ℝ) 1))
    (hBinj : ∀ j, Set.InjOn (B j) (Set.Icc (0 : ℝ) 1))
    (hAdisj : ∀ i i' : ι, i ≠ i' →
      Disjoint (A i '' Set.Icc (0 : ℝ) 1) (A i' '' Set.Icc (0 : ℝ) 1))
    (hBdisj : ∀ j j' : κ, j ≠ j' →
      Disjoint (B j '' Set.Icc (0 : ℝ) 1) (B j' '' Set.Icc (0 : ℝ) 1))
    (hint : ∀ (i : ι) (j : κ) (t s : ℝ), t ∈ Set.Icc (0 : ℝ) 1 → s ∈ Set.Icc (0 : ℝ) 1 →
      A i t = B j s → t ∈ Set.Ioo (0 : ℝ) 1 ∧ s ∈ Set.Ioo (0 : ℝ) 1 ∧ ‖A i t‖ < 1)
    (hendsA : ∀ i k : ι, A i 0 = A k 0 ∨ A i 0 = antipode (A k 0) → i = k)
    (hendsB : ∀ j l : κ, B j 0 = B l 0 ∨ B j 0 = antipode (B l 0) → j = l)
    (htrans : ∀ (i : ι) (j : κ) (t s : ℝ), t ∈ Set.Ioo (0 : ℝ) 1 → s ∈ Set.Ioo (0 : ℝ) 1 →
      A i t = B j s → det2 (deriv (A i) t) (deriv (B j) s) ≠ 0) :
    ((topBdryMeet CappingSpace (fun k => clampedSweep (c k) ψ (P k)) 0).ncard : ZMod 2)
      = ((chainMeetsLine A).ncard : ZMod 2) * ((chainMeetsLine B).ncard : ZMod 2) :=
  cast_eq_mul_of_iff_odd _ _ _
    (Capping.odd_ncard_topBdryMeet_zero_iff_arcParity_of_odd_fibres_strict Q P hQ c ψ hψ hfinV
      hfinW hfibV hfibW A B hVcut hWcut hchordA hchordB hAinj hBinj hAdisj hBdisj hint hendsA
      hendsB htrans)

end

end Work.Drive
