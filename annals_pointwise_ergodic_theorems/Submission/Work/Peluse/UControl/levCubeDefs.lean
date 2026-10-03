import Mathlib
import Submission.Work.Peluse.UControl.HistInv

/-!
# The level state of Peluse's Lemma 4.8 (the `d ≥ 3` part of `PetLevelChain`)

The remaining obligation of `Work.Peluse.UControl.petChapter5Holds` is `PetLevelChain P` for
`P.natDegree ≥ 3`.  Its mathematical content is Peluse's Lemma 4.8 iterated `d - 2` times, and the
engine of one application is the **round** defined here: a PET chain that takes a state whose slots
are the nonempty subsets of a parameter set `S` (all of degree `D`, with leading coefficients
additive over the subsets) to a state of the same shape with `D - 1` and a new parameter set `S'`.

`LevCube` is the exact description of such a state, stated on `HistData d L` (whose slot index is
`InitIdx d × (Fin L → Bool)`; during the level chain every slot is `P`-tagged, i.e.
`(Sum.inr 0, h)`):

* `A : Finset (Fin L)` is the set of the *current* parameters (the others are frozen);
* `f₀ : Fin L → Bool` is the frozen value (the live slots are the Boolean functions agreeing with
  `f₀` off `A`, *except* `f₀` itself — this is the `Bool^{S} ∖ {0}` of the nested family);
* `atoms : {s // s ∈ A} → MvPolynomial (Fin L) ℤ` are the atoms; the leading coefficient of the slot
  `h` is `Σ_{s ∈ A, h s} atoms_s` (the paper's `dir_j`).

`Reach` is the transitive closure of one PET step.  `LevRound` is the round of Lemma 4.8: the
statement that a *fixed, combinatorial* schedule carries every `LevCube`-state of degree `D` to a
`LevCube`-state of degree `D - 1` with a new parameter set.

## Why the round can be stated with the output data *before* the input state

The schedule of the round (which slot is stepped at, at each stage) is determined by the
*combinatorial* class structure (`s ↦ Σ_{s ∈ A, h s} atoms_s`), not by the lower coefficients of
the state's polynomials; and the new atoms produced by the closing step
(`D · (Σ_{s' ∈ par s} atoms_{s'}) · X_s`) are determined by `atoms`.  So `N`, `A'`, `f₀'` and
`atoms'` may be produced before the universally quantified input state `X`.

## What the round is *not* responsible for

The analytic transfer (`lam` and `ShiftBound` along the chain) is mechanical once `Reach` is known:
it is the iteration of `hstLamGen` + `PetState.lam_step` (correlation: `petChainLevel γ 1`) and
`hstSBGen` + `PetState.ShiftBound.step` (shift bound: `c - 1`, `2 * D`), all of which are already on
disk (`histStepTransfer.lean`, `PetStepChain.lean`, `PetStepLink`-style lemmas).

See `NOTES_petChapter5_session18.md` for the schedule, the counts, and the simulation evidence.
-/

set_option autoImplicit false
open scoped BigOperators

namespace Work.Peluse.UControl

noncomputable section

open Polynomial

attribute [local instance] Classical.propDecidable

variable {d : ℕ}

/-! ## The cube of histories and the live set -/

/-- The Boolean functions on `Fin L` agreeing with `f₀` outside `A`: a sub-cube of dimension `|A|`. -/
def cubeSet (L : ℕ) (A : Finset (Fin L)) (f₀ : Fin L → Bool) : Finset (Fin L → Bool) :=
  Finset.univ.filter (fun h => ∀ i, i ∉ A → h i = f₀ i)

/-- The live slots of a level state: the sub-cube with the frozen point `f₀` (the "zero" of the
nested family, i.e. the empty history) removed, all `P`-tagged. -/
def LevH (d L : ℕ) (A : Finset (Fin L)) (f₀ : Fin L → Bool) :
    Finset (InitIdx d × (Fin L → Bool)) :=
  ((cubeSet L A f₀).erase f₀).image (fun h => ((Sum.inr 0 : InitIdx d), h))

/-- The atom sum of a history: `Σ_{s ∈ A, h s} atoms_s`. -/
def atomSum {L : ℕ} (A : Finset (Fin L)) (atoms : {s // s ∈ A} → MvPolynomial (Fin L) ℤ)
    (h : Fin L → Bool) : MvPolynomial (Fin L) ℤ :=
  ∑ s : {s // s ∈ A}, if h s.1 then atoms s else 0

/-- **The level-state invariant.**  `X` is a state of the PET chain whose slots are exactly the
nonempty subsets of the current parameter set `A`, all of degree `D`, with leading coefficients
additive over those subsets with atoms `atoms`. -/
def LevCube (d D L : ℕ) (A : Finset (Fin L)) (f₀ : Fin L → Bool)
    (atoms : {s // s ∈ A} → MvPolynomial (Fin L) ℤ) (X : HistData d L) : Prop :=
  X.H = LevH d L A f₀ ∧
  (∀ h : Fin L → Bool, h ∈ cubeSet L A f₀ → h ≠ f₀ →
      (X.Q (Sum.inr 0 : InitIdx d) h).natDegree = D ∧
      (X.Q (Sum.inr 0 : InitIdx d) h).leadingCoeff = atomSum A atoms h)

/-- The live slots of `LevCube` are exactly the `P`-tagged histories of the punctured sub-cube. -/
lemma mem_LevH {L : ℕ} {A : Finset (Fin L)} {f₀ : Fin L → Bool}
    {x : InitIdx d × (Fin L → Bool)} :
    x ∈ LevH d L A f₀ ↔ x.1 = (Sum.inr 0 : InitIdx d) ∧ x.2 ∈ cubeSet L A f₀ ∧ x.2 ≠ f₀ := by
  constructor
  · intro hx
    rw [LevH, Finset.mem_image] at hx
    obtain ⟨h, hh, rfl⟩ := hx
    rw [Finset.mem_erase] at hh
    exact ⟨rfl, hh.2, hh.1⟩
  · rintro ⟨h1, h2, h3⟩
    rw [LevH, Finset.mem_image]
    refine ⟨x.2, ?_, ?_⟩
    · rw [Finset.mem_erase]; exact ⟨h3, h2⟩
    · exact Prod.ext h1.symm rfl

/-! ## The reachability relation -/

/-- `Reach X Z`: `Z` is obtained from `X` by a finite chain of PET steps (each step at a chosen live
slot). -/
inductive Reach {d : ℕ} : ∀ {L L' : ℕ}, HistData d L → HistData d L' → Prop
  | refl {L : ℕ} (X : HistData d L) : Reach X X
  | step {L : ℕ} (X : HistData d L) (i₀ : InitIdx d) (h₀ : Fin L → Bool)
      (hh : (i₀, h₀) ∈ X.H) {L' : ℕ} {Z : HistData d L'} (h : Reach (X.step i₀ h₀ hh) Z) :
      Reach X Z

/-! ## The round -/

/-- **The independence of the atoms**: distinct Boolean histories have distinct atom sums (the
paper's "the leading coefficients are all distinct"; satisfied by the real atoms
`C (d*lc) * X_s`, which are algebraically independent). -/
def LevIndep (L : ℕ) (A : Finset (Fin L)) (atoms : {s // s ∈ A} → MvPolynomial (Fin L) ℤ) : Prop :=
  ∀ h h' : Fin L → Bool, h ∈ cubeSet L A 0 → h' ∈ cubeSet L A 0 →
    atomSum A atoms h = atomSum A atoms h' → h = h'

/-- **The round of Peluse's Lemma 4.8.**  Assume the atoms independent (`LevIndep`); then from a
level state of degree `D ≥ 2` with current parameter set `A` and atoms `atoms` one reaches, by PET
steps, a level state of degree `D - 1` with a *new* parameter set `A'` (of size the number of steps),
a frozen vector `f₀'`, new atoms `atoms'` and an attachment `P` (the datum's `par`) such that

* each new atom factors as `atoms'_s = D · (Σ_{s' ∈ P s} atoms_{s'}) · X_s` — the recursion
  `dir_{j+1}(w) = (d-j)·Σ_{s∈w} dir_j(par s)·a_{j+1}(s)` of the nested family, with `d - j = D`;
* every `LevCube`-state `X` of degree `D` is carried by the steps to some state `X'` of degree
  `D - 1` with new parameter set `A'` and atoms `atoms'`.

The number of steps, and the output data, may depend on the input state `X` (the length of the
hydra kill depends on the input's lower coefficients), which is why the existential is *inside* the
universal quantifier — the target `PetLevelChain` produces its data after the terminal state `Y`, so
this is exactly the freedom available.

See `NOTES_petChapter5_session18.md` §1 for the schedule (class reduction at the reference class,
then the hydra kill at the least-degree slot, then the closing step) and the simulation evidence. -/
def LevRound (d D L : ℕ) (A : Finset (Fin L)) (f₀ : Fin L → Bool)
    (atoms : {s // s ∈ A} → MvPolynomial (Fin L) ℤ) : Prop :=
  LevIndep L A atoms → 2 ≤ D →
    ∀ X : HistData d L, LevCube d D L A f₀ atoms X →
      ∃ (N : ℕ) (A' : Finset (Fin (L + N))) (f₀' : Fin (L + N) → Bool)
        (P : {s // s ∈ A'} → Finset {s' // s' ∈ A})
        (atoms' : {s // s ∈ A'} → MvPolynomial (Fin (L + N)) ℤ)
        (X' : HistData d (L + N)),
        (∀ s, (P s).Nonempty) ∧
        (∀ s, atoms' s = MvPolynomial.C (D : ℤ) *
          ((∑ s' ∈ P s, MvPolynomial.rename (Fin.castLE (Nat.le_add_right L N)) (atoms s')) *
            MvPolynomial.X s.1)) ∧
        (∀ s : {s // s ∈ A'}, L ≤ s.1) ∧
        LevIndep (L + N) A' atoms' ∧
        LevCube d (D - 1) (L + N) A' f₀' atoms' X' ∧ Reach X X'

/-- **The round with the new parameter set pinned to the set of *new* coordinates** (totality).
This is `LevRound` with the freshness conjunct `∀ s ∈ A', L ≤ s.1` replaced by the equality
`A' = {i | L ≤ i.1}`, which subsumes freshness and gives `A'.card = N`.  It is the form the
*iteration* needs: with freshness alone, `A' = ∅` is admissible and `LevH d M ∅ f₀' = ∅` makes the
level-1 state degenerate (see `NOTES_petChapter5_session18.md` Appendices 11--12), which hands the
terminal comparison nothing.  `LevRound` itself is left untouched, so `levRoundHoldsV2` stays valid;
this stronger predicate is a separate target. -/
def LevRoundT (d D L : ℕ) (A : Finset (Fin L)) (f₀ : Fin L → Bool)
    (atoms : {s // s ∈ A} → MvPolynomial (Fin L) ℤ) : Prop :=
  LevIndep L A atoms → 2 ≤ D →
    ∀ X : HistData d L, LevCube d D L A f₀ atoms X →
      ∃ (N : ℕ) (A' : Finset (Fin (L + N))) (f₀' : Fin (L + N) → Bool)
        (P : {s // s ∈ A'} → Finset {s' // s' ∈ A})
        (atoms' : {s // s ∈ A'} → MvPolynomial (Fin (L + N)) ℤ)
        (X' : HistData d (L + N)),
        A' = Finset.univ.filter (fun i : Fin (L + N) => L ≤ i.1) ∧
        (∀ s, (P s).Nonempty) ∧
        (∀ s, atoms' s = MvPolynomial.C (D : ℤ) *
          ((∑ s' ∈ P s, MvPolynomial.rename (Fin.castLE (Nat.le_add_right L N)) (atoms s')) *
            MvPolynomial.X s.1)) ∧
        LevIndep (L + N) A' atoms' ∧
        LevCube d (D - 1) (L + N) A' f₀' atoms' X' ∧ Reach X X'

/-- `LevRoundT` implies `LevRound` (totality subsumes freshness). -/
theorem LevRound_of_LevRoundT {d D L : ℕ} {A : Finset (Fin L)} {f₀ : Fin L → Bool}
    {atoms : {s // s ∈ A} → MvPolynomial (Fin L) ℤ}
    (h : LevRoundT d D L A f₀ atoms) : LevRound d D L A f₀ atoms := by
  intro hind hD X hX
  obtain ⟨N, A', f₀', P, atoms', X', htot, hP, hat, hind', hcube, hreach⟩ := h hind hD X hX
  exact ⟨N, A', f₀', P, atoms', X', hP, hat,
    (fun s => by
      have hmem : s.1 ∈ Finset.univ.filter (fun i : Fin (L + N) => L ≤ i.1) := by
        rw [← htot]; exact s.2
      exact (Finset.mem_filter.mp hmem).2), hind', hcube, hreach⟩

/-- **The round of Lemma 4.8 in the form the *terminal identification* needs** (`LevRoundT` plus two
extra conjuncts).

* `∀ s ∈ A', f₀' s = false`: the frozen vector of the *output* is false on the new coordinates, so
  the live slots of the output are in bijection with the *nonempty* subsets of `A'` (the index set
  `I (d-1)` of the PET datum) via `h ↦ {s | h s = true}`.  This is what the terminal comparison
  (`linFamAvg`) needs; the round's own proof witnesses it by
  `f₀' = slotHist (histOf A f₀ A) N 0` (`slotHist_natAdd`).
* `2 ≤ A.card → 2 ≤ A'.card`: the new parameter set is non-degenerate whenever the old one is.  This
  is what makes `2 ≤ Fintype.card (D.I (d-1))` reachable at the end of the chain: the last round has
  a non-degenerate input, so it adds at least two coordinates.  The round's proof witnesses it by the
  class count: `S'.K` starts as the `2^{|A|} - 1` nonempty subsets of `A`, each class reduction
  removes one element of `K` while incrementing `r`, and the loop ends with `K = {A}`, so
  `N = S'.r + 1 ≥ 2^{|A|} ≥ 4` for `|A| ≥ 2`. -/
def LevRoundU (d D L : ℕ) (A : Finset (Fin L)) (f₀ : Fin L → Bool)
    (atoms : {s // s ∈ A} → MvPolynomial (Fin L) ℤ) : Prop :=
  LevIndep L A atoms → 2 ≤ D →
    ∀ X : HistData d L, LevCube d D L A f₀ atoms X →
      ∃ (N : ℕ) (A' : Finset (Fin (L + N))) (f₀' : Fin (L + N) → Bool)
        (P : {s // s ∈ A'} → Finset {s' // s' ∈ A})
        (atoms' : {s // s ∈ A'} → MvPolynomial (Fin (L + N)) ℤ)
        (X' : HistData d (L + N)),
        A' = Finset.univ.filter (fun i : Fin (L + N) => L ≤ i.1) ∧
        (∀ s ∈ A', f₀' s = false) ∧
        (2 ≤ A.card → 2 ≤ A'.card) ∧
        (∀ s, (P s).Nonempty) ∧
        (∀ s, atoms' s = MvPolynomial.C (D : ℤ) *
          ((∑ s' ∈ P s, MvPolynomial.rename (Fin.castLE (Nat.le_add_right L N)) (atoms s')) *
            MvPolynomial.X s.1)) ∧
        LevIndep (L + N) A' atoms' ∧
        LevCube d (D - 1) (L + N) A' f₀' atoms' X' ∧ Reach X X'

/-- `LevRoundU` gives `LevRoundT` (forgetting the two extra conjuncts). -/
theorem LevRoundT_of_LevRoundU {d D L : ℕ} {A : Finset (Fin L)} {f₀ : Fin L → Bool}
    {atoms : {s // s ∈ A} → MvPolynomial (Fin L) ℤ}
    (h : LevRoundU d D L A f₀ atoms) : LevRoundT d D L A f₀ atoms := by
  intro hind hD X hX
  obtain ⟨N, A', f₀', P, atoms', X', htot, -, -, hP, hat, hind', hcube, hreach⟩ := h hind hD X hX
  exact ⟨N, A', f₀', P, atoms', X', htot, hP, hat, hind', hcube, hreach⟩

end

end Work.Peluse.UControl
