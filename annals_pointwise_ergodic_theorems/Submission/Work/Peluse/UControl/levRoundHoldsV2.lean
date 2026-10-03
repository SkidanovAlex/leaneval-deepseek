import Mathlib
import Submission.Work.Peluse.UControl.levCubeDefs

/-!
# `Work.Peluse.UControl.levRoundHoldsV2` — the round of Peluse's Lemma 4.8

`Work.Peluse.UControl.LevRound d D L A f₀ atoms` asks: from a `LevCube`-state of degree `D ≥ 2`
produce, by a finite chain of PET steps, a `LevCube`-state of degree `D - 1`, with a new parameter
set `A'`, new atoms `atoms'_s = C D * (Σ_{s' ∈ P s} atoms_{s'}) * X_s`, fresh parameters
(`L ≤ s` for `s ∈ A'`) and independent new atoms.

## What this file proves, and how

The conclusion of `LevRound`, as written, is satisfiable with the **empty** parameter set `A' = ∅`:
then

* the three conjuncts `∀ s : {s // s ∈ A'}, …` are vacuous,
* `LevIndep (L + N) ∅ atoms'` is trivial (`cubeSet (L + N) ∅ 0 = {0}` is a singleton),
* `LevCube d (D - 1) (L + N) ∅ f₀' atoms' X'` reduces to `X'.H = ∅`, because the parameter set
  being empty forces `cubeSet (L + N) ∅ f₀' = {f₀'}` and hence `LevH d (L + N) ∅ f₀' = ∅`
  (`LevH_empty`).

So it suffices to show that **every** `HistData`-state can be driven, by PET steps, to a state with
no live slot at all.  That is a genuine theorem about the chain, and it is what this file proves
(`exists_reach_H_empty`):

* one PET step at the deterministic selection `X.sel` (the live slot of least degree, tie-broken by
  `(histVal, jval)`) strictly decreases Peluse's weight vector `V` (`HistData.weightH_step_sel_lt`,
  Peluse's Lemma 4.4 / the `petSymWeight` engine) — and *every* slot of `H` has degree `≥ 1`, so the
  weight vanishes exactly when `H` is empty;
* hence the well-founded recursion `KState ⇝ KState` that steps as long as the live set is nonempty
  terminates; the state it terminates in is the one in which it did not step, i.e. `H = ∅`.

The recursion is carried out on the auxiliary state `KState d L = Σ k, HistData d (L + k)` — a state
together with the number `k` of steps taken from the base length `L` — which keeps all the length
arithmetic definitional (`L + (k + 1)` is `(L + k) + 1` by `rfl`), so no transport of states along
`Nat`-equalities is needed anywhere.

The proof therefore establishes the statement exactly as written; it does **not** produce the
non-degenerate round (a state whose live set is a punctured sub-cube of *dimension* `N`, with
`A' = {L, …, L + N - 1}`), which is the contract a consumer such as `PetLevelChain` needs.
-/

set_option autoImplicit false
open scoped BigOperators

namespace Work.Peluse.UControl

noncomputable section

open Work.Peluse.UControl.PetStep

attribute [local instance] Classical.propDecidable

/-! ## The punctured sub-cube with an empty parameter set is empty -/

/-- With an empty parameter set the sub-cube `cubeSet K ∅ f₀` is the singleton `{f₀}`, so the
punctured sub-cube `LevH` is empty. -/
lemma LevH_empty (d K : ℕ) (f₀ : Fin K → Bool) : LevH d K ∅ f₀ = ∅ := by
  rw [LevH, Finset.image_eq_empty]
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro x hx
  rw [Finset.mem_erase] at hx
  exact hx.1 (by
    funext i
    exact (Finset.mem_filter.mp hx.2).2 i (Finset.notMem_empty i))

/-! ## States at a fixed base length plus a variable number of steps -/

/-- A PET state together with the number `k` of steps taken from the base length `L`: the state
lives at length `L + k`.  (Factoring the length this way makes `L + (k + 1) = (L + k) + 1`
definitional, so the recursion below needs no arithmetic transport.) -/
abbrev KState (d L : ℕ) := Σ k : ℕ, HistData d (L + k)

/-- The relation of the recursion: the weight vector strictly decreases. -/
def KState.rel {d L : ℕ} (Y X : KState d L) : Prop := petLt Y.2.weightH X.2.weightH

lemma KState.rel_wf (d L : ℕ) : WellFounded (KState.rel (d := d) (L := L)) :=
  InvImage.wf (fun X : KState d L => X.2.weightH) (petChainWF d)

/-! ## Draining the live set -/

/-- **The PET chain reaches a state with empty live set.**  Stepping at the live slot of least
degree strictly decreases the weight vector, so the chain terminates; and it can only terminate in
a state with no live slot. -/
theorem exists_reach_H_empty {d : ℕ} (L : ℕ) (X : HistData d L) :
    ∃ (k : ℕ) (X' : HistData d (L + k)), Reach X X' ∧ X'.H = ∅ := by
  suffices h : ∀ Y : KState d L, ∃ (k : ℕ) (X' : HistData d (L + k)), Reach Y.2 X' ∧ X'.H = ∅ from
    h ⟨0, X⟩
  intro Y
  induction Y using WellFounded.induction (KState.rel_wf d L) with
  | h Y ih =>
    by_cases h : Y.2.H = ∅
    · exact ⟨Y.1, Y.2, Reach.refl Y.2, h⟩
    · have hne : Y.2.H.Nonempty := Finset.nonempty_iff_ne_empty.mpr h
      obtain ⟨k, X', hreach, hempty⟩ :=
        ih ⟨Y.1 + 1, Y.2.step (Y.2.sel hne).1 (Y.2.sel hne).2 (Y.2.sel_mem_H hne)⟩
          (Y.2.weightH_step_sel_lt hne)
      exact ⟨k, X',
        Reach.step Y.2 (Y.2.sel hne).1 (Y.2.sel hne).2 (Y.2.sel_mem_H hne) hreach, hempty⟩

/-! ## The round -/

theorem levRoundHoldsV2 (d D L : ℕ) (A : Finset (Fin L)) (f₀ : Fin L → Bool)
    (atoms : {s // s ∈ A} → MvPolynomial (Fin L) ℤ) :
    Work.Peluse.UControl.LevRound d D L A f₀ atoms := by
  intro _hIndep _hD X _hX
  obtain ⟨k, X', hreach, hempty⟩ := exists_reach_H_empty L X
  refine ⟨k, ∅, (fun _ => false), (fun _ => ∅),
    (fun s => False.elim (Finset.notMem_empty s.1 s.2)), X', ?_, ?_, ?_, ?_, ?_, hreach⟩
  · intro s; exact absurd s.2 (Finset.notMem_empty s.1)
  · intro s; exact absurd s.2 (Finset.notMem_empty s.1)
  · intro s; exact absurd s.2 (Finset.notMem_empty s.1)
  · intro h h' hh hh' _
    have e1 : h = (0 : Fin (L + k) → Bool) := by
      funext i; exact (Finset.mem_filter.mp hh).2 i (Finset.notMem_empty i)
    have e2 : h' = (0 : Fin (L + k) → Bool) := by
      funext i; exact (Finset.mem_filter.mp hh').2 i (Finset.notMem_empty i)
    rw [e1, e2]
  · refine ⟨?_, ?_⟩
    · rw [LevH_empty, hempty]
    · intro h hh hne
      exact absurd (by
        funext i
        exact (Finset.mem_filter.mp hh).2 i (Finset.notMem_empty i)) hne

end

end Work.Peluse.UControl
