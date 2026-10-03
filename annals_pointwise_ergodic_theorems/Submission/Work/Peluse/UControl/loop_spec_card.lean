import Mathlib
import Submission.Work.Peluse.UControl.levRoundBase

/-!
# `loop_spec` with the count of the round's steps

`loop_spec` (`levRoundBase.lean`) runs the round of Peluse's Lemma 4.8 to a state with a single
alive class `{A}`.  For the *terminal identification* of the level chain we also need to know that
the round performs enough steps: the round's new parameter set has `S'.r + 1` elements, and the
terminal datum needs at least two of them.  This file adds the counting invariant

`S.r + S.K.card ≤ S'.r + S'.K.card`

(every step increments `r` by one; a class reduction additionally removes one element of `K`).

Consequence: starting from `K = {ω ⊆ A | ω.Nonempty}` and `r = 0`, the round ends with
`S'.r ≥ 2 ^ A.card - 2`, so `N = S'.r + 1 ≥ 2 ^ A.card - 1 ≥ 3` as soon as `A.card ≥ 2`.
-/

set_option autoImplicit false
open scoped BigOperators

namespace Work.Peluse.UControl

noncomputable section

open Polynomial

attribute [local instance] Classical.propDecidable

variable {d D L : ℕ}

/-- **The round process, with the step count.**  Same as `loop_spec`, plus
`S.r + S.K.card ≤ S'.r + S'.K.card`. -/
theorem loop_spec_card {A : Finset (Fin L)} {f₀ : Fin L → Bool}
    {atoms : {s // s ∈ A} → MvPolynomial (Fin L) ℤ} (hind : LevIndep L A atoms)
    (hkill : ∀ {r : ℕ} {K : Finset (Finset (Fin L))} {σ : Fin (r + 1) → Finset (Fin L)}
      {X : HistData d (L + r)} (hinv : LevInv d D A f₀ atoms r K σ X)
      (halldeg : ∀ x ∈ X.H, (X.Q x.1 x.2).natDegree = D)
      {ω₀ : Finset (Fin L)} (hω : ω₀ ∈ K) (hωA : ω₀ ≠ A),
      LevInv d D A f₀ atoms (r + 1) (K.erase ω₀) (Fin.snoc σ ω₀)
        (X.step (Sum.inr 0) (slotHist (histOf A f₀ ω₀) r 0)
          ((hinv.top_mem ω₀ hω (0 : Fin r → Bool)).1)))
    (S : RState d D L A f₀ atoms) :
    ∃ S' : RState d D L A f₀ atoms, Reach S.X S'.X ∧
      (∀ x ∈ S'.X.H, (S'.X.Q x.1 x.2).natDegree = D) ∧ S'.K = {A} ∧
      S.r + S.K.card ≤ S'.r + S'.K.card := by
  induction S using WellFounded.induction (RState.rel_wf (d := d) (D := D) (L := L) (A := A)
    (f₀ := f₀) (atoms := atoms)) with
  | h S ih =>
    by_cases hlt : (S.X.Q (S.X.sel S.hne).1 (S.X.sel S.hne).2).natDegree < D
    · -- hydra step
      obtain ⟨S', hreach, hdeg, hK, hcard⟩ := ih (RState.hydraStep S hlt) (hydraStep_rel S hlt)
      refine ⟨S', Reach.step S.X (S.X.sel S.hne).1 (S.X.sel S.hne).2 (S.X.sel_mem_H S.hne) hreach,
        hdeg, hK, ?_⟩
      have h1 : S.r + S.K.card ≤ (RState.hydraStep S hlt).r + (RState.hydraStep S hlt).K.card := by
        show S.r + S.K.card ≤ S.r + 1 + S.K.card
        omega
      exact le_trans h1 hcard
    · by_cases hKA : S.K = {A}
      · -- closing-ready state
        have hmin : S.X.minDeg S.hne = D := by
          refine le_antisymm ?_ ?_
          · calc S.X.minDeg S.hne
                ≤ (S.X.Q (Sum.inr 0) (slotHist (histOf A f₀ A) S.r 0)).natDegree :=
                  S.X.minDeg_le S.hne _ ((S.inv.top_mem A S.inv.memA (0 : Fin S.r → Bool)).1)
              _ = D := (S.inv.top_mem A S.inv.memA (0 : Fin S.r → Bool)).2.1
          · calc S.X.minDeg S.hne
                = (S.X.Q (S.X.sel S.hne).1 (S.X.sel S.hne).2).natDegree := (S.X.sel_degree S.hne).symm
              _ ≥ D := not_lt.mp hlt
        have halldeg : ∀ x ∈ S.X.H, (S.X.Q x.1 x.2).natDegree = D := by
          intro x hx
          refine le_antisymm (S.inv.degLe x hx) ?_
          calc D = S.X.minDeg S.hne := hmin.symm
            _ ≤ (S.X.Q x.1 x.2).natDegree := S.X.minDeg_le S.hne x hx
        exact ⟨S, Reach.refl S.X, halldeg, hKA, le_rfl⟩
      · -- class reduction
        obtain ⟨ω₀, hω, hωA⟩ : ∃ ω₀ ∈ S.K, ω₀ ≠ A := by
          by_contra hcon
          push_neg at hcon
          apply hKA
          refine Finset.Subset.antisymm ?_ ?_
          · intro ω hω
            simp only [Finset.mem_singleton]
            exact hcon ω hω
          · intro ω hω
            rw [Finset.mem_singleton] at hω
            rw [hω]
            exact S.inv.memA
        have hmin : S.X.minDeg S.hne = D := by
          refine le_antisymm ?_ ?_
          · calc S.X.minDeg S.hne
                ≤ (S.X.Q (Sum.inr 0) (slotHist (histOf A f₀ A) S.r 0)).natDegree :=
                  S.X.minDeg_le S.hne _ ((S.inv.top_mem A S.inv.memA (0 : Fin S.r → Bool)).1)
              _ = D := (S.inv.top_mem A S.inv.memA (0 : Fin S.r → Bool)).2.1
          · calc S.X.minDeg S.hne
                = (S.X.Q (S.X.sel S.hne).1 (S.X.sel S.hne).2).natDegree := (S.X.sel_degree S.hne).symm
              _ ≥ D := not_lt.mp hlt
        have halldeg : ∀ x ∈ S.X.H, (S.X.Q x.1 x.2).natDegree = D := by
          intro x hx
          refine le_antisymm (S.inv.degLe x hx) ?_
          calc D = S.X.minDeg S.hne := hmin.symm
            _ ≤ (S.X.Q x.1 x.2).natDegree := S.X.minDeg_le S.hne x hx
        have hkilldeg : (S.X.Q (Sum.inr 0) (slotHist (histOf A f₀ ω₀) S.r 0)).natDegree
            = S.X.minDeg S.hne := by
          rw [hmin]
          exact (S.inv.top_mem ω₀ hω (0 : Fin S.r → Bool)).2.1
        obtain ⟨S', hreach, hdeg, hK, hcard⟩ := ih
          (RState.killStep S ω₀ hω hωA (hkill S.inv halldeg hω hωA))
          (killStep_rel S ω₀ hω hωA (hkill S.inv halldeg hω hωA) hkilldeg)
        refine ⟨S', Reach.step S.X (Sum.inr 0) (slotHist (histOf A f₀ ω₀) S.r 0)
          ((S.inv.top_mem ω₀ hω (0 : Fin S.r → Bool)).1) hreach, hdeg, hK, ?_⟩
        have h1 : S.r + S.K.card
            ≤ (RState.killStep S ω₀ hω hωA (hkill S.inv halldeg hω hωA)).r
              + (RState.killStep S ω₀ hω hωA (hkill S.inv halldeg hω hωA)).K.card := by
          show S.r + S.K.card ≤ S.r + 1 + (S.K.erase ω₀).card
          rw [Finset.card_erase_of_mem hω]
          have : 1 ≤ S.K.card := Finset.card_pos.mpr ⟨ω₀, hω⟩
          omega
        exact le_trans h1 hcard

end

end Work.Peluse.UControl
