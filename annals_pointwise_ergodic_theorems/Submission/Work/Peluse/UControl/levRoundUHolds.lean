import Mathlib
import Submission.Work.Peluse.UControl.levInvInit
import Submission.Work.Peluse.UControl.levInvStepKill
import Submission.Work.Peluse.UControl.loop_spec_card

/-!
# The round of Peluse's Lemma 4.8 in the form the *terminal identification* needs (`LevRoundU`)

This is the proof of `levRoundTHolds` (`LevRoundT`), copied, with the two extra conjuncts of
`LevRoundU`:

* `∀ s ∈ A', f₀' s = false`: the explicit witness `f₀' = slotHist (histOf A f₀ A) N 0` is false on
  the fresh coordinates by `slotHist_natAdd`;
* `2 ≤ A.card → 2 ≤ A'.card`: by `loop_spec_card` the round performs at least
  `2 ^ A.card - 2` steps (the initial class set is the `2 ^ A.card - 1` nonempty subsets of `A`, each
  class reduction removes one, and the loop ends with the single class `{A}`), so
  `A'.card = N = S'.r + 1 ≥ 2 ^ A.card - 1 ≥ 3` for `A.card ≥ 2`.
-/

/-!
# The round of Peluse's Lemma 4.8 in the *totality* form (`LevRoundT`)

`Work.Peluse.UControl.LevRoundT d D L A f₀ atoms` asks: from a `LevCube`-state `X` of degree
`D ≥ 2` on the parameter set `A` with independent atoms, reach by PET steps a `LevCube`-state of
degree `D - 1` whose parameter set is **exactly** the set of the coordinates introduced by the
steps (`A' = {i | L ≤ i}`), i.e. a state whose live slots are the punctured sub-cube of the new
coordinates.

This file is the assembly.  The mathematical content lives in the modules it imports:

* `levRoundDefs.lean` — the class `LevInv` of a round state (the set `K` of alive classes, the
  reference `σ` of the class reductions, the top-degree slots, and the `ε`-recursion of the
  degree-`(D-1)` coefficients of the closing class `A`);
* `levInvInit.lean` — a `LevCube`-state is a round state (`levInvInit`; it also shows that in the
  non-degenerate case `f₀` is `false` on `A`);
* `levInvStepKill.lean` — the class-reduction step (`levInvStepKill`);
* `levRoundBase.lean` — the hydra step, the round process (`loop_spec`: it exhausts the hydras and
  kills every class other than `A`) and the closing step (`levRoundClosing`), together with
  `closingAtomsSpec` (the new atoms are independent, with the `ε`-recursions as atom sums).

The closing class is pinned to `A`, and that is forced: the new atoms have the target's shape
`C D · (Σ_{s' ∈ P s} atoms_{s'}) · X_s` with `P s ⊆ A`, so the reference of every class reduction
must be a subset of `A`; among the classes of a `LevCube`-state only `A` has that property.  (A
`LevCube`-state with `A` punctured out — `f₀ ≡ true` on `A ≠ ∅` — does not exist, since the
history `histOf A f₀ ∅` would then be live with atom sum `0`.)
-/

set_option autoImplicit false
open scoped BigOperators

namespace Work.Peluse.UControl

noncomputable section

open Polynomial

attribute [local instance] Classical.propDecidable

variable {d D L : ℕ}

/-- The fresh coordinates of a round number `r`. -/
lemma card_freshFin (L r : ℕ) : (freshFin L r).card = r := by
  have h : (Finset.univ : Finset (Fin r)).card = (freshFin L r).card := by
    refine Finset.card_bij (fun j _ => Fin.natAdd L j) ?_ ?_ ?_
    · intro j _
      rw [mem_freshFin]
      exact Nat.le_add_right L j.1
    · intro j₁ _ j₂ _ h
      have h2 : (j₁ : ℕ) = (j₂ : ℕ) := by
        have := congrArg Fin.val h
        simp only [Fin.val_natAdd] at this
        omega
      exact Fin.ext h2
    · intro i hi
      refine ⟨freshIdx ⟨i, hi⟩, Finset.mem_univ _, ?_⟩
      exact natAdd_freshIdx ⟨i, hi⟩
  simpa using h.symm

/-- **The round of Peluse's Lemma 4.8, with the new parameter set pinned to the new coordinates and
the frozen vector of the output pinned to `false` on them.** -/
theorem levRoundUHolds (d D L : ℕ) (A : Finset (Fin L)) (f₀ : Fin L → Bool)
    (atoms : {s // s ∈ A} → MvPolynomial (Fin L) ℤ) :
    Work.Peluse.UControl.LevRoundU d D L A f₀ atoms := by
  classical
  intro hind hD X hX
  by_cases hA : A = ∅
  · -- `A = ∅`: the state has no live slot, and so has the output.
    subst hA
    refine ⟨0, (∅ : Finset (Fin (L + 0))), f₀,
      (fun s => False.elim (Finset.notMem_empty s.1 s.2)),
      (fun s => False.elim (Finset.notMem_empty s.1 s.2)), X, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      Reach.refl X⟩
    · -- the new parameter set is the set of the new coordinates
      ext i
      simp only [Finset.notMem_empty, Finset.mem_filter, Finset.mem_univ, true_and]
      exact iff_of_false (by simp) (by have := i.2; omega)
    · -- `f₀` is false on the (empty) new parameter set
      intro s hs
      exact absurd hs (Finset.notMem_empty s)
    · -- the non-degeneracy of the old parameter set is impossible when it is empty
      intro h
      exact absurd h (by simp)
    · intro s
      exact absurd s.2 (Finset.notMem_empty s.1)
    · intro s
      exact absurd s.2 (Finset.notMem_empty s.1)
    · intro h h' hh hh' _
      have e1 : h = (0 : Fin (L + 0) → Bool) := by
        funext i
        exact (Finset.mem_filter.mp hh).2 i (Finset.notMem_empty i)
      have e2 : h' = (0 : Fin (L + 0) → Bool) := by
        funext i
        exact (Finset.mem_filter.mp hh').2 i (Finset.notMem_empty i)
      rw [e1, e2]
    · refine ⟨?_, ?_⟩
      · rw [hX.1, LevH_empty]
        exact (LevH_empty d (L + 0) f₀).symm
      · intro h hh hne
        exact absurd (by
          funext i
          exact (Finset.mem_filter.mp hh).2 i (Finset.notMem_empty i)) hne
  · -- `A ≠ ∅`: run the round.
    have hAne : A.Nonempty := Finset.nonempty_iff_ne_empty.mpr hA
    have hD1 : 1 ≤ D := by omega
    have hD0 : 0 < D := by omega
    -- the input is a round state
    have hinit := levInvInit (d := d) (D := D) (A := A) (f₀ := f₀) (atoms := atoms) hind hD1 hAne hX
    let S : RState d D L A f₀ atoms :=
      ⟨0, X, Finset.univ.filter (fun ω : Finset (Fin L) => ω ⊆ A ∧ ω.Nonempty),
        (fun _ => ∅), hinit⟩
    -- run the round
    obtain ⟨S', hreach, halldeg, hK, hcard⟩ :=
      loop_spec_card (d := d) (D := D) (A := A) (f₀ := f₀) (atoms := atoms) hind
        (fun {r K σ X} hinv halldeg' {ω₀} hω hωA =>
          levInvStepKill (d := d) (D := D) (A := A) (f₀ := f₀) (atoms := atoms)
            hinv hind halldeg' hω hωA) S
    -- the closing step
    have hclose := levRoundClosing (d := d) (D := D) (A := A) (f₀ := f₀) (atoms := atoms)
      (r := S'.r) (K := S'.K) (σ := S'.σ) (X := S'.X) S'.inv hind hD halldeg hK
    have hspec := closingAtomsSpec (A := A) (atoms := atoms) (f₀ := f₀) (r := S'.r) (σ := S'.σ)
      hind S'.inv.sigma_sub S'.inv.sigma_ne hD0
    refine ⟨S'.r + 1, freshFin L (S'.r + 1), slotHist (histOf A f₀ A) (S'.r + 1) 0,
      (fun s => freshSet A S'.σ s), closingAtoms A atoms D S'.r S'.σ,
      S'.X.step (Sum.inr 0) (slotHist (histOf A f₀ A) S'.r 0)
        ((S'.inv.top_mem A S'.inv.memA (0 : Fin S'.r → Bool)).1),
      ?_, ?_, ?_, ?_, ?_, hspec.1, hclose, ?_⟩
    · rfl
    · -- `f₀'` is false on the fresh coordinates
      intro s hs
      have h1 : (Fin.natAdd L (freshIdx (L := L) (r := S'.r + 1) ⟨s, hs⟩) : Fin (L + (S'.r + 1)))
          = s := natAdd_freshIdx ⟨s, hs⟩
      rw [← h1, slotHist_natAdd]
      rfl
    · -- the round performs at least `2 ^ A.card - 2 ≥ 2` steps when `A.card ≥ 2`
      intro hAcard
      have hKA : S'.K.card = 1 := by rw [hK]; simp
      have hKcard : S.K.card = 2 ^ A.card - 1 := by
        have hSK : S.K = A.powerset.erase ∅ := by
          ext ω
          constructor
          · intro h
            rw [Finset.mem_filter] at h
            exact Finset.mem_erase.mpr
              ⟨Finset.nonempty_iff_ne_empty.mp h.2.2, Finset.mem_powerset.mpr h.2.1⟩
          · intro h
            rw [Finset.mem_erase] at h
            exact Finset.mem_filter.mpr
              ⟨Finset.mem_univ _, Finset.mem_powerset.mp h.2,
                Finset.nonempty_iff_ne_empty.mpr h.1⟩
        rw [hSK, Finset.card_erase_of_mem (Finset.mem_powerset.mpr (Finset.empty_subset A)),
          Finset.card_powerset]
      have hSr : S.r = 0 := rfl
      rw [hKA, hSr, hKcard] at hcard
      rw [card_freshFin]
      have h4 : 4 ≤ 2 ^ A.card := by
        have h := Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) hAcard
        simpa using h
      omega
    · -- the killed classes are proper subsets of `A`, so `P s` is nonempty
      intro s
      unfold freshSet
      refine Finset.image_nonempty.mpr ?_
      rw [Finset.attach_nonempty_iff]
      by_contra h
      rw [Finset.not_nonempty_iff_eq_empty] at h
      exact S'.inv.sigma_ne (freshIdx s)
        (Finset.Subset.antisymm (S'.inv.sigma_sub (freshIdx s))
          (Finset.sdiff_eq_empty_iff_subset.mp h))
    · intro s
      rfl
    · -- the chain: the round's steps, then the closing step
      exact Reach.trans hreach
        (Reach.step S'.X (Sum.inr 0) (slotHist (histOf A f₀ A) S'.r 0)
          ((S'.inv.top_mem A S'.inv.memA (0 : Fin S'.r → Bool)).1) (Reach.refl _))

end

end Work.Peluse.UControl
