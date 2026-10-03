import Mathlib
import Submission.Work.Peluse.UControl.HistReach
import Submission.Work.Peluse.UControl.histWeightStepEq

/-!
# The phase-1 chain and its reachability theorem

`phase1Chain` iterates `HState.step` (the PET step at the deterministic selection) until the state
is `Phase1Done` or linear, and `phase1Chain_done` proves that the terminal state of a chain started
in a `Phase1` state is `Phase1Done`: a `Phase1` state is never linear (for `d ≥ 2`), so the chain
cannot stop early, and the invariant is preserved at every step by `Phase1.step_sel`.

The recursion is well-founded because one step strictly decreases Peluse's weight vector:
`HistData.weightH_step_sel_lt` transports the `PetStateSym`-level `petSymWeight` through
`histWeightStepEq`.
-/

set_option autoImplicit false
open scoped BigOperators

namespace Work.Peluse.UControl

noncomputable section

open Polynomial
open Work.Peluse.UControl.PetStep

attribute [local instance] Classical.propDecidable

/-- The relation of the recursion: the weight vector strictly decreases. -/
def HState.rel {d : ℕ} (Y X : HState d) : Prop := petLt (Y.2.weightH) (X.2.weightH)

lemma HState.rel_wf (d : ℕ) : WellFounded (HState.rel (d := d)) :=
  InvImage.wf (fun X : HState d => X.2.weightH) (petChainWF d)

/-- A `Phase1` state has no slot of degree `0`, so the weight vector vanishes at coordinate `0`. -/
lemma HistData.weightH_zero_coord {d n : ℕ} (X : HistData d n) :
    X.weightH ⟨0, Nat.succ_pos d⟩ = 0 := by
  simp only [HistData.weightH, HistData.toSym, PetStep.PetStateSym.weight]
  refine Finset.card_eq_zero.mpr ?_
  rw [← Finset.not_nonempty_iff_eq_empty]
  rintro ⟨c, hc⟩
  obtain ⟨i, hi, -⟩ := Finset.mem_image.mp hc
  have hi2 : (X.Q i.1.1 i.1.2).natDegree = 0 := (Finset.mem_filter.mp hi).2
  exact absurd (X.hnc i.1 i.2) (by rw [hi2]; omega)

/-- One PET step at the deterministic selection strictly decreases the weight vector. -/
theorem HistData.weightH_step_sel_lt {d n : ℕ} (X : HistData d n) (hne : X.H.Nonempty) :
    petLt ((X.step (X.sel hne).1 (X.sel hne).2 (X.sel_mem_H hne)).weightH) X.weightH := by
  classical
  have hW0 : (X.toSym).S.weight d ⟨0, Nat.succ_pos d⟩ = 0 := by
    show X.weightH ⟨0, Nat.succ_pos d⟩ = 0
    exact X.weightH_zero_coord
  have hkey : petLt
      (((X.toSym).S.step (⟨X.sel hne, X.sel_mem_H hne⟩ : (X.toSym).S.ι)).weight d)
      ((X.toSym).S.weight d) := by
    refine petSymWeight (X.toSym).S (⟨X.sel hne, X.sel_mem_H hne⟩ : (X.toSym).S.ι)
      (d := d) (d' := X.minDeg hne) ?_ ?_ ?_ ?_
    · intro i
      exact X.hnc i.1 i.2
    · intro i
      exact X.hd i.1 i.2
    · intro i _
      exact X.minDeg_le hne i.1 i.2
    · show ((X.toSym).S.P (⟨X.sel hne, X.sel_mem_H hne⟩ : (X.toSym).S.ι)).natDegree
        = X.minDeg hne
      exact X.sel_degree hne
  obtain ⟨j₀, hj₀, hjm⟩ := hkey
  have hj0pos : 1 ≤ (j₀ : ℕ) := by
    by_contra hcon
    have h0 : (j₀ : ℕ) = 0 := by omega
    have hj0 : j₀ = ⟨0, Nat.succ_pos d⟩ := Fin.ext h0
    have h1 : (X.toSym).S.weight d j₀ = 0 := by rw [hj0]; exact hW0
    rw [h1] at hj₀
    omega
  refine ⟨j₀, ?_, ?_⟩
  · rw [histWeightStepEq X (X.sel hne).1 (X.sel hne).2 (X.sel_mem_H hne) j₀ hj0pos]
    exact hj₀
  · intro m hm
    rw [histWeightStepEq X (X.sel hne).1 (X.sel hne).2 (X.sel_mem_H hne) m (by omega)]
    exact hjm m hm

/-- **The phase-1 chain**: step at the deterministic selection until `Phase1Done` or linear. -/
def phase1Chain {d : ℕ} (X : HState d) : HState d :=
  WellFounded.fix (HState.rel_wf d) (fun X rec =>
    if h : X.2.IsLinearX ∨ Phase1Done X.2 then X
    else rec (HState.step X (X.2.H_nonempty_of_not_linear (fun hl => h (Or.inl hl)))) (by
      show HState.rel (HState.step X (X.2.H_nonempty_of_not_linear (fun hl => h (Or.inl hl)))) X
      exact X.2.weightH_step_sel_lt _)) X

/-- **Reachability of the end of phase 1.**  A chain started in a `Phase1` state (with `d ≥ 2`)
ends in a `Phase1Done` state. -/
theorem phase1Chain_done {d : ℕ} (hd2 : 2 ≤ d) (lc : ℤ) :
    ∀ X : HState d, Phase1 d X.1 lc X.2 → Phase1Done (phase1Chain X).2 := by
  intro X
  induction X using WellFounded.induction (HState.rel_wf d) with
  | h X ih =>
    intro h
    rw [phase1Chain, WellFounded.fix_eq]
    by_cases hstop : X.2.IsLinearX ∨ Phase1Done X.2
    · rw [dif_pos hstop]
      rcases hstop with hl | hdone
      · exact absurd hl (Phase1.not_linear hd2 h)
      · exact hdone
    · rw [dif_neg hstop]
      refine ih (HState.step X (X.2.H_nonempty_of_not_linear (fun hl => hstop (Or.inl hl))))
        (X.2.weightH_step_sel_lt _) ?_
      exact Phase1.step_sel (by omega) h (fun hd => hstop (Or.inr hd))
        (X.2.H_nonempty_of_not_linear (fun hl => hstop (Or.inl hl)))

end

end Work.Peluse.UControl
