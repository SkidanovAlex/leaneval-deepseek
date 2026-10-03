import Mathlib
import Submission.Work.Peluse.UControl.petStepLink
import Submission.Work.Peluse.UControl.histStepTransfer

/-!
# Running the phase-1 history chain

`phase1Chain` iterates `HState.step` (the PET step at the deterministic selection `HistData.sel`)
until the state is `Phase1Done` or linear; `histLen X` counts those steps.  This file runs the
*analytic* invariant `HistInv` along that chain (`histStepInv` below) and deduces the target
`histPhase1Run`: from `HistInv N M γ' X.2 F f γ D c` there are functions at the terminal state
`(phase1Chain X).2` whose correlation is at least `petChainLevel γ (histLen X)`, with shift bound
`ShiftBound N M (c - histLen X) (2 ^ histLen X * D)`.

The one-step input is exactly the PET step of the concrete state `(X.2.toSym).S.toPetP H F f` at
the selected slot followed by the dropping of the constant slots (`PetState.lam_step`,
`petChainEvalStep`, `petChainDrop`), together with the slot-reindexing identification
`histStepTransfer` (`Submission/Work/Peluse/UControl/histStepTransfer.lean`) which compares the
concrete polynomial state of the *history* successor `(histStep X hnl).2` with
`histNextPet X hnl H F f`.
-/

set_option autoImplicit false
open scoped BigOperators

namespace Work.Peluse.UControl

noncomputable section

open Work.Peluse.UControl.PetStep

attribute [local instance] Classical.propDecidable

variable {d : ℕ}

/-! ## Unfolding the chain -/

/-- The chain does nothing at a stopped state. -/
lemma phase1Chain_eq_of (X : HState d) (h : X.2.IsLinearX ∨ Phase1Done X.2) :
    phase1Chain X = X := by
  rw [phase1Chain, WellFounded.fix_eq]
  exact dif_pos h

/-- Outside the stopped states the chain takes one PET step at the deterministic selection. -/
lemma phase1Chain_eq_not (X : HState d) (h : HState.Go X) :
    phase1Chain X = phase1Chain (histStep X h) := by
  rw [phase1Chain, WellFounded.fix_eq]
  rw [dif_neg h]
  rfl

/-- A chain started at a non-stopped state has at least one step. -/
lemma histLen_pos_of_go (X : HState d) (h : HState.Go X) : 0 < histLen X := by
  have := histLen_eq_not X h
  omega

/-! ## The one-step invariant preservation -/

/-- **One link of the history-indexed analytic chain.**  From `HistInv` at the history state `X`
one gets `HistInv` at the successor `histStep X hnl`, at the level `petChainLevel γ 1`, with the
shift constant doubled and the range constant decreased by one. -/
theorem histStepInv {d : ℕ} (N M : ℕ) (γ' : ℝ) (X : HState d) (hnl : HState.Go X)
    (F : (X.2.toSym).S.ι → ℤ → ℂ) (f : WinTower ⌊γ' * (M : ℝ)⌋.toNat X.1 → ℤ → ℂ)
    (γ : ℝ) (D c : ℕ) (h : HistInv N M γ' X.2 F f γ D c) :
    HistInv N M γ' (histStep X hnl).2 (histNextF X hnl F)
      (histNextf X hnl ⌊γ' * (M : ℝ)⌋.toNat F f) (petChainLevel γ 1) (2 * D) (c - 1) := by
  obtain ⟨hN, hM, hH, hγ'0, hγ'1, hγ0, hγ1, hc, hD, hFb, hFs, hfb, hfs, hlam, hSB, hw⟩ := h
  let Hf := ⌊γ' * (M : ℝ)⌋.toNat
  have hcl : 0 < histLen X := histLen_pos_of_go X hnl
  have hc1 : 1 ≤ c := by omega
  have hγ'γ : γ' ≤ γ ^ 2 / (20000 * ((D : ℝ) + 1)) := by
    have := hw 0 hcl
    simpa using this
  -- the correlation bound of the concrete state after the step
  have hstep := PetState.lam_step ((X.2.toSym).S.toPetP Hf F f).toState
    (histSelIdx X hnl) hc1 hN hM hγ0 hγ1 hγ'0
    (toPetP_nu_nonneg (X.2.toSym).S Hf F f)
    (toPetP_sum_nu (X.2.toSym).S Hf F f hH) hγ'γ hH hfb hfs hFb hFs hSB hlam
  have h2 : (((X.2.toSym).S.toPetP Hf F f).step (histSelIdx X hnl) Hf).toState.lam N M
      = (((X.2.toSym).S.toPetP Hf F f).toState.step (histSelIdx X hnl) Hf).lam N M :=
    petChainEvalStep _ _ _ N M
  have hcst : ∀ j ∈ petStepConsts (X.2.toSym).S (histSelIdx X hnl), ∀ a y,
      ((((X.2.toSym).S.toPetP Hf F f).step (histSelIdx X hnl) Hf).P j a).eval y
        = ((((X.2.toSym).S.toPetP Hf F f).step (histSelIdx X hnl) Hf).P j a).eval 0 :=
    toPetP_step_drop_hc (X.2.toSym).S (histSelIdx X hnl) Hf F f
      (petStepConsts (X.2.toSym).S (histSelIdx X hnl))
      (fun j hj => (Finset.mem_filter.mp hj).2)
  have h3 : ((((X.2.toSym).S.toPetP Hf F f).step (histSelIdx X hnl) Hf).drop
        (petStepConsts (X.2.toSym).S (histSelIdx X hnl))).lam N M
      = (((X.2.toSym).S.toPetP Hf F f).step (histSelIdx X hnl) Hf).lam N M :=
    petChainDrop _ _ hcst N M
  have hnextlam : petChainLevel γ 1 ≤ (histNextPet X hnl Hf F f).toState.lam N M := by
    calc petChainLevel γ 1 = γ ^ 2 / 2000 := rfl
      _ ≤ (((X.2.toSym).S.toPetP Hf F f).toState.step (histSelIdx X hnl) Hf).lam N M := hstep
      _ = (((X.2.toSym).S.toPetP Hf F f).step (histSelIdx X hnl) Hf).toState.lam N M := h2.symm
      _ = ((((X.2.toSym).S.toPetP Hf F f).step (histSelIdx X hnl) Hf).drop
            (petStepConsts (X.2.toSym).S (histSelIdx X hnl))).toState.lam N M := h3.symm
      _ = (histNextPet X hnl Hf F f).toState.lam N M := rfl
  -- the shift bound of the concrete state after the step
  have hHM : ((Hf : ℕ) : ℤ) ≤ (M : ℤ) := winNat_cast_le hγ'0 M hγ'1
  have hSBstep : (((X.2.toSym).S.toPetP Hf F f).step (histSelIdx X hnl) Hf).toState.ShiftBound
      N M (c - 1) (2 * D) :=
    PetStateP.step_ShiftBound ((X.2.toSym).S.toPetP Hf F f) (histSelIdx X hnl) Hf N M (c - 1) (2 * D)
      (PetState.ShiftBound.step ((X.2.toSym).S.toPetP Hf F f).toState (histSelIdx X hnl) hc1 hHM hSB)
  have hnextSB : (histNextPet X hnl Hf F f).toState.ShiftBound N M (c - 1) (2 * D) :=
    PetStateP.drop_ShiftBound _ _ hSBstep
  -- the slot-reindexing identification of the history successor with `histNextPet`
  have hTr := histStepTransfer Hf N M (c - 1) (2 * D) X hnl F f
  refine ⟨hN, hM, hH, hγ'0, hγ'1, petChainLevel_pos γ hγ0 1,
    petChainLevel_le_one γ hγ0 hγ1 1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show histLen (histStep X hnl) + 1 ≤ c - 1
    have hc' : histLen (histStep X hnl) + 1 + 1 ≤ c := by
      have h' := hc
      rw [histLen_eq_not X hnl] at h'
      exact h'
    exact Nat.le_sub_one_of_lt (Nat.lt_of_succ_le hc')
  · omega
  · exact histNextF_bdd hFb
  · exact histNextF_supp hFs
  · exact toPetP_stepf_bdd (X.2.toSym).S (histSelIdx X hnl) F f
      (petStepConsts (X.2.toSym).S (histSelIdx X hnl)) hFb
  · exact toPetP_stepf_supp (X.2.toSym).S (histSelIdx X hnl) F f
      (petStepConsts (X.2.toSym).S (histSelIdx X hnl)) hFs
  · change petChainLevel γ 1 ≤ (histPet (histStep X hnl).2 Hf (histNextF X hnl F)
      (histNextf X hnl Hf F f)).toState.lam N M
    rw [hTr.1]
    exact hnextlam
  · exact hTr.2.mp hnextSB
  · intro k hk
    have h1 : petChainLevel (petChainLevel γ 1) k = petChainLevel γ (k + 1) := petChainLevel_div γ k
    have h2 : (2 ^ k * (2 * D) : ℕ) = 2 ^ (k + 1) * D := by rw [pow_succ]; ring
    have hk' : k < histLen (histStep X hnl) := hk
    have h3 : k + 1 < histLen X := by
      rw [histLen_eq_not X hnl]
      exact Nat.succ_lt_succ hk'
    rw [h1, h2]
    exact hw (k + 1) h3

/-! ## Running the chain -/

/-- **The analytic invariant at the end of phase 1.** -/
theorem histInv_phase1Chain {d : ℕ} (N M : ℕ) (γ' : ℝ) (X : HState d)
    (F : (X.2.toSym).S.ι → ℤ → ℂ) (f : WinTower ⌊γ' * (M : ℝ)⌋.toNat X.1 → ℤ → ℂ)
    (γ : ℝ) (D c : ℕ) (h : HistInv N M γ' X.2 F f γ D c) :
    ∃ (G : ((phase1Chain X).2.toSym).S.ι → ℤ → ℂ)
      (g : WinTower ⌊γ' * (M : ℝ)⌋.toNat (phase1Chain X).1 → ℤ → ℂ),
      HistInv N M γ' (phase1Chain X).2 G g (petChainLevel γ (histLen X)) (2 ^ histLen X * D)
        (c - histLen X) := by
  classical
  revert F f γ D c
  induction X using WellFounded.induction (HState.rel_wf d) with
  | h X ih =>
    intro F f γ D c h
    by_cases hstop : X.2.IsLinearX ∨ Phase1Done X.2
    · rw [histLen_eq_of X hstop, phase1Chain_eq_of X hstop]
      exact ⟨F, f, by simpa using h⟩
    · have hgo : HState.Go X := hstop
      obtain ⟨G, g, hG⟩ := ih (histStep X hgo) (X.2.weightH_step_sel_lt (histHne X hgo))
        (histNextF X hgo F) (histNextf X hgo ⌊γ' * (M : ℝ)⌋.toNat F f)
        (petChainLevel γ 1) (2 * D) (c - 1)
        (histStepInv N M γ' X hgo F f γ D c h)
      have hlen : histLen X = histLen (histStep X hgo) + 1 := histLen_eq_not X hgo
      rw [hlen, phase1Chain_eq_not X hgo]
      refine ⟨G, g, ?_⟩
      have h1 : petChainLevel (petChainLevel γ 1) (histLen (histStep X hgo))
          = petChainLevel γ (histLen (histStep X hgo) + 1) := petChainLevel_div γ _
      have h2 : (2 ^ histLen (histStep X hgo) * (2 * D) : ℕ)
          = 2 ^ (histLen (histStep X hgo) + 1) * D := by rw [pow_succ]; ring
      have h3 : (c - 1) - histLen (histStep X hgo) = c - (histLen (histStep X hgo) + 1) := by
        rw [Nat.sub_sub, Nat.add_comm]
      rw [← h1, ← h2, ← h3]
      exact hG

/-! ## The target -/

theorem histPhase1Run {d : ℕ} (N M : ℕ) (γ' : ℝ) (X : HState d)
    (F : (X.2.toSym).S.ι → ℤ → ℂ) (f : WinTower ⌊γ' * (M : ℝ)⌋.toNat X.1 → ℤ → ℂ)
    (γ : ℝ) (D c : ℕ) (h : HistInv N M γ' X.2 F f γ D c) :
    ∃ (G : ((phase1Chain X).2.toSym).S.ι → ℤ → ℂ)
      (g : WinTower ⌊γ' * (M : ℝ)⌋.toNat (phase1Chain X).1 → ℤ → ℂ),
      petChainLevel γ (histLen X) ≤
          (histPet (phase1Chain X).2 ⌊γ' * (M : ℝ)⌋.toNat G g).toState.lam N M
        ∧ (histPet (phase1Chain X).2 ⌊γ' * (M : ℝ)⌋.toNat G g).toState.ShiftBound N M
            (c - histLen X) (2 ^ histLen X * D) := by
  obtain ⟨G, g, hG⟩ := histInv_phase1Chain N M γ' X F f γ D c h
  exact ⟨G, g, hG.hlam, hG.hSB⟩

end

end Work.Peluse.UControl
