import Mathlib
import Submission.Work.Peluse.UControl.PetChainInv
import Submission.Work.Peluse.UControl.petChainEvalStep
import Submission.Work.Peluse.UControl.petChainDrop

/-!
# One link of the analytic PET chain

`petStepLink` is the one-step invariant preservation of the analytic PET chain: from a state at a
symbolic level `X` with correlation `≥ γ`, applying the PET step at the slot of least degree
(`SymState.stepMin`) with the window `⌊γ'M⌋` and then dropping the constant slots
(`SymState.consts`) produces a state at the symbolic level `SymState.stepMin X hE` whose correlation
is `≥ petChainLevel γ 1 = γ²/2000`, with the shift constant doubled (`D ↦ 2D`) and the range
constant decreased by one (`c ↦ c-1`).

The analytic input is `PetState.lam_step`; the bridges are `petChainEvalStep` (`PetStateP.step`
commutes with the evaluation), `petChainDrop` (dropping constant slots preserves `lam`), and
`toPetP_stepDrop_lam`/`toPetP_step_SB` (the concrete state of the stepped *symbolic* state is the
step-and-drop of the concrete state).
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
open scoped BigOperators

namespace Work.Peluse.UControl

noncomputable section

open Work.Peluse.UControl.PetStep

/-- The window height `⌊γ'M⌋` is at most `M` when `0 < γ' ≤ 1`. -/
lemma winNat_cast_le {γ' : ℝ} (hγ'0 : 0 < γ') (M : ℕ) (hγ'1 : γ' ≤ 1) :
    ((⌊γ' * (M : ℝ)⌋.toNat : ℕ) : ℤ) ≤ (M : ℤ) := by
  have h1 : (0 : ℤ) ≤ ⌊γ' * (M : ℝ)⌋ :=
    Int.floor_nonneg.mpr (mul_nonneg (le_of_lt hγ'0) (by positivity))
  rw [Int.toNat_of_nonneg h1]
  have h2 : (⌊γ' * (M : ℝ)⌋ : ℝ) ≤ (M : ℝ) := by
    have h3 := Int.floor_le (γ' * (M : ℝ))
    have h4 : γ' * (M : ℝ) ≤ 1 * (M : ℝ) :=
      mul_le_mul_of_nonneg_right hγ'1 (by positivity)
    linarith
  exact_mod_cast h2

/-- The shift bound is preserved by dropping slots. -/
lemma PetStateP.drop_ShiftBound (S : PetStateP) (J : Finset S.ι) {N M c D : ℕ}
    (h : S.toState.ShiftBound N M c D) : (S.drop J).toState.ShiftBound N M c D :=
  fun i a z hz => h i.1 a z hz

/-- **One link of the analytic PET chain.** -/
theorem petStepLink {d : ℕ} (N M : ℕ) (γ' : ℝ) (X : SymState d)
    (F : (SymState.dropC X).S.ι → ℤ → ℂ)
    (f : WinTower ⌊γ' * (M : ℝ)⌋.toNat X.nv → ℤ → ℂ)
    (γ : ℝ) (D c : ℕ) (hE : (Finset.univ : Finset (SymState.dropC X).S.ι).Nonempty)
    (hnl : ¬ SymState.IsLinear X) (h : PetInv N M γ' X F f γ D c) :
    PetInv N M γ' (SymState.stepMin X hE) (petNextF X hE F)
      (petNextf X hE ⌊γ' * (M : ℝ)⌋.toNat F f) (petChainLevel γ 1) (2 * D) (c - 1) := by
  obtain ⟨hN, hM, hH, hγ'0, hγ'1, hγ0, hγ1, hc, hD, hFb, hFs, hfb, hfs, hlam, hSB, hw⟩ := h
  have hc1 : 1 ≤ c := by
    have := chainLen_eq_not X hnl
    omega
  have hHM : (((⌊γ' * (M : ℝ)⌋.toNat : ℕ) : ℤ)) ≤ (M : ℤ) := winNat_cast_le hγ'0 M hγ'1
  have hcl : 0 < chainLen X := by
    have := chainLen_eq_not X hnl; omega
  have hw0 : γ' ≤ γ ^ 2 / (20000 * ((D : ℝ) + 1)) := by
    have := hw 0 hcl
    simpa using this
  have hstep := PetState.lam_step ((SymState.dropC X).S.toPetP ⌊γ' * (M : ℝ)⌋.toNat F f).toState
    (SymState.minSlot X hE) (c := c) (D := D) (γ := γ) (γ' := γ') hc1 hN hM hγ0 hγ1 hγ'0
    (toPetP_nu_nonneg (SymState.dropC X).S ⌊γ' * (M : ℝ)⌋.toNat F f)
    (toPetP_sum_nu (SymState.dropC X).S ⌊γ' * (M : ℝ)⌋.toNat F f hH) hw0 hH hfb hfs hFb hFs
    hSB hlam
  have h2 : (((SymState.dropC X).S.toPetP ⌊γ' * (M : ℝ)⌋.toNat F f).step
        (SymState.minSlot X hE) ⌊γ' * (M : ℝ)⌋.toNat).toState.lam N M
      = (((SymState.dropC X).S.toPetP ⌊γ' * (M : ℝ)⌋.toNat F f).toState.step
        (SymState.minSlot X hE) ⌊γ' * (M : ℝ)⌋.toNat).lam N M :=
    petChainEvalStep _ _ _ N M
  have hcst : ∀ j ∈ SymState.consts (SymState.stepMin X hE), ∀ a y,
      ((((SymState.dropC X).S.toPetP ⌊γ' * (M : ℝ)⌋.toNat F f).step
          (SymState.minSlot X hE) ⌊γ' * (M : ℝ)⌋.toNat).P j a).eval y
        = ((((SymState.dropC X).S.toPetP ⌊γ' * (M : ℝ)⌋.toNat F f).step
          (SymState.minSlot X hE) ⌊γ' * (M : ℝ)⌋.toNat).P j a).eval 0 :=
    toPetP_step_drop_hc (SymState.dropC X).S (SymState.minSlot X hE) _
      F f (SymState.consts (SymState.stepMin X hE)) (fun j hj => SymState.mem_consts.mp hj)
  have h3 : ((((SymState.dropC X).S.toPetP ⌊γ' * (M : ℝ)⌋.toNat F f).step
        (SymState.minSlot X hE) ⌊γ' * (M : ℝ)⌋.toNat).drop
        (SymState.consts (SymState.stepMin X hE))).lam N M
      = (((SymState.dropC X).S.toPetP ⌊γ' * (M : ℝ)⌋.toNat F f).step
        (SymState.minSlot X hE) ⌊γ' * (M : ℝ)⌋.toNat).lam N M :=
    petChainDrop _ _ hcst N M
  have h4 := toPetP_stepDrop_lam (SymState.dropC X).S (SymState.minSlot X hE)
    ⌊γ' * (M : ℝ)⌋.toNat N M F f (SymState.consts (SymState.stepMin X hE))
  have hlam' : petChainLevel γ 1
      ≤ (((SymState.dropC (SymState.stepMin X hE)).S).toPetP ⌊γ' * (M : ℝ)⌋.toNat
          (petNextF X hE F) (petNextf X hE ⌊γ' * (M : ℝ)⌋.toNat F f)).toState.lam N M := by
    calc petChainLevel γ 1 = γ ^ 2 / 2000 := rfl
      _ ≤ (((SymState.dropC X).S.toPetP ⌊γ' * (M : ℝ)⌋.toNat F f).toState.step
            (SymState.minSlot X hE) ⌊γ' * (M : ℝ)⌋.toNat).lam N M := hstep
      _ = (((SymState.dropC X).S.toPetP ⌊γ' * (M : ℝ)⌋.toNat F f).step
            (SymState.minSlot X hE) ⌊γ' * (M : ℝ)⌋.toNat).toState.lam N M := h2.symm
      _ = ((((SymState.dropC X).S.toPetP ⌊γ' * (M : ℝ)⌋.toNat F f).step
            (SymState.minSlot X hE) ⌊γ' * (M : ℝ)⌋.toNat).drop
            (SymState.consts (SymState.stepMin X hE))).lam N M := h3.symm
      _ = (((SymState.dropC (SymState.stepMin X hE)).S).toPetP ⌊γ' * (M : ℝ)⌋.toNat
            (petNextF X hE F) (petNextf X hE ⌊γ' * (M : ℝ)⌋.toNat F f)).toState.lam N M :=
          h4.symm
  have hSB' : (((SymState.dropC (SymState.stepMin X hE)).S).toPetP ⌊γ' * (M : ℝ)⌋.toNat
      (petNextF X hE F) (petNextf X hE ⌊γ' * (M : ℝ)⌋.toNat F f)).toState.ShiftBound
      N M (c - 1) (2 * D) :=
    PetStateP.drop_ShiftBound _ (SymState.consts (SymState.stepMin X hE))
      (toPetP_step_SB (SymState.dropC X).S (SymState.minSlot X hE) ⌊γ' * (M : ℝ)⌋.toNat F f
        (PetState.ShiftBound.step
          ((SymState.dropC X).S.toPetP ⌊γ' * (M : ℝ)⌋.toNat F f).toState
          (SymState.minSlot X hE) hc1 hHM hSB))
  have hw' : ∀ k : ℕ, k < chainLen (SymState.stepMin X hE) →
      γ' ≤ petChainLevel (petChainLevel γ 1) k ^ 2
        / (20000 * (((2 ^ k * (2 * D) : ℕ) : ℝ) + 1)) := by
    intro k hk
    have h1 : petChainLevel (petChainLevel γ 1) k = petChainLevel γ (k + 1) :=
      petChainLevel_div γ k
    have h2 : (2 ^ k * (2 * D) : ℕ) = 2 ^ (k + 1) * D := by
      rw [pow_succ]; ring
    have h3 : k + 1 < chainLen X := by
      have := chainLen_eq_not X hnl; omega
    rw [h1, h2]
    exact hw (k + 1) h3
  have hc' : chainLen (SymState.stepMin X hE) + 1 ≤ c - 1 := by
    have := chainLen_eq_not X hnl; omega
  have hD2 : 1 ≤ 2 * D := by omega
  refine ⟨hN, hM, hH, hγ'0, hγ'1, petChainLevel_pos γ hγ0 1,
    petChainLevel_le_one γ hγ0 hγ1 1, hc', hD2, ?_, ?_, ?_, ?_, hlam', hSB', hw'⟩
  · exact toPetP_stepF_bdd (SymState.dropC X).S (SymState.minSlot X hE) F
      (SymState.consts (SymState.stepMin X hE)) hFb
  · exact toPetP_stepF_supp (SymState.dropC X).S (SymState.minSlot X hE) F
      (SymState.consts (SymState.stepMin X hE)) hFs
  · exact toPetP_stepf_bdd (SymState.dropC X).S (SymState.minSlot X hE) F f
      (SymState.consts (SymState.stepMin X hE)) hFb
  · exact toPetP_stepf_supp (SymState.dropC X).S (SymState.minSlot X hE) F f
      (SymState.consts (SymState.stepMin X hE)) hFs

end

end Work.Peluse.UControl
