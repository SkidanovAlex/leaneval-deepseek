import Mathlib
import Submission.Work.Peluse.UControl.PetChainIter
import Submission.Work.Peluse.UControl.PetConcreteD

/-!
# The setup of the analytic PET chain

`SymState.chain` (`PetChainIter.lean`) is the *combinatorial* PET chain of Peluse's §4: it iterates
the PET step at a slot of least degree until every slot polynomial is linear in `y`.  This file
supplies the vocabulary of the *analytic* chain, which runs the concrete `PetState` of
`PetStateSym.toPetP` in lockstep with it:

* `chainLen X` — the number of steps of the chain started at `X` (so that `chain d X` is reached
  after `chainLen X` steps);
* `petChainLevel γ n` — the level after `n` PET steps from a level `γ`, i.e. `γ` with the recursion
  `γ ↦ γ²/2000` applied `n` times (`PetState.lam_step`); its closed form is
  `γ^(2^n)/2000^(2^n-1)`;
* `PetInv` — the invariant of the state along the chain: the window data (`N`, `M`, the fixed window
  radius `γ'`, the shift constant `D`, the range constant `c`), the 1-boundedness and the support of
  the base and slot functions, the correlation bound `γ ≤ lam` and the shift bound
  `ShiftBound N M c D`, together with the *window condition*
  `γ' ≤ petChainLevel γ k ^ 2 / (20000 * (2^k * D + 1))` for every `k` (which is what each step
  consumes, and which survives the passage `γ ↦ petChainLevel γ 1`, `D ↦ 2D`).

The main theorem the analytic chain must produce is stated (and delegated) separately.
-/

set_option autoImplicit false
open scoped BigOperators

attribute [local instance] Classical.propDecidable

namespace Work.Peluse.UControl

noncomputable section

open Work.Peluse.UControl.PetStep

/-- The level after `n` PET steps from the level `γ`: the recursion `γ ↦ γ²/2000` applied `n`
times (this is exactly the content of `PetState.lam_step`). -/
noncomputable def petChainLevel (γ : ℝ) : ℕ → ℝ
  | 0 => γ
  | (n + 1) => petChainLevel γ n ^ 2 / 2000

@[simp] lemma petChainLevel_zero (γ : ℝ) : petChainLevel γ 0 = γ := rfl

lemma petChainLevel_succ (γ : ℝ) (n : ℕ) :
    petChainLevel γ (n + 1) = petChainLevel γ n ^ 2 / 2000 := rfl

/-- The level of a shifted starting point: stepping once from `γ²/2000` and doing `n` further steps
is doing `n+1` steps from `γ`.  This is the identity that lets the chain be iterated. -/
lemma petChainLevel_div (γ : ℝ) (n : ℕ) :
    petChainLevel (γ ^ 2 / 2000) n = petChainLevel γ (n + 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change petChainLevel (γ ^ 2 / 2000) n ^ 2 / 2000 = petChainLevel γ (n + 1) ^ 2 / 2000
    rw [ih]

lemma petChainLevel_nonneg (γ : ℝ) (hγ : 0 ≤ γ) (n : ℕ) : 0 ≤ petChainLevel γ n := by
  induction n with
  | zero => simpa using hγ
  | succ n ih => rw [petChainLevel_succ]; positivity

lemma petChainLevel_pos (γ : ℝ) (hγ : 0 < γ) (n : ℕ) : 0 < petChainLevel γ n := by
  induction n with
  | zero => simpa using hγ
  | succ n ih => rw [petChainLevel_succ]; positivity

lemma petChainLevel_le_one (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (n : ℕ) :
    petChainLevel γ n ≤ 1 := by
  induction n with
  | zero => simpa using hγ1
  | succ n ih =>
    rw [petChainLevel_succ]
    have h2 : petChainLevel γ n ^ 2 ≤ 1 := by nlinarith [petChainLevel_pos γ hγ0 n]
    linarith

/-- The number of PET steps of the chain started at `X`. -/
noncomputable def chainLen {d : ℕ} (X : SymState d) : ℕ :=
  WellFounded.fix (petRel_wf d)
    (fun X rec => if h : SymState.IsLinear X then 0
      else rec (SymState.stepMin X (SymState.dropC_nonempty X h))
        (SymState.stepMin_lt_full X (SymState.dropC_nonempty X h)) + 1) X

lemma chainLen_eq_of {d : ℕ} (X : SymState d) (h : SymState.IsLinear X) : chainLen X = 0 := by
  show WellFounded.fix (petRel_wf d) _ X = 0
  rw [WellFounded.fix_eq]
  exact dif_pos h

lemma chainLen_eq_not {d : ℕ} (X : SymState d) (h : ¬ SymState.IsLinear X) :
    chainLen X = chainLen (SymState.stepMin X (SymState.dropC_nonempty X h)) + 1 := by
  show WellFounded.fix (petRel_wf d) _ X = _
  rw [WellFounded.fix_eq]
  rw [dif_neg h]
  rfl

end

end Work.Peluse.UControl
