import Mathlib
import Submission.Work.Peluse.UControl.HistReach2
import Submission.Work.Peluse.UControl.PetChainInv

/-!
# The analytic invariant of the history-indexed PET chain

`HistData`/`HState` (`HistReach.lean`) carry the *combinatorial* half of the history-indexed PET
chain of Peluse's §4 (her Lemmas 4.4-4.7); this file supplies the vocabulary of the *analytic* half:
the concrete `PetStateP` attached to a history state, its one-step successor (with the constant slots
absorbed into the base function, exactly as in `PetStateP.drop`), and the invariant `HistInv` that is
threaded along the chain.

* `histLen X` — the number of steps of `phase1Chain` started at `X`;
* `histHne`/`histStep` — one step of the chain at the deterministic selection (`X.2.sel`), in the
  form used by the recursions (`hne` derived from the stopping condition);
* `histPet X H F f` — the concrete polynomial state of a history state (the state of `X.toSym`);
* `histNextPet X h H F f` — the concrete state after one step, with the constant slots of the new
  symbolic state (`PetStateSym.consts`) absorbed into the base function;
* `histNextF`/`histNextf` — the slot and base functions of the *history* successor;  they are the
  images of `histNextPet`'s under the slot bijection `HistData.stepIdx`;
* `HistInv` — the invariant of the analytic chain.

The two identifications that make the step work are

* `histStepLam` — the concrete state of the history successor has the same correlation as
  `histNextPet` (a `Finset.prod_bij` along `HistData.stepIdx`), and
* `histStepSB` — the same for the shift bound.

`/tmp` is not writable in this sandbox: `export TMPDIR=$PWD/.tmpdir` before any `lake` call.
-/

set_option autoImplicit false
open scoped BigOperators

namespace Work.Peluse.UControl

noncomputable section

open Work.Peluse.UControl.PetStep

attribute [local instance] Classical.propDecidable

variable {d : ℕ}

/-! ## The chain length -/

/-- The non-stopping hypothesis: neither linear nor `Phase1Done`. -/
abbrev HState.Go (X : HState d) : Prop := ¬ (X.2.IsLinearX ∨ Phase1Done X.2)

/-- The nonemptiness of the live slots derived from the non-stopping condition. -/
def histHne (X : HState d) (hnl : HState.Go X) : X.2.H.Nonempty :=
  X.2.H_nonempty_of_not_linear (fun hl => hnl (Or.inl hl))

/-- One step of the chain at the deterministic selection. -/
def histStep (X : HState d) (hnl : HState.Go X) : HState d :=
  HState.step X (histHne X hnl)

/-- The number of steps of the chain started at `X`. -/
def histLen (X : HState d) : ℕ :=
  WellFounded.fix (HState.rel_wf d)
    (fun X rec => if h : X.2.IsLinearX ∨ Phase1Done X.2 then 0
      else rec (histStep X h) (X.2.weightH_step_sel_lt (histHne X h)) + 1) X

lemma histLen_eq_of (X : HState d) (h : X.2.IsLinearX ∨ Phase1Done X.2) : histLen X = 0 := by
  show WellFounded.fix (HState.rel_wf d) _ X = 0
  rw [WellFounded.fix_eq]
  exact dif_pos h

lemma histLen_eq_not (X : HState d) (h : HState.Go X) :
    histLen X = histLen (histStep X h) + 1 := by
  show WellFounded.fix (HState.rel_wf d) _ X = _
  rw [WellFounded.fix_eq]
  rw [dif_neg h]
  rfl

/-! ## The constant slots of one step -/

/-- The slots of one PET step whose shift polynomial is constant in `y`. -/
def petStepConsts {k : ℕ} (S : PetStateSym k) (i₀ : S.ι) : Finset (S.step i₀).ι :=
  Finset.univ.filter (fun j => ((S.step i₀).P j).natDegree = 0)

/-! ## The concrete states -/

/-- The concrete polynomial state attached to a history state. -/
def histPet {d n : ℕ} (X : HistData d n) (H : ℕ) (F : (X.toSym).S.ι → ℤ → ℂ)
    (f : WinTower H n → ℤ → ℂ) : PetStateP :=
  (X.toSym).S.toPetP H F f

/-- The selected slot of a non-stopping history state, as a slot of its symbolic companion. -/
def histSelIdx (X : HState d) (hnl : HState.Go X) : (X.2.toSym).S.ι :=
  ⟨X.2.sel (histHne X hnl), X.2.sel_mem_H (histHne X hnl)⟩

/-- The concrete state after one step of the history chain, with the constant slots of the new
symbolic state absorbed into the base function. -/
def histNextPet (X : HState d) (hnl : HState.Go X) (H : ℕ)
    (F : (X.2.toSym).S.ι → ℤ → ℂ) (f : WinTower H X.1 → ℤ → ℂ) : PetStateP :=
  (((X.2.toSym).S.toPetP H F f).step (histSelIdx X hnl) H).drop
    (petStepConsts (X.2.toSym).S (histSelIdx X hnl))

/-- The slot functions of the history successor: the `stepF` of the old ones, transported along the
slot bijection `HistData.stepIdx`. -/
def histNextF (X : HState d) (hnl : HState.Go X) (F : (X.2.toSym).S.ι → ℤ → ℂ) :
    ((histStep X hnl).2.toSym).S.ι → ℤ → ℂ :=
  fun x => stepF F ((X.2.stepIdx (X.2.sel (histHne X hnl)).1 (X.2.sel (histHne X hnl)).2
    (X.2.sel_mem_H (histHne X hnl)) x).1)

/-- The base function of the history successor. -/
def histNextf (X : HState d) (hnl : HState.Go X) (H : ℕ)
    (F : (X.2.toSym).S.ι → ℤ → ℂ) (f : WinTower H X.1 → ℤ → ℂ) :
    WinTower H (X.1 + 1) → ℤ → ℂ :=
  fun a x => (histNextPet X hnl H F f).f a x

/-! ## The invariant -/

/-- The invariant of the analytic history chain. -/
structure HistInv {d n : ℕ} (N M : ℕ) (γ' : ℝ) (X : HistData d n)
    (F : (X.toSym).S.ι → ℤ → ℂ) (f : WinTower ⌊γ' * (M : ℝ)⌋.toNat n → ℤ → ℂ)
    (γ : ℝ) (D c : ℕ) : Prop where
  hN : 0 < N
  hM : 0 < M
  hH : 1 ≤ ⌊γ' * (M : ℝ)⌋.toNat
  hγ'0 : 0 < γ'
  hγ'1 : γ' ≤ 1
  hγ0 : 0 < γ
  hγ1 : γ ≤ 1
  hc : histLen (⟨n, X⟩ : HState d) + 1 ≤ c
  hD : 1 ≤ D
  hFb : ∀ i x, ‖F i x‖ ≤ 1
  hFs : ∀ i, SupportIn (F i) N
  hfb : ∀ a x, ‖f a x‖ ≤ 1
  hfs : ∀ a, SupportIn (f a) N
  hlam : γ ≤ ((X.toSym).S.toPetP ⌊γ' * (M : ℝ)⌋.toNat F f).toState.lam N M
  hSB : ((X.toSym).S.toPetP ⌊γ' * (M : ℝ)⌋.toNat F f).toState.ShiftBound N M c D
  hw : ∀ k : ℕ, k < histLen (⟨n, X⟩ : HState d) →
    γ' ≤ petChainLevel γ k ^ 2 / (20000 * (((2 ^ k * D : ℕ) : ℝ) + 1))

/-! ## Elementary facts about the next functions -/

lemma histNextF_bdd {X : HState d} {hnl : HState.Go X} {F : (X.2.toSym).S.ι → ℤ → ℂ}
    (hFb : ∀ i x, ‖F i x‖ ≤ 1) : ∀ i x, ‖histNextF X hnl F i x‖ ≤ 1 := by
  intro i x
  rw [histNextF]
  exact stepF_bdd F hFb _ x

lemma histNextF_supp {X : HState d} {hnl : HState.Go X} {F : (X.2.toSym).S.ι → ℤ → ℂ}
    {N : ℕ} (hFs : ∀ i, SupportIn (F i) N) : ∀ i, SupportIn (histNextF X hnl F i) N := by
  intro i
  rw [histNextF]
  exact stepF_supp F hFs _

end

end Work.Peluse.UControl
