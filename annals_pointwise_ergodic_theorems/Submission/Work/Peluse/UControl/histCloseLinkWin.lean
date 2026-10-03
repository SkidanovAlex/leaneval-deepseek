import Mathlib
import Submission.Work.Peluse.UControl.histStepTransfer
import Submission.Work.Peluse.UControl.petStepLink

/-!
# The closing link of the history-indexed PET chain

The phase-1 chain (Peluse's §4) steps at the deterministic selection
`HistData.sel` while some live slot is *not* a descendant of the top slot.  When it stops
(`Phase1Done`) all live slots are descendants of the top slot, all of degree `d`, and the
deterministic selection is the zero history `(Sum.inr 0, 0)` of the top slot
(`HistPhase1.histPhase1SelZero`).  The closing step (Peluse's Lemma 4.5,
`HistPhase1.histPhase1Terminal`) produces the terminal shape `Phase1Terminal`; this file attaches
the *analytic* bookkeeping to it:

* the closing step has **no** `y`-constant slots, so the "drop the constant slots" operation is the
  identity and the base function of the terminal state is the slot function of the distinguished
  slot (`petStepConsts_close_eq_empty`, `histCloseStep_base`);
* consequently `histCloseLinkWin`: from `HistInv N M γ' X F f γ D c`, the window hypothesis
  `γ' ≤ γ^2/(20000(D+1))` and the top-slot hypothesis `htop`, there are `G`, `g` at the terminal
  state with `Phase1Terminal`, correlation `≥ petChainLevel γ 1`, shift bound
  `ShiftBound N M (c-1) (2D)`, every slot function of `G` equal to `Ftop` or `star Ftop`, and `g`
  a single global choice `Ftop` or `star Ftop`.

The analytic input is `PetState.lam_step` (Peluse's Lemma 4.2) and `PetState.ShiftBound.step`; the
bridges are `petChainEvalStep`, `petChainDrop`, `PetStateP.step_ShiftBound`,
`PetStateP.drop_ShiftBound`, and the slot-reindexing identifications `hstLamGen`/`hstSBGen`
(`histStepTransfer.lean`).
-/

set_option autoImplicit false
open scoped BigOperators

namespace Work.Peluse.UControl

noncomputable section

open Work.Peluse.UControl.PetStep

attribute [local instance] Classical.propDecidable

/-! ## The closing step has no constant slots -/

/-- **The closing step has no `y`-constant slots.**  At a `Phase1Done` state every live slot is a
descendant of the top slot, so the only slot of the symbolic step that could be constant in `y`
is the dropped continuation `(i₀, false)`, which is not in the index type. -/
lemma petStepConsts_close_eq_empty {d n : ℕ} (lc : ℤ) (X : HistData d n)
    (h : Phase1 d n lc X) (hdone : Phase1Done X) (hd2 : 2 ≤ d) (hlc : lc ≠ 0) :
    petStepConsts (X.toSym).S ⟨((Sum.inr 0 : InitIdx d), 0), h.pLive 0⟩ = ∅ := by
  classical
  have hne : X.H.Nonempty := ⟨_, h.pLive 0⟩
  have hterm := histPhase1Terminal hd2 hlc X h hdone hne
  refine Finset.eq_empty_of_forall_notMem (fun j hj => ?_)
  simp only [petStepConsts, Finset.mem_filter, Finset.mem_univ, true_and] at hj
  obtain ⟨⟨⟨⟨a₀, h₀'⟩, hmem⟩, ε⟩, hne'⟩ := j
  have ha₀ : a₀ = (Sum.inr 0 : InitIdx d) := hdone (a₀, h₀') hmem
  subst ha₀
  set h' : Fin (n + 1) → Bool := Fin.snoc h₀' ε with hh'
  have hgoal : ((X.toSym).S.step ⟨((Sum.inr 0 : InitIdx d), 0), h.pLive 0⟩).P
        ⟨(⟨((Sum.inr 0 : InitIdx d), h₀'), hmem⟩, ε), hne'⟩
      = X.stepQ (Sum.inr 0) 0 (Sum.inr 0) h' := by
    simp only [HistData.stepQ, PetStep.PetStateSym.step, HistData.toSym, hh', Fin.init_snoc,
      Fin.snoc_last]
    rfl
  have h'ne : h' ≠ 0 := by
    rw [hh']
    intro hzero
    apply hne'
    have h1 : h₀' = 0 := by
      have hc := congrArg Fin.init hzero
      rwa [Fin.init_snoc] at hc
    have h2 : ε = false := by
      have hc := congrFun hzero (Fin.last n)
      rwa [Fin.snoc_last] at hc
    exact Prod.ext (Subtype.ext (Prod.ext rfl h1)) h2
  have hmem' : (((Sum.inr 0 : InitIdx d), h')) ∈ (X.step (Sum.inr 0) 0 (h.pLive 0)).H :=
    hterm.2 h' h'ne
  have hdeg : (X.stepQ (Sum.inr 0) 0 (Sum.inr 0) h').natDegree = d - 1 :=
    (hterm.1 _ hmem').2.2.1
  rw [hgoal] at hj
  have h0 : d - 1 = 0 := hdeg.symm.trans hj
  omega

/-! ## The base function of the terminal state -/

/-- **The base function of the closing step.**  Since the closing step has no constant slots, the
step-and-drop state's base function is the slot function of the distinguished slot itself. -/
lemma histCloseStep_base {d n : ℕ} (X : HistData d n) (Hf : ℕ) (F : (X.toSym).S.ι → ℤ → ℂ)
    (f : WinTower Hf n → ℤ → ℂ) (hmem : ((Sum.inr 0 : InitIdx d), 0) ∈ X.H)
    (a : WinTower Hf (n + 1)) (x : ℤ) :
    ((((X.toSym).S.toPetP Hf F f).step ⟨((Sum.inr 0 : InitIdx d), 0), hmem⟩ Hf).drop
        (∅ : Finset _)).f a x
      = F ⟨((Sum.inr 0 : InitIdx d), 0), hmem⟩ x := by
  simp only [PetStateP.drop]
  rw [Finset.prod_empty, mul_one]
  rfl

/-! ## The requested statement -/

theorem histCloseLinkWin {d n : ℕ} (N M : ℕ) (γ' : ℝ) (lc : ℤ) (X : HistData d n)
    (h : Phase1 d n lc X) (hdone : Phase1Done X) (hd2 : 2 ≤ d) (hlc : lc ≠ 0)
    (Ftop : ℤ → ℂ) (F : (X.toSym).S.ι → ℤ → ℂ)
    (f : WinTower ⌊γ' * (M : ℝ)⌋.toNat n → ℤ → ℂ)
    (γ : ℝ) (D c : ℕ) (hinv : HistInv N M γ' X F f γ D c)
    (htop : ∀ i, (∀ x, F i x = Ftop x) ∨ (∀ x, F i x = star (Ftop x)))
    (hwin : γ' ≤ γ ^ 2 / (20000 * ((D : ℝ) + 1))) :
    ∃ (G : ((X.step (Sum.inr 0) 0 (h.pLive 0)).toSym).S.ι → ℤ → ℂ)
      (g : WinTower ⌊γ' * (M : ℝ)⌋.toNat (n + 1) → ℤ → ℂ),
      Phase1Terminal d (n + 1) lc (X.step (Sum.inr 0) 0 (h.pLive 0))
      ∧ petChainLevel γ 1 ≤ (histPet (X.step (Sum.inr 0) 0 (h.pLive 0))
            ⌊γ' * (M : ℝ)⌋.toNat G g).toState.lam N M
      ∧ (histPet (X.step (Sum.inr 0) 0 (h.pLive 0)) ⌊γ' * (M : ℝ)⌋.toNat G g).toState.ShiftBound
            N M (c - 1) (2 * D)
      ∧ (∀ i, (∀ x, G i x = Ftop x) ∨ (∀ x, G i x = star (Ftop x)))
      ∧ (∃ c₀ : Bool, ∀ a x, g a x = (if c₀ then star (Ftop x) else Ftop x)) := by
  classical
  obtain ⟨hN, hM, hH, hγ'0, hγ'1, hγ0, hγ1, hc, hD, hFb, hFs, hfb, hfs, hlam, hSB, hw⟩ := hinv
  have hne : X.H.Nonempty := ⟨_, h.pLive 0⟩
  have hc1 : 1 ≤ c := by
    have h0 : histLen (⟨n, X⟩ : HState d) = 0 := histLen_eq_of ⟨n, X⟩ (Or.inr hdone)
    omega
  refine ⟨(fun i => stepF F ((X.stepIdx (Sum.inr 0) 0 (h.pLive 0) i).1)),
    (fun a x => ((((X.toSym).S.toPetP ⌊γ' * (M : ℝ)⌋.toNat F f).step ⟨((Sum.inr 0 : InitIdx d), 0), h.pLive 0⟩ ⌊γ' * (M : ℝ)⌋.toNat).drop ∅).f a x),
    histPhase1Terminal hd2 hlc X h hdone hne, ?_, ?_, ?_, ?_⟩
  · -- the correlation
    have hJ : petStepConsts (X.toSym).S ⟨((Sum.inr 0 : InitIdx d), 0), h.pLive 0⟩ = ∅ :=
      petStepConsts_close_eq_empty lc X h hdone hd2 hlc
    have hLamEq := hstLamGen X (Sum.inr 0) 0 (h.pLive 0) ⌊γ' * (M : ℝ)⌋.toNat N M F f
    rw [hJ] at hLamEq
    have h3 : ((((X.toSym).S.toPetP ⌊γ' * (M : ℝ)⌋.toNat F f).step ⟨((Sum.inr 0 : InitIdx d), 0), h.pLive 0⟩ ⌊γ' * (M : ℝ)⌋.toNat).drop (∅ : Finset _)).lam N M
        = ((((X.toSym).S.toPetP ⌊γ' * (M : ℝ)⌋.toNat F f).step ⟨((Sum.inr 0 : InitIdx d), 0), h.pLive 0⟩ ⌊γ' * (M : ℝ)⌋.toNat)).lam N M :=
      petChainDrop _ ∅ (fun i hi => by simp at hi) N M
    have h4 : ((((X.toSym).S.toPetP ⌊γ' * (M : ℝ)⌋.toNat F f).step ⟨((Sum.inr 0 : InitIdx d), 0), h.pLive 0⟩ ⌊γ' * (M : ℝ)⌋.toNat)).lam N M
        = ((((X.toSym).S.toPetP ⌊γ' * (M : ℝ)⌋.toNat F f).toState.step ⟨((Sum.inr 0 : InitIdx d), 0), h.pLive 0⟩ ⌊γ' * (M : ℝ)⌋.toNat)).lam N M :=
      petChainEvalStep _ _ _ N M
    have h5 : γ ^ 2 / 2000 ≤
        ((((X.toSym).S.toPetP ⌊γ' * (M : ℝ)⌋.toNat F f).toState.step ⟨((Sum.inr 0 : InitIdx d), 0), h.pLive 0⟩ ⌊γ' * (M : ℝ)⌋.toNat)).lam N M :=
      PetState.lam_step ((X.toSym).S.toPetP ⌊γ' * (M : ℝ)⌋.toNat F f).toState
        ⟨((Sum.inr 0 : InitIdx d), 0), h.pLive 0⟩ hc1 hN hM hγ0 hγ1 hγ'0
        (toPetP_nu_nonneg (X.toSym).S ⌊γ' * (M : ℝ)⌋.toNat F f)
        (toPetP_sum_nu (X.toSym).S ⌊γ' * (M : ℝ)⌋.toNat F f hH)
        hwin hH hfb hfs hFb hFs hSB hlam
    calc petChainLevel γ 1 = γ ^ 2 / 2000 := rfl
      _ ≤ _ := h5
      _ = _ := h4.symm
      _ = _ := h3.symm
      _ = _ := hLamEq.symm
  · -- the shift bound
    have hJ : petStepConsts (X.toSym).S ⟨((Sum.inr 0 : InitIdx d), 0), h.pLive 0⟩ = ∅ :=
      petStepConsts_close_eq_empty lc X h hdone hd2 hlc
    have hstepSB : ((((X.toSym).S.toPetP ⌊γ' * (M : ℝ)⌋.toNat F f).step ⟨((Sum.inr 0 : InitIdx d), 0), h.pLive 0⟩ ⌊γ' * (M : ℝ)⌋.toNat)).toState.ShiftBound N M (c - 1) (2 * D) :=
      PetStateP.step_ShiftBound ((X.toSym).S.toPetP ⌊γ' * (M : ℝ)⌋.toNat F f) ⟨((Sum.inr 0 : InitIdx d), 0), h.pLive 0⟩ ⌊γ' * (M : ℝ)⌋.toNat N M (c - 1) (2 * D)
        (PetState.ShiftBound.step (((X.toSym).S.toPetP ⌊γ' * (M : ℝ)⌋.toNat F f).toState) ⟨((Sum.inr 0 : InitIdx d), 0), h.pLive 0⟩ hc1 (winNat_cast_le hγ'0 M hγ'1) hSB)
    have hdropSB : (((((X.toSym).S.toPetP ⌊γ' * (M : ℝ)⌋.toNat F f).step ⟨((Sum.inr 0 : InitIdx d), 0), h.pLive 0⟩ ⌊γ' * (M : ℝ)⌋.toNat).drop (∅ : Finset _))).toState.ShiftBound N M (c - 1) (2 * D) :=
      PetStateP.drop_ShiftBound _ _ hstepSB
    have hiff := hstSBGen X (Sum.inr 0) 0 (h.pLive 0) ⌊γ' * (M : ℝ)⌋.toNat N M (c - 1) (2 * D) F f
    rw [hJ] at hiff
    exact hiff.mp hdropSB
  · -- the slot functions are `±Ftop`
    intro i
    rcases htop ((X.stepIdx (Sum.inr 0) 0 (h.pLive 0) i).1.1) with hF | hF
    · by_cases hε : (X.stepIdx (Sum.inr 0) 0 (h.pLive 0) i).1.2
      · right
        intro x
        show (if (X.stepIdx (Sum.inr 0) 0 (h.pLive 0) i).1.2 = true then star (F ((X.stepIdx (Sum.inr 0) 0 (h.pLive 0) i).1.1) x) else F ((X.stepIdx (Sum.inr 0) 0 (h.pLive 0) i).1.1) x) = star (Ftop x)
        rw [if_pos hε]
        exact congrArg star (hF x)
      · left
        intro x
        show (if (X.stepIdx (Sum.inr 0) 0 (h.pLive 0) i).1.2 = true then star (F ((X.stepIdx (Sum.inr 0) 0 (h.pLive 0) i).1.1) x) else F ((X.stepIdx (Sum.inr 0) 0 (h.pLive 0) i).1.1) x) = Ftop x
        rw [if_neg hε]
        exact hF x
    · by_cases hε : (X.stepIdx (Sum.inr 0) 0 (h.pLive 0) i).1.2
      · left
        intro x
        show (if (X.stepIdx (Sum.inr 0) 0 (h.pLive 0) i).1.2 = true then star (F ((X.stepIdx (Sum.inr 0) 0 (h.pLive 0) i).1.1) x) else F ((X.stepIdx (Sum.inr 0) 0 (h.pLive 0) i).1.1) x) = Ftop x
        rw [if_pos hε, hF x, star_star]
      · right
        intro x
        show (if (X.stepIdx (Sum.inr 0) 0 (h.pLive 0) i).1.2 = true then star (F ((X.stepIdx (Sum.inr 0) 0 (h.pLive 0) i).1.1) x) else F ((X.stepIdx (Sum.inr 0) 0 (h.pLive 0) i).1.1) x) = star (Ftop x)
        rw [if_neg hε]
        exact hF x
  · -- the base function
    rcases htop ⟨((Sum.inr 0 : InitIdx d), 0), h.pLive 0⟩ with hF | hF
    · refine ⟨false, fun a x => ?_⟩
      show ((((X.toSym).S.toPetP ⌊γ' * (M : ℝ)⌋.toNat F f).step ⟨((Sum.inr 0 : InitIdx d), 0), h.pLive 0⟩ ⌊γ' * (M : ℝ)⌋.toNat).drop ∅).f a x = Ftop x
      rw [histCloseStep_base X ⌊γ' * (M : ℝ)⌋.toNat F f (h.pLive 0) a x]
      exact hF x
    · refine ⟨true, fun a x => ?_⟩
      show ((((X.toSym).S.toPetP ⌊γ' * (M : ℝ)⌋.toNat F f).step ⟨((Sum.inr 0 : InitIdx d), 0), h.pLive 0⟩ ⌊γ' * (M : ℝ)⌋.toNat).drop ∅).f a x = star (Ftop x)
      rw [histCloseStep_base X ⌊γ' * (M : ℝ)⌋.toNat F f (h.pLive 0) a x]
      exact hF x

end

end Work.Peluse.UControl
