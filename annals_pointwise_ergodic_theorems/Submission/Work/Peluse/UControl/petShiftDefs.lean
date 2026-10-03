import Mathlib
import Submission.Work.Peluse.UControl.histPhase1Inv
import Submission.Work.Peluse.UControl.petHistInit_inv
import Submission.Work.Peluse.UControl.petQuad2Defs

/-!
# The shift-bound vocabulary of the PET chapter (`PetChapter5`)

The conclusion of `PetChapter5` requires a **sharp** shift bound at the terminal state
`histTerminal P hd` of the phase-1 chain: `|Q i a z| ≤ Cne · N` with `Cne ≤ Cne₀ · A` for a
constant `Cne₀` depending on `P` alone.  The analytic chain (`HistInv`) tracks only the *coarse*
bound (`PetState.ShiftBound` with the range `c·M` and the constant `D ≈ A/γ`), which is useless for
this purpose; the sharp bound is proved directly from the structure of the terminal slot
polynomials.

The tool is the following coefficient-wise bound: every coefficient `Q.coeff j` of a slot polynomial
`Q` (a polynomial in the `n` tower parameters) is bounded by `C · B^{d - j}` on the box
`|a_s| ≤ B`.  It is preserved by the PET step (composition with `X + ε a_new` multiplies the
`j`-th coefficient by terms of degree `j' - j` in the parameters, and the leading degree `d - j` is
exactly the invariant), and at the terminal state it yields
`|Q(a,z)| ≤ C · d · γ · M^d ≤ C · d · A · N` for `|z| ≤ M` and `|a_s| ≤ γ M`, using
`M^d ≤ A γ⁻¹ N`.

* `coeffBd d C Q` — the coefficient bound;
* `histTerminal P hd` — the terminal state of the phase-1 chain of `P` (after the closing step).
-/

set_option autoImplicit false
open scoped BigOperators

namespace Work.Peluse.UControl

noncomputable section

open Polynomial

/-- **The coefficient-wise bound on a slot polynomial.**  For every bound `B ≥ 1` on the tower
parameters `a : Fin n → ℤ` and every `j`, the `j`-th `y`-coefficient of `Q` is bounded by
`C · B^{d - j}`. -/
def coeffBd (d : ℕ) (C : ℝ) {n : ℕ} (Q : Polynomial (MvPolynomial (Fin n) ℤ)) : Prop :=
  ∀ (B : ℝ), 1 ≤ B → ∀ (a : Fin n → ℤ), (∀ s, |a s| ≤ B) →
    ∀ j : ℕ, ‖(Q.coeff j).eval a‖ ≤ C * B ^ (d - j)

/-- The initial state of the history-indexed chain, as an `HState`. -/
def petHistInitState (P : Polynomial ℤ) (hd : 1 ≤ P.natDegree) : HState P.natDegree :=
  ⟨0, petHistInit P hd⟩

/-- The number of histories of the terminal state of the phase-1 chain. -/
def petTermLen (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) : ℕ :=
  (phase1Chain (petHistInitState P (by omega))).1

lemma petTermLen_eq (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) :
    petTermLen P hd = histLen (petHistInitState P (by omega)) := by
  rw [petTermLen, phase1Chain_fst, petHistInitState]
  simp

/-- **The terminal state of the phase-1 chain** of `P`: the state reached after the phase-1 chain
has ended (`Phase1Done`) and the closing step (Peluse's Lemma 4.5) has been performed.  Its live
slots are the `(P, h)` with `h ≠ 0`, of `y`-degree `d - 1` and leading coefficient
`C d · C (lc P) · shift h` (`Phase1Terminal`). -/
def histTerminal (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) :
    HistData P.natDegree (petTermLen P hd + 1) :=
  HistData.step (phase1Chain (petHistInitState P (by omega))).2 (Sum.inr 0) 0
    ((histPhase1Inv hd P.leadingCoeff (petHistInitState P (by omega))
      (petHistInit_phase1 P (by omega))).pLive 0)

/-- The terminal state is `Phase1Terminal` (Peluse's Lemma 4.5). -/
theorem histTerminal_phase1Terminal (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree)
    (hlc : P.leadingCoeff ≠ 0) :
    Phase1Terminal P.natDegree _ P.leadingCoeff (histTerminal P hd) := by
  have hPh1 : Phase1 P.natDegree 0 P.leadingCoeff (petHistInit P (by omega)) :=
    petHistInit_phase1 P (by omega)
  have hdone := phase1Chain_done hd P.leadingCoeff
    (⟨0, petHistInit P (by omega)⟩ : HState P.natDegree) hPh1
  have hh := histPhase1Inv hd P.leadingCoeff
    (⟨0, petHistInit P (by omega)⟩ : HState P.natDegree) hPh1
  exact histPhase1Terminal hd hlc _ hh hdone ⟨_, hh.pLive 0⟩

/-- The number of histories at the terminal state is at least two. -/
theorem two_le_petTermLen_add_one (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) :
    2 ≤ petTermLen P hd + 1 := by
  rw [petTermLen_eq]
  have hPh1 : Phase1 P.natDegree 0 P.leadingCoeff (petHistInit P (by omega)) :=
    petHistInit_phase1 P (by omega)
  have hgo : HState.Go (petHistInitState P (by omega)) := by
    intro hh
    rcases hh with hl | hdone
    · exact Phase1.not_linear hd hPh1 hl
    · have hmem : ((Sum.inl (⟨0, by omega⟩ : Fin (P.natDegree - 1))), (0 : Fin 0 → Bool))
          ∈ (petHistInitState P (by omega)).2.H := Finset.mem_univ _
      exact Sum.inl_ne_inr (hdone _ hmem)
  have := histLen_eq_not (petHistInitState P (by omega)) hgo
  omega

/-- **A dummy datum for the degenerate case `P.natDegree ≤ 1`**, where `Phase1Terminal` states do
not exist but `PetChapter5` still has to produce *some* datum with `2 ≤ |I (d-1)|`. -/
def twoS : ℕ → Type
  | 0 => Fin 2
  | _ => PEmpty

instance twoS.instFintype (j : ℕ) : Fintype (twoS j) := by unfold twoS; split <;> infer_instance

instance twoS.instDecidableEq (j : ℕ) : DecidableEq (twoS j) := by
  unfold twoS; split <;> infer_instance

/-- The dummy `IdxDatum` with two level-`0` slots. -/
def twoDatum : IdxDatum where
  S := twoS
  finS := fun j => twoS.instFintype j
  decS := fun j => twoS.instDecidableEq j
  par := fun j => by
    rcases j with _ | j
    · exact fun s => nomatch s
    · exact fun s => nomatch s

/-- The level-`0` index set of the dummy datum has `3 ≥ 2` elements. -/
theorem twoDatum_card_I_zero : 2 ≤ Fintype.card (twoDatum.I 0) := by
  have h : Fintype.card (twoDatum.I 0)
      = Fintype.card {T : Finset (twoS 0) // T.Nonempty} := rfl
  rw [h, Fintype.card_subtype]
  have hf : (Finset.univ.filter (fun T : Finset (twoS 0) => T.Nonempty))
      = (Finset.univ : Finset (Finset (twoS 0))).erase ∅ := by
    ext T
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
    constructor
    · intro hne; exact ⟨Finset.nonempty_iff_ne_empty.mp hne, trivial⟩
    · rintro ⟨hne, -⟩; exact Finset.nonempty_iff_ne_empty.mpr hne
  rw [hf, Finset.card_erase_of_mem (Finset.mem_univ (∅ : Finset (twoS 0))), Finset.card_univ]
  have h2 : Fintype.card (Finset (twoS 0)) = 4 := by
    rw [Fintype.card_finset]
    have : Fintype.card (twoS 0) = 2 := rfl
    rw [this]; norm_num
  rw [h2]; norm_num

end

end Work.Peluse.UControl
