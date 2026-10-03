import Mathlib
import Submission.Work.Peluse.UControl.histStepTransfer
import Submission.Work.Peluse.UControl.petInitSym_lamDrop
import Submission.Work.Peluse.UControl.petInitSym_SB

/-!
# The analytic invariant at the initial state of the history-indexed chain

`HistInv` at `⟨0, petHistInit P hd⟩` with the initial slot/base functions, at the same data
`γ, D, c` as the `LambdaMD` state.  The two analytic fields (`hlam`, `hSB`) are read off
`LambdaMD` through the two identification lemmas of the symbolic initial state
(`petInitSym_lamDrop`, `petInitSym_SB`), transported along the slot equivalence
`petHistInitEquiv` between the history initial state `(petHistInit P hd).toSym` and the dropped
symbolic initial state `SymState.dropC (petInitSym P)`; the transport itself is the reusable
`hstLam_equiv`/`hstSlotsBound_congr` of `histStepTransfer`.  The remaining fields are the
hypotheses, and `hw` is copied verbatim.
-/

set_option autoImplicit false
open scoped BigOperators

namespace Work.Peluse.UControl

open Work.Peluse.UControl.PetStep

noncomputable section

attribute [local instance] Classical.propDecidable

/-- The slot equivalence between the initial state of the history-indexed chain and the dropped
initial symbolic state: the live slots of `petHistInit P hd` are the pairs `(j, h)` with
`h : Fin 0 → Bool` (a subsingleton) and `j : InitIdx d`, and `SymState.dropC (petInitSym P)` is
indexed by the same `j` (there is no constant slot to drop, `petInitSym_consts P hd`). -/
def petHistInitEquiv (P : Polynomial ℤ) (hd : 1 ≤ P.natDegree) :
    (((petHistInit P hd).toSym).S.ι) ≃ ((SymState.dropC (petInitSym P)).S.ι) where
  toFun x := ⟨x.1.1, Finset.mem_compl.mpr (by
    rw [petInitSym_consts P hd]
    exact Finset.notMem_empty _)⟩
  invFun j := ⟨(j.1, fun _ => false), Finset.mem_univ _⟩
  left_inv := by
    rintro ⟨⟨j, h⟩, hm⟩
    refine Subtype.ext (Prod.ext rfl ?_)
    funext i
    exact i.elim0
  right_inv := by
    rintro ⟨j, hj⟩
    exact Subtype.ext rfl

/-- The slot polynomials of the two initial states agree along the equivalence (both carry the
shifts `y^(i+1)` and `P`). -/
lemma petHistInitEquiv_P (P : Polynomial ℤ) (hd : 1 ≤ P.natDegree) :
    ∀ i : (((petHistInit P hd).toSym).S.ι),
      ((SymState.dropC (petInitSym P)).S).P (petHistInitEquiv P hd i)
        = (((petHistInit P hd).toSym).S).P i := fun _ => rfl

/-- The slot functions agree along the equivalence. -/
lemma petHistInitEquiv_F (P : Polynomial ℤ) (hd : 1 ≤ P.natDegree)
    (F : Fin (P.natDegree + 1) → ℤ → ℂ) :
    ∀ i : (((petHistInit P hd).toSym).S.ι),
      (fun j => petInitSlotF P F j.1) (petHistInitEquiv P hd i)
        = (fun i => petInitSlotF P F i.1.1) i := fun _ => rfl

theorem petHistInit_inv (P : Polynomial ℤ) (hd : 1 ≤ P.natDegree) (N M : ℕ)
    (F : Fin (P.natDegree + 1) → ℤ → ℂ) (γ γ' : ℝ) (D c : ℕ)
    (hN : 0 < N) (hM : 0 < M) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1)
    (hγ'0 : 0 < γ') (hγ'1 : γ' ≤ 1)
    (hFb : ∀ i x, ‖F i x‖ ≤ 1) (hFs : ∀ i, SupportIn (F i) N)
    (hD : 1 ≤ D) (hc : histLen (⟨0, petHistInit P hd⟩ : HState P.natDegree) + 1 ≤ c)
    (hSB : (Work.Peluse.UControl.PetStep.LambdaMDPetState N M P F).ShiftBound N M c D)
    (hH : 1 ≤ ⌊γ' * (M : ℝ)⌋.toNat)
    (hw : ∀ k : ℕ, k < histLen (⟨0, petHistInit P hd⟩ : HState P.natDegree) →
      γ' ≤ petChainLevel γ k ^ 2 / (20000 * (((2 ^ k * D : ℕ) : ℝ) + 1)))
    (hLam : γ ≤ ‖LambdaMD N M P F‖) :
    HistInv N M γ' (petHistInit P hd)
      (fun i => petInitSlotF P F i.1.1)
      (petInitBase ⌊γ' * (M : ℝ)⌋.toNat P F) γ D c := by
  classical
  refine
    { hN := hN
      hM := hM
      hH := hH
      hγ'0 := hγ'0
      hγ'1 := hγ'1
      hγ0 := hγ0
      hγ1 := hγ1
      hc := hc
      hD := hD
      hFb := ?_
      hFs := ?_
      hfb := ?_
      hfs := ?_
      hlam := ?_
      hSB := ?_
      hw := hw }
  · rintro ⟨⟨j, h⟩, hm⟩ x
    rcases j with k | k <;> exact hFb _ x
  · rintro ⟨⟨j, h⟩, hm⟩
    rcases j with k | k <;> exact hFs _
  · intro a x
    exact hFb _ x
  · intro a
    exact hFs _
  · -- the correlation: transport to the dropped initial symbolic state, where it is `‖LambdaMD‖`
    have hlamEq := hstLam_equiv N M (((petHistInit P hd).toSym).S)
      ((SymState.dropC (petInitSym P)).S) (petHistInitEquiv P hd)
      (petHistInitEquiv_P P hd) (fun i => petInitSlotF P F i.1.1)
      (fun j => petInitSlotF P F j.1) (petHistInitEquiv_F P hd F)
      (petInitBase ⌊γ' * (M : ℝ)⌋.toNat P F) (petInitBase ⌊γ' * (M : ℝ)⌋.toNat P F)
      (fun _ => rfl)
    have h1 : ((((petHistInit P hd).toSym).S.toPetP ⌊γ' * (M : ℝ)⌋.toNat
        (fun i => petInitSlotF P F i.1.1)
        (petInitBase ⌊γ' * (M : ℝ)⌋.toNat P F)).toState.lam N M) = ‖LambdaMD N M P F‖ := by
      calc ((((petHistInit P hd).toSym).S.toPetP ⌊γ' * (M : ℝ)⌋.toNat
            (fun i => petInitSlotF P F i.1.1)
            (petInitBase ⌊γ' * (M : ℝ)⌋.toNat P F)).toState.lam N M)
          = ((((petHistInit P hd).toSym).S.toPetP ⌊γ' * (M : ℝ)⌋.toNat
              (fun i => petInitSlotF P F i.1.1)
              (petInitBase ⌊γ' * (M : ℝ)⌋.toNat P F)).lam N M) := PetStateP.lam_eq _ N M
        _ = (((SymState.dropC (petInitSym P)).S.toPetP ⌊γ' * (M : ℝ)⌋.toNat
              (fun j => petInitSlotF P F j.1)
              (petInitBase ⌊γ' * (M : ℝ)⌋.toNat P F)).lam N M) := hlamEq
        _ = (((SymState.dropC (petInitSym P)).S.toPetP ⌊γ' * (M : ℝ)⌋.toNat
              (fun j => petInitSlotF P F j.1)
              (petInitBase ⌊γ' * (M : ℝ)⌋.toNat P F)).toState.lam N M) :=
            (PetStateP.lam_eq _ N M).symm
        _ = ‖LambdaMD N M P F‖ := petInitSym_lamDrop P hd N M ⌊γ' * (M : ℝ)⌋.toNat F
    rw [h1]
    exact hLam
  · -- the shift bound: transport to the dropped initial symbolic state, where it is `hSB`
    have hT : hstSlotsBound ((SymState.dropC (petInitSym P)).S)
        ⌊γ' * (M : ℝ)⌋.toNat N M c D :=
      (hstSlotsBound_toPetP ((SymState.dropC (petInitSym P)).S)
        (fun j => petInitSlotF P F j.1)
        (petInitBase ⌊γ' * (M : ℝ)⌋.toNat P F)).mp
        (petInitSym_SB P N M ⌊γ' * (M : ℝ)⌋.toNat c D F hSB)
    have hS : hstSlotsBound (((petHistInit P hd).toSym).S)
        ⌊γ' * (M : ℝ)⌋.toNat N M c D :=
      (hstSlotsBound_congr (petHistInitEquiv P hd) (petHistInitEquiv_P P hd)).mp hT
    exact (hstSlotsBound_toPetP (((petHistInit P hd).toSym).S)
      (fun i => petInitSlotF P F i.1.1)
      (petInitBase ⌊γ' * (M : ℝ)⌋.toNat P F)).mpr hS

end

end Work.Peluse.UControl
