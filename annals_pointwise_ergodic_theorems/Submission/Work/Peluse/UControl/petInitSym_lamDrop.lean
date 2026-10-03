import Mathlib
import Submission.Work.Peluse.UControl.petInitSym_lam

/-!
# The initial symbolic PET state, after dropping the constant slots

`petInitSym_lam` identifies the correlation of the initial symbolic state `petInitSym P` with
`‖LambdaMD N M P F‖`.  The analytic chain of `PetInv`/`petStepLink`, however, always runs on the
*dropped* state `SymState.dropC X` (the constant slots are absorbed into the base function before
each PET step, so that the weight vector strictly decreases).

Here the two initial states are identified: the initial state has no constant slot
(`SymState.consts (petInitSym P) = ∅`, because every slot polynomial `X^(i+1)`, `1 ≤ i ≤ d-1`, and
`P` itself has degree `≥ 1`), so `dropC` removes nothing and the index type shrinks only to the
subtype `{i : ι // i ∈ ∅ᶜ}` of the full index type.  The correlation is read through that subtype
with `Finset.prod_coe_sort`, and the resulting state is the one of `petInitSym_lam`.
-/

set_option autoImplicit false
open scoped BigOperators

namespace Work.Peluse.UControl

open Work.Peluse.UControl.PetStep

noncomputable section

/-- **Dropping an empty set of slots does not change the correlation.**

If `J = ∅` then the index type of `PetStateSym.dropSym S J` is the subtype
`{i : S.ι // i ∈ (∅ : Finset S.ι)ᶜ}` of the full index type and its slot polynomials are those of
`S`, so the product over the slots is the same as the product over `S.ι` (`Finset.prod_coe_sort`,
after which `(∅ : Finset S.ι)ᶜ = Finset.univ`).  Everything is read through the subtype, so the
statement is an ordinary identity of correlations — no transport along the (propositional, not
definitional) equality `J = ∅` of the index types is involved. -/
lemma toPetP_dropSym_empty_lam {n : ℕ} (S : PetStateSym n) (J : Finset S.ι) (hJ : J = ∅)
    (H N M : ℕ) (F : S.ι → ℤ → ℂ) (f : WinTower H n → ℤ → ℂ) :
    ((PetStateSym.dropSym S J).toPetP H (fun i => F i.1) f).toState.lam N M
      = (S.toPetP H F f).toState.lam N M := by
  rw [PetStateP.lam_eq, PetStateP.lam_eq]
  unfold PetStateP.lam
  refine Finset.sum_congr rfl (fun a _ => ?_)
  have hν : ((PetStateSym.dropSym S J).toPetP H (fun i => F i.1) f).ν a
      = (S.toPetP H F f).ν a := rfl
  rw [hν]
  refine congrArg (fun t : ℝ => (S.toPetP H F f).ν a * t) ?_
  refine congrArg (fun z : ℂ => ‖z‖) ?_
  refine congrArg (fun z : ℂ => ((N : ℂ) * (M : ℂ))⁻¹ * z) ?_
  refine tsum_congr (fun x => ?_)
  refine congrArg (fun z : ℂ => (S.toPetP H F f).f a x * z) ?_
  refine Finset.sum_congr rfl (fun y _ => ?_)
  change ∏ i : ↥(Jᶜ),
      (fun i => F i.1) i
        (x + (((S.P i.1)).map (MvPolynomial.eval (WinTower.param H n a))).eval (y : ℤ))
      = ∏ i : S.ι, F i (x + ((S.P i).map (MvPolynomial.eval (WinTower.param H n a))).eval (y : ℤ))
  rw [Finset.prod_coe_sort (Jᶜ)
      (fun i => F i (x + ((S.P i).map (MvPolynomial.eval (WinTower.param H n a))).eval (y : ℤ)))]
  rw [hJ, Finset.compl_empty]

/-- The initial symbolic state has no constant slot: every slot polynomial `X ^ (i.val + 1)`
(`i : Fin (P.natDegree - 1)`) has degree `i.val + 1 ≥ 1`, and the slot `P` has degree
`P.natDegree ≥ 1` by hypothesis. -/
lemma petInitSym_consts (P : Polynomial ℤ) (hd : 1 ≤ P.natDegree) :
    SymState.consts (petInitSym P) = ∅ := by
  rw [SymState.consts, Finset.filter_eq_empty_iff]
  rintro (i | i) _
  · show ((Polynomial.X ^ (i.val + 1)).map
        (MvPolynomial.C : ℤ →+* MvPolynomial (Fin 0) ℤ)).natDegree ≠ 0
    rw [Polynomial.map_pow, Polynomial.map_X, Polynomial.natDegree_X_pow]
    omega
  · show (P.map (MvPolynomial.C : ℤ →+* MvPolynomial (Fin 0) ℤ)).natDegree ≠ 0
    rw [Polynomial.natDegree_map_eq_of_injective (MvPolynomial.C_injective (Fin 0) ℤ)]
    omega

/-- **The initial symbolic state computes `LambdaMD` also after the constant slots are dropped.**

Since `SymState.consts (petInitSym P) = ∅`, the state `SymState.dropC (petInitSym P)` is the initial
state `petInitSym P` with its index type read through the subtype `{i // i ∈ ∅ᶜ}`, so its
correlation is unchanged (`toPetP_dropSym_empty_lam`) and equal to `‖LambdaMD N M P F‖`
(`petInitSym_lam`). -/
theorem petInitSym_lamDrop (P : Polynomial ℤ) (hd : 1 ≤ P.natDegree) (N M H : ℕ)
    (F : Fin (P.natDegree + 1) → ℤ → ℂ) :
    ((SymState.dropC (petInitSym P)).S.toPetP H (fun j => petInitSlotF P F j.1)
        (petInitBase H P F)).toState.lam N M = ‖LambdaMD N M P F‖ := by
  exact (toPetP_dropSym_empty_lam (petInitSym P).S (SymState.consts (petInitSym P))
      (petInitSym_consts P hd) H N M (petInitSlotF P F)
      (petInitBase H P F)).trans (petInitSym_lam P hd N M H F)

end

end Work.Peluse.UControl
