import Mathlib
import Submission.Work.Peluse.UControl.petInitDefs

namespace Work.Peluse.UControl

open Work.Peluse.UControl.PetStep

noncomputable section

theorem petInitSym_SB (P : Polynomial ℤ) (N M H c D : ℕ) (F : Fin (P.natDegree + 1) → ℤ → ℂ)
    (hSB : Work.Peluse.UControl.PetStep.PetState.ShiftBound
      (Work.Peluse.UControl.PetStep.LambdaMDPetState N M P F) N M c D) :
    Work.Peluse.UControl.PetStep.PetState.ShiftBound
      (((SymState.dropC (petInitSym P)).S.toPetP H (fun j => petInitSlotF P F j.1)
        (petInitBase H P F)).toState) N M c D := by
  classical
  -- The initial symbolic state has no formal parameters, so evaluating its slot polynomials at the
  -- (unique) tower point does nothing: the concrete `Q` of the dropped initial state is literally
  -- the `Q` of `LambdaMDPetState`, read through the subtype index.
  intro i a z hz
  have hcomp : (MvPolynomial.eval (WinTower.param H 0 a) :
        MvPolynomial (Fin 0) ℤ →+* ℤ).comp MvPolynomial.C = RingHom.id ℤ := by
    ext r; simp
  have key : ∀ (k : Fin (P.natDegree - 1) ⊕ Fin 1),
      (((petInitSym P).S.P k).map (MvPolynomial.eval (WinTower.param H 0 a))).eval z
        = (LambdaMDPetState N M P F).Q k (0 : Fin 1) z := by
    intro k
    rcases k with k | k
    · show ((((Polynomial.X : Polynomial ℤ) ^ (k.val + 1)).map (MvPolynomial.C)).map
        (MvPolynomial.eval (WinTower.param H 0 a))).eval z = z ^ (k.val + 1)
      simp
    · show (((P.map (MvPolynomial.C)).map
        (MvPolynomial.eval (WinTower.param H 0 a)))).eval z = P.eval z
      rw [Polynomial.map_map, hcomp, Polynomial.map_id]
  change |(((petInitSym P).S.P i.1).map (MvPolynomial.eval (WinTower.param H 0 a))).eval z|
      ≤ (D : ℤ) * (N : ℤ)
  rw [key i.1]
  exact hSB i.1 (0 : Fin 1) z hz

end

end Work.Peluse.UControl
