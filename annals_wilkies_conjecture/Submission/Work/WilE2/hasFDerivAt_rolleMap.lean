import Mathlib
import Submission.Work.WilE2.KhoGood
import Submission.Work.WilE2.RegSol
import Submission.Work.WilE2.ev_hasFDerivAt

namespace Work.WilE2

theorem hasFDerivAt_rolleMap {n s : ℕ} (S : ESys n (s + 1)) (F : Fin n → EPoly n (s + 1))
    (z : Fin (n + 1) → ℝ) :
    HasFDerivAt (rolleMap S F)
      (ContinuousLinearMap.pi (Fin.snoc
        (fun i : Fin n => fderiv ℝ (fun w => liftSystem S F w i) z)
        (fderiv ℝ (rolleDetFun S F) z))) z := by
  -- Each coordinate of the lifted system is differentiable, with derivative given by
  -- the symbolic derivative `liftChain.grad` of `ev_hasFDerivAt`.
  have hcomp : ∀ i : Fin n, HasFDerivAt (fun w : Fin (n + 1) → ℝ => liftSystem S F w i)
      (fderiv ℝ (fun w : Fin (n + 1) → ℝ => liftSystem S F w i) z) z := by
    intro i
    have h := ev_hasFDerivAt S.liftChain (liftP (F i)) z
    change HasFDerivAt (fun w : Fin (n + 1) → ℝ => (S.liftChain).ev (liftP (F i)) w)
      (fderiv ℝ (fun w : Fin (n + 1) → ℝ => (S.liftChain).ev (liftP (F i)) w) z) z
    rw [h.fderiv]
    exact h
  -- The Rolle determinant is differentiable as well.
  have hdet : HasFDerivAt (rolleDetFun S F) (fderiv ℝ (rolleDetFun S F) z) z := by
    have h := ev_hasFDerivAt S.liftChain (S.rolleDet F) z
    change HasFDerivAt (fun w : Fin (n + 1) → ℝ => (S.liftChain).ev (S.rolleDet F) w)
      (fderiv ℝ (fun w : Fin (n + 1) → ℝ => (S.liftChain).ev (S.rolleDet F) w) z) z
    rw [h.fderiv]
    exact h
  -- `rolleMap` is the `Fin.snoc` of the lifted system and the Rolle determinant, so we work
  -- coordinatewise.
  refine hasFDerivAt_pi'' (Φ := rolleMap S F)
    (Φ' := ContinuousLinearMap.pi (Fin.snoc
        (fun i : Fin n => fderiv ℝ (fun w => liftSystem S F w i) z)
        (fderiv ℝ (rolleDetFun S F) z))) (fun i => ?_)
  rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
  · have hproj : (ContinuousLinearMap.proj (Fin.castSucc j) : ((Fin (n + 1) → ℝ) →L[ℝ] ℝ)) ∘SL
        (ContinuousLinearMap.pi (Fin.snoc
          (fun i : Fin n => fderiv ℝ (fun w => liftSystem S F w i) z)
          (fderiv ℝ (rolleDetFun S F) z)))
        = fderiv ℝ (fun w => liftSystem S F w j) z := by
      ext v
      simp [Fin.snoc_castSucc]
    have heq : (fun x => rolleMap S F x (Fin.castSucc j)) = fun w => liftSystem S F w j := by
      funext x; exact rolleMap_apply_castSucc S F x j
    rw [heq, hproj]
    exact hcomp j
  · have hproj : (ContinuousLinearMap.proj (Fin.last n) : ((Fin (n + 1) → ℝ) →L[ℝ] ℝ)) ∘SL
        (ContinuousLinearMap.pi (Fin.snoc
          (fun i : Fin n => fderiv ℝ (fun w => liftSystem S F w i) z)
          (fderiv ℝ (rolleDetFun S F) z)))
        = fderiv ℝ (rolleDetFun S F) z := by
      ext v
      simp [Fin.snoc_last]
    have heq : (fun x => rolleMap S F x (Fin.last n)) = rolleDetFun S F := by
      funext x; exact rolleMap_apply_last S F x
    rw [heq, hproj]
    exact hdet

end Work.WilE2
