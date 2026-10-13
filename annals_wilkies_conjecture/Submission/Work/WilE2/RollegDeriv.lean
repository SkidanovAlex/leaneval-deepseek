/-
  Work.WilE2 — area E2.  Derivatives of the graph function and of evaluated polynomials.

  * `fderiv_rolleg_apply` : the derivative of `g = rolleg S` — in the `x`-directions it is the
    corresponding `η` entry `a_{s+1,i} ψ_{s+1}`, in the new coordinate it is `-1`;
  * `fderiv_ev_single` : the Fréchet derivative of an evaluated EA polynomial on a basis vector
    is the evaluated symbolic derivative `S.d i`.
-/
import Mathlib
import Submission.Work.WilE2.RegSol

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

namespace Work.WilE2

open Classical
open WilkiesDesign WilkiesDesign.E WilkiesConjecture

variable {n s : ℕ}

theorem fderiv_rolleg_apply (S : ESys n (s + 1)) (z : Fin (n + 1) → ℝ) :
    (∀ i : Fin n, fderiv ℝ (rolleg S) z (Pi.single (Fin.castSucc i) 1)
        = S.a (Fin.last s) i * S.lastPsi (Fin.init z)) ∧
      (fderiv ℝ (rolleg S) z (Pi.single (Fin.last n) 1) = -1) := by
  have hd1 : ∀ w : Fin (n + 1) → ℝ, HasFDerivAt (fun z : Fin (n + 1) → ℝ => (S.ravel).psi (Fin.last s) z)
      ((S.ravel).psi (Fin.last s) w • (S.ravel).ellGrad (Fin.last s)) w :=
    fun w => ESys.hasFDerivAt_psi S.ravel (Fin.last s) w
  have hd2 : ∀ w : Fin (n + 1) → ℝ, HasFDerivAt (fun z : Fin (n + 1) → ℝ => z (Fin.last n))
      (ContinuousLinearMap.proj (Fin.last n) : (Fin (n + 1) → ℝ) →L[ℝ] ℝ) w :=
    fun w => ContinuousLinearMap.hasFDerivAt (ContinuousLinearMap.proj (Fin.last n) :
      (Fin (n + 1) → ℝ) →L[ℝ] ℝ) (x := w)
  have hdiff : HasFDerivAt (fun z : Fin (n + 1) → ℝ => (S.ravel).psi (Fin.last s) z - z (Fin.last n))
      (((S.ravel).psi (Fin.last s) z • (S.ravel).ellGrad (Fin.last s)) -
        (ContinuousLinearMap.proj (Fin.last n) : (Fin (n + 1) → ℝ) →L[ℝ] ℝ)) z :=
    (hd1 z).sub (hd2 z)
  constructor
  · intro i
    rw [rolleg_eq_ravel S, hdiff.fderiv]
    rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, ESys.ellGrad_apply,
      ContinuousLinearMap.proj_apply, Pi.single_eq_of_ne (Fin.castSucc_ne_last i).symm, sub_zero]
    have hsum : (∑ a : Fin (n + 1), (S.ravel).a (Fin.last s) a *
        (Pi.single (Fin.castSucc i) 1 : Fin (n + 1) → ℝ) a) = S.a (Fin.last s) i := by
      refine (Finset.sum_eq_single (Fin.castSucc i) ?_ ?_).trans ?_
      · intro b _ hb
        rw [Pi.single_eq_of_ne hb, mul_zero]
      · intro h; exact absurd (Finset.mem_univ _) h
      · rw [Pi.single_eq_same, mul_one, ESys.ravel_a_castSucc]
    rw [hsum, smul_eq_mul, ESys.ravel_psi, mul_comm, ESys.lastPsi]
  · rw [rolleg_eq_ravel S, hdiff.fderiv]
    rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, ESys.ellGrad_apply,
      ContinuousLinearMap.proj_apply, Pi.single_eq_same]
    have hsum : (∑ a : Fin (n + 1), (S.ravel).a (Fin.last s) a *
        (Pi.single (Fin.last n) 1 : Fin (n + 1) → ℝ) a) = 0 := by
      refine Finset.sum_eq_zero fun a _ => ?_
      rcases Fin.eq_castSucc_or_eq_last a with ⟨j, rfl⟩ | rfl
      · rw [Pi.single_eq_of_ne (Fin.castSucc_ne_last j), mul_zero]
      · rw [ESys.ravel_a_last, zero_mul]
    rw [hsum, smul_eq_mul, mul_zero, zero_sub]

theorem fderiv_ev_single (S : ESys n s) (P : EPoly n s) (x : Fin n → ℝ) (i : Fin n) :
    fderiv ℝ (S.ev P) x (Pi.single i 1) = S.ev (S.d i P) x := by
  rw [(ev_hasFDerivAt S P x).fderiv, ESys.grad_apply]
  refine (Finset.sum_eq_single i ?_ ?_).trans ?_
  · intro b _ hb
    rw [Pi.single_eq_of_ne hb, mul_zero]
  · intro h; exact absurd (Finset.mem_univ i) h
  · rw [Pi.single_eq_same, mul_one]

end Work.WilE2
