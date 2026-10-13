import Mathlib
import Submission.Work.WilE2.KhoSphereDefs

namespace Work.WilE2

open WilkiesDesign WilkiesDesign.E

/-- Evaluation of the "sphere" polynomial `∑ x_k² + ψ_s² - c` at an arbitrary point of
`Fin (n+1) ⊕ Fin (s+1) → ℝ`: only the coordinates occur, the chain variables only through the
last one. -/
theorem eval_spherePoly {n s : ℕ} (c : ℝ) (f : Fin (n + 1) ⊕ Fin (s + 1) → ℝ) :
    MvPolynomial.eval f (spherePoly (n := n) (s := s) c)
      = (∑ k : Fin (n + 1), (f (Sum.inl k)) ^ 2) + (f (Sum.inr (Fin.last s))) ^ 2 - c := by
  simp only [spherePoly, map_add, map_sum, map_mul, MvPolynomial.eval_X, MvPolynomial.eval_C]
  simp [pow_two, sub_eq_add_neg]

/-- The last component of the lifted system of `newF F c` (which is the sphere equation)
evaluates to `∑_{k<n+1} v_k² + v_{n+1}² - c` — i.e. the last chain function is replaced by the
new coordinate `v (Fin.last (n+1))`. -/
theorem liftSystem_ravel_newF_last {n s : ℕ} (S : ESys n (s + 1))
    (F : Fin n → EPoly n (s + 1)) (c : ℝ) (v : Fin (n + 2) → ℝ) :
    liftSystem (S.ravel) (newF (n := n) (s := s) F c) v (Fin.last n)
      = (∑ k : Fin (n + 1), (v (Fin.castSucc k)) ^ 2) + (v (Fin.last (n + 1))) ^ 2 - c := by
  have h1 : liftSystem (S.ravel) (newF (n := n) (s := s) F c) v (Fin.last n)
      = ((S.ravel).liftChain).ev (liftP (spherePoly (n := n) (s := s) c)) v := by
    simp [liftSystem]
  rw [h1]
  conv_lhs => rw [← Fin.snoc_init_self v]
  rw [ESys.ev_liftP, eval_spherePoly]
  simp [ESys.liftEval, Fin.lastCases_last, Fin.init]

/-- The last component of the lifted system of `newF F c` is the sphere equation
`∑_j w_j² - c`; the last chain function has become the last coordinate. -/
theorem liftSystem_last_apply {n s : ℕ} (S : ESys n (s + 1)) (F : Fin n → EPoly n (s + 1))
    (c : ℝ) (w : Fin (n + 2) → ℝ) :
    liftSystem (S.ravel) (newF (n := n) (s := s) F c) w (Fin.last n)
      = (∑ j : Fin (n + 2), (w j) ^ 2) - c := by
  rw [liftSystem_ravel_newF_last S F c w,
    Fin.sum_univ_castSucc (fun j : Fin (n + 2) => (w j) ^ 2)]

end Work.WilE2
