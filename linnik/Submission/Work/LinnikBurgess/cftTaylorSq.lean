import Mathlib

namespace Work.LinnikBurgess

lemma cftTaylorSq (G : Polynomial ℤ) (x y : ℤ) :
    (x - y) ^ 2 ∣ (G.eval x - G.eval y - (x - y) * G.derivative.eval y) := by
  obtain ⟨Q, hQ⟩ :
      ∃ Q : Polynomial ℤ, G - Polynomial.C (G.eval y) = (Polynomial.X - Polynomial.C y) * Q :=
    Polynomial.X_sub_C_dvd_sub_C_eval
  have hG : G = Polynomial.C (G.eval y) + (Polynomial.X - Polynomial.C y) * Q := by
    rw [← hQ]; ring
  have hderiv : G.derivative = Q + (Polynomial.X - Polynomial.C y) * Q.derivative := by
    rw [hG, Polynomial.derivative_add, Polynomial.derivative_C, Polynomial.derivative_mul,
      Polynomial.derivative_sub, Polynomial.derivative_X, Polynomial.derivative_C]
    ring
  have hQy : G.derivative.eval y = Q.eval y := by
    rw [hderiv]; simp
  have heval : G.eval x - G.eval y = (x - y) * Q.eval x := by
    have := congrArg (fun p : Polynomial ℤ => p.eval x) hQ
    simpa using this
  obtain ⟨W, hW⟩ := Polynomial.sub_dvd_eval_sub x y Q
  refine ⟨W, ?_⟩
  rw [hQy, heval, ← mul_sub, hW]
  ring

end Work.LinnikBurgess
