import Mathlib
import Submission.Work.MotK.TwRuling.sexticTw_notMem_kernel

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotK.TwRuling

/-- Evaluation at a point commutes with `kleinTwP`: the value of the `k`-th twisted Pfaffian at
the family of polynomials `X` is obtained by substituting the point coordinates into the
coefficients. -/
private lemma aeval_kleinTwP_point {R : Type} [CommRing R] (a b h : R) (p : Fin 5 → R)
    (k : Fin 5) :
    MvPolynomial.aeval p (Work.MotK.kleinTwP (MvPolynomial.C a) (MvPolynomial.C b)
        (MvPolynomial.C h) (fun i => MvPolynomial.X i) k)
      = Work.MotK.kleinTwP a b h p k := by
  fin_cases k <;>
    simp only [Work.MotK.kleinTwP, Work.MotK.kleinTwP0, Work.MotK.kleinTwP1, Work.MotK.kleinTwP2,
      Work.MotK.kleinTwP3, Work.MotK.kleinTwP4, Fin.isValue, Matrix.cons_val_zero',
      Matrix.cons_val_succ']
  all_goals simp

/-- If `p = (a, 0, -a, -b, b)` is a common zero of the five twisted Pfaffians, then it annihilates
the whole degree-six part `twIdeal6 R a b 1` of the twisted Pfaffian ideal: evaluation at `p` is a
ring homomorphism, so it kills every generator of the span. -/
theorem twIdeal6_aeval_point {R : Type} [Field R] (a b : R)
    (hx : ∀ k : Fin 5, Work.MotK.kleinTwP a b 1 ![a, 0, -a, -b, b] k = 0) :
    ∀ F ∈ Work.MotK.TwRuling.twIdeal6 R a b 1,
      MvPolynomial.aeval ![a, 0, -a, -b, b] F = 0 := by
  intro F hF
  rw [twIdeal6] at hF
  refine Submodule.span_induction (p := fun x _ => MvPolynomial.aeval ![a, 0, -a, -b, b] x = 0)
    ?_ ?_ ?_ ?_ hF
  · rintro x ⟨q, rfl⟩
    rw [map_mul, aeval_kleinTwP_point a b 1 ![a, 0, -a, -b, b] q.1, hx q.1, zero_mul]
  · simp
  · intro x y _ _ hx' hy'
    rw [map_add, hx', hy', add_zero]
  · intro c x _ hx'
    rw [map_smul, hx', smul_zero]

end Work.MotK.TwRuling
