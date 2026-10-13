import Mathlib
import Submission.Work.CoreStep.sigmaFamily_len
import Submission.Work.WilE7.CoreStep.CoreLTSuccNodes

set_option autoImplicit false
noncomputable section
open Classical Filter Topology

namespace Work.WilE7.Endgame

open WilkiesDesign WilkiesDesign.E
open Work.WilE7.MainDesign

/-! ## Helpers for the length accounting of `sigmaFamily_len_unif` -/

/-- The `MvPolynomial.eval` of the substitution of the univariate polynomial `p` into the
variable `X 0` (evaluated at `f`) is the evaluation of `p` at `f 0`. -/
theorem mv_eval_aeval_X0 (f : Fin 2 → ℕ) (p : Polynomial ℕ) :
    MvPolynomial.eval f (Polynomial.aeval (MvPolynomial.X 0) p) = p.eval (f 0) := by
  have h := Polynomial.aeval_algHom_apply (MvPolynomial.aeval f) (MvPolynomial.X 0) p
  rw [MvPolynomial.aeval_X] at h
  exact h.symm

/-- Length of a `flatMap`: if all the fibres are bounded by `B`, the total length is at most
`l.length * B`. -/
theorem length_flatMap_le {α β : Type*} (l : List α) (f : α → List β) (B : ℕ)
    (h : ∀ a ∈ l, (f a).length ≤ B) : (l.flatMap f).length ≤ l.length * B := by
  induction l with
  | nil => simp
  | cons a t ih =>
      rw [List.flatMap_cons, List.length_append, List.length_cons]
      have ha : (f a).length ≤ B := h a (by simp)
      have ht : (t.flatMap f).length ≤ t.length * B := ih (fun b hb => h b (by simp [hb]))
      calc (f a).length + (t.flatMap f).length ≤ B + t.length * B := Nat.add_le_add ha ht
        _ = (t.length + 1) * B := by ring

end Work.WilE7.Endgame
