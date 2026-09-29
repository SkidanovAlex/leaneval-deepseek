import Mathlib
import Submission.Work.ZeroEst.subP_defs
import Submission.Work.ZeroEst.one_var_defs

namespace Work.ZeroEst

open Polynomial

/-! ## `subP c` is the substitution `X ↦ X + c` -/

lemma subP_eq_compRingHom (c : ℚ) :
    subP c = Polynomial.compRingHom (Polynomial.X + Polynomial.C c) := by
  apply Polynomial.ringHom_ext
  · intro a
    simp [subP]
  · simp [subP]

lemma subP_apply (c : ℚ) (Q : Polynomial ℚ) :
    subP c Q = Q.comp (Polynomial.X + Polynomial.C c) := by
  rw [subP_eq_compRingHom]; rfl

/-- `subP c` commutes with the (formal) derivative. -/
lemma subP_derivative (c : ℚ) (Q : Polynomial ℚ) :
    subP c (Polynomial.derivative Q) = Polynomial.derivative (subP c Q) := by
  rw [subP_apply, subP_apply, Polynomial.derivative_comp]
  simp

/-- `subP c` intertwines the coefficient operator `Λ` built from `(q, A)` with the one
built from `(subP c q, subP c ∘ A)`. -/
lemma subP_Lam {m : ℕ} (c : ℚ) (q : Polynomial ℚ) (A : Fin m → Fin m → Polynomial ℚ)
    (Q : Fin m → Polynomial ℚ) :
    Lam (subP c q) (fun i j => subP c (A i j)) (fun i => subP c (Q i))
      = fun i => subP c (Lam q A Q i) := by
  funext i
  simp only [Lam, map_add, map_mul, map_sum]
  rw [← subP_derivative]

/-- Iterating the previous lemma: `subP c` intertwines the orbits. -/
lemma subP_iterate {m : ℕ} (c : ℚ) (q : Polynomial ℚ) (A : Fin m → Fin m → Polynomial ℚ)
    (P : Fin m → Polynomial ℚ) (k : ℕ) :
    (fun i => subP c (((Lam q A)^[k]) P i)) =
      ((Lam (subP c q) (fun i j => subP c (A i j)))^[k]) (fun i => subP c (P i)) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih, subP_Lam]

theorem subP_orbit (c : ℚ) {m : ℕ} (q : Polynomial ℚ) (A : Fin m → Fin m → Polynomial ℚ)
    (P : Fin m → Polynomial ℚ) (k : ℕ) :
    (fun i => subP c (orbit q A P k i)) =
      orbit (subP c q) (fun i j => subP c (A i j)) (fun i => subP c (P i)) k := by
  simpa only [orbit] using subP_iterate c q A P k

end Work.ZeroEst
