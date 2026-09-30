import Mathlib
import Submission.Work.BW.Defs
import Submission.Work.BW.DefsMult

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- `derC` applied to the indicator vector `e₀ = Pi.single 0 1` is `∂/∂Y₀`. -/
lemma derC_piSingle (N : ℕ) :
    derC (N := N) (Pi.single (0 : Fin (N + 1)) (1 : ℂ))
      = MvPolynomial.pderiv (0 : Fin (N + 1)) := by
  funext Q
  simp only [derC, Pi.single_eq_same, map_one, one_mul]
  rw [Finset.sum_eq_zero]
  · simp
  · intro i _
    rw [Pi.single_eq_of_ne (Fin.succ_ne_zero i)]
    simp

/-- `derC` applied to the vector `(0, c₁, …, c_N)` is the invariant (Euler) derivation. -/
lemma derC_cons_zero_eq_eulerDer {N : ℕ} (c : Fin N → ℚ) :
    derC (N := N) (Fin.cons (0 : ℂ) (fun i : Fin N => ((c i : ℚ) : ℂ)))
      = eulerDer c := by
  funext Q
  simp only [derC, eulerDer, Fin.cons_zero, Fin.cons_succ, map_zero, zero_mul, zero_add]

theorem applyW_cons_eq_applyDer {r : ℕ} (c : Fin (r - 1) → Fin r → ℚ)
    (t : Fin (r - 1 + 1) → ℕ) (P : MvPolynomial (Fin (r + 1)) ℂ) :
    applyW (N := r) (q := r - 1 + 1)
      (Fin.cons (Pi.single (0 : Fin (r + 1)) (1 : ℂ))
        (fun m : Fin (r - 1) => Fin.cons 0 (fun i : Fin r => ((c m i : ℚ) : ℂ))))
      t P = applyDer c (t 0) (fun m : Fin (r - 1) => t m.succ) P := by
  simp only [applyW, applyDer]
  have hWs : ∀ m : Fin (r - 1),
      derC (N := r) (((Fin.cons (Pi.single (0 : Fin (r + 1)) (1 : ℂ))
        (fun m : Fin (r - 1) => Fin.cons 0 (fun i : Fin r => ((c m i : ℚ) : ℂ))))
          : Fin (r - 1 + 1) → Fin (r + 1) → ℂ) m.succ)
      = eulerDer (c m) := by
    intro m
    rw [Fin.cons_succ]
    exact derC_cons_zero_eq_eulerDer (c m)
  rw [List.finRange_succ, List.foldr_cons, List.foldr_map]
  rw [Fin.cons_zero, derC_piSingle r]
  have hF : (fun x y => (derC (N := r) (((Fin.cons (Pi.single (0 : Fin (r + 1)) (1 : ℂ))
        (fun m : Fin (r - 1) => Fin.cons 0 (fun i : Fin r => ((c m i : ℚ) : ℂ))))
          : Fin (r - 1 + 1) → Fin (r + 1) → ℂ) x.succ))^[t x.succ] y)
      = (fun m Q => (eulerDer (c m))^[t m.succ] Q) := by
    funext x y
    rw [hWs x]
  rw [hF]

end Work.BW
