import Mathlib

open scoped BigOperators

namespace Work.WilE9.Deriv

/-- Expansion of a continuous multilinear map on `(Fin n → ℝ)^m` in terms of its values on
tuples of standard basis vectors.

Namespace `Work.WilE9.Deriv`; imports `Mathlib`; needs `open scoped BigOperators`. -/
theorem contMultilinear_eq_sum_basis {n m : ℕ}
    (M : (Fin n → ℝ) [×m]→L[ℝ] ℝ) (x : Fin m → (Fin n → ℝ)) :
    M x = ∑ v : Fin m → Fin n, M (fun j => Pi.single (v j) (1:ℝ)) * ∏ j, x j (v j) := by
  have hx : x = fun j => ∑ k : Fin n, x j k • Pi.single k (1:ℝ) := by
    funext j
    nth_rewrite 1 [← Module.Basis.sum_repr (Pi.basisFun ℝ (Fin n)) (x j)]
    apply Finset.sum_congr rfl
    intro k _
    rw [Pi.basisFun_repr, Pi.basisFun_apply]
  conv_lhs => rw [hx]
  rw [M.map_sum]
  apply Finset.sum_congr rfl
  intro v _
  rw [M.map_smul_univ, smul_eq_mul, mul_comm]

end Work.WilE9.Deriv
