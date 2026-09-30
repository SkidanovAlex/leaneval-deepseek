import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- The monomial `∏ᵢ X_{(i.succ,1)}^{aᵢ} · X_{(i.succ,0)}^{bᵢ}` is weighted homogeneous for the
weight `w (j,c) = εⱼ` (the first coordinate of the index), of total weight
`∑ᵢ (aᵢ + bᵢ) • ε_{i.succ}`. -/
theorem charPoly_homPiece {N : ℕ} (a b : Fin N → ℕ) :
    (∏ i : Fin N, (MvPolynomial.X ((i.succ, (1 : Fin 2)) : Fin (N + 1) × Fin 2)) ^ (a i)
        * (MvPolynomial.X ((i.succ, (0 : Fin 2)) : Fin (N + 1) × Fin 2)) ^ (b i)) ∈
      MvPolynomial.weightedHomogeneousSubmodule ℂ
        (fun v : Fin (N + 1) × Fin 2 => Finsupp.single v.1 1)
        (∑ i : Fin N, (a i + b i) • (Finsupp.single i.succ 1 : Fin (N + 1) →₀ ℕ)) := by
  classical
  rw [MvPolynomial.mem_weightedHomogeneousSubmodule]
  apply MvPolynomial.IsWeightedHomogeneous.prod
  intro i _
  have h1 : MvPolynomial.IsWeightedHomogeneous
      (fun v : Fin (N + 1) × Fin 2 => Finsupp.single v.1 1)
      (MvPolynomial.X ((i.succ, (1 : Fin 2)) : Fin (N + 1) × Fin 2) :
        MvPolynomial (Fin (N + 1) × Fin 2) ℂ)
      (Finsupp.single i.succ 1 : Fin (N + 1) →₀ ℕ) :=
    MvPolynomial.isWeightedHomogeneous_X ℂ _ _
  have h2 : MvPolynomial.IsWeightedHomogeneous
      (fun v : Fin (N + 1) × Fin 2 => Finsupp.single v.1 1)
      (MvPolynomial.X ((i.succ, (0 : Fin 2)) : Fin (N + 1) × Fin 2) :
        MvPolynomial (Fin (N + 1) × Fin 2) ℂ)
      (Finsupp.single i.succ 1 : Fin (N + 1) →₀ ℕ) :=
    MvPolynomial.isWeightedHomogeneous_X ℂ _ _
  have hmul := (h1.pow (a i)).mul (h2.pow (b i))
  simpa [add_nsmul] using hmul

end Work.BW
