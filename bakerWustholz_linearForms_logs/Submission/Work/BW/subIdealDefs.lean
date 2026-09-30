import Mathlib
import Submission.Work.BW.DefsMult

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-! # Auxiliary definitions for `Work.BW.subIdeal_isPrime`

The multihomogeneous ideal `subIdeal N ρ ε M` is the ideal of the closure of
`G' = G_a^ε × ker 𝒵 ⊂ (P¹)^{N+1}`, where `𝒵 = span_ℤ (range M)` is a saturated rank-`ρ`
sublattice of `ℤ^N`.  A primitive system `M` gives an isomorphism of tori
`ker 𝒵 ≅ (ℂ^×)^{N-ρ}` (see `Work.BW.kerZ_param`); writing `y_i = ∏_j t_j^{c_{ij}}` for the
corresponding exponents `c`, restrictions of multihomogeneous polynomials to `G'` become Laurent
polynomials in `t` (and polynomials in the `G_a` coordinate `u`).

The two rings and the substitution used below:
* `Laur m = ℂ[ℤ^m]` is the Laurent polynomial ring in `m` variables;
* `RingA m = (Laur m)[u]` adjoins the `G_a` coordinate;
* `psiMap ε c : MR N →ₐ[ℂ] RingA m` is the induced pull-back
  `X_{i,0} ↦ 1`, `X_{i,1} ↦ t^{(c_{ij})_j}` (`i ≥ 1`), `X_{0,1} ↦ u` if `ε`, else `0`;
* `charEval` and `EV` evaluate at a torus point and at `u = a`;
* `gammaPt` is the corresponding point of `G'`.
-/

namespace Work.BW

open MvPolynomial

noncomputable section

/-- Laurent polynomial ring in `m` variables: the group algebra of `ℤ^m`. -/
abbrev Laur (m : ℕ) : Type := AddMonoidAlgebra ℂ (Fin m → ℤ)

/-- `RingA m = (Laur m)[u]`: Laurent in the torus variables, polynomial in the `G_a` coordinate. -/
abbrev RingA (m : ℕ) : Type := Polynomial (Laur m)

/-- Evaluation of a Laurent monomial at a torus point `x`: `δ_w ↦ ∏_j x_j^{w_j}`. -/
noncomputable def charEval {m : ℕ} (x : Fin m → ℂˣ) : Laur m →ₐ[ℂ] ℂ :=
  AddMonoidAlgebra.lift ℂ ℂ (Fin m → ℤ)
    ((Units.coeHom ℂ).comp
      { toFun := fun w => ∏ j, x j ^ (Multiplicative.toAdd w j)
        map_one' := by simp
        map_mul' := by
          intro w w'
          rw [← Finset.prod_mul_distrib]
          refine Finset.prod_congr rfl (fun j _ => ?_)
          rw [show Multiplicative.toAdd (w * w') j
                = Multiplicative.toAdd w j + Multiplicative.toAdd w' j from rfl, zpow_add] })

/-- Evaluation of `RingA m` at `u = a` and the torus point `x`. -/
noncomputable def EV {m : ℕ} (a : ℂ) (x : Fin m → ℂˣ) : RingA m →+* ℂ :=
  ((charEval x : Laur m →+* ℂ)).comp (Polynomial.evalRingHom (algebraMap ℂ (Laur m) a))

/-- The substitution `X_{i,0} ↦ 1`, `X_{i,1} ↦ t^{(c_{ij})_j}` (`i ≥ 1`), `X_{0,1} ↦ u` (if
`ε`) else `0`. -/
noncomputable def psiMap {N m : ℕ} (ε : Bool) (c : Fin N → Fin m → ℤ) :
    MR N →ₐ[ℂ] RingA m :=
  MvPolynomial.aeval (fun v : Fin (N + 1) × Fin 2 =>
    if v.2 = 0 then 1
    else if h : v.1 = 0 then (if ε then Polynomial.X else 0)
    else Polynomial.C (AddMonoidAlgebra.single (fun j : Fin m => c (Fin.pred v.1 h) j) 1))

/-- The point of `G` (affine coordinates) attached to the parameters `(a, x)`: `y₀ = a` if `ε`
(else `y₀ = 0`) and `y_i = ∏_j x_j^{c_{ij}}` for `i ≥ 1`. -/
noncomputable def gammaPt {N m : ℕ} (ε : Bool) (c : Fin N → Fin m → ℤ) (a : ℂ)
    (x : Fin m → ℂ) : Fin (N + 1) → ℂ :=
  Fin.cons (if ε then a else 0) (fun i : Fin N => ∏ j : Fin m, x j ^ (c i j))

end

end Work.BW

namespace Work.BW

open MvPolynomial

noncomputable section

/-- The multidegree weight, packaged in `Lex` so that the grading index carries a linear order
(Mathlib's graded-ideal API needs `[LinearOrder ι] [IsOrderedCancelAddMonoid ι]`). -/
noncomputable abbrev mdegLex (N : ℕ) : Fin (N + 1) × Fin 2 → Lex (Fin (N + 1) →₀ ℕ) :=
  fun v => toLex (mdeg N v)

/-- The multigrading of `MR N` by `Lex`-ordered multidegrees; `multigrade N (toLex d)` is
definitionally `homPiece N d`. -/
noncomputable abbrev multigrade (N : ℕ) : Lex (Fin (N + 1) →₀ ℕ) → Submodule ℂ (MR N) :=
  MvPolynomial.weightedHomogeneousSubmodule ℂ (mdegLex N)

/-- `multigrade N` is a ring grading, so Mathlib's graded-ideal API applies to it. -/
noncomputable instance (N : ℕ) : GradedRing (multigrade N) := by
  letI := MvPolynomial.weightedGradedAlgebra ℂ (mdegLex N)
  infer_instance

end

end Work.BW
