import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Multigraded Hilbert function: definitions

Setting: `R = MvPolynomial σ ℂ` graded by `ℕ^n = (Fin n →₀ ℕ)` via a weight function
`w : σ → Fin n →₀ ℕ` (each variable gets a weight).  `homPiece w d` is the span of the
monomials of weighted degree `d`, and `hilb w I d` is `dim_ℂ (R/I)_d` for a `w`-homogeneous
ideal `I`.  `IsEventuallyPoly` is the "eventually equal to a polynomial" predicate on the
monoid `Fin n →₀ ℕ`.
-/

namespace Work.RB

open MvPolynomial

noncomputable section

variable {n : ℕ} {σ : Type*} [Fintype σ]

/-- The `d`-th multigraded piece of `R = MvPolynomial σ ℂ`. -/
def homPiece (w : σ → Fin n →₀ ℕ) (d : Fin n →₀ ℕ) : Submodule ℂ (MvPolynomial σ ℂ) :=
  MvPolynomial.weightedHomogeneousSubmodule ℂ w d

@[simp] theorem mem_homPiece (w : σ → Fin n →₀ ℕ) (d : Fin n →₀ ℕ)
    (p : MvPolynomial σ ℂ) :
    p ∈ homPiece w d ↔ p.IsWeightedHomogeneous w d := Iff.rfl

/-- The Hilbert function of `R/I` at multidegree `d`. -/
def hilb (w : σ → Fin n →₀ ℕ) (I : Ideal (MvPolynomial σ ℂ)) (d : Fin n →₀ ℕ) : ℕ :=
  Module.finrank ℂ (homPiece w d ⧸
    Submodule.comap (homPiece w d).subtype (I.restrictScalars ℂ))

/-- `I` is a `w`-homogeneous (multigraded) ideal. -/
def IsWHomog (w : σ → Fin n →₀ ℕ) (I : Ideal (MvPolynomial σ ℂ)) : Prop :=
  ∀ p ∈ I, ∀ d, MvPolynomial.weightedHomogeneousComponent w d p ∈ I

/-- `f` agrees with a polynomial on all `d` with all coordinates large enough. -/
def IsEventuallyPoly (f : (Fin n →₀ ℕ) → ℚ) : Prop :=
  ∃ (P : MvPolynomial (Fin n) ℚ) (N : ℕ),
    ∀ d : Fin n →₀ ℕ, (∀ i, N ≤ d i) → f d = P.eval (fun i => (d i : ℚ))

end

end Work.RB
