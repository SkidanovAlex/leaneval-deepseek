import Mathlib
import Submission.Work.RB.Defs
import Submission.Work.BW.weightedHomogeneousComponent_mul_of_mem

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.RB

/-- The colon ideal `(I : X v)` of a `w`-homogeneous ideal `I` is again `w`-homogeneous. -/
theorem isWHomog_colon {n : ℕ} {σ : Type*} [Fintype σ] (w : σ → Fin n →₀ ℕ) {v : σ}
    {I : Ideal (MvPolynomial σ ℂ)} (hI : IsWHomog w I) :
    IsWHomog w (Submodule.colon (I : Submodule (MvPolynomial σ ℂ) (MvPolynomial σ ℂ))
      ({MvPolynomial.X v} : Set (MvPolynomial σ ℂ))) := by
  intro p hp d
  -- Unfold the colon: `p ∈ (I : X v) ↔ p * X v ∈ I`, and likewise for the goal.
  rw [Submodule.mem_colon_singleton, smul_eq_mul] at hp ⊢
  -- `I` is `w`-homogeneous, so the `(d + w v)`-component of `p * X v` lies in `I`.
  have key := hI (p * MvPolynomial.X v) hp (d + w v)
  -- `X v` is weighted homogeneous of degree `w v`, so multiplying by it shifts the
  -- weighted homogeneous component by exactly `w v`; the other components die.
  have h1 := Work.BW.weightedHomogeneousComponent_mul_of_mem (R := ℂ) (w := w) (D := w v)
    (P := MvPolynomial.X v) (MvPolynomial.isWeightedHomogeneous_X ℂ w v) p d
  have hcomp : MvPolynomial.weightedHomogeneousComponent w (d + w v) (p * MvPolynomial.X v)
      = MvPolynomial.weightedHomogeneousComponent w d p * MvPolynomial.X v := by
    rw [mul_comm p (MvPolynomial.X v), h1, mul_comm]
  rwa [hcomp] at key

end Work.RB
