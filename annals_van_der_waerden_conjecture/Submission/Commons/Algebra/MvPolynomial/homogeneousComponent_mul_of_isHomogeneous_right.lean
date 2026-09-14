import Mathlib.RingTheory.MvPolynomial.Homogeneous

namespace Commons.Algebra.MvPolynomial

-- The graded-algebra structure on `MvPolynomial` induced by the total degree.  Mathlib
-- deliberately does not register it globally (one may want another grading), so we bring it
-- into scope locally for the proof below.
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Multiplying a polynomial `u` on the right by a homogeneous polynomial `g` of degree `a`
shifts the homogeneous decomposition by `a`: the `(j + a)`-th homogeneous component of `u * g`
is the `j`-th homogeneous component of `u` multiplied by `g`.

This is the `MvPolynomial` analogue of the graded-ring fact
`DirectSum.coe_decompose_mul_add_of_right_mem`. -/
theorem homogeneousComponent_mul_of_isHomogeneous_right {σ K : Type*} [CommSemiring K]
    {g : MvPolynomial σ K} {a : ℕ} (hg : g.IsHomogeneous a) (u : MvPolynomial σ K) (j : ℕ) :
    MvPolynomial.homogeneousComponent (j + a) (u * g) = MvPolynomial.homogeneousComponent j u * g := by
  classical
  -- `homogeneousComponent` is the graded projection attached to the total-degree grading.
  have hbridge : ∀ (x : MvPolynomial σ K) (i : ℕ),
      ((DirectSum.decompose (MvPolynomial.homogeneousSubmodule σ K) x) i : MvPolynomial σ K) =
        MvPolynomial.homogeneousComponent i x := by
    intro x i
    rw [← MvPolynomial.decomposition.decompose'_apply]
    rfl
  have hgmem : g ∈ MvPolynomial.homogeneousSubmodule σ K a := hg
  have key : ((DirectSum.decompose (MvPolynomial.homogeneousSubmodule σ K) (u * g)) (j + a) :
      MvPolynomial σ K) = (DirectSum.decompose (MvPolynomial.homogeneousSubmodule σ K) u j :
        MvPolynomial σ K) * g :=
    DirectSum.coe_decompose_mul_add_of_right_mem (MvPolynomial.homogeneousSubmodule σ K)
      (i := j) (j := a) hgmem
  rw [hbridge, hbridge] at key
  exact key

end Commons.Algebra.MvPolynomial