import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

open MvPolynomial

/-- If `P` is weighted homogeneous of weighted degree `D`, then the weighted homogeneous
component of `P * f` of weighted degree `m + D` is `P` times the weighted homogeneous
component of `f` of weighted degree `m`. -/
theorem weightedHomogeneousComponent_mul_of_mem {R : Type*} [CommSemiring R] {σ M : Type*}
    [AddCommMonoid M] [IsCancelAdd M] {w : σ → M} {D : M} {P : MvPolynomial σ R}
    (hP : P ∈ MvPolynomial.weightedHomogeneousSubmodule R w D) (f : MvPolynomial σ R) (m : M) :
    MvPolynomial.weightedHomogeneousComponent w (m + D) (P * f) =
      P * MvPolynomial.weightedHomogeneousComponent w m f := by
  classical
  rw [MvPolynomial.mem_weightedHomogeneousSubmodule] at hP
  induction f using MvPolynomial.induction_on' with
  | monomial d a =>
    by_cases h : Finsupp.weight w d = m
    · -- `monomial d a` is homogeneous of degree `m`, so `P * monomial d a` has degree `D + m`.
      have hhom : IsWeightedHomogeneous w (P * monomial d a) (m + D) := by
        have := hP.mul (isWeightedHomogeneous_monomial w d a h)
        simpa [add_comm] using this
      rw [IsWeightedHomogeneous.weightedHomogeneousComponent_same hhom,
        IsWeightedHomogeneous.weightedHomogeneousComponent_same
          (isWeightedHomogeneous_monomial w d a h)]
    · -- Otherwise `monomial d a` has no component of degree `m`, and `P * monomial d a` has no
      -- component of degree `m + D` because `M` is cancellative.
      have hcomp : weightedHomogeneousComponent w m (monomial d a) = 0 :=
        IsWeightedHomogeneous.weightedHomogeneousComponent_ne (w := w) m
          (isWeightedHomogeneous_monomial w d a rfl) (Ne.symm h)
      have hhom : IsWeightedHomogeneous w (P * monomial d a) (D + Finsupp.weight w d) :=
        hP.mul (isWeightedHomogeneous_monomial w d a rfl)
      have hne : (m + D) ≠ (D + Finsupp.weight w d) := by
        rw [add_comm m D]
        intro heq
        exact h (add_left_cancel heq).symm
      rw [IsWeightedHomogeneous.weightedHomogeneousComponent_ne (w := w) (m + D) hhom hne,
        hcomp, mul_zero]
  | add p q ihp ihq =>
    -- Both sides are additive in `f`.
    rw [mul_add, map_add, map_add, mul_add, ihp, ihq]

end Work.BW
