import Mathlib
import Submission.Work.BW.DefsMult
import Submission.Work.BW.BWGradedBase

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW.RB

open MvPolynomial

set_option linter.style.haveILetI false

/-- The ideal spanned by a set of multihomogeneous polynomials (each lying in some
`homPiece N d`) is multihomogeneous, i.e. closed under taking multihomogeneous components.

Indeed, `MR N` is graded by `Fin (N+1) →₀ ℤ` with pieces `pieceZ N u` (the same as `homPiece N d`
with `u = castF d`), and Mathlib's `Ideal.homogeneous_span` says the span of homogeneous elements
is a homogeneous ideal; `MvPolynomial.weightedHomogeneousComponent_mem_of_mem` then converts
homogeneity into the componentwise closure that `MultiHomZ` (hence `MultiHom`) states. -/
theorem multiHom_span_of_homPiece {N : ℕ} (S : Set (MR N))
    (hS : ∀ x ∈ S, ∃ d : Fin (N + 1) →₀ ℕ, x ∈ homPiece N d) :
    MultiHom N (Ideal.span S) := by
  letI := MvPolynomial.weightedGradedAlgebra ℂ (wZ N)
  rw [multiHom_iff_multiHomZ]
  have hhom : Ideal.IsHomogeneous (MvPolynomial.weightedHomogeneousSubmodule ℂ (wZ N))
      (Ideal.span S) := by
    apply Ideal.homogeneous_span
    intro x hx
    obtain ⟨d, hd⟩ := hS x hx
    refine ⟨castF d, ?_⟩
    rw [homPiece_eq_pieceZ d] at hd
    exact hd
  intro p hp u
  exact MvPolynomial.weightedHomogeneousComponent_mem_of_mem ℂ (wZ N) hhom hp u

end Work.BW.RB
