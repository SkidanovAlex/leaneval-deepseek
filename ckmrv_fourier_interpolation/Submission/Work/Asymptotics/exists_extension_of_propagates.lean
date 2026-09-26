import Mathlib
import Submission.Work.Asymptotics.PropagateDefs
import Submission.Work.Asymptotics.DomainD
import Submission.Work.Asymptotics.exists_extension_of_propagates_even
import Submission.Work.Asymptotics.exists_extension_of_propagates_odd

namespace Work.Asymptotics

/-- CKMRV Proposition 3.2(1), the analytic continuation half (declare in namespace
`Work.Asymptotics`).  Let `O` be an open subset of `UpperHalfPlane` containing the closure of the
`Γ(2)`-fundamental domain `𝒟`, let `h₁`, `h₂` be holomorphic on `ℍ`, and let `f` be holomorphic
on `O` satisfying the two transformation laws `f|(T-I)² = h₁` and `f|S(T-I)² = h₂` wherever both
sides are defined (the predicate `Work.Asymptotics.Propagates k O f h₁ h₂`; the slash is a right
action, so `S(T-I)²` acts by `S` first).  Then `f` extends to a holomorphic function `F` on all
of `ℍ` which agrees with `f` on some open neighbourhood `U` of `𝒟̄` contained in `O`, and which
satisfies `(T-I)²F = h₁` and `S(T-I)²F = h₂` on all of `ℍ`.  The group-algebra input is
`Work.Modular.sigmaAlg` with `Work.Modular.quotient_basis` and
`Work.Modular.mul_basisElem_sub_mem_idealI`; the geometric input
`Work.Asymptotics.triple_mem_closure_DomainD` is available. -/
theorem exists_extension_of_propagates {k : ℤ} {O : Set UpperHalfPlane}
    {f h₁ h₂ : UpperHalfPlane → ℂ}
    (h : Work.Asymptotics.Propagates k O f h₁ h₂)
    (hO : closure Work.Asymptotics.DomainD ⊆ O) :
    ∃ F : UpperHalfPlane → ℂ,
      MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) F ∧
      (∃ U : Set UpperHalfPlane, IsOpen U ∧ closure Work.Asymptotics.DomainD ⊆ U ∧ U ⊆ O ∧
        ∀ τ ∈ U, F τ = f τ) ∧
      (∀ τ : UpperHalfPlane, Work.Kernels.T2op F τ = h₁ τ) ∧
      (∀ τ : UpperHalfPlane, Work.Asymptotics.S2op k F τ = h₂ τ) := by
  rcases k.even_or_odd with hk | hk
  · exact Work.Asymptotics.exists_extension_of_propagates_even hk h hO
  · exact Work.Asymptotics.exists_extension_of_propagates_odd hk h hO

end Work.Asymptotics
