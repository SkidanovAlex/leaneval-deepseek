import Mathlib
import Submission.Work.Asymptotics.PropagateDefs
import Submission.Work.Asymptotics.DomainD
import Submission.Work.Asymptotics.exists_extension_of_propagates_even_aux

namespace Work.Asymptotics

/-- **CKMRV Proposition 3.2(1), analytic continuation half, at even weight.**  The proof is the
work of a colleague in `Submission/Work/Asymptotics/exists_extension_of_propagates_even_aux.lean`
(`Work.Asymptotics.exists_extension_of_propagates_even_aux`): the carries of the ideal
`𝓘 = (T-I)²R + S(T-I)²R + (z-1)R` (`Submission/Work/Asymptotics/PropagateCarries.lean`), their
cocycle modulo `(z-1)R`, the second basis `M' = (I, T⁻¹, STS, S, ST⁻¹, TS)` and its neighbours
(`PropagateMpDefs`, `carryP_exists`, `exists_neighbour_nbdh_of_Propagates`), the tiling of
`closure 𝒟` by the six translates of `closure 𝓕` (`closure_DomainD_subset_iUnion_Mp`,
`exists_Mp_nbdh`), and the identity theorem step (`defects_of_local_agreement`) assemble into the
analytic continuation. -/
theorem exists_extension_of_propagates_even {k : ℤ} (hk : Even k) {O : Set UpperHalfPlane}
    {f h₁ h₂ : UpperHalfPlane → ℂ}
    (h : Work.Asymptotics.Propagates k O f h₁ h₂)
    (hO : closure Work.Asymptotics.DomainD ⊆ O) :
    ∃ F : UpperHalfPlane → ℂ,
      MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) F ∧
      (∃ U : Set UpperHalfPlane, IsOpen U ∧ closure Work.Asymptotics.DomainD ⊆ U ∧ U ⊆ O ∧
        ∀ τ ∈ U, F τ = f τ) ∧
      (∀ τ : UpperHalfPlane, Work.Kernels.T2op F τ = h₁ τ) ∧
      (∀ τ : UpperHalfPlane, Work.Asymptotics.S2op k F τ = h₂ τ) :=
  exists_extension_of_propagates_even_aux hk h hO

end Work.Asymptotics
