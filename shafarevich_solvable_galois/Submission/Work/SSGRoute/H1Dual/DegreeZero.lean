import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
import Mathlib.RepresentationTheory.Homological.GroupHomology.LowDegree
import Submission.Work.SSGRoute.H1Dual.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open CategoryTheory

namespace Work.SSGRoute

universe u

variable {k : Type u} [CommRing k] {G : Type u} [Group G]

/-- The map `(N_G)^∨ →ₗ (N^∨)^G`, `l ↦ l ∘ (N → N_G)`. The functional `l ∘ mkQ` is invariant
because `mkQ` kills `I_G·N`. -/
def H0DualAux (N : Rep k G) :
    Module.Dual k ((Rep.coinvariantsFunctor k G).obj N) →ₗ[k]
      ↥((dualRep N).ρ.invariants) where
  toFun l :=
    ⟨(l : (Rep.coinvariantsFunctor k G).obj N →ₗ[k] k).comp
        (Representation.Coinvariants.mk N.ρ), by
      intro g
      ext x
      simp only [LinearMap.comp_apply, Representation.dual_apply, Module.Dual.transpose_apply]
      congr 1
      exact (Representation.Coinvariants.mk_eq_iff N.ρ).2
        (Representation.Coinvariants.mem_ker_of_eq g⁻¹ x ((N.ρ g⁻¹) x - x) rfl)⟩
  map_add' l μ := by
    ext x
    simp [LinearMap.add_apply, map_add]
  map_smul' c l := by
    ext x
    simp [LinearMap.smul_apply, map_smul]

/-- **The degree-`0` evaluation pairing** `(H₀(G,N))^∨ →ₗ H⁰(G, N^∨)`. -/
def H0DualMap (N : Rep k G) :
    Module.Dual k (groupHomology.H0 N) →ₗ[k] groupCohomology.H0 (dualRep N) :=
  ((Iso.toLinearEquiv (groupCohomology.H0Iso (dualRep N))).symm.toLinearMap).comp
    ((H0DualAux N).comp
      ((LinearEquiv.dualMap (Iso.toLinearEquiv (groupHomology.H0Iso N)).symm).toLinearMap))

end Work.SSGRoute
