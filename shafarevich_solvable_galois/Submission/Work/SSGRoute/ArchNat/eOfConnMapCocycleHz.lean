import Mathlib
import Submission.Work.SSGRoute.homRep
import Submission.Work.SSGRoute.freeLift_id_epi
import Submission.Work.SSGRoute.ArchDictionary.extOneDictNatAux
import Submission.Work.SSGRoute.ArchDictionary.extOneDictNaturalH1
import Submission.Work.GroupCohomology.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The `Z¹` half of `eOf_connMap_cocycle` (dispatch D3, step 0)

`ARCHP2_PLAN.md` §B (`eOf_connMap_cocycle`, the lead's D3) asks for the *cochain formula*

`eOf (connMap (ses_shortExact M) N a) = ± H¹π ⟨ψ, hz⟩`.

Its conclusion binds `hz : ψ ∈ Z¹(G, M.V →ₗ N.V)` — and that membership is **pure group
cohomology**, independent of `eOf`, `N`-injectivity, or the `X`/`hX` resolution data.  This file
isolates it: for a `1`-cocycle *candidate* `ψ` written as the "coboundary of a lift"
(`hψ : ψ g (cover f) = N.ρ g (ã (ρ g⁻¹ f)) − ã f`), the crossed-homomorphism identity holds.

Proof.  `freeCover M` is epi (`Work.SSGRoute.freeLift_id_epi`), hence surjective on underlying types
(`Rep.epi_iff_surjective`); so it suffices to check the identity on `cover f`.  There the claim is
the algebraic identity obtained from `hψ` at `f`, `ρ g⁻¹ f` and `(g*h)⁻¹ f`, the equivariance of
`cover` (`Rep.hom_comm_apply`), `map_mul` of the two representations and `mul_inv_rev`.
-/

namespace Work.SSGRoute.ArchNat

open CategoryTheory SSGRoute.PTExt

/-- **The `Z¹` half of D3.**  A map `ψ : G → (M.V →ₗ N.V)` satisfying the lift formula `hψ` is a
`1`-cocycle for the conjugation action `homRepDistribMulAction M N`. -/
theorem eOf_connMap_cocycle_hz {G : Type} [Group G]
    (M N : Rep.{0} SSGRoute.PTExt.Coeff G)
    (atil : (Rep.free SSGRoute.PTExt.Coeff G M.V).V →+ N.V)
    (ψ : G → (M.V →ₗ[SSGRoute.PTExt.Coeff] N.V))
    (hψ : ∀ g f, ψ g (Rep.Hom.hom (Work.SSGRoute.freeCover M) f)
      = N.ρ g (atil ((Rep.free SSGRoute.PTExt.Coeff G M.V).ρ g⁻¹ f)) - atil f) :
    ψ ∈ @Work.GroupCohomology.Z1 G (M.V →ₗ[SSGRoute.PTExt.Coeff] N.V) _ _
      (Work.SSGRoute.homRepDistribMulAction M N) := by
  have hsurj : Function.Surjective (Rep.Hom.hom (Work.SSGRoute.freeCover M)) := by
    simpa using (Rep.epi_iff_surjective (Work.SSGRoute.freeCover M)).mp
      (Work.SSGRoute.freeLift_id_epi G M)
  intro g h
  ext m
  obtain ⟨f, rfl⟩ := hsurj m
  simp only [LinearMap.add_apply, LinearMap.sub_apply,
    Work.SSGRoute.homRep_smul_apply]
  rw [← Rep.hom_comm_apply (Work.SSGRoute.freeCover M) g⁻¹ f]
  rw [hψ (g * h) f, hψ g f, hψ h ((Rep.free SSGRoute.PTExt.Coeff G M.V).ρ g⁻¹ f)]
  -- Both sides are now expressions in `N.ρ`, `atil` and `ρ_f` alone, and the identity is the
  -- additive bookkeeping `A - C = (A - B) + (B - C)`:  `map_mul` splits `N.ρ (g*h)` and
  -- `mul_inv_rev` + `map_mul` splits `ρ_f ((g*h)⁻¹)`, `Module.End.mul_apply` turns the products of
  -- endomorphisms into compositions, and `map_sub` is linearity of `N.ρ g`.
  rw [map_mul, mul_inv_rev, map_mul]
  simp only [Module.End.mul_apply]
  rw [map_sub]
  abel

end Work.SSGRoute.ArchNat
