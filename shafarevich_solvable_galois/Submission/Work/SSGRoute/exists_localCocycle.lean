import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.FlowGroupSuccDefs
import Submission.Work.SSGRoute.local_factorisation
import Submission.Work.SSGRoute.exists_kerSuccAddEquiv_equivariant
import Submission.Work.SSGRoute.kerSuccCocycle_transport_mem_Z2
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

open Work.CohomologicalShrinking

/-! ## The pulled back section cocycle at a decomposition group is a `2`-cocycle

This file proves `Work.SSGRoute.exists_localCocycle`: for a place `A` over `ℚ`, the section
cocycle `κ = kerSuccCocycle φA s` of the projection `Γ(τ+1) ↠ Γ(τ)`, pulled back along the
factorisation `φA : D_A(K/ℚ) →* Γ(τ)` of a Scholz solution, is a `2`-cocycle with values in the
graded piece `E(m,τ)`, for the action of `D_A(K/ℚ)` induced by the inclusion into
`Gal(K/ℚ) = G` through the restriction map.

The mathematical content is already available abstractly as
`Work.SSGRoute.kerSuccCocycle_transport_mem_Z2`, which proves the cocycle identity for an abstract
group `H` acting on `E(m,τ)` through `flowQuot ∘ ρ`.  Since `hφA` says exactly that `flowQuot ∘ φA`
is the subgroup inclusion `D_A(K/ℚ) ↪ Gal(K/ℚ)`, the two coefficient actions agree and the
abstract statement specialises to the present one. -/

theorem exists_localCocycle (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ SSGRoute.QBar)
    [FiniteDimensional ℚ K] [Normal ℚ K] (i j m : ℕ)
    (A : ValuationSubring SSGRoute.QBar)
    (φA : ↥((SSGRoute.decomp ℚ A).map (AlgEquiv.restrictNormalHom K)) →*
        Work.CohomologicalShrinking.flowGroup p (K ≃ₐ[ℚ] K) m i j)
    (hφA : ∀ h : ↥((SSGRoute.decomp ℚ A).map (AlgEquiv.restrictNormalHom K)),
        Work.CohomologicalShrinking.flowQuot p (K ≃ₐ[ℚ] K) m i j (φA h)
          = (h : K ≃ₐ[ℚ] K))
    (s : Work.CohomologicalShrinking.flowGroup p (K ≃ₐ[ℚ] K) m i j →
        Work.CohomologicalShrinking.flowGroup p (K ≃ₐ[ℚ] K) m
          (Work.CohomologicalShrinking.tauSucc i j).1 (Work.CohomologicalShrinking.tauSucc i j).2)
    (hs : ∀ x, Work.SSGRoute.flowGroupSucc p (K ≃ₐ[ℚ] K) m i j (s x) = x) (h1 : s 1 = 1)
    (e : Additive ↥(Work.SSGRoute.flowGroupSucc p (K ≃ₐ[ℚ] K) m i j).ker →+
        Work.CohomologicalShrinking.E p (K ≃ₐ[ℚ] K) m i j)
    (he : ∀ (g : K ≃ₐ[ℚ] K)
        (x : Additive ↥(Work.SSGRoute.flowGroupSucc p (K ≃ₐ[ℚ] K) m i j).ker),
        e (Additive.ofMul (Work.AbsoluteGalois.conjKernelMul
            (Work.SSGRoute.flowGroupSucc p (K ≃ₐ[ℚ] K) m i j)
            (SemidirectProduct.mk 1 g : Work.CohomologicalShrinking.flowGroup p (K ≃ₐ[ℚ] K) m
              (Work.CohomologicalShrinking.tauSucc i j).1
              (Work.CohomologicalShrinking.tauSucc i j).2) (Additive.toMul x))) = g • e x) :
    (letI : DistribMulAction ↥((SSGRoute.decomp ℚ A).map (AlgEquiv.restrictNormalHom K))
        (Work.CohomologicalShrinking.E p (K ≃ₐ[ℚ] K) m i j) :=
      DistribMulAction.compHom _ (Subgroup.subtype _)
     (fun x : ↥((SSGRoute.decomp ℚ A).map (AlgEquiv.restrictNormalHom K)) ×
              ↥((SSGRoute.decomp ℚ A).map (AlgEquiv.restrictNormalHom K)) =>
        e (Work.SSGRoute.kerSuccCocycle p (K ≃ₐ[ℚ] K) m i j φA s hs x.1 x.2))
       ∈ Work.GroupCohomology.Z2 _ (Work.CohomologicalShrinking.E p (K ≃ₐ[ℚ] K) m i j)) := by
  -- the kernel of the projection is commutative (graded piece of a `p`-central series)
  have hcomm : ∀ a b : ↥(flowGroupSucc p (K ≃ₐ[ℚ] K) m i j).ker, a * b = b * a :=
    fun a b => (flowGroupSucc_ker_isMulCommutative p (K ≃ₐ[ℚ] K) m i j).is_comm.comm a b
  -- the abstract transport lemma, with `H = D_A(K/ℚ)` and `ρ = φA`
  have hmain := kerSuccCocycle_transport_mem_Z2 (p := p) (G := K ≃ₐ[ℚ] K) m i j
    (H := ↥((SSGRoute.decomp ℚ A).map (AlgEquiv.restrictNormalHom K))) φA s hs h1 hcomm e he
  -- `hφA` says that `flowQuot ∘ φA` is the inclusion `D_A(K/ℚ) ↪ Gal(K/ℚ)`
  have hψ : (flowQuot p (K ≃ₐ[ℚ] K) m i j).comp φA
      = (Subgroup.map (AlgEquiv.restrictNormalHom K) (SSGRoute.decomp ℚ A)).subtype :=
    MonoidHom.ext (fun h => hφA h)
  -- hence the two coefficient actions coincide
  have hact : DistribMulAction.compHom (E p (K ≃ₐ[ℚ] K) m i j)
        ((flowQuot p (K ≃ₐ[ℚ] K) m i j).comp φA)
      = DistribMulAction.compHom (E p (K ≃ₐ[ℚ] K) m i j)
        (Subgroup.map (AlgEquiv.restrictNormalHom K) (SSGRoute.decomp ℚ A)).subtype :=
    congrArg _ hψ
  rw [hact] at hmain
  exact hmain

end Work.SSGRoute
