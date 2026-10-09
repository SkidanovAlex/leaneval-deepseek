import Submission.Work.SSGRoute.sha2_hasse.Gateway
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open CategoryTheory

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace Work.SSGRoute.sha2_hasse

variable {k : Type} [Field k] [NumberField k]

/-- **The localisation of an explicitly given class**: for a place `w` of a finite Galois level
`L` of `k̄`, the localisation of the class of the explicit `2`-cocycle `c` is the class of the
pushed-forward cocycle `(γ,δ) ↦ (unitsToLocalUnits k L w) (c (γ, δ))` on the decomposition
group of `w`. -/

theorem locUnits_mkClass_apply
    (L : FiniteGaloisIntermediateField k (AlgebraicClosure k))
    (w : NK.GlobalCFT.Place (Lf L))
    (c : (Lf L ≃ₐ[k] Lf L) × (Lf L ≃ₐ[k] Lf L) → Additive (Lf L)ˣ)
    (hc : c ∈ groupCohomology.cocycles₂ (NK.HassePrinciple.unitsRep k (Lf L))) :
    (NK.HassePrinciple.locUnits k (Lf L) w).hom
        (mkClass (NK.HassePrinciple.unitsRep k (Lf L)) c hc)
      = groupCohomology.H2π (NK.HassePrinciple.localUnitsRep k (Lf L) w)
          (groupCohomology.mapCocycles₂ (MulAction.stabilizer (Lf L ≃ₐ[k] Lf L) w).subtype
            (NK.HassePrinciple.unitsToLocalUnits k (Lf L) w) ⟨c, hc⟩) := by
  have hloc : NK.HassePrinciple.locUnits k (Lf L) w
      = groupCohomology.map (MulAction.stabilizer (Lf L ≃ₐ[k] Lf L) w).subtype
          (NK.HassePrinciple.unitsToLocalUnits k (Lf L) w) 2 := by
    rw [NK.HassePrinciple.locUnits, groupCohomology.resNatTrans_app,
      NK.NUV2.LC.RouteB.map_id_comp_apply]
  rw [hloc, mkClass]
  conv_rhs => rw [← ModuleCat.comp_apply
    (groupCohomology.mapCocycles₂ (MulAction.stabilizer (Lf L ≃ₐ[k] Lf L) w).subtype
      (NK.HassePrinciple.unitsToLocalUnits k (Lf L) w))
    (groupCohomology.H2π (NK.HassePrinciple.localUnitsRep k (Lf L) w)) ⟨c, hc⟩]
  rw [← groupCohomology.H2π_comp_map (MulAction.stabilizer (Lf L ≃ₐ[k] Lf L) w).subtype
      (NK.HassePrinciple.unitsToLocalUnits k (Lf L) w)]
  rw [ModuleCat.comp_apply]

end Work.SSGRoute.sha2_hasse
