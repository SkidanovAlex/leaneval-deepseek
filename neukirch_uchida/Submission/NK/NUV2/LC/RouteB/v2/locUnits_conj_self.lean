import Mathlib
import Submission.NK.NUV2.LC.RouteB.locUnits_tower_fibre

namespace NK.NUV2.LC.RouteB.v2

open CategoryTheory

/-- Naturality of the units localisation under the conjugation action. To be placed in namespace `NK.NUV2.LC.RouteB.v2`. -/
theorem locUnits_conj_self {F M : Type} [Field F] [NumberField F] [Field M] [NumberField M]
    [Algebra F M] [FiniteDimensional F M] [IsGalois F M]
    (σ : M ≃ₐ[F] M) (w : NK.GlobalCFT.Place M) :
    CategoryTheory.CategoryStruct.comp (NK.NUV2.LC.RouteB.conjH2 (F := F) (M := M) σ)
        (NK.HassePrinciple.locUnits F M (σ • w)) =
      CategoryTheory.CategoryStruct.comp (NK.HassePrinciple.locUnits F M w)
        (NK.NUV2.LC.RouteB.conjLoc (F := F) (M := M) σ w) := by
  rw [NK.NUV2.LC.RouteB.locUnits_eq_map (K := F) (L := M) (σ • w)]
  rw [NK.NUV2.LC.RouteB.locUnits_eq_map (K := F) (L := M) w]
  rw [NK.NUV2.LC.RouteB.conjH2, NK.NUV2.LC.RouteB.conjLoc]
  rw [← groupCohomology.map_comp, ← groupCohomology.map_comp]
  refine groupCohomology.map_congr ?_ ?_ 2
  · apply MonoidHom.ext
    intro g
    apply AlgEquiv.ext
    intro a
    change (σ⁻¹ * (g : M ≃ₐ[F] M) * σ) a =
      ((NK.NUV2.LC.RouteB.conjStab σ w g :
        MulAction.stabilizer (M ≃ₐ[F] M) w) : M ≃ₐ[F] M) a
    rw [NK.NUV2.LC.RouteB.conjStab_coe]
    group
  · apply LinearMap.ext
    intro x
    rw [Rep.hom_comp]
    simp only [Representation.IntertwiningMap.comp_toLinearMap, LinearMap.comp_apply]
    set y : Mˣ := Additive.toMul x
    show Additive.ofMul (Units.map
          (algebraMap M (NK.GlobalCFT.Place.localField M (σ • w))).toMonoidHom
        (Units.map σ.toMulEquiv.toMonoidHom y)) =
      Additive.ofMul (Units.map
          (NK.GlobalCFT.Place.localRingEquiv σ w).toMulEquiv.toMonoidHom
        (Units.map (algebraMap M (NK.GlobalCFT.Place.localField M w)).toMonoidHom y))
    congr 1
    apply Units.ext
    show algebraMap M (NK.GlobalCFT.Place.localField M (σ • w)) (σ (y : M)) =
      NK.GlobalCFT.Place.localRingEquiv σ w
        (algebraMap M (NK.GlobalCFT.Place.localField M w) (y : M))
    rw [NK.GlobalCFT.Place.localRingEquiv_algebraMap]

end NK.NUV2.LC.RouteB.v2
