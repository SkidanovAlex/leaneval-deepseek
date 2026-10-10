import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LongExactSequence
import Submission.NK.NUV2.RouteC.LevelInf
import Submission.NK.NUV2.RouteC.map_powHom_eq_zero_iff_of_isCyclic
import Submission.NK.NUV2.RouteE.levelSymbol

/-!
# Naturality of the cup product under the level inflation (Brick E)

For a tower of fields `F ⊆ M ⊆ L` (`M/F` normal), the *level inflation*
`Inf = NK.NUV2.RouteC.levelInfMap : H²(Gal(M/F), Mˣ) → H²(Gal(L/F), Lˣ)` commutes with the
`H⁰ × H²` cup product:

`Inf (a ∪ δχ) = a ∪ δ (χ ∘ res)`.

This is the compatibility of the character pairings of the level symbols under restriction; it is
the remaining input of the character-formula route to the local reciprocity law (route C's
"Brick E", `RouteC/_bricks.lean`).

## The proof

Write the connecting map `δ : H¹(G, ℚ/ℤ) → H²(G, ℤ)` through its explicit cocycle: for a lift
`y : G → ℚ` of the character `χ` (`ratToQmodZ (y g) = χ g`), the class `δχ` is represented by
`χ-cocycle (g,h) = y h - y (gh) + y g ∈ ℤ`
(`NK.NUV2.RouteC.deltaHomChar_eq_H2π`, proved elsewhere in the workspace).  This description is
manifestly natural: pulling the character back along a group hom `f` pulls the cocycle back, so
`map f (trivialCoeff) 2 (δχ) = δ (χ ∘ f)`.

The cup product is then evaluated in the low-degree cocycle model: both sides of the identity are
`H2π` of a `2`-cocycle with the same values `p ↦ (z (res p)) • a`.
-/

open scoped BigOperators
open CategoryTheory

namespace NK.NUV2.RouteE

set_option linter.style.haveILetI false
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false

/-- The coefficient morphism of the trivial `ℤ`-representation along a group homomorphism `f`: the
identity linear map, viewed as a morphism `Res_f (ℤ) ⟶ ℤ`. -/
noncomputable def trivialCoeffHom {G G' : Type} [Group G] [Group G'] (f : G' →* G) :
    Rep.res f (Rep.trivial ℤ G ℤ) ⟶ Rep.trivial ℤ G' ℤ :=
  Rep.ofHom
    { toLinearMap := LinearMap.id
      isIntertwining' := fun g => by
        apply LinearMap.ext
        intro x
        show (Rep.trivial ℤ G' ℤ).ρ g x = (Rep.res f (Rep.trivial ℤ G ℤ)).ρ g x
        show LinearMap.id x = (Rep.trivial ℤ G ℤ).ρ (f g) x
        rw [Rep.trivial_ρ] }

@[simp]
theorem trivialCoeffHom_apply {G G' : Type} [Group G] [Group G'] (f : G' →* G) (x : ℤ) :
    (trivialCoeffHom f).hom x = x := rfl

/-- **Naturality of `δ` under a group homomorphism**: pulling the character `χ` back along `f` and
then applying `δ` is the same as applying `δ` first and pulling back the class. -/
theorem deltaHomChar_naturality {G G' : Type} [Group G] [Group G'] [Fintype G] [Fintype G']
    (f : G' →* G) (φ : Additive G →+ NK.NUV2.RouteC.qmodZ) :
    (groupCohomology.map f (trivialCoeffHom f) 2)
        (NK.NUV2.RouteC.deltaHomChar G φ)
      = NK.NUV2.RouteC.deltaHomChar G' (φ.comp (MonoidHom.toAdditive f)) := by
  classical
  -- lifts of the characters to `ℚ`
  set y : G → ℚ := fun g => Quotient.out (φ (Additive.ofMul g)) with hydef
  have hy : ∀ g : G, NK.NUV2.RouteC.ratToQmodZ (y g) = φ (Additive.ofMul g) :=
    fun g => Quotient.out_eq _
  set y' : G' → ℚ := fun g => y (f g) with hy'def
  have hy' : ∀ g : G', NK.NUV2.RouteC.ratToQmodZ (y' g)
      = (φ.comp (MonoidHom.toAdditive f)) (Additive.ofMul g) := by
    intro g
    rw [hy'def]
    exact hy (f g)
  -- the explicit cocycles
  set z : ↥(groupCohomology.cocycles₂ (Rep.trivial ℤ G ℤ)) :=
    ⟨NK.NUV2.RouteC.chiCocycle φ y hy,
      groupCohomology.mem_cocycles₂_of_comp_eq_d₁₂ (NK.NUV2.RouteC.coeffSes_shortExact G)
        (NK.NUV2.RouteC.chiCocycle_d_eq φ y hy)⟩ with hz
  set z' : ↥(groupCohomology.cocycles₂ (Rep.trivial ℤ G' ℤ)) :=
    ⟨NK.NUV2.RouteC.chiCocycle (φ.comp (MonoidHom.toAdditive f)) y' hy',
      groupCohomology.mem_cocycles₂_of_comp_eq_d₁₂
        (NK.NUV2.RouteC.coeffSes_shortExact G')
        (NK.NUV2.RouteC.chiCocycle_d_eq (φ.comp (MonoidHom.toAdditive f)) y' hy')⟩ with hz'
  have hδ : NK.NUV2.RouteC.deltaHomChar G φ
      = (ConcreteCategory.hom (groupCohomology.H2π (Rep.trivial ℤ G ℤ))) z :=
    NK.NUV2.RouteC.deltaHomChar_eq_H2π φ y hy
  have hδ' : NK.NUV2.RouteC.deltaHomChar G' (φ.comp (MonoidHom.toAdditive f))
      = (ConcreteCategory.hom (groupCohomology.H2π (Rep.trivial ℤ G' ℤ))) z' :=
    NK.NUV2.RouteC.deltaHomChar_eq_H2π (φ.comp (MonoidHom.toAdditive f)) y' hy'
  have hnat : (groupCohomology.map f (trivialCoeffHom f) 2)
        ((ConcreteCategory.hom (groupCohomology.H2π (Rep.trivial ℤ G ℤ))) z)
      = (ConcreteCategory.hom (groupCohomology.H2π (Rep.trivial ℤ G' ℤ)))
          ((ConcreteCategory.hom (groupCohomology.mapCocycles₂ f (trivialCoeffHom f))) z) :=
    congrArg (fun m => m z) (groupCohomology.H2π_comp_map f (trivialCoeffHom f))
  have hcoe : (ConcreteCategory.hom (groupCohomology.mapCocycles₂ f (trivialCoeffHom f))) z = z' := by
    apply groupCohomology.cocycles₂_ext
    intro g h
    rw [groupCohomology.coe_mapCocycles₂, cochainsMap₂_apply, trivialCoeffHom_apply]
    simp only [hz, hz']
    apply Int.cast_injective (α := ℚ)
    show ((NK.NUV2.RouteC.chiCocycle φ y hy (f g, f h) : ℤ) : ℚ)
      = ((NK.NUV2.RouteC.chiCocycle (φ.comp (MonoidHom.toAdditive f)) y' hy' (g, h) : ℤ) : ℚ)
    rw [NK.NUV2.RouteC.chiCocycle_spec φ y hy (f g) (f h),
      NK.NUV2.RouteC.chiCocycle_spec (φ.comp (MonoidHom.toAdditive f)) y' hy' g h]
    simp only [hy'def, map_mul]
  rw [hδ, hδ']
  rw [hnat, hcoe]

end NK.NUV2.RouteE

namespace NK.NUV2.RouteE

set_option linter.style.haveILetI false
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false

open scoped BigOperators
open CategoryTheory

section Cup

variable {F M L : Type} [Field F] [Field M] [Field L]
  [Algebra F M] [Algebra F L] [Algebra M L] [IsScalarTower F M L] [Normal F M]

/-- The units inclusion is `ℤ`-linear in the obvious way: it sends `n • u` to `n` times the image
of `u`, and the image of the unit of `F` is the same unit. -/
theorem unitsInclCoeff_apply (x : Additive Mˣ) :
    (NK.NUV2.RouteC.unitsInclCoeff (F := F) (M := M) (L := L)).hom x
      = Additive.ofMul (Units.map (algebraMap M L).toMonoidHom (Additive.toMul x)) := rfl

theorem unitsInclCoeff_zsmul (n : ℤ) (u : Fˣ) :
    (NK.NUV2.RouteC.unitsInclCoeff (F := F) (M := M) (L := L)).hom
        (n • (Additive.ofMul (Units.map (algebraMap F M).toMonoidHom u) : Additive Mˣ))
      = n • (Additive.ofMul (Units.map (algebraMap F L).toMonoidHom u) : Additive Lˣ) := by
  rw [show (Rep.Hom.hom (NK.NUV2.RouteC.unitsInclCoeff (F := F) (M := M) (L := L)))
        (n • (Additive.ofMul (Units.map (algebraMap F M).toMonoidHom u) : Additive Mˣ))
      = n • (Rep.Hom.hom (NK.NUV2.RouteC.unitsInclCoeff (F := F) (M := M) (L := L)))
          (Additive.ofMul (Units.map (algebraMap F M).toMonoidHom u) : Additive Mˣ) from
    map_zsmul _ n _]
  congr 1
  rw [unitsInclCoeff_apply]
  congr 1
  apply Units.ext
  simp only [Units.coe_map]
  exact (IsScalarTower.algebraMap_apply F M L (u : F)).symm

/-- The pointwise value of the cup product `a ∪ -`: `n ↦ n • a`. -/
theorem powHom_apply (a : Fˣ) (n : ℤ) :
    (NK.NUV2.RouteC.powHom (F := F) (E := M) a).hom n
      = n • (Additive.ofMul (Units.map (algebraMap F M).toMonoidHom a) : Additive Mˣ) := rfl

theorem map_H2π_apply {k : Type} [CommRing k] {G H : Type} [Group G] [Group H]
    {A : Rep k H} {B : Rep k G} (f : G →* H) (φ : Rep.res f A ⟶ B)
    (z : ↥(groupCohomology.cocycles₂ A)) :
    (groupCohomology.map f φ 2) ((ConcreteCategory.hom (groupCohomology.H2π A)) z)
      = (ConcreteCategory.hom (groupCohomology.H2π B))
          ((ConcreteCategory.hom (groupCohomology.mapCocycles₂ f φ)) z) :=
  congrArg (fun m => m z) (groupCohomology.H2π_comp_map f φ)

end Cup

set_option maxHeartbeats 8000000

section CupCoeff

variable {F M L : Type} [Field F] [Field M] [Field L]
  [Algebra F M] [Algebra F L] [Algebra M L] [IsScalarTower F M L] [Normal F M] [Normal F L]

local notation "GM" => (M ≃ₐ[F] M)
local notation "GL" => (L ≃ₐ[F] L)
local notation "resGL" => (AlgEquiv.restrictNormalHom (F := F) (K₁ := L) (E := M))
local notation "unitsIncl" => (NK.NUV2.RouteC.unitsInclCoeff (F := F) (M := M) (L := L))

/-- The pointwise computation underlying the coefficient half of Brick E: the two `2`-cocycles
obtained by transporting the cup product are equal on every pair `(g,h)`. -/
theorem mapCocycles₂_cup_eval (a : Fˣ)
    (z : ↥(groupCohomology.cocycles₂ (Rep.trivial ℤ (M ≃ₐ[F] M) ℤ))) (g h : L ≃ₐ[F] L) :
    (ConcreteCategory.hom (groupCohomology.mapCocycles₂ (MonoidHom.id GL)
        (NK.NUV2.RouteC.powHom (F := F) (E := L) a)))
        ((ConcreteCategory.hom (groupCohomology.mapCocycles₂ resGL
          (trivialCoeffHom resGL))) z) (g, h)
      = (ConcreteCategory.hom (groupCohomology.mapCocycles₂ resGL unitsIncl))
          ((ConcreteCategory.hom (groupCohomology.mapCocycles₂ (MonoidHom.id GM)
            (NK.NUV2.RouteC.powHom (F := F) (E := M) a))) z) (g, h) := by
  rw [groupCohomology.coe_mapCocycles₂, groupCohomology.coe_mapCocycles₂,
    groupCohomology.coe_mapCocycles₂, groupCohomology.coe_mapCocycles₂,
    cochainsMap₂_apply, cochainsMap₂_apply, cochainsMap₂_apply, cochainsMap₂_apply,
    powHom_apply, powHom_apply, trivialCoeffHom_apply, unitsInclCoeff_zsmul]
  simp only [Prod.fst, Prod.snd, MonoidHom.id_apply]
  rfl

/-- The two `2`-cocycles obtained by transporting the cup product agree. -/
theorem mapCocycles₂_cup_eq (a : Fˣ)
    (z : ↥(groupCohomology.cocycles₂ (Rep.trivial ℤ (M ≃ₐ[F] M) ℤ))) :
    (ConcreteCategory.hom (groupCohomology.mapCocycles₂ (MonoidHom.id GL)
        (NK.NUV2.RouteC.powHom (F := F) (E := L) a)))
        ((ConcreteCategory.hom (groupCohomology.mapCocycles₂ resGL
          (trivialCoeffHom resGL))) z)
      = (ConcreteCategory.hom (groupCohomology.mapCocycles₂ resGL unitsIncl))
          ((ConcreteCategory.hom (groupCohomology.mapCocycles₂ (MonoidHom.id GM)
            (NK.NUV2.RouteC.powHom (F := F) (E := M) a))) z) := by
  apply groupCohomology.cocycles₂_ext
  intro g h
  exact mapCocycles₂_cup_eval (F := F) (M := M) (L := L) a z g h

/-- **The coefficient half of Brick E, on cocycles.** -/
theorem levelInfMap_cup_coeff_cocycle (a : Fˣ)
    (z : ↥(groupCohomology.cocycles₂ (Rep.trivial ℤ (M ≃ₐ[F] M) ℤ))) :
    (NK.NUV2.RouteC.levelInfMap (F := F) (M := M) (L := L))
        ((groupCohomology.map (MonoidHom.id GM)
          (NK.NUV2.RouteC.powHom (F := F) (E := M) a) 2)
          ((ConcreteCategory.hom (groupCohomology.H2π (Rep.trivial ℤ GM ℤ))) z))
      = (groupCohomology.map (MonoidHom.id GL)
          (NK.NUV2.RouteC.powHom (F := F) (E := L) a) 2)
          ((groupCohomology.map resGL (trivialCoeffHom resGL) 2)
            ((ConcreteCategory.hom (groupCohomology.H2π (Rep.trivial ℤ GM ℤ))) z)) := by
  rw [show NK.NUV2.RouteC.levelInfMap (F := F) (M := M) (L := L)
      = groupCohomology.map resGL unitsIncl 2 from rfl]
  rw [map_H2π_apply (A := Rep.trivial ℤ (M ≃ₐ[F] M) ℤ) (B := Rep.ofAlgebraAutOnUnits F M)
    (MonoidHom.id GM) (NK.NUV2.RouteC.powHom (F := F) (E := M) a) z]
  rw [map_H2π_apply (A := Rep.trivial ℤ (M ≃ₐ[F] M) ℤ) (B := Rep.trivial ℤ (L ≃ₐ[F] L) ℤ)
    resGL (trivialCoeffHom resGL) z]
  rw [map_H2π_apply (A := Rep.trivial ℤ (L ≃ₐ[F] L) ℤ) (B := Rep.ofAlgebraAutOnUnits F L)
    (MonoidHom.id GL) (NK.NUV2.RouteC.powHom (F := F) (E := L) a) _]
  rw [map_H2π_apply (A := Rep.ofAlgebraAutOnUnits F M) (B := Rep.ofAlgebraAutOnUnits F L)
    resGL unitsIncl _]
  rw [mapCocycles₂_cup_eq (F := F) (M := M) (L := L) a z]

/-- **The coefficient half of Brick E.** -/
theorem levelInfMap_cup_coeff (a : Fˣ)
    (x : groupCohomology (Rep.trivial ℤ (M ≃ₐ[F] M) ℤ) 2) :
    (NK.NUV2.RouteC.levelInfMap (F := F) (M := M) (L := L))
        ((groupCohomology.map (MonoidHom.id GM)
          (NK.NUV2.RouteC.powHom (F := F) (E := M) a) 2) x)
      = (groupCohomology.map (MonoidHom.id GL)
          (NK.NUV2.RouteC.powHom (F := F) (E := L) a) 2)
          ((groupCohomology.map resGL (trivialCoeffHom resGL) 2) x) :=
  groupCohomology.H2_induction_on x
    (fun z => levelInfMap_cup_coeff_cocycle (F := F) (M := M) (L := L) a z)

end CupCoeff

end NK.NUV2.RouteE
