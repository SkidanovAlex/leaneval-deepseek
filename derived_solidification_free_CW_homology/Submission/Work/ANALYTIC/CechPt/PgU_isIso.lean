import Mathlib
import Submission.Work.ANALYTIC.CechPt.doubleDualUnit_sigma_unit

/-!
# The coordinate map `PgU J` of the free object `∐_J 𝟙` is an isomorphism

For a finite index type `J`, the coordinate map

`PgU J : sd (∐_J 𝟙) ⟶ ∏_J 𝟙`,  `λ ↦ (λ (ι_j))_j`

is an isomorphism.  Indeed `sd (∐_J 𝟙) = [∐_J 𝟙, 𝟙]` and the canonical comparison morphism
of a monoidal closed category

`[∐_j A_j, Z] ⟶ ∏_j [A_j, Z]`,  `Pi.lift (fun j => (pre (Sigma.ι A j)).app Z)`

is an isomorphism (this is the "internal hom turns coproducts into products" statement, here
proved by exhibiting it as the comparison of two limit cones for the same diagram: the image
under the right adjoint `[-, Z]` of the coproduct cocone, and the product cone).  The final
factor `∏_j [𝟙, 𝟙] ⟶ ∏_j 𝟙` is `Pi.map` of the isomorphisms `MonoidalClosed.unitIsoSelf`.
-/

namespace Work.ANALYTIC.CechPt

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed

open _root_.LightCondensed _root_.LightCondensed.Solid

noncomputable section

set_option linter.style.haveILetI false

/-- **Internal hom out of a coproduct.**  For any family `A : J → LightCondAb` and any
`Z : LightCondAb`, the canonical comparison morphism

`[∐_j A_j, Z] ⟶ ∏_j [A_j, Z]`,  `Pi.lift (fun j => (pre (Sigma.ι A j)).app Z)`

is an isomorphism. -/
theorem isIso_piLift_pre (J : Type) (A : J → LightCondAb) (Z : LightCondAb)
    [HasCoproduct A] [HasProduct (fun j => (ihom (A j)).obj Z)] :
    IsIso (Pi.lift (fun j => (MonoidalClosed.pre (Sigma.ι A j)).app Z)) := by
  classical
  -- `f j = [A_j, Z]`
  let f : J → LightCondAb := fun j => (ihom (A j)).obj Z
  -- the functor `[-, Z] : Cᵒᵖ ⥤ C`, a right adjoint
  let G : LightCondAbᵒᵖ ⥤ LightCondAb := MonoidalClosed.internalHom.flip.obj Z
  -- the coproduct cocone of `A`; it is a limit cone after applying `G` (contravariantly)
  let c : Cofan A := Cofan.mk (sigmaObj A) (Sigma.ι A)
  have hc : IsColimit c := coproductIsCoproduct A
  have hlim0 : IsLimit (G.mapCone (Cocone.op c)) := isLimitOfPreserves G (IsColimit.op hc)
  -- reindex along the equivalence `(Discrete J)ᵒᵖ ≌ Discrete J`
  have hlim1 :
      IsLimit (Cone.whisker (Discrete.opposite J).symm.functor (G.mapCone (Cocone.op c))) :=
    hlim0.whiskerEquivalence (Discrete.opposite J).symm
  have hD : (Discrete.opposite J).symm.functor ⋙ ((Discrete.functor A).op ⋙ G) =
      Discrete.functor f := by
    apply Discrete.functor_ext
    intro j
    rfl
  have α : ((Discrete.opposite J).symm.functor ⋙ ((Discrete.functor A).op ⋙ G)) ≅
      Discrete.functor f := eqToIso hD
  have hlim2 : IsLimit ((Cone.postcompose α.hom).obj
      (Cone.whisker (Discrete.opposite J).symm.functor (G.mapCone (Cocone.op c)))) :=
    (IsLimit.postcomposeHomEquiv α _).symm hlim1
  let C2 : Fan f := (Cone.postcompose α.hom).obj
    (Cone.whisker (Discrete.opposite J).symm.functor (G.mapCone (Cocone.op c)))
  have hlim2' : IsLimit C2 := hlim2
  -- hence the comparison morphism `C2.pt ⟶ ∏_j f j` is an isomorphism
  have hiso : IsIso (Pi.lift C2.proj) := by
    let m : C2 ⟶ (Fan.mk (∏ᶜ f) (Pi.π f)) :=
      { hom := Pi.lift C2.proj
        w := fun j => Pi.lift_comp_π C2.proj j.as }
    haveI : IsIso m := hlim2'.hom_isIso (productIsProduct f) m
    exact Functor.map_isIso (Cone.forget (Discrete.functor f)) m
  -- the legs of `C2` differ from the legs of the product cone only by the `eqToHom`-factors
  -- of the diagram identification `α`, which are isomorphisms
  let i : ∀ j : J, f j ≅ f j := fun j => α.app (Discrete.mk j)
  let c₁ : Fan f := Fan.mk C2.pt (fun j => (MonoidalClosed.pre (Sigma.ι A j)).app Z)
  have hC : ∀ j : J, C2.proj j = c₁.proj j ≫ (i j).hom := fun j => rfl
  let P : (∏ᶜ f) ⟶ (∏ᶜ f) :=
    CategoryTheory.Limits.Pi.map (f := f) (g := f) (fun j => (i j).hom)
  have hP : IsIso P := by
    have h : IsIso (CategoryTheory.Limits.Pi.map (f := f) (g := f) (fun j => (i j).hom)) := by
      have h2 : CategoryTheory.Limits.Pi.map (f := f) (g := f) (fun j => (i j).hom) =
          (Pi.mapIso i).hom := by
        refine Pi.hom_ext _ _ (fun j => ?_)
        rw [Pi.mapIso_hom_π, Pi.map_π]
      rw [h2]
      exact (Pi.mapIso i).isIso_hom
    exact h
  have hcomp : Pi.lift C2.proj = Pi.lift c₁.proj ≫ P := by
    refine Pi.hom_ext _ _ (fun j => ?_)
    rw [Pi.lift_comp_π, hC j, Category.assoc, CategoryTheory.Limits.Pi.map_π,
      ← Category.assoc, Pi.lift_comp_π]
  have hL : IsIso (Pi.lift c₁.proj ≫ P) := by rw [← hcomp]; exact hiso
  haveI := hP
  haveI := hL
  exact IsIso.of_isIso_comp_right (Pi.lift c₁.proj) P

/-- **The coordinate map `PgU J` is an isomorphism.**  For a finite index type `J`, the
coordinate map `PgU J : sd (∐_J 𝟙) ⟶ ∏_J 𝟙` is an isomorphism: it is the composite of the
canonical isomorphism `[∐_J 𝟙, 𝟙] ≅ ∏_J [𝟙, 𝟙]` and `Pi.map` of the isomorphisms
`[𝟙, 𝟙] ≅ 𝟙`. -/
theorem PgU_isIso (J : Type) [Fintype J] :
    CategoryTheory.IsIso (Work.ANALYTIC.CechPt.PgU J) := by
  classical
  let L := Pi.lift (fun j : J =>
    (MonoidalClosed.pre (Sigma.ι (fun _ : J => 𝟙_ LightCondAb) j)).app (𝟙_ LightCondAb))
  have hL : IsIso L :=
    isIso_piLift_pre J (fun _ : J => 𝟙_ LightCondAb) (𝟙_ LightCondAb)
  let Q : (∏ᶜ (fun _ : J => (ihom (𝟙_ LightCondAb)).obj (𝟙_ LightCondAb))) ⟶ prodU J :=
    CategoryTheory.Limits.Pi.map
      (f := fun _ : J => (ihom (𝟙_ LightCondAb)).obj (𝟙_ LightCondAb))
      (g := fun _ : J => 𝟙_ LightCondAb)
      (fun _ : J => (MonoidalClosed.unitIsoSelf (𝟙_ LightCondAb)).hom)
  have hQ : IsIso Q := by
    have h2 : Q = (Pi.mapIso (fun _ : J =>
        MonoidalClosed.unitIsoSelf (𝟙_ LightCondAb))).hom := by
      refine Pi.hom_ext _ _ (fun j => ?_)
      rw [Pi.mapIso_hom_π, CategoryTheory.Limits.Pi.map_π]
    rw [h2]
    exact (Pi.mapIso _).isIso_hom
  have hsplit : PgU J = L ≫ Q := by
    show (Pi.lift (fun j : J => (MonoidalClosed.pre (inclU J j)).app (𝟙_ LightCondAb) ≫
      (MonoidalClosed.unitIsoSelf (𝟙_ LightCondAb)).hom)) = L ≫ Q
    refine Pi.hom_ext _ _ (fun j => ?_)
    rw [Pi.lift_comp_π, Category.assoc, CategoryTheory.Limits.Pi.map_π,
      ← Category.assoc, Pi.lift_comp_π]
    rfl
  haveI := hL
  haveI := hQ
  rw [hsplit]
  exact (asIso L ≪≫ asIso Q).isIso_hom

end

end Work.ANALYTIC.CechPt
