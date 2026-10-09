import Mathlib
import Submission.Work.SSGRoute.PTDefsOmega
import Submission.Work.SSGRoute.ext_idele_shapiro
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

open SSGRoute.PTExt CategoryTheory

/-- A set of representatives of the orbits of a group action. -/
theorem exists_transversal_of_mulAction (G α : Type) [Group G] [MulAction G α] :
    ∃ R : Set α, ∀ w : α, ∃! w' : R, ∃ σ : G, σ • w = w'.1 := by
  refine ⟨Set.range (fun w : α =>
    Quotient.out (Quotient.mk'' w : Quotient (MulAction.orbitRel G α))), ?_⟩
  intro w
  refine ⟨⟨Quotient.out (Quotient.mk'' w), w, rfl⟩, ?_, ?_⟩
  · have h1 : (Quotient.mk'' (Quotient.out (Quotient.mk'' w : Quotient (MulAction.orbitRel G α)))
        : Quotient (MulAction.orbitRel G α)) = Quotient.mk'' w := Quotient.out_eq _
    have h2 : (MulAction.orbitRel G α)
        (Quotient.out (Quotient.mk'' w : Quotient (MulAction.orbitRel G α))) w :=
      Quotient.exact h1
    rw [MulAction.orbitRel_apply] at h2
    exact h2
  · rintro ⟨y, hy⟩ ⟨σ, hσ⟩
    obtain ⟨w₀, hw₀⟩ := hy
    have hrel : (MulAction.orbitRel G α) y w := by
      rw [MulAction.orbitRel_apply]
      exact ⟨σ, hσ⟩
    have hq : (Quotient.mk'' y : Quotient (MulAction.orbitRel G α)) = Quotient.mk'' w :=
      Quotient.sound hrel
    have hq' : (Quotient.mk'' w₀ : Quotient (MulAction.orbitRel G α)) = Quotient.mk'' y := by
      rw [← hw₀]
      exact (Quotient.out_eq (Quotient.mk'' w₀)).symm
    apply Subtype.ext
    exact hw₀.symm.trans (congrArg Quotient.out (hq'.trans hq))

/-- Restriction to a subgroup `D ≤ G` of a cohomology class `x ∈ H^n(G, A)` agrees, as a class in
`H^n(D, res A)`, with the image `extRes D.subtype x` under the exact functor `Rep.resFunctor`: the
two differ only by the factor `mk₀ (unitRes D.subtype)`, which is the identity because
`unitRes D.subtype = 𝟙 (unitRep D)` definitionally. -/
theorem extRes_eq_extHRestrict {G : Type} [Group G] (D : Subgroup G)
    {A : Rep.{0} Coeff G} {n : ℕ} (x : extH A n) :
    extHRestrict D x = extRes D.subtype x := by
  rw [extHRestrict, extHMap]
  have h2 : (extRes D.subtype x).comp
      (Abelian.Ext.mk₀ (𝟙 (Rep.res D.subtype A))) (add_zero n) = extRes D.subtype x :=
    Abelian.Ext.comp_mk₀_id _
  rw [h2]
  exact Abelian.Ext.mk₀_id_comp _

/-- **Idèle localisation is injective on `H²`.**  A class `y ∈ H²(Gal(L/k), 𝕀_L)` whose
localisation at every place `w` of `L` (i.e. the restriction to the decomposition group `D_w`
pushed to the `w`-component `L_wˣ`) vanishes is itself zero.

This is the injectivity half of the idèle Shapiro theorem (E2,
`Work.SSGRoute.ext_idele_shapiro_aux`) applied to a transversal of the `Gal(L/k)`-orbits of the
places: the localisations at the places of a transversal detect `y`, and the localisation map is
written equivalently through `extHRestrict` and `mk₀ (ideleToLocalUnits k L w)`. -/
theorem extIdele_localisation_injective (k L : Type) [Field k]
    [NumberField k] [Field L] [NumberField L] [Algebra k L] [FiniteDimensional k L]
    [IsGalois k L] (y : SSGRoute.PTExt.extH (SSGRoute.PTExt.idelesK k L) 2)
    (h : ∀ w : NK.GlobalCFT.Place L,
      (SSGRoute.PTExt.extHRestrict (MulAction.stabilizer (L ≃ₐ[k] L) w) y).comp
        (CategoryTheory.Abelian.Ext.mk₀ (NK.HassePrinciple.ideleToLocalUnits k L w)) (add_zero 2) = 0) :
    y = 0 := by
  obtain ⟨R, hR⟩ := exists_transversal_of_mulAction (L ≃ₐ[k] L) (NK.GlobalCFT.Place L)
  refine (Work.SSGRoute.ext_idele_shapiro_aux (k := k) (K := L)
    (unitRep (L ≃ₐ[k] L)) (by infer_instance) 2 R hR).1 y ?_
  intro w _hw
  show (extRes (decompK (k := k) w).subtype y).comp
    (Abelian.Ext.mk₀ (NK.HassePrinciple.ideleToLocalUnits k L w)) (add_zero 2) = 0
  rw [← extRes_eq_extHRestrict (D := decompK (k := k) w) y]
  exact h w

end Work.SSGRoute
