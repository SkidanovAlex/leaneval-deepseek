import Mathlib
import Submission.Work.Pi6.MSSK.LastEdge
import Submission.Work.SSSR.serreE1PieceExplicit
import Submission.Work.SSSR.iotaStatement_zero_c_one
import Submission.Work.SSSR.serreE1PieceIsoZero
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 800000

namespace Work.Pi6.MSSK

open CategoryTheory CategoryTheory.Limits Simplicial Opposite

variable {R : Type} [CommRing R] [Nontrivial R]
variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

/-! ## Two elementary pieces

The cokernel identification `pieceAlongZeroCokerIso` is a (degreewise) inverse of the quotient map
`pieceπOf`, and `pieceAlongZeroIso` is, at every degree, `pieceAlongZeroCokerIso` followed by the
chain map induced by `pullAlongVertexIsoIso` (the third factor of the definition is a transport
along a definitional equality, hence invisible).  Everything below is a formal consequence of those
two facts together with the degree transport `Work.SSSR.izo_castElem_map`. -/

/-- `pieceπOf` followed by `pieceAlongZeroCokerIso` is the identity, elementwise. -/
theorem pieceπOf_cokerIso_apply (p : C(E, B))
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk 0) : SSet.{0}) ⟶ Work.SSSR.sSing B)
    (n : ℕ) (b : (Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)).X n) :
    (Work.SSSR.pieceAlongZeroCokerIso (R := R) p σ).hom.f n
      ((Work.SSSR.pieceπOf (Work.SSSR.sSingP p) σ).f n b) = b := by
  have h := Work.SSSR.SZero.zc_cokerIso_comp (R := R) p σ
  have h2 := congrArg (fun (g : Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ) ⟶
      Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)) => g.f n) h
  have h3 := congrArg (fun (g : (Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)).X n ⟶
      (Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)).X n) => g b) h2
  simpa only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply,
    HomologicalComplex.id_f, CategoryTheory.id_apply] using h3

/-- Degreewise unfolding of `pieceAlongZeroIso`. -/
theorem pieceAlongZeroIso_fac (p : C(E, B))
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk 0) : SSet.{0}) ⟶ Work.SSSR.sSing B) (k : ℕ) :
    (Work.SSSR.pieceAlongZeroIso (R := R) p σ).hom.f k
      = (Work.SSSR.pieceAlongZeroCokerIso (R := R) p σ).hom.f k ≫
        (Work.SSSR.sCCMap R ((Work.SSSR.pullAlongVertexIsoIso p σ).hom)).f k := by
  rw [Work.SSSR.pieceAlongZeroIso]
  simp only [Iso.trans_hom, CategoryTheory.Functor.mapIso_hom, HomologicalComplex.comp_f,
    CategoryTheory.eqToIso.hom, CategoryTheory.eqToHom_refl, Category.comp_id, Work.SSSR.sCCMap]

theorem pieceAlongZeroIsoCast {R : Type} [CommRing R] [Nontrivial R] {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (σ : (SSet.stdSimplex.obj (SimplexCategory.mk 0) : SSet.{0}) ⟶ Work.SSSR.sSing B) (k : ℕ)
    (x : (Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)).X (0 + k)) :
    (Work.SSSR.pieceAlongZeroIso p σ).hom.f k
        (Work.SSSR.castElem (Work.SSSR.pieceAlong R (Work.SSSR.sSingP p) σ) (Nat.zero_add k)
          ((Work.SSSR.pieceπOf (Work.SSSR.sSingP p) σ).f (0 + k) x))
      = (Work.SSSR.sCCMap R (Work.Pi6.MSSK.vertexIso p σ).hom).f k
          (Work.SSSR.castElem (Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ))
            (Nat.zero_add k) x) := by
  rw [pieceAlongZeroIso_fac (R := R) p σ k]
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
  rw [← Work.SSSR.izo_castElem_map (R := R)
        (φ := (Work.SSSR.pieceAlongZeroCokerIso (R := R) p σ).hom)
        (i := 0 + k) (j := k) (h := Nat.zero_add k)
        ((Work.SSSR.pieceπOf (Work.SSSR.sSingP p) σ).f (0 + k) x)]
  rw [pieceπOf_cokerIso_apply (R := R) p σ (0 + k) x]
  simp only [Work.Pi6.MSSK.vertexIso]
  rfl

end Work.Pi6.MSSK
