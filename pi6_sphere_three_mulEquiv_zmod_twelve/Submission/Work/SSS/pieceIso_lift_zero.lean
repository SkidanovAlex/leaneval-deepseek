import Mathlib
import Submission.Work.SSS.piszDefs
import Submission.Work.SSS.serreE1PieceExplicit
import Submission.Work.SSS.pieceAlongZero
import Submission.Work.SSS.serreE1EZ
import Submission.Work.SSS.iotaStatement_zero_c_one

namespace Work.SSS

open CategoryTheory CategoryTheory.Limits Simplicial Opposite MonoidalCategory
open scoped MonoidalCategory Simplicial Topology

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

/-- **The simplicial identity behind the `P = 0` tower comparison.**  For an arbitrary lift `ez` of
`pr₁ ≫ σ` along a vertex `σ`, and a map `v` of fibres whose composite with the fibre inclusion is
the `v₀`-slice `vertIncl p b 0 ≫ ez ≫ pullback.snd σ (sSingP p)` of the lift, one has
`v ≫ phiAlong p σ = vertIncl p b 0 ≫ ez`. -/
theorem pieceIsoLiftZero_v_comp_phiAlong (p : C(E, B)) (b : B)
    (σ : ((SSet.stdSimplex.obj (SimplexCategory.mk 0) : SSet.{0})) ⟶ Work.SSS.sSing B)
    (ez : (((SSet.stdSimplex.obj (SimplexCategory.mk 0) : SSet.{0})) ⊗
        Work.SSS.sSing (Work.StemsB.fibre p b)) ⟶ Work.SSS.pullAlong (Work.SSS.sSingP p) σ)
    (hez : ez ≫ pullback.fst σ (Work.SSS.sSingP p) = SemiCartesianMonoidalCategory.fst _ _)
    (v : Work.SSS.sSing (Work.StemsB.fibre p b) ⟶
      Work.SSS.sSing (Work.StemsB.fibre p (Work.SSS.sigmaVert σ)))
    (hv : v ≫ Work.SSS.sSingP (Work.StemsB.fibreIncl p (Work.SSS.sigmaVert σ))
      = Work.SSS.vertIncl p b 0 ≫ ez ≫ pullback.snd σ (Work.SSS.sSingP p)) :
    v ≫ Work.SSS.phiAlong p σ = Work.SSS.vertIncl p b 0 ≫ ez := by
  apply pullback.hom_ext
  · -- first component: both land in the terminal `Δ[0]`
    have h3 : Work.SSS.phiAlongFst p σ
        = SSet.const (X := Work.SSS.sSing (Work.StemsB.fibre p (Work.SSS.sigmaVert σ)))
            (ssetVertex 0) := by
      unfold Work.SSS.phiAlongFst
      rw [Work.SSS.izo_ssetVertex_zero_eq_yoneda]
    simp only [Category.assoc, Work.SSS.phiAlong_fst, hez, Work.SSS.vertIncl_fst]
    rw [h3, SSet.comp_const]
  · -- second component: this is `hv`
    simp only [Category.assoc, Work.SSS.phiAlong_snd]
    exact hv

/-- **The `(0,t)` shuffle at the vertex is the vertex inclusion** (after the degree transport
`0 + t = t`). -/
theorem castElem_ezGen_zero_vertIncl (p : C(E, B)) (b : B) (t : ℕ)
    (τ : (Work.SSS.sSing (Work.StemsB.fibre p b)) _⦋t⦌) :
    Work.SSS.castElem
        (Work.SSS.sCC (((SSet.stdSimplex.obj (SimplexCategory.mk 0) : SSet.{0})) ⊗
          Work.SSS.sSing (Work.StemsB.fibre p b))) (Nat.zero_add t)
        (Work.Cohomology.Crux33.ezGen 0 t
          (SSet.stdSimplex.obj (SimplexCategory.mk 0) : SSet.{0})
          (Work.SSS.sSing (Work.StemsB.fibre p b)) (Work.SSS.stdIdSimplex 0) τ)
      = (Work.SSS.sCCMap (Work.SSS.vertIncl p b 0)).f t
          (((Work.SSS.sSing (Work.StemsB.fibre p b)).ιChainComplex
            (R := ModuleCat.of ℤ ℤ) τ).hom 1) := by
  rw [Work.SSS.izo_ezGen_zero_eq_vertIncl p b t τ]
  rw [Work.SSS.izo_castElem_map]
  rw [Work.SSS.izo_castElem_ιChainComplex]
  rw [Work.SSS.izo_castSimp_zSh_bHom]

/-- **The base case `P = 0` of the tower comparison for an arbitrary lift.**

For a *vertex* `σ : Δ[0] ⟶ Sing B`, a lift `ez : Δ[0] ⊗ Sing (p⁻¹b) ⟶ T_σ` of `pr₁ ≫ σ`, a map
`v : Sing (p⁻¹b) ⟶ Sing (p⁻¹σ(v₀))` whose composite with the fibre inclusion is the `v₀`-slice
`vertIncl p b 0 ≫ ez ≫ pullback.snd σ (sSingP p)` of the lift (`hv`), and a cycle `τ` of `p⁻¹b`,
the base-piece isomorphism `ε_σ = serreE1PieceIso p hfib 0 t σ` sends the class of the projection of
`ez_*(EZ(0,t,[id],τ))` to the class of `v_*(τ)`.

Here `∂T_σ = ⊥`, so `pieceAlong (sSingP p) σ ≅ C(T_σ)`, `pullAlong (sSingP p) σ ≅ Sing (p⁻¹σ(v₀))`
(via `Work.SSS.phiAlong`, an isomorphism for a vertex) and `EZ(0,t,[id],τ)` is the shuffle chain of
the vertex and `τ`; the conclusion is a computation with `Work.SSS.pieceAlongZeroIso`,
`Work.SSS.phiAlong_snd` and `Work.SSS.vertIncl_snd`.  This is the `P = 0` instance of the planned
general comparison `Work.SSS.pieceIso_lift_gen` (in `piszReq.lean`), with the sign `1`. -/
theorem pieceIso_lift_zero (p : C(E, B)) (hfib : Work.StemsB.IsSerreFibration p) (t : ℕ) (b : B)
    (σ : ((SSet.stdSimplex.obj (SimplexCategory.mk 0) : SSet.{0})) ⟶ Work.SSS.sSing B)
    (ez : (((SSet.stdSimplex.obj (SimplexCategory.mk 0) : SSet.{0})) ⊗
        Work.SSS.sSing (Work.StemsB.fibre p b)) ⟶ Work.SSS.pullAlong (Work.SSS.sSingP p) σ)
    (hez : ez ≫ pullback.fst σ (Work.SSS.sSingP p) = SemiCartesianMonoidalCategory.fst _ _)
    (v : Work.SSS.sSing (Work.StemsB.fibre p b) ⟶
      Work.SSS.sSing (Work.StemsB.fibre p (Work.SSS.sigmaVert σ)))
    (hv : v ≫ Work.SSS.sSingP (Work.StemsB.fibreIncl p (Work.SSS.sigmaVert σ))
      = Work.SSS.vertIncl p b 0 ≫ ez ≫ pullback.snd σ (Work.SSS.sSingP p))
    (τ : Work.SSS.sSing (Work.StemsB.fibre p b) _⦋t⦌)
    (hτ : (ModuleCat.Hom.hom ((Work.SSS.sCC (Work.SSS.sSing (Work.StemsB.fibre p b))).d t
        ((ComplexShape.down ℕ).next t)))
        (((Work.SSS.sSing (Work.StemsB.fibre p b)).ιChainComplex (R := ModuleCat.of ℤ ℤ) τ).hom 1) = 0)
    (hcyc : (ModuleCat.Hom.hom ((Work.SSS.pieceAlong (Work.SSS.sSingP p) σ).d (0+t)
        ((ComplexShape.down ℕ).next (0+t))))
        ((ModuleCat.Hom.hom ((Work.SSS.pieceπOf (Work.SSS.sSingP p) σ).f (0+t)))
          ((ModuleCat.Hom.hom ((Work.SSS.sCCMap ez).f (0+t)))
            (Work.Cohomology.Crux33.ezGen 0 t
              (SSet.stdSimplex.obj (SimplexCategory.mk 0) : SSet.{0})
              (Work.SSS.sSing (Work.StemsB.fibre p b)) (Work.SSS.stdIdSimplex 0) τ))) = 0)
    (hcyc' : (ModuleCat.Hom.hom ((Work.SSS.sCC (Work.SSS.sSing
        (Work.StemsB.fibre p (Work.SSS.sigmaVert σ)))).d t ((ComplexShape.down ℕ).next t)))
        ((ModuleCat.Hom.hom ((Work.SSS.sCCMap v).f t))
          (((Work.SSS.sSing (Work.StemsB.fibre p b)).ιChainComplex
            (R := ModuleCat.of ℤ ℤ) τ).hom 1)) = 0) :
    (Work.SSS.serreE1PieceIso p hfib 0 t σ).hom
        ((HomologicalComplex.homologyπ (Work.SSS.pieceAlong (Work.SSS.sSingP p) σ) (0+t))
          ((Work.SSS.pieceAlong (Work.SSS.sSingP p) σ).cyclesMk
            ((ModuleCat.Hom.hom ((Work.SSS.pieceπOf (Work.SSS.sSingP p) σ).f (0+t)))
              ((ModuleCat.Hom.hom ((Work.SSS.sCCMap ez).f (0+t)))
                (Work.Cohomology.Crux33.ezGen 0 t
                  (SSet.stdSimplex.obj (SimplexCategory.mk 0) : SSet.{0})
                  (Work.SSS.sSing (Work.StemsB.fibre p b)) (Work.SSS.stdIdSimplex 0) τ)))
            ((ComplexShape.down ℕ).next (0+t)) rfl hcyc))
      = (HomologicalComplex.homologyπ
            (Work.SSS.sCC (Work.SSS.sSing (Work.StemsB.fibre p (Work.SSS.sigmaVert σ)))) t)
          ((Work.SSS.sCC (Work.SSS.sSing (Work.StemsB.fibre p
              (Work.SSS.sigmaVert σ)))).cyclesMk
            ((ModuleCat.Hom.hom ((Work.SSS.sCCMap v).f t))
              (((Work.SSS.sSing (Work.StemsB.fibre p b)).ιChainComplex
                (R := ModuleCat.of ℤ ℤ) τ).hom 1))
            ((ComplexShape.down ℕ).next t) rfl hcyc') := by
  haveI hφiso : IsIso (Work.SSS.phiAlong p σ) := Work.SSS.phiAlong_isIso p σ
  -- (1) `v` is the vertex slice of the lift
  have hvcomp : v ≫ Work.SSS.phiAlong p σ = Work.SSS.vertIncl p b 0 ≫ ez :=
    pieceIsoLiftZero_v_comp_phiAlong p b σ ez hez v hv
  have hv_eq : v = Work.SSS.vertIncl p b 0 ≫ ez
      ≫ CategoryTheory.inv (Work.SSS.phiAlong p σ) := by
    calc v = v ≫ 𝟙 (Work.SSS.sSing (Work.StemsB.fibre p (Work.SSS.sigmaVert σ))) :=
            (Category.comp_id v).symm
      _ = v ≫ (Work.SSS.phiAlong p σ ≫ CategoryTheory.inv (Work.SSS.phiAlong p σ)) := by
            rw [CategoryTheory.IsIso.hom_inv_id]
      _ = (v ≫ Work.SSS.phiAlong p σ) ≫ CategoryTheory.inv (Work.SSS.phiAlong p σ) :=
            (Category.assoc _ _ _).symm
      _ = (Work.SSS.vertIncl p b 0 ≫ ez) ≫ CategoryTheory.inv (Work.SSS.phiAlong p σ) := by
            rw [hvcomp]
      _ = Work.SSS.vertIncl p b 0 ≫ ez ≫ CategoryTheory.inv (Work.SSS.phiAlong p σ) :=
            Category.assoc _ _ _
  -- (2) the unfolding of `pieceAlongZeroIso` at degree `t`
  have hfac : (Work.SSS.pieceAlongZeroIso p σ).hom.f t
      = (Work.SSS.pieceAlongZeroCokerIso p σ).hom.f t ≫
        (Work.SSS.sCCMap ((Work.SSS.pullAlongVertexIsoIso p σ).hom)).f t := by
    rw [Work.SSS.pieceAlongZeroIso]
    simp only [CategoryTheory.Iso.trans_hom, CategoryTheory.Functor.mapIso_hom,
      HomologicalComplex.comp_f, CategoryTheory.eqToIso.hom, CategoryTheory.eqToHom_refl,
      HomologicalComplex.id_f, Category.comp_id, Work.SSS.sCCMap]
  -- (3) the cokernel projection is undone by `pieceAlongZeroCokerIso`
  have hmor : (Work.SSS.pieceπOf (Work.SSS.sSingP p) σ).f t
      ≫ (Work.SSS.pieceAlongZeroCokerIso p σ).hom.f t = 𝟙 _ := by
    have hh := congrArg (fun (g : Work.SSS.sCC (Work.SSS.pullAlong (Work.SSS.sSingP p) σ) ⟶
        Work.SSS.sCC (Work.SSS.pullAlong (Work.SSS.sSingP p) σ)) => g.f t)
      (Work.SSS.izo_cokerIso_comp p σ)
    simpa using hh
  have hmor' : ∀ y : (Work.SSS.sCC (Work.SSS.pullAlong (Work.SSS.sSingP p) σ)).X t,
      (Work.SSS.pieceAlongZeroCokerIso p σ).hom.f t
        ((Work.SSS.pieceπOf (Work.SSS.sSingP p) σ).f t y) = y := by
    intro y
    have hh := congrArg (fun (g : (Work.SSS.sCC (Work.SSS.pullAlong (Work.SSS.sSingP p) σ)).X t ⟶
        (Work.SSS.sCC (Work.SSS.pullAlong (Work.SSS.sSingP p) σ)).X t) => g y) hmor
    simpa only [HomologicalComplex.comp_f, ModuleCat.hom_comp,
      LinearMap.comp_apply, CategoryTheory.id_apply] using hh
  -- (4) the shuffle chain at `P = 0` is the vertex inclusion
  have hce : Work.SSS.castElem
        (Work.SSS.sCC (((SSet.stdSimplex.obj (SimplexCategory.mk 0) : SSet.{0})) ⊗
          Work.SSS.sSing (Work.StemsB.fibre p b))) (Nat.zero_add t)
        (Work.Cohomology.Crux33.ezGen 0 t
          (SSet.stdSimplex.obj (SimplexCategory.mk 0) : SSet.{0})
          (Work.SSS.sSing (Work.StemsB.fibre p b)) (Work.SSS.stdIdSimplex 0) τ)
      = (Work.SSS.sCCMap (Work.SSS.vertIncl p b 0)).f t
          (((Work.SSS.sSing (Work.StemsB.fibre p b)).ιChainComplex
            (R := ModuleCat.of ℤ ℤ) τ).hom 1) :=
    castElem_ezGen_zero_vertIncl p b t τ
  -- (5) the chain-level equality `H` required by `izo_homology_apply`
  have H : (Work.SSS.pieceAlongZeroIso p σ).hom.f t
      (Work.SSS.castElem (Work.SSS.pieceAlong (Work.SSS.sSingP p) σ) (Nat.zero_add t)
        ((Work.SSS.pieceπOf (Work.SSS.sSingP p) σ).f (0+t)
          ((Work.SSS.sCCMap ez).f (0+t)
            (Work.Cohomology.Crux33.ezGen 0 t
              (SSet.stdSimplex.obj (SimplexCategory.mk 0) : SSet.{0})
              (Work.SSS.sSing (Work.StemsB.fibre p b)) (Work.SSS.stdIdSimplex 0) τ))))
    = (Work.SSS.sCCMap v).f t
        (((Work.SSS.sSing (Work.StemsB.fibre p b)).ιChainComplex
          (R := ModuleCat.of ℤ ℤ) τ).hom 1) := by
    rw [hfac]
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
    rw [Work.SSS.izo_castElem_map]
    rw [hmor']
    rw [Work.SSS.izo_castElem_map]
    rw [hce]
    rw [show (Work.SSS.pullAlongVertexIsoIso p σ).hom
        = CategoryTheory.inv (Work.SSS.phiAlong p σ) from rfl]
    rw [hv_eq]
    simp only [Work.SSS.izo_sCCMap_comp, HomologicalComplex.comp_f, ModuleCat.hom_comp,
      LinearMap.comp_apply]
    rfl
  -- (6) assemble
  rw [Work.SSS.izo_serreE1PieceIso_zero_eq p hfib (Work.SSS.sigmaVert σ) σ rfl t]
  simp only [CategoryTheory.Iso.trans_hom, CategoryTheory.comp_apply]
  exact Work.SSS.izo_homology_apply (Work.SSS.pieceAlongZeroIso p σ).hom (Nat.zero_add t)
    ((Work.SSS.pieceπOf (Work.SSS.sSingP p) σ).f (0+t)
      ((Work.SSS.sCCMap ez).f (0+t)
        (Work.Cohomology.Crux33.ezGen 0 t
          (SSet.stdSimplex.obj (SimplexCategory.mk 0) : SSet.{0})
          (Work.SSS.sSing (Work.StemsB.fibre p b)) (Work.SSS.stdIdSimplex 0) τ)))
    hcyc
    ((Work.SSS.sCCMap v).f t
      (((Work.SSS.sSing (Work.StemsB.fibre p b)).ιChainComplex
        (R := ModuleCat.of ℤ ℤ) τ).hom 1))
    hcyc' H

end Work.SSS
