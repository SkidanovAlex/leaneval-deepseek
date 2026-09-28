import Mathlib
import Submission.Work.SSS.pieceAlongZero
import Submission.Work.SSS.serreE1PieceExplicit
import Submission.Work.SSS.ezGen_snd_sum_zero
import Submission.Work.SSS.serreE1EZ
import Submission.Work.SSS.serreE1PieceIotaDefs
import Submission.Work.SSS.pieceIso_lift_zero

namespace Work.SSS

open CategoryTheory CategoryTheory.Limits Simplicial Opposite MonoidalCategory
open scoped MonoidalCategory Simplicial Topology

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

/-- The `castElem` transport of a chain complex is the `eqToHom` transport, in `ModuleCat.Hom.hom`
form. -/
lemma castElem_eqToHom_hom {K : ChainComplex (ModuleCat ℤ) ℕ} {i j : ℕ} (h : i = j)
    (x : K.X i) : (ModuleCat.Hom.hom (eqToHom (congr_arg K.X h))) x = castElem K h x := by
  subst h; simp [castElem]

/-- **The `P = 0` shuffle is the vertex inclusion, for an arbitrary chain.**  The map
`ezLinSnd 0 t Δ[0] (Sing F) (id)`, transported from degree `0 + t` to degree `t`, is the map
induced on chains by the vertex inclusion `vertIncl p b 0`.  This linearises
`Work.SSS.castElem_ezGen_zero_vertIncl` from a simplex `τ` to an arbitrary chain `z`. -/
lemma ezLinSnd_zero_vertIncl {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (b : B) (t : ℕ) (z : (Work.SSS.fibreCC p b).X t) :
    Work.SSS.castElem (Work.SSS.sCC ((SSet.stdSimplex.obj (SimplexCategory.mk 0) : SSet.{0}) ⊗
        Work.SSS.sSing (Work.StemsB.fibre p b))) (Nat.zero_add t)
      (Work.SSS.ezLinSnd 0 t (SSet.stdSimplex.obj (SimplexCategory.mk 0) : SSet.{0})
        (Work.SSS.sSing (Work.StemsB.fibre p b)) (Work.SSS.stdIdSimplex 0) z)
      = (Work.SSS.sCCMap (Work.SSS.vertIncl p b 0)).f t z := by
  have key : Work.SSS.ezLinSnd 0 t (SSet.stdSimplex.obj (SimplexCategory.mk 0) : SSet.{0})
        (Work.SSS.sSing (Work.StemsB.fibre p b)) (Work.SSS.stdIdSimplex 0) ≫
      eqToHom (congrArg (fun m => (((SSet.stdSimplex.obj (SimplexCategory.mk 0) : SSet.{0}) ⊗
        Work.SSS.sSing (Work.StemsB.fibre p b)).chainComplex Work.SSS.ezR).X m) (Nat.zero_add t))
      = (Work.SSS.sCCMap (Work.SSS.vertIncl p b 0)).f t := by
    apply SSet.chainComplex_hom_ext
    intro τ
    rw [← Category.assoc, ezLinSnd_ι]
    apply ModuleCat.hom_ext
    apply LinearMap.ext_ring
    simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply,
      LinearMap.toSpanSingleton_apply_one]
    rw [castElem_eqToHom_hom]
    exact Work.SSS.castElem_ezGen_zero_vertIncl p b t τ
  have h2 := congrArg (fun g => (ModuleCat.Hom.hom g) z) key
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h2
  rw [← castElem_eqToHom_hom]
  exact h2

/-- The `P = 0` case of the tower comparison, for an arbitrary CHAIN: at a vertex `σ : Δ[0] → Sing B`
with base point `b = sigmaVert σ`, an arbitrary lift `ez : Δ[0] ⊗ Sing (p⁻¹b) → T_σ` of `pr₁ ≫ σ`
and a map `v : Sing (p⁻¹b) → Sing (p⁻¹σ(v₀))` whose composite with the fibre inclusion is the
`v₀`-slice of `ez`, the connecting map `ε_σ = serreE1PieceIso p hfib 0 t σ` sends the class of the
projection of the shuffle chain of `z` to the class of `v_*(z)`. -/
theorem pieceIso_lift_zero_chain {E B : Type} [TopologicalSpace E] [TopologicalSpace B] (p : C(E, B)) (hfib : Work.StemsB.IsSerreFibration p) (t : ℕ) (b : B)
    (σ : ((SSet.stdSimplex.obj (SimplexCategory.mk 0) : SSet.{0})) ⟶ Work.SSS.sSing B)
    (ez : (((SSet.stdSimplex.obj (SimplexCategory.mk 0) : SSet.{0})) ⊗
        Work.SSS.sSing (Work.StemsB.fibre p b)) ⟶ Work.SSS.pullAlong (Work.SSS.sSingP p) σ)
    (hez : ez ≫ pullback.fst σ (Work.SSS.sSingP p) = SemiCartesianMonoidalCategory.fst _ _)
    (v : Work.SSS.sSing (Work.StemsB.fibre p b) ⟶
      Work.SSS.sSing (Work.StemsB.fibre p (Work.SSS.sigmaVert σ)))
    (hv : v ≫ Work.SSS.sSingP (Work.StemsB.fibreIncl p (Work.SSS.sigmaVert σ))
      = Work.SSS.vertIncl p b 0 ≫ ez ≫ pullback.snd σ (Work.SSS.sSingP p))
    (z : (Work.SSS.fibreCC p b).X t)
    (hz : (ModuleCat.Hom.hom ((Work.SSS.fibreCC p b).d t
        ((ComplexShape.down ℕ).next t))) z = 0)
    (hcyc : (ModuleCat.Hom.hom ((Work.SSS.pieceAlong (Work.SSS.sSingP p) σ).d (0+t)
        ((ComplexShape.down ℕ).next (0+t))))
        ((ModuleCat.Hom.hom ((Work.SSS.pieceπOf (Work.SSS.sSingP p) σ).f (0+t)))
          ((ModuleCat.Hom.hom ((Work.SSS.sCCMap ez).f (0+t)))
            (Work.SSS.ezLinSnd 0 t
              (SSet.stdSimplex.obj (SimplexCategory.mk 0) : SSet.{0})
              (Work.SSS.sSing (Work.StemsB.fibre p b)) (Work.SSS.stdIdSimplex 0) z))) = 0)
    (hcyc' : (ModuleCat.Hom.hom ((Work.SSS.sCC (Work.SSS.sSing
        (Work.StemsB.fibre p (Work.SSS.sigmaVert σ)))).d t ((ComplexShape.down ℕ).next t)))
        ((ModuleCat.Hom.hom ((Work.SSS.sCCMap v).f t))
          (z)) = 0) :
    (Work.SSS.serreE1PieceIso p hfib 0 t σ).hom
        ((HomologicalComplex.homologyπ (Work.SSS.pieceAlong (Work.SSS.sSingP p) σ) (0+t))
          ((Work.SSS.pieceAlong (Work.SSS.sSingP p) σ).cyclesMk
            ((ModuleCat.Hom.hom ((Work.SSS.pieceπOf (Work.SSS.sSingP p) σ).f (0+t)))
              ((ModuleCat.Hom.hom ((Work.SSS.sCCMap ez).f (0+t)))
                (Work.SSS.ezLinSnd 0 t
              (SSet.stdSimplex.obj (SimplexCategory.mk 0) : SSet.{0})
              (Work.SSS.sSing (Work.StemsB.fibre p b)) (Work.SSS.stdIdSimplex 0) z)))
            ((ComplexShape.down ℕ).next (0+t)) rfl hcyc))
      = (HomologicalComplex.homologyπ
            (Work.SSS.sCC (Work.SSS.sSing (Work.StemsB.fibre p (Work.SSS.sigmaVert σ)))) t)
          ((Work.SSS.sCC (Work.SSS.sSing (Work.StemsB.fibre p
              (Work.SSS.sigmaVert σ)))).cyclesMk
            ((ModuleCat.Hom.hom ((Work.SSS.sCCMap v).f t))
              (z))
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
  -- (4) the shuffle chain at `P = 0` is the vertex inclusion, for the chain `z`
  have hce : Work.SSS.castElem
        (Work.SSS.sCC (((SSet.stdSimplex.obj (SimplexCategory.mk 0) : SSet.{0})) ⊗
          Work.SSS.sSing (Work.StemsB.fibre p b))) (Nat.zero_add t)
        (Work.SSS.ezLinSnd 0 t
          (SSet.stdSimplex.obj (SimplexCategory.mk 0) : SSet.{0})
          (Work.SSS.sSing (Work.StemsB.fibre p b)) (Work.SSS.stdIdSimplex 0) z)
      = (Work.SSS.sCCMap (Work.SSS.vertIncl p b 0)).f t z :=
    ezLinSnd_zero_vertIncl p b t z
  -- (5) the chain-level equality `H` required by `izo_homology_apply`
  have H : (Work.SSS.pieceAlongZeroIso p σ).hom.f t
      (Work.SSS.castElem (Work.SSS.pieceAlong (Work.SSS.sSingP p) σ) (Nat.zero_add t)
        ((Work.SSS.pieceπOf (Work.SSS.sSingP p) σ).f (0+t)
          ((Work.SSS.sCCMap ez).f (0+t)
            (Work.SSS.ezLinSnd 0 t
              (SSet.stdSimplex.obj (SimplexCategory.mk 0) : SSet.{0})
              (Work.SSS.sSing (Work.StemsB.fibre p b)) (Work.SSS.stdIdSimplex 0) z))))
    = (Work.SSS.sCCMap v).f t
        (z) := by
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
        (Work.SSS.ezLinSnd 0 t
          (SSet.stdSimplex.obj (SimplexCategory.mk 0) : SSet.{0})
          (Work.SSS.sSing (Work.StemsB.fibre p b)) (Work.SSS.stdIdSimplex 0) z)))
    hcyc
    ((Work.SSS.sCCMap v).f t
      (z))
    hcyc' H

end Work.SSS
