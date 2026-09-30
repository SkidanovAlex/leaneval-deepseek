import Mathlib
import Submission.Work.SSSR.pieceAlongZero
import Submission.Work.SSSR.serreE1PieceExplicit
import Submission.Work.SSSR.ezGen_snd_sum_zero
import Submission.Work.SSSR.serreE1EZ
import Submission.Work.SSSR.serreE1PieceIotaDefs
import Submission.Work.SSSR.pieceIso_lift_zero
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

variable {R : Type} [CommRing R] [Nontrivial R]

namespace Work.SSSR

open CategoryTheory CategoryTheory.Limits Simplicial Opposite MonoidalCategory
open scoped MonoidalCategory Simplicial Topology
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

/-- The `castElem` transport of a chain complex is the `eqToHom` transport, in `ModuleCat.Hom.hom`
form. -/
lemma castElem_eqToHom_hom {K : ChainComplex (ModuleCat R) ℕ} {i j : ℕ} (h : i = j)
    (x : K.X i) : (ModuleCat.Hom.hom (eqToHom (congr_arg K.X h))) x = castElem K h x := by
  subst h; simp [castElem]

/-- **The `P = 0` shuffle is the vertex inclusion, for an arbitrary chain.**  The map
`ezLinSnd 0 t Δ[0] (Sing F) (id)`, transported from degree `0 + t` to degree `t`, is the map
induced on chains by the vertex inclusion `vertIncl p b 0`.  This linearises
`Work.SSSR.castElem_ezGen_zero_vertIncl` from a simplex `τ` to an arbitrary chain `z`. -/
lemma ezLinSnd_zero_vertIncl {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (b : B) (t : ℕ) (z : (Work.SSSR.fibreCC p b).X t) :
    Work.SSSR.castElem (Work.SSSR.sCC R ((SSet.stdSimplex.obj (SimplexCategory.mk 0) : SSet.{0}) ⊗
        Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b))) (Nat.zero_add t)
      (Work.SSSR.ezLinSnd 0 t (SSet.stdSimplex.obj (SimplexCategory.mk 0) : SSet.{0})
        (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b)) (Work.SSSR.stdIdSimplex 0) z)
      = (Work.SSSR.sCCMap R (Work.SSSR.vertIncl p b 0)).f t z := by
  have key : Work.SSSR.ezLinSnd 0 t (SSet.stdSimplex.obj (SimplexCategory.mk 0) : SSet.{0})
        (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b)) (Work.SSSR.stdIdSimplex 0) ≫
      eqToHom (congrArg (fun m => (((SSet.stdSimplex.obj (SimplexCategory.mk 0) : SSet.{0}) ⊗
        Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b)).chainComplex (Work.SSSR.ezR R)).X m) (Nat.zero_add t))
      = (Work.SSSR.sCCMap R (Work.SSSR.vertIncl p b 0)).f t := by
    apply SSet.chainComplex_hom_ext
    intro τ
    rw [← Category.assoc, ezLinSnd_ι]
    apply ModuleCat.hom_ext
    apply LinearMap.ext_ring
    simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply,
      LinearMap.toSpanSingleton_apply_one]
    rw [castElem_eqToHom_hom]
    exact Work.SSSR.castElem_ezGen_zero_vertIncl p b t τ
  have h2 := congrArg (fun g => (ModuleCat.Hom.hom g) z) key
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h2
  rw [← castElem_eqToHom_hom]
  exact h2

/-- The `P = 0` case of the tower comparison, for an arbitrary CHAIN: at a vertex `σ : Δ[0] → Sing B`
with base point `b = sigmaVert σ`, an arbitrary lift `ez : Δ[0] ⊗ Sing (p⁻¹b) → T_σ` of `pr₁ ≫ σ`
and a map `v : Sing (p⁻¹b) → Sing (p⁻¹σ(v₀))` whose composite with the fibre inclusion is the
`v₀`-slice of `ez`, the connecting map `ε_σ = serreE1PieceIso p hfib 0 t σ` sends the class of the
projection of the shuffle chain of `z` to the class of `v_*(z)`. -/
theorem pieceIso_lift_zero_chain {E B : Type} [TopologicalSpace E] [TopologicalSpace B] (p : C(E, B)) (hfib : Work.SSSR.StemsB.IsSerreFibration p) (t : ℕ) (b : B)
    (σ : ((SSet.stdSimplex.obj (SimplexCategory.mk 0) : SSet.{0})) ⟶ Work.SSSR.sSing B)
    (ez : (((SSet.stdSimplex.obj (SimplexCategory.mk 0) : SSet.{0})) ⊗
        Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b)) ⟶ Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)
    (hez : ez ≫ pullback.fst σ (Work.SSSR.sSingP p) = SemiCartesianMonoidalCategory.fst _ _)
    (v : Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b) ⟶
      Work.SSSR.sSing (Work.SSSR.StemsB.fibre p (Work.SSSR.sigmaVert σ)))
    (hv : v ≫ Work.SSSR.sSingP (Work.SSSR.StemsB.fibreIncl p (Work.SSSR.sigmaVert σ))
      = Work.SSSR.vertIncl p b 0 ≫ ez ≫ pullback.snd σ (Work.SSSR.sSingP p))
    (z : (Work.SSSR.fibreCC p b).X t)
    (hz : (ModuleCat.Hom.hom ((Work.SSSR.fibreCC p b).d t
        ((ComplexShape.down ℕ).next t))) z = 0)
    (hcyc : (ModuleCat.Hom.hom ((Work.SSSR.pieceAlong R (Work.SSSR.sSingP p) σ).d (0+t)
        ((ComplexShape.down ℕ).next (0+t))))
        ((ModuleCat.Hom.hom ((Work.SSSR.pieceπOf (Work.SSSR.sSingP p) σ).f (0+t)))
          ((ModuleCat.Hom.hom ((Work.SSSR.sCCMap R ez).f (0+t)))
            (Work.SSSR.ezLinSnd 0 t
              (SSet.stdSimplex.obj (SimplexCategory.mk 0) : SSet.{0})
              (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b)) (Work.SSSR.stdIdSimplex 0) z))) = 0)
    (hcyc' : (ModuleCat.Hom.hom ((Work.SSSR.sCC R (Work.SSSR.sSing
        (Work.SSSR.StemsB.fibre p (Work.SSSR.sigmaVert σ)))).d t ((ComplexShape.down ℕ).next t)))
        ((ModuleCat.Hom.hom ((Work.SSSR.sCCMap R v).f t))
          (z)) = 0) :
    (Work.SSSR.serreE1PieceIso p hfib 0 t σ).hom
        ((HomologicalComplex.homologyπ (Work.SSSR.pieceAlong R (Work.SSSR.sSingP p) σ) (0+t))
          ((Work.SSSR.pieceAlong R (Work.SSSR.sSingP p) σ).cyclesMk
            ((ModuleCat.Hom.hom ((Work.SSSR.pieceπOf (Work.SSSR.sSingP p) σ).f (0+t)))
              ((ModuleCat.Hom.hom ((Work.SSSR.sCCMap R ez).f (0+t)))
                (Work.SSSR.ezLinSnd 0 t
              (SSet.stdSimplex.obj (SimplexCategory.mk 0) : SSet.{0})
              (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b)) (Work.SSSR.stdIdSimplex 0) z)))
            ((ComplexShape.down ℕ).next (0+t)) rfl hcyc))
      = (HomologicalComplex.homologyπ
            (Work.SSSR.sCC R (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p (Work.SSSR.sigmaVert σ)))) t)
          ((Work.SSSR.sCC R (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p
              (Work.SSSR.sigmaVert σ)))).cyclesMk
            ((ModuleCat.Hom.hom ((Work.SSSR.sCCMap R v).f t))
              (z))
            ((ComplexShape.down ℕ).next t) rfl hcyc') := by
  haveI hφiso : IsIso (Work.SSSR.phiAlong p σ) := Work.SSSR.phiAlong_isIso p σ
  -- (1) `v` is the vertex slice of the lift
  have hvcomp : v ≫ Work.SSSR.phiAlong p σ = Work.SSSR.vertIncl p b 0 ≫ ez :=
    pieceIsoLiftZero_v_comp_phiAlong p b σ ez hez v hv
  have hv_eq : v = Work.SSSR.vertIncl p b 0 ≫ ez
      ≫ CategoryTheory.inv (Work.SSSR.phiAlong p σ) := by
    calc v = v ≫ 𝟙 (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p (Work.SSSR.sigmaVert σ))) :=
            (Category.comp_id v).symm
      _ = v ≫ (Work.SSSR.phiAlong p σ ≫ CategoryTheory.inv (Work.SSSR.phiAlong p σ)) := by
            rw [CategoryTheory.IsIso.hom_inv_id]
      _ = (v ≫ Work.SSSR.phiAlong p σ) ≫ CategoryTheory.inv (Work.SSSR.phiAlong p σ) :=
            (Category.assoc _ _ _).symm
      _ = (Work.SSSR.vertIncl p b 0 ≫ ez) ≫ CategoryTheory.inv (Work.SSSR.phiAlong p σ) := by
            rw [hvcomp]
      _ = Work.SSSR.vertIncl p b 0 ≫ ez ≫ CategoryTheory.inv (Work.SSSR.phiAlong p σ) :=
            Category.assoc _ _ _
  -- (2) the unfolding of `pieceAlongZeroIso` at degree `t`
  have hfac : (Work.SSSR.pieceAlongZeroIso p σ).hom.f t
      = (Work.SSSR.pieceAlongZeroCokerIso p σ).hom.f t ≫
        (Work.SSSR.sCCMap R ((Work.SSSR.pullAlongVertexIsoIso p σ).hom)).f t := by
    rw [Work.SSSR.pieceAlongZeroIso]
    simp only [CategoryTheory.Iso.trans_hom, CategoryTheory.Functor.mapIso_hom,
      HomologicalComplex.comp_f, CategoryTheory.eqToIso.hom, CategoryTheory.eqToHom_refl,
      HomologicalComplex.id_f, Category.comp_id, Work.SSSR.sCCMap]
  -- (3) the cokernel projection is undone by `pieceAlongZeroCokerIso`
  have hmor : (Work.SSSR.pieceπOf (Work.SSSR.sSingP p) σ).f t
      ≫ (Work.SSSR.pieceAlongZeroCokerIso (R := R) p σ).hom.f t = 𝟙 _ := by
    have hh := congrArg (fun (g : Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ) ⟶
        Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)) => g.f t)
      (Work.SSSR.izo_cokerIso_comp p σ)
    simpa using hh
  have hmor' : ∀ y : (Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)).X t,
      (Work.SSSR.pieceAlongZeroCokerIso p σ).hom.f t
        ((Work.SSSR.pieceπOf (Work.SSSR.sSingP p) σ).f t y) = y := by
    intro y
    have hh := congrArg (fun (g : (Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)).X t ⟶
        (Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)).X t) => g y) hmor
    simpa only [HomologicalComplex.comp_f, ModuleCat.hom_comp,
      LinearMap.comp_apply, CategoryTheory.id_apply] using hh
  -- (4) the shuffle chain at `P = 0` is the vertex inclusion, for the chain `z`
  have hce : Work.SSSR.castElem
        (Work.SSSR.sCC R (((SSet.stdSimplex.obj (SimplexCategory.mk 0) : SSet.{0})) ⊗
          Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b))) (Nat.zero_add t)
        (Work.SSSR.ezLinSnd 0 t
          (SSet.stdSimplex.obj (SimplexCategory.mk 0) : SSet.{0})
          (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b)) (Work.SSSR.stdIdSimplex 0) z)
      = (Work.SSSR.sCCMap R (Work.SSSR.vertIncl p b 0)).f t z :=
    ezLinSnd_zero_vertIncl p b t z
  -- (5) the chain-level equality `H` required by `izo_homology_apply`
  have H : (Work.SSSR.pieceAlongZeroIso p σ).hom.f t
      (Work.SSSR.castElem (Work.SSSR.pieceAlong R (Work.SSSR.sSingP p) σ) (Nat.zero_add t)
        ((Work.SSSR.pieceπOf (Work.SSSR.sSingP p) σ).f (0+t)
          ((Work.SSSR.sCCMap R ez).f (0+t)
            (Work.SSSR.ezLinSnd 0 t
              (SSet.stdSimplex.obj (SimplexCategory.mk 0) : SSet.{0})
              (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b)) (Work.SSSR.stdIdSimplex 0) z))))
    = (Work.SSSR.sCCMap R v).f t
        (z) := by
    rw [hfac]
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
    rw [Work.SSSR.izo_castElem_map]
    rw [hmor']
    rw [Work.SSSR.izo_castElem_map]
    rw [hce]
    rw [show (Work.SSSR.pullAlongVertexIsoIso p σ).hom
        = CategoryTheory.inv (Work.SSSR.phiAlong p σ) from rfl]
    rw [hv_eq]
    simp only [Work.SSSR.izo_sCCMap_comp, HomologicalComplex.comp_f, ModuleCat.hom_comp,
      LinearMap.comp_apply]
    rfl
  -- (6) assemble
  rw [Work.SSSR.izo_serreE1PieceIso_zero_eq p hfib (Work.SSSR.sigmaVert σ) σ rfl t]
  simp only [CategoryTheory.Iso.trans_hom, CategoryTheory.comp_apply]
  exact Work.SSSR.izo_homology_apply (Work.SSSR.pieceAlongZeroIso p σ).hom (Nat.zero_add t)
    ((Work.SSSR.pieceπOf (Work.SSSR.sSingP p) σ).f (0+t)
      ((Work.SSSR.sCCMap R ez).f (0+t)
        (Work.SSSR.ezLinSnd 0 t
          (SSet.stdSimplex.obj (SimplexCategory.mk 0) : SSet.{0})
          (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b)) (Work.SSSR.stdIdSimplex 0) z)))
    hcyc
    ((Work.SSSR.sCCMap R v).f t
      (z))
    hcyc' H

end Work.SSSR
