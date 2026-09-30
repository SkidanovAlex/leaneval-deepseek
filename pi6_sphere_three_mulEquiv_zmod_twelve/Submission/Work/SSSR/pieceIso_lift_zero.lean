import Mathlib
import Submission.Work.SSSR.piszDefs
import Submission.Work.SSSR.serreE1PieceExplicit
import Submission.Work.SSSR.pieceAlongZero
import Submission.Work.SSSR.serreE1EZ
import Submission.Work.SSSR.iotaStatement_zero_c_one
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

variable {R : Type} [CommRing R] [Nontrivial R]

namespace Work.SSSR

open CategoryTheory CategoryTheory.Limits Simplicial Opposite MonoidalCategory
open scoped MonoidalCategory Simplicial Topology
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

/-- **The simplicial identity behind the `P = 0` tower comparison.**  For an arbitrary lift `ez` of
`pr₁ ≫ σ` along a vertex `σ`, and a map `v` of fibres whose composite with the fibre inclusion is
the `v₀`-slice `vertIncl p b 0 ≫ ez ≫ pullback.snd σ (sSingP p)` of the lift, one has
`v ≫ phiAlong p σ = vertIncl p b 0 ≫ ez`. -/
theorem pieceIsoLiftZero_v_comp_phiAlong (p : C(E, B)) (b : B)
    (σ : ((SSet.stdSimplex.obj (SimplexCategory.mk 0) : SSet.{0})) ⟶ Work.SSSR.sSing B)
    (ez : (((SSet.stdSimplex.obj (SimplexCategory.mk 0) : SSet.{0})) ⊗
        Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b)) ⟶ Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)
    (hez : ez ≫ pullback.fst σ (Work.SSSR.sSingP p) = SemiCartesianMonoidalCategory.fst _ _)
    (v : Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b) ⟶
      Work.SSSR.sSing (Work.SSSR.StemsB.fibre p (Work.SSSR.sigmaVert σ)))
    (hv : v ≫ Work.SSSR.sSingP (Work.SSSR.StemsB.fibreIncl p (Work.SSSR.sigmaVert σ))
      = Work.SSSR.vertIncl p b 0 ≫ ez ≫ pullback.snd σ (Work.SSSR.sSingP p)) :
    v ≫ Work.SSSR.phiAlong p σ = Work.SSSR.vertIncl p b 0 ≫ ez := by
  apply pullback.hom_ext
  · -- first component: both land in the terminal `Δ[0]`
    have h3 : Work.SSSR.phiAlongFst p σ
        = SSet.const (X := Work.SSSR.sSing (Work.SSSR.StemsB.fibre p (Work.SSSR.sigmaVert σ)))
            (ssetVertex 0) := by
      unfold Work.SSSR.phiAlongFst
      rw [Work.SSSR.izo_ssetVertex_zero_eq_yoneda]
    simp only [Category.assoc, Work.SSSR.phiAlong_fst, hez, Work.SSSR.vertIncl_fst]
    rw [h3, SSet.comp_const]
  · -- second component: this is `hv`
    simp only [Category.assoc, Work.SSSR.phiAlong_snd]
    exact hv

/-- **The `(0,t)` shuffle at the vertex is the vertex inclusion** (after the degree transport
`0 + t = t`). -/
theorem castElem_ezGen_zero_vertIncl (p : C(E, B)) (b : B) (t : ℕ)
    (τ : (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b)) _⦋t⦌) :
    Work.SSSR.castElem
        (Work.SSSR.sCC R (((SSet.stdSimplex.obj (SimplexCategory.mk 0) : SSet.{0})) ⊗
          Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b))) (Nat.zero_add t)
        (Work.SSSR.Cohomology.Crux33.ezGen 0 t
          (SSet.stdSimplex.obj (SimplexCategory.mk 0) : SSet.{0})
          (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b)) (Work.SSSR.stdIdSimplex 0) τ)
      = (Work.SSSR.sCCMap R (Work.SSSR.vertIncl p b 0)).f t
          (((Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b)).ιChainComplex
            (R := ModuleCat.of R R) τ).hom 1) := by
  rw [Work.SSSR.izo_ezGen_zero_eq_vertIncl p b t τ]
  rw [Work.SSSR.izo_castElem_map]
  rw [Work.SSSR.izo_castElem_ιChainComplex]
  rw [Work.SSSR.izo_castSimp_zSh_bHom]

end Work.SSSR
