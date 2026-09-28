import Mathlib
import Submission.Work.SSS.pieceIso_lift_genC
import Submission.Work.SSS.pieceIso_peel
import Submission.Work.SSS.pieceIso_lift_zero_chain
import Submission.Work.SSS.hornCok_d_faceLift_chain_j1
import Submission.Work.SSS.ezLinSnd_chain_cycle

namespace Work.SSS

open CategoryTheory CategoryTheory.Limits Simplicial Opposite MonoidalCategory
open scoped MonoidalCategory Simplicial Topology

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-- **The tower comparison for an arbitrary lift of a simplex, on an arbitrary CYCLE CHAIN.**

For a simplex `σ : Δ[P] ⟶ Sing B`, a lift `ez : Δ[P] ⊗ Sing (p⁻¹b) ⟶ T_σ` of `pr₁ ≫ σ`, a map
`v : Sing (p⁻¹b) ⟶ Sing (p⁻¹σ(v₀))` whose composite with the fibre inclusion is the `v₀`-slice
`vertIncl p b P ≫ ez ≫ pullback.snd σ (sSingP p)` of the lift (`hv`), a CYCLE CHAIN `z` of
`C_t(p⁻¹b)` (`hz`), and a sign family `c` with `c 0 = 1` and `c (n+1) = (-1)^(n+1) c n`, the
iterated last-face connecting map `ε_σ = serreE1PieceIso p hfib P t σ` sends the class of the
projection of `ez_*(EZ(P,t,[id],z))` to `c P` times the class of `v_*(z)`.

This is the CHAIN-level (non-vacuous) form of the PROVED simplex-level
`Work.SSS.pieceIso_lift_genC`: there the fibre element is a single cycle SIMPLEX `τ`, which does
not exist in even fibre degrees `t ≥ 2`, whereas here `z` is an arbitrary cycle chain.  The proof is
the same induction on `P`: at `P = 0` this is `Work.SSS.pieceIso_lift_zero_chain` (sign `1`); for
`P = n+1` the `n`-th case applies to the *face restriction*
`Work.SSS.faceLift (sSingP p) σ ez hez (Fin.last (n+1))` of the lift (with the same `v` and `z`,
using `Work.SSS.vertIncl_coface` and `Work.SSS.faceLift_pullFaceIncl`; note
`Work.SSS.sigmaVert_face` identifies the base point), the peel is `Work.SSS.pieceIso_peel` whose
hypothesis `hpeel` is `Work.SSS.hornCok_d_faceLift_chain_j1`, and the cycle condition of the
restricted chain is `Work.SSS.ezLinSnd_chain_cycle`. -/
theorem pieceIso_lift_chain {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (hfib : Work.StemsB.IsSerreFibration p)
    (c : ℕ → ℤ) (hc0 : c 0 = 1) (hcsucc : ∀ n, c (n+1) = ((-1 : ℤ) ^ (n+1)) * c n)
    (P t : ℕ) (b : B)
    (σ : ((SSet.stdSimplex.obj (SimplexCategory.mk P) : SSet.{0})) ⟶ Work.SSS.sSing B)
    (ez : (((SSet.stdSimplex.obj (SimplexCategory.mk P) : SSet.{0})) ⊗
        Work.SSS.sSing (Work.StemsB.fibre p b)) ⟶ Work.SSS.pullAlong (Work.SSS.sSingP p) σ)
    (hez : ez ≫ pullback.fst σ (Work.SSS.sSingP p) = SemiCartesianMonoidalCategory.fst _ _)
    (v : Work.SSS.sSing (Work.StemsB.fibre p b) ⟶
      Work.SSS.sSing (Work.StemsB.fibre p (Work.SSS.sigmaVert σ)))
    (hv : v ≫ Work.SSS.sSingP (Work.StemsB.fibreIncl p (Work.SSS.sigmaVert σ))
      = Work.SSS.vertIncl p b P ≫ ez ≫ pullback.snd σ (Work.SSS.sSingP p))
    (z : (Work.SSS.fibreCC p b).X t)
    (hz : (ModuleCat.Hom.hom ((Work.SSS.fibreCC p b).d t ((ComplexShape.down ℕ).next t))) z = 0)
    (hcyc : (ModuleCat.Hom.hom ((Work.SSS.pieceAlong (Work.SSS.sSingP p) σ).d (P+t)
        ((ComplexShape.down ℕ).next (P+t))))
        ((ModuleCat.Hom.hom ((Work.SSS.pieceπOf (Work.SSS.sSingP p) σ).f (P+t)))
          ((ModuleCat.Hom.hom ((Work.SSS.sCCMap ez).f (P+t)))
            (Work.SSS.ezLinSnd P t
              (SSet.stdSimplex.obj (SimplexCategory.mk P) : SSet.{0})
              (Work.SSS.sSing (Work.StemsB.fibre p b)) (Work.SSS.stdIdSimplex P) z))) = 0)
    (hcyc' : (ModuleCat.Hom.hom ((Work.SSS.sCC (Work.SSS.sSing
        (Work.StemsB.fibre p (Work.SSS.sigmaVert σ)))).d t ((ComplexShape.down ℕ).next t)))
        ((ModuleCat.Hom.hom ((Work.SSS.sCCMap v).f t)) z) = 0) :
    (Work.SSS.serreE1PieceIso p hfib P t σ).hom
        ((HomologicalComplex.homologyπ (Work.SSS.pieceAlong (Work.SSS.sSingP p) σ) (P+t))
          ((Work.SSS.pieceAlong (Work.SSS.sSingP p) σ).cyclesMk
            ((ModuleCat.Hom.hom ((Work.SSS.pieceπOf (Work.SSS.sSingP p) σ).f (P+t)))
              ((ModuleCat.Hom.hom ((Work.SSS.sCCMap ez).f (P+t)))
                (Work.SSS.ezLinSnd P t
                  (SSet.stdSimplex.obj (SimplexCategory.mk P) : SSet.{0})
                  (Work.SSS.sSing (Work.StemsB.fibre p b)) (Work.SSS.stdIdSimplex P) z)))
            ((ComplexShape.down ℕ).next (P+t)) rfl hcyc))
      = c P • ((HomologicalComplex.homologyπ
            (Work.SSS.sCC (Work.SSS.sSing (Work.StemsB.fibre p (Work.SSS.sigmaVert σ)))) t)
          ((Work.SSS.sCC (Work.SSS.sSing (Work.StemsB.fibre p
              (Work.SSS.sigmaVert σ)))).cyclesMk
            ((ModuleCat.Hom.hom ((Work.SSS.sCCMap v).f t)) z)
            ((ComplexShape.down ℕ).next t) rfl hcyc')) := by
  induction P with
  | zero =>
    rw [hc0, one_smul]
    exact pieceIso_lift_zero_chain p hfib t b σ ez hez v hv z hz hcyc hcyc'
  | succ n ih =>
    have hne : Fin.last (n+1) ≠ (0 : Fin (n+2)) := by
      intro hh
      have hv := congrArg Fin.val hh
      simp [Fin.last] at hv
    have hsv : Work.SSS.sigmaVert (SSet.stdSimplex.δ (n := n) (Fin.last (n+1)) ≫ σ)
        = Work.SSS.sigmaVert σ := Work.SSS.sigmaVert_face (Fin.last (n+1)) hne σ
    have hv_face : (v ≫ eqToHom (congrArg (fun z : B => Work.SSS.sSing (Work.StemsB.fibre p z)) hsv.symm))
        ≫ Work.SSS.sSingP (Work.StemsB.fibreIncl p
            (Work.SSS.sigmaVert (SSet.stdSimplex.δ (n := n) (Fin.last (n+1)) ≫ σ)))
        = Work.SSS.vertIncl p b n
          ≫ Work.SSS.faceLift (Work.SSS.sSingP p) σ ez hez (Fin.last (n+1))
          ≫ pullback.snd (SSet.stdSimplex.δ (n := n) (Fin.last (n+1)) ≫ σ) (Work.SSS.sSingP p) := by
      let dd : ((SSet.stdSimplex.obj (SimplexCategory.mk n) : SSet.{0}) ⊗
          Work.SSS.sSing (Work.StemsB.fibre p b))
          ⟶ ((SSet.stdSimplex.obj (SimplexCategory.mk (n+1)) : SSet.{0}) ⊗
          Work.SSS.sSing (Work.StemsB.fibre p b)) :=
        SSet.stdSimplex.δ (n := n) (Fin.last (n+1)) ⊗ₘ 𝟙 (Work.SSS.sSing (Work.StemsB.fibre p b))
      have h2 : Work.SSS.vertIncl p b (n+1) = Work.SSS.vertIncl p b n ≫ dd :=
        (Work.SSS.vertIncl_coface p b n).symm
      have h3 : dd ≫ ez
          = Work.SSS.faceLift (Work.SSS.sSingP p) σ ez hez (Fin.last (n+1))
            ≫ Work.SSS.pullFaceIncl (Work.SSS.sSingP p) σ (Fin.last (n+1)) :=
        (Work.SSS.faceLift_pullFaceIncl (Work.SSS.sSingP p) σ ez hez (Fin.last (n+1))).symm
      have h4 : Work.SSS.pullFaceIncl (Work.SSS.sSingP p) σ (Fin.last (n+1))
          ≫ pullback.snd σ (Work.SSS.sSingP p)
          = pullback.snd (SSet.stdSimplex.δ (n := n) (Fin.last (n+1)) ≫ σ) (Work.SSS.sSingP p) :=
        Work.SSS.pullFaceIncl_snd (Work.SSS.sSingP p) σ (Fin.last (n+1))
      have hA : (v ≫ eqToHom (congrArg (fun z : B => Work.SSS.sSing (Work.StemsB.fibre p z)) hsv.symm))
            ≫ Work.SSS.sSingP (Work.StemsB.fibreIncl p
                (Work.SSS.sigmaVert (SSet.stdSimplex.δ (n := n) (Fin.last (n+1)) ≫ σ)))
          = v ≫ Work.SSS.sSingP (Work.StemsB.fibreIncl p (Work.SSS.sigmaVert σ)) := by
        rw [Category.assoc, eqToHom_sSingP_fibreIncl' p hsv.symm]
      have hB : v ≫ Work.SSS.sSingP (Work.StemsB.fibreIncl p (Work.SSS.sigmaVert σ))
          = (Work.SSS.vertIncl p b n ≫ (dd ≫ ez)) ≫ pullback.snd σ (Work.SSS.sSingP p) := by
        rw [hv]
        simp only [Category.assoc]
        rw [h2]
        simp only [Category.assoc]
      have hC : (Work.SSS.vertIncl p b n ≫ (dd ≫ ez)) ≫ pullback.snd σ (Work.SSS.sSingP p)
          = (Work.SSS.vertIncl p b n
              ≫ (Work.SSS.faceLift (Work.SSS.sSingP p) σ ez hez (Fin.last (n+1))
                ≫ Work.SSS.pullFaceIncl (Work.SSS.sSingP p) σ (Fin.last (n+1))))
            ≫ pullback.snd σ (Work.SSS.sSingP p) :=
        congrArg (fun w => (Work.SSS.vertIncl p b n ≫ w) ≫ pullback.snd σ (Work.SSS.sSingP p)) h3
      have hD : (Work.SSS.vertIncl p b n
              ≫ (Work.SSS.faceLift (Work.SSS.sSingP p) σ ez hez (Fin.last (n+1))
                ≫ Work.SSS.pullFaceIncl (Work.SSS.sSingP p) σ (Fin.last (n+1))))
            ≫ pullback.snd σ (Work.SSS.sSingP p)
          = (Work.SSS.vertIncl p b n
              ≫ Work.SSS.faceLift (Work.SSS.sSingP p) σ ez hez (Fin.last (n+1)))
            ≫ pullback.snd (SSet.stdSimplex.δ (n := n) (Fin.last (n+1)) ≫ σ) (Work.SSS.sSingP p) := by
        simp only [Category.assoc]
        rw [h4]
      exact hA.trans (hB.trans (hC.trans hD))
    have hcycface : (ModuleCat.Hom.hom ((Work.SSS.pieceAlong (Work.SSS.sSingP p)
          (SSet.stdSimplex.δ (n := n) (Fin.last (n+1)) ≫ σ)).d (n+t)
        ((ComplexShape.down ℕ).next (n+t))))
        ((ModuleCat.Hom.hom ((Work.SSS.pieceπOf (Work.SSS.sSingP p)
            (SSet.stdSimplex.δ (n := n) (Fin.last (n+1)) ≫ σ)).f (n+t)))
          ((ModuleCat.Hom.hom ((Work.SSS.sCCMap (Work.SSS.faceLift (Work.SSS.sSingP p) σ ez hez
            (Fin.last (n+1)))).f (n+t)))
            (Work.SSS.ezLinSnd n t
              (SSet.stdSimplex.obj (SimplexCategory.mk n) : SSet.{0})
              (Work.SSS.sSing (Work.StemsB.fibre p b)) (Work.SSS.stdIdSimplex n) z))) = 0 :=
      Work.SSS.ezLinSnd_chain_cycle p n t b
        (SSet.stdSimplex.δ (n := n) (Fin.last (n+1)) ≫ σ)
        (Work.SSS.faceLift (Work.SSS.sSingP p) σ ez hez (Fin.last (n+1)))
        (Work.SSS.faceLift_fst (Work.SSS.sSingP p) σ ez hez (Fin.last (n+1))) z hz
    have hcyc'face : (Work.SSS.sCC (Work.SSS.sSing (Work.StemsB.fibre p
          (Work.SSS.sigmaVert (SSet.stdSimplex.δ (n := n) (Fin.last (n+1)) ≫ σ))))).d t
        ((ComplexShape.down ℕ).next t)
        ((Work.SSS.sCCMap (v ≫ eqToHom (congrArg (fun z : B =>
          Work.SSS.sSing (Work.StemsB.fibre p z)) hsv.symm))).f t z) = 0 := by
      rw [chainMap_d_apply', hz, map_zero]
    have hih := ih (SSet.stdSimplex.δ (n := n) (Fin.last (n+1)) ≫ σ)
      (Work.SSS.faceLift (Work.SSS.sSingP p) σ ez hez (Fin.last (n+1)))
      (Work.SSS.faceLift_fst (Work.SSS.sSingP p) σ ez hez (Fin.last (n+1)))
      (v ≫ eqToHom (congrArg (fun z : B => Work.SSS.sSing (Work.StemsB.fibre p z)) hsv.symm))
      hv_face hcycface hcyc'face
    have hpeel := Work.SSS.pieceIso_peel p hfib n t b σ
      ((ModuleCat.Hom.hom ((Work.SSS.sCCMap ez).f ((n+1)+t)))
        (Work.SSS.ezLinSnd (n+1) t
          (SSet.stdSimplex.obj (SimplexCategory.mk (n+1)) : SSet.{0})
          (Work.SSS.sSing (Work.StemsB.fibre p b)) (Work.SSS.stdIdSimplex (n+1)) z))
      hcyc
      ((ModuleCat.Hom.hom ((Work.SSS.sCCMap (Work.SSS.faceLift (Work.SSS.sSingP p) σ ez hez
          (Fin.last (n+1)))).f (n+t)))
        (Work.SSS.ezLinSnd n t
          (SSet.stdSimplex.obj (SimplexCategory.mk n) : SSet.{0})
          (Work.SSS.sSing (Work.StemsB.fibre p b)) (Work.SSS.stdIdSimplex n) z))
      hcycface
      (Work.SSS.hornCok_d_faceLift_chain_j1 p hfib n t b σ ez hez z hz)
    rw [hpeel, hih, map_zsmul]
    have hT : (eqToIso (congrArg (fun x : B => (Work.Cohomology.singularChains ℤ
          (TopCat.of (Work.StemsB.fibre p x))).homology t)
        (Work.SSS.sigmaVert_face (Fin.last (n+1)) (by
          intro hh; have hv := congrArg Fin.val hh; simp [Fin.last] at hv) σ))).hom
      = Work.SSS.fibreConj p hsv t := by
      have hp : Work.SSS.sigmaVert_face (Fin.last (n+1)) (by
          intro hh; have hv := congrArg Fin.val hh; simp [Fin.last] at hv) σ = hsv :=
        Subsingleton.elim _ _
      rw [hp]
      exact (Work.SSS.fibreConj_eq p hsv t).symm
    rw [hT]
    refine (congrArg (fun w => (-1 : ℤ)^(n+1) • (c n • w))
      (Work.SSS.fibreConj_homologyπ_v_face hsv v z hcyc'face hcyc')).trans ?_
    rw [smul_smul, hcsucc n]

end Work.SSS
