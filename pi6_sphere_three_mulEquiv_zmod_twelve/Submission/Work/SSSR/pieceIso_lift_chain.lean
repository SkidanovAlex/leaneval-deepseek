import Mathlib
import Submission.Work.SSSR.pieceIso_lift_genC
import Submission.Work.SSSR.pieceIso_peel
import Submission.Work.SSSR.pieceIso_lift_zero_chain
import Submission.Work.SSSR.hornCok_d_faceLift_chain_j1
import Submission.Work.SSSR.ezLinSnd_chain_cycle
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

variable {R : Type} [CommRing R] [Nontrivial R]

namespace Work.SSSR

open CategoryTheory CategoryTheory.Limits Simplicial Opposite MonoidalCategory
open scoped MonoidalCategory Simplicial Topology
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

/-- **The tower comparison for an arbitrary lift of a simplex, on an arbitrary CYCLE CHAIN.**

For a simplex `σ : Δ[P] ⟶ Sing B`, a lift `ez : Δ[P] ⊗ Sing (p⁻¹b) ⟶ T_σ` of `pr₁ ≫ σ`, a map
`v : Sing (p⁻¹b) ⟶ Sing (p⁻¹σ(v₀))` whose composite with the fibre inclusion is the `v₀`-slice
`vertIncl p b P ≫ ez ≫ pullback.snd σ (sSingP p)` of the lift (`hv`), a CYCLE CHAIN `z` of
`C_t(p⁻¹b)` (`hz`), and a sign family `c` with `c 0 = 1` and `c (n+1) = (-1)^(n+1) c n`, the
iterated last-face connecting map `ε_σ = serreE1PieceIso p hfib P t σ` sends the class of the
projection of `ez_*(EZ(P,t,[id],z))` to `c P` times the class of `v_*(z)`.

This is the CHAIN-level (non-vacuous) form of the PROVED simplex-level
`Work.SSSR.pieceIso_lift_genC`: there the fibre element is a single cycle SIMPLEX `τ`, which does
not exist in even fibre degrees `t ≥ 2`, whereas here `z` is an arbitrary cycle chain.  The proof is
the same induction on `P`: at `P = 0` this is `Work.SSSR.pieceIso_lift_zero_chain` (sign `1`); for
`P = n+1` the `n`-th case applies to the *face restriction*
`Work.SSSR.faceLift (sSingP p) σ ez hez (Fin.last (n+1))` of the lift (with the same `v` and `z`,
using `Work.SSSR.vertIncl_coface` and `Work.SSSR.faceLift_pullFaceIncl`; note
`Work.SSSR.sigmaVert_face` identifies the base point), the peel is `Work.SSSR.pieceIso_peel` whose
hypothesis `hpeel` is `Work.SSSR.hornCok_d_faceLift_chain_j1`, and the cycle condition of the
restricted chain is `Work.SSSR.ezLinSnd_chain_cycle`. -/
theorem pieceIso_lift_chain {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (hfib : Work.SSSR.StemsB.IsSerreFibration p)
    (c : ℕ → ℤ) (hc0 : c 0 = 1) (hcsucc : ∀ n, c (n+1) = ((-1 : ℤ) ^ (n+1)) * c n)
    (P t : ℕ) (b : B)
    (σ : ((SSet.stdSimplex.obj (SimplexCategory.mk P) : SSet.{0})) ⟶ Work.SSSR.sSing B)
    (ez : (((SSet.stdSimplex.obj (SimplexCategory.mk P) : SSet.{0})) ⊗
        Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b)) ⟶ Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)
    (hez : ez ≫ pullback.fst σ (Work.SSSR.sSingP p) = SemiCartesianMonoidalCategory.fst _ _)
    (v : Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b) ⟶
      Work.SSSR.sSing (Work.SSSR.StemsB.fibre p (Work.SSSR.sigmaVert σ)))
    (hv : v ≫ Work.SSSR.sSingP (Work.SSSR.StemsB.fibreIncl p (Work.SSSR.sigmaVert σ))
      = Work.SSSR.vertIncl p b P ≫ ez ≫ pullback.snd σ (Work.SSSR.sSingP p))
    (z : (Work.SSSR.fibreCC p b).X t)
    (hz : (ModuleCat.Hom.hom ((Work.SSSR.fibreCC p b).d t ((ComplexShape.down ℕ).next t))) z = 0)
    (hcyc : (ModuleCat.Hom.hom ((Work.SSSR.pieceAlong R (Work.SSSR.sSingP p) σ).d (P+t)
        ((ComplexShape.down ℕ).next (P+t))))
        ((ModuleCat.Hom.hom ((Work.SSSR.pieceπOf (Work.SSSR.sSingP p) σ).f (P+t)))
          ((ModuleCat.Hom.hom ((Work.SSSR.sCCMap R ez).f (P+t)))
            (Work.SSSR.ezLinSnd P t
              (SSet.stdSimplex.obj (SimplexCategory.mk P) : SSet.{0})
              (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b)) (Work.SSSR.stdIdSimplex P) z))) = 0)
    (hcyc' : (ModuleCat.Hom.hom ((Work.SSSR.sCC R (Work.SSSR.sSing
        (Work.SSSR.StemsB.fibre p (Work.SSSR.sigmaVert σ)))).d t ((ComplexShape.down ℕ).next t)))
        ((ModuleCat.Hom.hom ((Work.SSSR.sCCMap R v).f t)) z) = 0) :
    (Work.SSSR.serreE1PieceIso p hfib P t σ).hom
        ((HomologicalComplex.homologyπ (Work.SSSR.pieceAlong R (Work.SSSR.sSingP p) σ) (P+t))
          ((Work.SSSR.pieceAlong R (Work.SSSR.sSingP p) σ).cyclesMk
            ((ModuleCat.Hom.hom ((Work.SSSR.pieceπOf (Work.SSSR.sSingP p) σ).f (P+t)))
              ((ModuleCat.Hom.hom ((Work.SSSR.sCCMap R ez).f (P+t)))
                (Work.SSSR.ezLinSnd P t
                  (SSet.stdSimplex.obj (SimplexCategory.mk P) : SSet.{0})
                  (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b)) (Work.SSSR.stdIdSimplex P) z)))
            ((ComplexShape.down ℕ).next (P+t)) rfl hcyc))
      = c P • ((HomologicalComplex.homologyπ
            (Work.SSSR.sCC R (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p (Work.SSSR.sigmaVert σ)))) t)
          ((Work.SSSR.sCC R (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p
              (Work.SSSR.sigmaVert σ)))).cyclesMk
            ((ModuleCat.Hom.hom ((Work.SSSR.sCCMap R v).f t)) z)
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
    have hsv : Work.SSSR.sigmaVert (SSet.stdSimplex.δ (n := n) (Fin.last (n+1)) ≫ σ)
        = Work.SSSR.sigmaVert σ := Work.SSSR.sigmaVert_face (Fin.last (n+1)) hne σ
    have hv_face : (v ≫ eqToHom (congrArg (fun z : B => Work.SSSR.sSing (Work.SSSR.StemsB.fibre p z)) hsv.symm))
        ≫ Work.SSSR.sSingP (Work.SSSR.StemsB.fibreIncl p
            (Work.SSSR.sigmaVert (SSet.stdSimplex.δ (n := n) (Fin.last (n+1)) ≫ σ)))
        = Work.SSSR.vertIncl p b n
          ≫ Work.SSSR.faceLift (Work.SSSR.sSingP p) σ ez hez (Fin.last (n+1))
          ≫ pullback.snd (SSet.stdSimplex.δ (n := n) (Fin.last (n+1)) ≫ σ) (Work.SSSR.sSingP p) := by
      let dd : ((SSet.stdSimplex.obj (SimplexCategory.mk n) : SSet.{0}) ⊗
          Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b))
          ⟶ ((SSet.stdSimplex.obj (SimplexCategory.mk (n+1)) : SSet.{0}) ⊗
          Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b)) :=
        SSet.stdSimplex.δ (n := n) (Fin.last (n+1)) ⊗ₘ 𝟙 (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b))
      have h2 : Work.SSSR.vertIncl p b (n+1) = Work.SSSR.vertIncl p b n ≫ dd :=
        (Work.SSSR.vertIncl_coface p b n).symm
      have h3 : dd ≫ ez
          = Work.SSSR.faceLift (Work.SSSR.sSingP p) σ ez hez (Fin.last (n+1))
            ≫ Work.SSSR.pullFaceIncl (Work.SSSR.sSingP p) σ (Fin.last (n+1)) :=
        (Work.SSSR.faceLift_pullFaceIncl (Work.SSSR.sSingP p) σ ez hez (Fin.last (n+1))).symm
      have h4 : Work.SSSR.pullFaceIncl (Work.SSSR.sSingP p) σ (Fin.last (n+1))
          ≫ pullback.snd σ (Work.SSSR.sSingP p)
          = pullback.snd (SSet.stdSimplex.δ (n := n) (Fin.last (n+1)) ≫ σ) (Work.SSSR.sSingP p) :=
        Work.SSSR.pullFaceIncl_snd (Work.SSSR.sSingP p) σ (Fin.last (n+1))
      have hA : (v ≫ eqToHom (congrArg (fun z : B => Work.SSSR.sSing (Work.SSSR.StemsB.fibre p z)) hsv.symm))
            ≫ Work.SSSR.sSingP (Work.SSSR.StemsB.fibreIncl p
                (Work.SSSR.sigmaVert (SSet.stdSimplex.δ (n := n) (Fin.last (n+1)) ≫ σ)))
          = v ≫ Work.SSSR.sSingP (Work.SSSR.StemsB.fibreIncl p (Work.SSSR.sigmaVert σ)) := by
        rw [Category.assoc, eqToHom_sSingP_fibreIncl' p hsv.symm]
      have hB : v ≫ Work.SSSR.sSingP (Work.SSSR.StemsB.fibreIncl p (Work.SSSR.sigmaVert σ))
          = (Work.SSSR.vertIncl p b n ≫ (dd ≫ ez)) ≫ pullback.snd σ (Work.SSSR.sSingP p) := by
        rw [hv]
        simp only [Category.assoc]
        rw [h2]
        simp only [Category.assoc]
      have hC : (Work.SSSR.vertIncl p b n ≫ (dd ≫ ez)) ≫ pullback.snd σ (Work.SSSR.sSingP p)
          = (Work.SSSR.vertIncl p b n
              ≫ (Work.SSSR.faceLift (Work.SSSR.sSingP p) σ ez hez (Fin.last (n+1))
                ≫ Work.SSSR.pullFaceIncl (Work.SSSR.sSingP p) σ (Fin.last (n+1))))
            ≫ pullback.snd σ (Work.SSSR.sSingP p) :=
        congrArg (fun w => (Work.SSSR.vertIncl p b n ≫ w) ≫ pullback.snd σ (Work.SSSR.sSingP p)) h3
      have hD : (Work.SSSR.vertIncl p b n
              ≫ (Work.SSSR.faceLift (Work.SSSR.sSingP p) σ ez hez (Fin.last (n+1))
                ≫ Work.SSSR.pullFaceIncl (Work.SSSR.sSingP p) σ (Fin.last (n+1))))
            ≫ pullback.snd σ (Work.SSSR.sSingP p)
          = (Work.SSSR.vertIncl p b n
              ≫ Work.SSSR.faceLift (Work.SSSR.sSingP p) σ ez hez (Fin.last (n+1)))
            ≫ pullback.snd (SSet.stdSimplex.δ (n := n) (Fin.last (n+1)) ≫ σ) (Work.SSSR.sSingP p) := by
        simp only [Category.assoc]
        rw [h4]
      exact hA.trans (hB.trans (hC.trans hD))
    have hcycface : (ModuleCat.Hom.hom ((Work.SSSR.pieceAlong R (Work.SSSR.sSingP p)
          (SSet.stdSimplex.δ (n := n) (Fin.last (n+1)) ≫ σ)).d (n+t)
        ((ComplexShape.down ℕ).next (n+t))))
        ((ModuleCat.Hom.hom ((Work.SSSR.pieceπOf (Work.SSSR.sSingP p)
            (SSet.stdSimplex.δ (n := n) (Fin.last (n+1)) ≫ σ)).f (n+t)))
          ((ModuleCat.Hom.hom ((Work.SSSR.sCCMap R (Work.SSSR.faceLift (Work.SSSR.sSingP p) σ ez hez
            (Fin.last (n+1)))).f (n+t)))
            (Work.SSSR.ezLinSnd n t
              (SSet.stdSimplex.obj (SimplexCategory.mk n) : SSet.{0})
              (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b)) (Work.SSSR.stdIdSimplex n) z))) = 0 :=
      Work.SSSR.ezLinSnd_chain_cycle p n t b
        (SSet.stdSimplex.δ (n := n) (Fin.last (n+1)) ≫ σ)
        (Work.SSSR.faceLift (Work.SSSR.sSingP p) σ ez hez (Fin.last (n+1)))
        (Work.SSSR.faceLift_fst (Work.SSSR.sSingP p) σ ez hez (Fin.last (n+1))) z hz
    have hcyc'face : (Work.SSSR.sCC R (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p
          (Work.SSSR.sigmaVert (SSet.stdSimplex.δ (n := n) (Fin.last (n+1)) ≫ σ))))).d t
        ((ComplexShape.down ℕ).next t)
        ((Work.SSSR.sCCMap R (v ≫ eqToHom (congrArg (fun z : B =>
          Work.SSSR.sSing (Work.SSSR.StemsB.fibre p z)) hsv.symm))).f t z) = 0 := by
      rw [chainMap_d_apply', hz, map_zero]
    have hih := ih (SSet.stdSimplex.δ (n := n) (Fin.last (n+1)) ≫ σ)
      (Work.SSSR.faceLift (Work.SSSR.sSingP p) σ ez hez (Fin.last (n+1)))
      (Work.SSSR.faceLift_fst (Work.SSSR.sSingP p) σ ez hez (Fin.last (n+1)))
      (v ≫ eqToHom (congrArg (fun z : B => Work.SSSR.sSing (Work.SSSR.StemsB.fibre p z)) hsv.symm))
      hv_face hcycface hcyc'face
    have hpeel := Work.SSSR.pieceIso_peel p hfib n t b σ
      ((ModuleCat.Hom.hom ((Work.SSSR.sCCMap R ez).f ((n+1)+t)))
        (Work.SSSR.ezLinSnd (n+1) t
          (SSet.stdSimplex.obj (SimplexCategory.mk (n+1)) : SSet.{0})
          (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b)) (Work.SSSR.stdIdSimplex (n+1)) z))
      hcyc
      ((ModuleCat.Hom.hom ((Work.SSSR.sCCMap R (Work.SSSR.faceLift (Work.SSSR.sSingP p) σ ez hez
          (Fin.last (n+1)))).f (n+t)))
        (Work.SSSR.ezLinSnd n t
          (SSet.stdSimplex.obj (SimplexCategory.mk n) : SSet.{0})
          (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b)) (Work.SSSR.stdIdSimplex n) z))
      hcycface
      (Work.SSSR.hornCok_d_faceLift_chain_j1 p hfib n t b σ ez hez z hz)
    rw [hpeel, hih, map_zsmul]
    have hT : (eqToIso (congrArg (fun x : B => (Work.SSSR.Cohomology.singularChains R
          (TopCat.of (Work.SSSR.StemsB.fibre p x))).homology t)
        (Work.SSSR.sigmaVert_face (Fin.last (n+1)) (by
          intro hh; have hv := congrArg Fin.val hh; simp [Fin.last] at hv) σ))).hom
      = Work.SSSR.fibreConj p hsv t := by
      have hp : Work.SSSR.sigmaVert_face (Fin.last (n+1)) (by
          intro hh; have hv := congrArg Fin.val hh; simp [Fin.last] at hv) σ = hsv :=
        Subsingleton.elim _ _
      rw [hp]
      exact (Work.SSSR.fibreConj_eq p hsv t).symm
    rw [hT]
    refine (congrArg (fun w => (-1 : ℤ)^(n+1) • (c n • w))
      (Work.SSSR.fibreConj_homologyπ_v_face hsv v z hcyc'face hcyc')).trans ?_
    rw [smul_smul, hcsucc n]

end Work.SSSR
