import Mathlib
import Submission.Work.SSS.piszDefs
import Submission.Work.SSS.serreE1PieceExplicit
import Submission.Work.SSS.serreE1PieceIotaDefs
import Submission.Work.SSS.serreE1StepAux
import Submission.Work.SSS.ezSimplexZero_aux
import Submission.Work.SSS.hornCok_d_faceLift
import Submission.Work.SSS.pieceIso_peel
import Submission.Work.SSS.pieceIso_lift_zero
import Submission.Work.SSS.sigmaVert_face
import Submission.Work.SSS.sSingP_fibreIncl_comp

namespace Work.SSS

open CategoryTheory CategoryTheory.Limits Simplicial Opposite MonoidalCategory
open scoped MonoidalCategory Simplicial Topology

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

/-! ## Elementary transport lemmas -/

/-- `eqToHom`-naturality of the singular simplicial set of the fibres (local copy of
`Work.SSS.eqToHom_sSingP_fibreIncl`, to avoid importing `piszTower`). -/
lemma eqToHom_sSingP_fibreIncl' (p : C(E, B)) {x y : B} (h : x = y) :
    eqToHom (congrArg (fun z : B => Work.SSS.sSing (Work.StemsB.fibre p z)) h)
        ≫ Work.SSS.sSingP (Work.StemsB.fibreIncl p y)
      = Work.SSS.sSingP (Work.StemsB.fibreIncl p x) := by
  cases h
  rw [eqToHom_refl, Category.id_comp]

/-- The differential of a chain map, elementwise. -/
lemma chainMap_d_apply' {K L : ChainComplex (ModuleCat ℤ) ℕ} (φ : K ⟶ L) (i j : ℕ) (x : K.X i) :
    (L.d i j) ((φ.f i) x) = (φ.f j) ((K.d i j) x) := by
  have h := congrArg (fun (g : K.X i ⟶ L.X j) => (ModuleCat.Hom.hom g) x)
    (HomologicalComplex.Hom.comm φ i j)
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h

/-- A `homologyπ` applied to a degree-transported cycle. -/
lemma homologyπ_cyclesMk_castElem {K : ChainComplex (ModuleCat ℤ) ℕ} {i j : ℕ} (h : i = j)
    (x : K.X i) (hx : K.d i ((ComplexShape.down ℕ).next i) x = 0)
    (hx' : K.d j ((ComplexShape.down ℕ).next j) (castElem K h x) = 0) :
    (HomologicalComplex.homologyπ K j)
        (HomologicalComplex.cyclesMk K (castElem K h x) ((ComplexShape.down ℕ).next j) rfl hx')
      = (eqToIso (congrArg (fun m => K.homology m) h)).hom
          ((HomologicalComplex.homologyπ K i)
            (HomologicalComplex.cyclesMk K x ((ComplexShape.down ℕ).next i) rfl hx)) := by
  rw [Work.SSS.StepAux.eqToIso_homologyπ]
  congr 1
  exact (Work.SSS.StepAux.castCycles_cyclesMk K h rfl rfl x hx hx').symm


/-! ## The mod-horn boundary formula in the degrees used by `pieceIso_peel` -/

/-- **The `hpeel` hypothesis of `Work.SSS.pieceIso_peel`**, obtained from
`Work.SSS.hornCok_d_faceLift` (stated with the degrees `P+t`) by moving to the canonical
degree `(P+1)+t-1 = next ((P+1)+t)`. -/
lemma hornCok_d_faceLift_j1 (p : C(E, B)) (hfib : Work.StemsB.IsSerreFibration p) (P t : ℕ)
    (b : B)
    (σ : ((SSet.stdSimplex.obj (SimplexCategory.mk (P+1)) : SSet.{0})) ⟶ Work.SSS.sSing B)
    (ez : (((SSet.stdSimplex.obj (SimplexCategory.mk (P+1)) : SSet.{0})) ⊗
        Work.SSS.sSing (Work.StemsB.fibre p b)) ⟶ Work.SSS.pullAlong (Work.SSS.sSingP p) σ)
    (hez : ez ≫ pullback.fst σ (Work.SSS.sSingP p) = SemiCartesianMonoidalCategory.fst _ _)
    (τ : Work.SSS.sSing (Work.StemsB.fibre p b) _⦋t⦌)
    (hτ : (ModuleCat.Hom.hom ((Work.SSS.sCC (Work.SSS.sSing (Work.StemsB.fibre p b))).d t
        ((ComplexShape.down ℕ).next t)))
        (((Work.SSS.sSing (Work.StemsB.fibre p b)).ιChainComplex (R := ModuleCat.of ℤ ℤ) τ).hom 1) = 0) :
    (ModuleCat.Hom.hom ((Work.SSS.hornCokπ (Work.SSS.sSingP p) σ).f ((P+1)+t-1)))
        ((ModuleCat.Hom.hom ((Work.SSS.sCC (Work.SSS.pullAlong (Work.SSS.sSingP p) σ)).d
            ((P+1)+t) ((P+1)+t-1)))
          ((ModuleCat.Hom.hom ((Work.SSS.sCCMap ez).f ((P+1)+t)))
            (Work.Cohomology.Crux33.ezGen (P+1) t
              (SSet.stdSimplex.obj (SimplexCategory.mk (P+1)) : SSet.{0})
              (Work.SSS.sSing (Work.StemsB.fibre p b)) (Work.SSS.stdIdSimplex (P+1)) τ)))
      = (-1 : ℤ)^(P+1) •
          (ModuleCat.Hom.hom ((Work.SSS.hornCokπ (Work.SSS.sSingP p) σ).f ((P+1)+t-1)))
            ((ModuleCat.Hom.hom ((Work.SSS.TIncl (Work.SSS.sSingP p) σ).f ((P+1)+t-1)))
              ((ModuleCat.Hom.hom ((Work.SSS.lastFaceChain (Work.SSS.sSingP p) P σ).f ((P+1)+t-1)))
                (Work.SSS.castElem (Work.SSS.sCC (Work.SSS.pullAlong (Work.SSS.sSingP p)
                    (SSet.stdSimplex.δ (n := P) (Fin.last (P+1)) ≫ σ)))
                  (by omega : P+t = (P+1)+t-1)
                  ((ModuleCat.Hom.hom ((Work.SSS.sCCMap
                    (Work.SSS.faceLift (Work.SSS.sSingP p) σ ez hez (Fin.last (P+1)))).f (P+t)))
                  (Work.Cohomology.Crux33.ezGen P t
                    (SSet.stdSimplex.obj (SimplexCategory.mk P) : SSet.{0})
                    (Work.SSS.sSing (Work.StemsB.fibre p b)) (Work.SSS.stdIdSimplex P) τ))))) := by
  have h := Work.SSS.hornCok_d_faceLift p hfib P t b σ ez hez τ hτ
  have he : P+t = (P+1)+t-1 := by omega
  have he' : (P+1)+t-1 = P+t := by omega
  have hL : Work.SSS.castElem (cokernel (Work.SSS.bdryIncl (Work.SSS.sSingP p) σ ≫ Work.SSS.TIncl (Work.SSS.sSingP p) σ)) he
        ((ModuleCat.Hom.hom ((Work.SSS.hornCokπ (Work.SSS.sSingP p) σ).f (P+t)))
          ((ModuleCat.Hom.hom ((Work.SSS.sCC (Work.SSS.pullAlong (Work.SSS.sSingP p) σ)).d
            ((P+1)+t) (P+t)))
            ((ModuleCat.Hom.hom ((Work.SSS.sCCMap ez).f ((P+1)+t)))
              (Work.Cohomology.Crux33.ezGen (P+1) t
                (SSet.stdSimplex.obj (SimplexCategory.mk (P+1)) : SSet.{0})
                (Work.SSS.sSing (Work.StemsB.fibre p b)) (Work.SSS.stdIdSimplex (P+1)) τ))))
      = (ModuleCat.Hom.hom ((Work.SSS.hornCokπ (Work.SSS.sSingP p) σ).f ((P+1)+t-1)))
          ((ModuleCat.Hom.hom ((Work.SSS.sCC (Work.SSS.pullAlong (Work.SSS.sSingP p) σ)).d
            ((P+1)+t) ((P+1)+t-1)))
            ((ModuleCat.Hom.hom ((Work.SSS.sCCMap ez).f ((P+1)+t)))
              (Work.Cohomology.Crux33.ezGen (P+1) t
                (SSet.stdSimplex.obj (SimplexCategory.mk (P+1)) : SSet.{0})
                (Work.SSS.sSing (Work.StemsB.fibre p b)) (Work.SSS.stdIdSimplex (P+1)) τ))) := by
    rw [Work.SSS.StepAux.castElem_map]
    congr 1
    exact (Work.SSS.StepAux.d_eq_castElem (Work.SSS.sCC (Work.SSS.pullAlong (Work.SSS.sSingP p) σ))
      he
      ((ModuleCat.Hom.hom ((Work.SSS.sCCMap ez).f ((P+1)+t)))
        (Work.Cohomology.Crux33.ezGen (P+1) t
          (SSet.stdSimplex.obj (SimplexCategory.mk (P+1)) : SSet.{0})
          (Work.SSS.sSing (Work.StemsB.fibre p b)) (Work.SSS.stdIdSimplex (P+1)) τ))).symm
  have hR : Work.SSS.castElem (cokernel (Work.SSS.bdryIncl (Work.SSS.sSingP p) σ ≫ Work.SSS.TIncl (Work.SSS.sSingP p) σ)) he
        ((ModuleCat.Hom.hom ((Work.SSS.hornCokπ (Work.SSS.sSingP p) σ).f (P+t)))
          ((ModuleCat.Hom.hom ((Work.SSS.TIncl (Work.SSS.sSingP p) σ).f (P+t)))
            ((ModuleCat.Hom.hom ((Work.SSS.lastFaceChain (Work.SSS.sSingP p) P σ).f (P+t)))
              ((ModuleCat.Hom.hom ((Work.SSS.sCCMap (Work.SSS.faceLift (Work.SSS.sSingP p) σ ez hez
                  (Fin.last (P+1)))).f (P+t)))
                (Work.Cohomology.Crux33.ezGen P t
                  (SSet.stdSimplex.obj (SimplexCategory.mk P) : SSet.{0})
                  (Work.SSS.sSing (Work.StemsB.fibre p b)) (Work.SSS.stdIdSimplex P) τ)))))
      = (ModuleCat.Hom.hom ((Work.SSS.hornCokπ (Work.SSS.sSingP p) σ).f ((P+1)+t-1)))
          ((ModuleCat.Hom.hom ((Work.SSS.TIncl (Work.SSS.sSingP p) σ).f ((P+1)+t-1)))
            ((ModuleCat.Hom.hom ((Work.SSS.lastFaceChain (Work.SSS.sSingP p) P σ).f ((P+1)+t-1)))
              (Work.SSS.castElem (Work.SSS.sCC (Work.SSS.pullAlong (Work.SSS.sSingP p)
                  (SSet.stdSimplex.δ (n := P) (Fin.last (P+1)) ≫ σ)))
                he
                ((ModuleCat.Hom.hom ((Work.SSS.sCCMap
                  (Work.SSS.faceLift (Work.SSS.sSingP p) σ ez hez (Fin.last (P+1)))).f (P+t)))
                (Work.Cohomology.Crux33.ezGen P t
                  (SSet.stdSimplex.obj (SimplexCategory.mk P) : SSet.{0})
                  (Work.SSS.sSing (Work.StemsB.fibre p b)) (Work.SSS.stdIdSimplex P) τ))))) := by
    rw [Work.SSS.StepAux.castElem_map]
    congr 1
    rw [Work.SSS.StepAux.castElem_map]
    congr 1
    rw [Work.SSS.StepAux.castElem_map]
  have h2 := congrArg (Work.SSS.castElem (cokernel (Work.SSS.bdryIncl (Work.SSS.sSingP p) σ ≫ Work.SSS.TIncl (Work.SSS.sSingP p) σ)) he) h
  rw [Work.SSS.StepAux.castElem_zsmul] at h2
  rw [hL, hR] at h2
  exact h2

/-- **The transport of a fibre-homology class along a base-point equality**, for the map induced by
a lift composed with the transport. -/
lemma fibreConj_homologyπ_v_face {p : C(E, B)} {b : B} {t : ℕ} {x' x : B} (h : x' = x)
    (v : Work.SSS.sSing (Work.StemsB.fibre p b) ⟶ Work.SSS.sSing (Work.StemsB.fibre p x))
    (gen : (Work.SSS.sCC (Work.SSS.sSing (Work.StemsB.fibre p b))).X t)
    (h1 : (Work.SSS.sCC (Work.SSS.sSing (Work.StemsB.fibre p x'))).d t ((ComplexShape.down ℕ).next t)
        ((Work.SSS.sCCMap (v ≫ eqToHom (congrArg (fun z : B => Work.SSS.sSing (Work.StemsB.fibre p z)) h.symm))).f t gen) = 0)
    (h2 : (Work.SSS.sCC (Work.SSS.sSing (Work.StemsB.fibre p x))).d t ((ComplexShape.down ℕ).next t)
        ((Work.SSS.sCCMap v).f t gen) = 0) :
    (Work.SSS.fibreConj p h t)
      ((HomologicalComplex.homologyπ (Work.SSS.sCC (Work.SSS.sSing (Work.StemsB.fibre p x'))) t)
        (HomologicalComplex.cyclesMk (Work.SSS.sCC (Work.SSS.sSing (Work.StemsB.fibre p x')))
          ((Work.SSS.sCCMap (v ≫ eqToHom (congrArg (fun z : B => Work.SSS.sSing (Work.StemsB.fibre p z)) h.symm))).f t gen)
          ((ComplexShape.down ℕ).next t) rfl h1))
    = (HomologicalComplex.homologyπ (Work.SSS.sCC (Work.SSS.sSing (Work.StemsB.fibre p x))) t)
        (HomologicalComplex.cyclesMk (Work.SSS.sCC (Work.SSS.sSing (Work.StemsB.fibre p x)))
          ((Work.SSS.sCCMap v).f t gen) ((ComplexShape.down ℕ).next t) rfl h2) := by
  subst h
  simp only [eqToHom_refl, Work.SSS.fibreConj_rfl, ModuleCat.hom_id, LinearMap.id_apply]
  congr 1

/-- **The tower comparison for an arbitrary lift of a simplex.**

For a simplex `σ : Δ[P] ⟶ Sing B`, a lift `ez : Δ[P] ⊗ Sing (p⁻¹b) ⟶ T_σ` of `pr₁ ≫ σ`, a map
`v : Sing (p⁻¹b) ⟶ Sing (p⁻¹σ(v₀))` whose composite with the fibre inclusion is the `v₀`-slice
`vertIncl p b P ≫ ez ≫ pullback.snd σ (sSingP p)` of the lift (`hv`), a cycle `τ` of `p⁻¹b`, and a
sign family `c` with `c 0 = 1` and `c (n+1) = (-1)^(n+1) c n`, the iterated last-face connecting map
`ε_σ = serreE1PieceIso p hfib P t σ` sends the class of the projection of `ez_*(EZ(P,t,[id],τ))` to
`c P` times the class of `v_*(τ)`.

Induction on `P`: at `P = 0` this is `Work.SSS.pieceIso_lift_zero` (sign `1`); for `P = n+1` the
`n`-th case applies to the *face restriction* `Work.SSS.faceLift (sSingP p) σ ez hez (Fin.last (n+1))`
of the lift (with the same `v` and `τ`, using `Work.SSS.vertIncl_coface` and
`Work.SSS.faceLift_pullFaceIncl`; note `Work.SSS.sigmaVert_face` identifies the base point), the peel
is `Work.SSS.pieceIso_peel` whose hypothesis `hpeel` is `Work.SSS.hornCok_d_faceLift`, and the cycle
condition of the restricted chain follows from `Work.SSS.hornCok_d_faceLift` together with the facts
that `pieceπOf` kills `TIncl`-images and factors through `hornCokπ`. -/
theorem pieceIso_lift_genC (p : C(E, B)) (hfib : Work.StemsB.IsSerreFibration p)
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
    (τ : Work.SSS.sSing (Work.StemsB.fibre p b) _⦋t⦌)
    (hτ : (ModuleCat.Hom.hom ((Work.SSS.sCC (Work.SSS.sSing (Work.StemsB.fibre p b))).d t
        ((ComplexShape.down ℕ).next t)))
        (((Work.SSS.sSing (Work.StemsB.fibre p b)).ιChainComplex (R := ModuleCat.of ℤ ℤ) τ).hom 1) = 0)
    (hcyc : (ModuleCat.Hom.hom ((Work.SSS.pieceAlong (Work.SSS.sSingP p) σ).d (P+t)
        ((ComplexShape.down ℕ).next (P+t))))
        ((ModuleCat.Hom.hom ((Work.SSS.pieceπOf (Work.SSS.sSingP p) σ).f (P+t)))
          ((ModuleCat.Hom.hom ((Work.SSS.sCCMap ez).f (P+t)))
            (Work.Cohomology.Crux33.ezGen P t
              (SSet.stdSimplex.obj (SimplexCategory.mk P) : SSet.{0})
              (Work.SSS.sSing (Work.StemsB.fibre p b)) (Work.SSS.stdIdSimplex P) τ))) = 0)
    (hcyc' : (ModuleCat.Hom.hom ((Work.SSS.sCC (Work.SSS.sSing
        (Work.StemsB.fibre p (Work.SSS.sigmaVert σ)))).d t ((ComplexShape.down ℕ).next t)))
        ((ModuleCat.Hom.hom ((Work.SSS.sCCMap v).f t))
          (((Work.SSS.sSing (Work.StemsB.fibre p b)).ιChainComplex
            (R := ModuleCat.of ℤ ℤ) τ).hom 1)) = 0) :
    (Work.SSS.serreE1PieceIso p hfib P t σ).hom
        ((HomologicalComplex.homologyπ (Work.SSS.pieceAlong (Work.SSS.sSingP p) σ) (P+t))
          ((Work.SSS.pieceAlong (Work.SSS.sSingP p) σ).cyclesMk
            ((ModuleCat.Hom.hom ((Work.SSS.pieceπOf (Work.SSS.sSingP p) σ).f (P+t)))
              ((ModuleCat.Hom.hom ((Work.SSS.sCCMap ez).f (P+t)))
                (Work.Cohomology.Crux33.ezGen P t
                  (SSet.stdSimplex.obj (SimplexCategory.mk P) : SSet.{0})
                  (Work.SSS.sSing (Work.StemsB.fibre p b)) (Work.SSS.stdIdSimplex P) τ)))
            ((ComplexShape.down ℕ).next (P+t)) rfl hcyc))
      = c P • ((HomologicalComplex.homologyπ
            (Work.SSS.sCC (Work.SSS.sSing (Work.StemsB.fibre p (Work.SSS.sigmaVert σ)))) t)
          ((Work.SSS.sCC (Work.SSS.sSing (Work.StemsB.fibre p
              (Work.SSS.sigmaVert σ)))).cyclesMk
            ((ModuleCat.Hom.hom ((Work.SSS.sCCMap v).f t))
              (((Work.SSS.sSing (Work.StemsB.fibre p b)).ιChainComplex
                (R := ModuleCat.of ℤ ℤ) τ).hom 1))
            ((ComplexShape.down ℕ).next t) rfl hcyc')) := by
  induction P with
  | zero =>
    rw [hc0, one_smul]
    exact pieceIso_lift_zero p hfib t b σ ez hez v hv τ hτ hcyc hcyc'
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
    have hcycface : (Work.SSS.pieceAlong (Work.SSS.sSingP p)
          (SSet.stdSimplex.δ (n := n) (Fin.last (n+1)) ≫ σ)).d (n+t)
        ((ComplexShape.down ℕ).next (n+t))
        ((Work.SSS.pieceπOf (Work.SSS.sSingP p)
            (SSet.stdSimplex.δ (n := n) (Fin.last (n+1)) ≫ σ)).f (n+t)
          ((Work.SSS.sCCMap (Work.SSS.faceLift (Work.SSS.sSingP p) σ ez hez (Fin.last (n+1)))).f (n+t)
            (Work.Cohomology.Crux33.ezGen n t
              (SSet.stdSimplex.obj (SimplexCategory.mk n) : SSet.{0})
              (Work.SSS.sSing (Work.StemsB.fibre p b)) (Work.SSS.stdIdSimplex n) τ))) = 0 :=
      Work.SSS.sCCMap_ezGen_chain_cycle (Work.SSS.sSingP p) n t
        (SSet.stdSimplex.δ (n := n) (Fin.last (n+1)) ≫ σ)
        (Work.SSS.faceLift (Work.SSS.sSingP p) σ ez hez (Fin.last (n+1)))
        (Work.SSS.faceLift_fst (Work.SSS.sSingP p) σ ez hez (Fin.last (n+1))) τ hτ
    have hcyc'face : (Work.SSS.sCC (Work.SSS.sSing (Work.StemsB.fibre p
          (Work.SSS.sigmaVert (SSet.stdSimplex.δ (n := n) (Fin.last (n+1)) ≫ σ))))).d t
        ((ComplexShape.down ℕ).next t)
        ((Work.SSS.sCCMap (v ≫ eqToHom (congrArg (fun z : B =>
          Work.SSS.sSing (Work.StemsB.fibre p z)) hsv.symm))).f t
          (((Work.SSS.sSing (Work.StemsB.fibre p b)).ιChainComplex
            (R := ModuleCat.of ℤ ℤ) τ).hom 1)) = 0 := by
      rw [chainMap_d_apply', hτ, map_zero]
    have hih := ih (SSet.stdSimplex.δ (n := n) (Fin.last (n+1)) ≫ σ)
      (Work.SSS.faceLift (Work.SSS.sSingP p) σ ez hez (Fin.last (n+1)))
      (Work.SSS.faceLift_fst (Work.SSS.sSingP p) σ ez hez (Fin.last (n+1)))
      (v ≫ eqToHom (congrArg (fun z : B => Work.SSS.sSing (Work.StemsB.fibre p z)) hsv.symm))
      hv_face hcycface hcyc'face
    have hpeel := Work.SSS.pieceIso_peel p hfib n t b σ
      ((ModuleCat.Hom.hom ((Work.SSS.sCCMap ez).f ((n+1)+t)))
        (Work.Cohomology.Crux33.ezGen (n+1) t
          (SSet.stdSimplex.obj (SimplexCategory.mk (n+1)) : SSet.{0})
          (Work.SSS.sSing (Work.StemsB.fibre p b)) (Work.SSS.stdIdSimplex (n+1)) τ))
      hcyc
      ((ModuleCat.Hom.hom ((Work.SSS.sCCMap (Work.SSS.faceLift (Work.SSS.sSingP p) σ ez hez
          (Fin.last (n+1)))).f (n+t)))
        (Work.Cohomology.Crux33.ezGen n t
          (SSet.stdSimplex.obj (SimplexCategory.mk n) : SSet.{0})
          (Work.SSS.sSing (Work.StemsB.fibre p b)) (Work.SSS.stdIdSimplex n) τ))
      hcycface
      (Work.SSS.hornCok_d_faceLift_j1 p hfib n t b σ ez hez τ hτ)
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
      (Work.SSS.fibreConj_homologyπ_v_face hsv v
        (((Work.SSS.sSing (Work.StemsB.fibre p b)).ιChainComplex
          (R := ModuleCat.of ℤ ℤ) τ).hom 1) hcyc'face hcyc')).trans ?_
    rw [smul_smul, hcsucc n]

end Work.SSS
