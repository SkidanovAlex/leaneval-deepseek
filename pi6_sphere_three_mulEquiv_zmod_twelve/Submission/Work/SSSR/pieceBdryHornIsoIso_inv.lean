import Mathlib
import Submission.Work.SSSR.serreE1PieceIotaDefs
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

variable {R : Type} [CommRing R] [Nontrivial R]

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 4000000

attribute [local implicit_reducible] Work.SSSR.pullAlong
attribute [local implicit_reducible] Work.SSSR.pieceHorn
attribute [local implicit_reducible] Work.SSSR.pieceLastFace
attribute [local implicit_reducible] Work.SSSR.bdryAlong
attribute [local implicit_reducible] Work.SSSR.pieceAlong
attribute [local implicit_reducible] Work.SSSR.pieceBdryHornC
attribute [local implicit_reducible] Work.SSSR.pieceHornC
attribute [local implicit_reducible] Work.SSSR.lastFaceChain

namespace Work.SSSR

open CategoryTheory CategoryTheory.Limits Simplicial Opposite MonoidalCategory
open scoped MonoidalCategory Simplicial
/-- The basic computation: `cokernel.π f ≫ cokernel.map f f' p q w = q ≫ cokernel.π f'`. -/
theorem pieceInv_cok_pi_comp_map {C : Type*} [Category* C] [HasZeroMorphisms C]
    {X Y X' Y' : C} (f : X ⟶ Y) [HasCokernel f] (f' : X' ⟶ Y') [HasCokernel f']
    (p : X ⟶ X') (q : Y ⟶ Y') (w : f ≫ q = p ≫ f') :
    cokernel.π f ≫ cokernel.map f f' p q w = q ≫ cokernel.π f' := by
  rw [cokernel.map, cokernel.π_desc]

/-- `cokerIotaCongrIso` on the inverse direction is invisible. -/
theorem pieceInv_cokerIotaCongrIso_inv_π {Z : SSet.{0}} {P Q : Z.Subcomplex} (h : P = Q) :
    cokernel.π (sCCMap R Q.ι) ≫ (cokerIotaCongrIso h).inv = cokernel.π (sCCMap R P.ι) := by
  subst h
  simp [cokerIotaCongrIso]

/-- `cokerConjIso` on the inverse direction pushes forward along `toRange`. -/
theorem pieceInv_cokerConjIso_inv_π {W Z : SSet.{0}} (Φ : W ⟶ Z) [Mono Φ]
    (P : W.Subcomplex) :
    cokernel.π (sCCMap R P.ι) ≫ (cokerConjIso Φ P).inv
      = sCCMap R (SSet.Subcomplex.toRange Φ) ≫
        cokernel.π (sCCMap R (SSet.Subcomplex.homOfLE (SSet.Subcomplex.image_le_range P Φ))) := by
  rw [cokerConjIso, Iso.symm_inv, cokernel.mapIso_hom]
  exact pieceInv_cok_pi_comp_map (sCCMap R P.ι)
    (sCCMap R (SSet.Subcomplex.homOfLE (SSet.Subcomplex.image_le_range P Φ)))
    (sCCMap R (P.toImage Φ)) (sCCMap R (SSet.Subcomplex.toRange Φ)) _

/-- `cokerHomOfLECongrIso` on the inverse direction is the transport of the target subcomplex. -/
theorem pieceInv_cokerHomOfLECongrIso_inv_π {Z : SSet.{0}} {A A' B B' : Z.Subcomplex}
    (hA : A = A') (hB : B = B') (hAB : A ≤ B) (hAB' : A' ≤ B') :
    cokernel.π (sCCMap R (SSet.Subcomplex.homOfLE hAB'))
      ≫ (cokerHomOfLECongrIso hA hB hAB hAB').inv
      = sCCMap R (SSet.Subcomplex.homOfLE hB.symm.le) ≫
        cokernel.π (sCCMap R (SSet.Subcomplex.homOfLE hAB)) := by
  rw [cokerHomOfLECongrIso, cokernel.mapIso_inv]
  exact pieceInv_cok_pi_comp_map (sCCMap R (SSet.Subcomplex.homOfLE hAB'))
    (sCCMap R (SSet.Subcomplex.homOfLE hAB))
    (sCCFunctor.mapIso (SSet.Subcomplex.eqToIso hA)).inv
    (sCCFunctor.mapIso (SSet.Subcomplex.eqToIso hB)).inv _

/-- `cokerInfSupChainIso` (the second isomorphism theorem) on the forward direction. -/
theorem pieceInv_cokerInfSupChainIso_hom_π {Z : SSet.{0}} (A M : Z.Subcomplex) :
    cokernel.π (sCCMap R (SSet.Subcomplex.homOfLE (inf_le_right : A ⊓ M ≤ M)))
      ≫ (cokerInfSupChainIso Z A M).hom
      = sCCMap R (SSet.Subcomplex.homOfLE (le_sup_right : M ≤ A ⊔ M))
        ≫ cokernel.π (sCCMap R (SSet.Subcomplex.homOfLE (le_sup_left : A ≤ A ⊔ M))) := by
  rw [cokerInfSupChainIso, CategoryTheory.asIso_hom]
  exact pieceInv_cok_pi_comp_map
    (sCCMap R (SSet.Subcomplex.homOfLE (inf_le_right : A ⊓ M ≤ M)))
    (sCCMap R (SSet.Subcomplex.homOfLE (le_sup_left : A ≤ A ⊔ M)))
    (sCCMap R (SSet.Subcomplex.homOfLE (inf_le_left : A ⊓ M ≤ A)))
    (sCCMap R (SSet.Subcomplex.homOfLE (le_sup_right : M ≤ A ⊔ M))) _

/-- The `cokerIotaCongrIso` step of the composite, with the remaining tail `e` kept explicit. -/
theorem pieceInv_cc1 {Z : SSet.{0}} {P Q : Z.Subcomplex} (h : P = Q)
    {P' : ChainComplex (ModuleCat R) ℕ} (e : cokernel (sCCMap R P.ι) ⟶ P') :
    cokernel.π (sCCMap R Q.ι) ≫ ((cokerIotaCongrIso h).inv ≫ e)
      = cokernel.π (sCCMap R P.ι) ≫ e := by
  rw [← Category.assoc, pieceInv_cokerIotaCongrIso_inv_π]

/-- The `cokerConjIso` step of the composite, with the remaining tail `e` kept explicit. -/
theorem pieceInv_cc2 {W Z : SSet.{0}} (Φ : W ⟶ Z) [Mono Φ] (P : W.Subcomplex)
    {P' : ChainComplex (ModuleCat R) ℕ}
    (e : cokernel (sCCMap R (SSet.Subcomplex.homOfLE (SSet.Subcomplex.image_le_range P Φ)))
      ⟶ P') :
    cokernel.π (sCCMap R P.ι) ≫ ((cokerConjIso Φ P).inv ≫ e)
      = (sCCMap R (SSet.Subcomplex.toRange Φ) ≫
          cokernel.π (sCCMap R (SSet.Subcomplex.homOfLE
            (SSet.Subcomplex.image_le_range P Φ)))) ≫ e := by
  rw [← Category.assoc, pieceInv_cokerConjIso_inv_π]

/-- The first `cokerHomOfLECongrIso` step of the composite, with the remaining tail `e`. -/
theorem pieceInv_cc3 {Z : SSet.{0}} {A A' B B' : Z.Subcomplex}
    (hA : A = A') (hB : B = B') (hAB : A ≤ B) (hAB' : A' ≤ B')
    {P' : ChainComplex (ModuleCat R) ℕ}
    (e : cokernel (sCCMap R (SSet.Subcomplex.homOfLE hAB)) ⟶ P') :
    cokernel.π (sCCMap R (SSet.Subcomplex.homOfLE hAB'))
      ≫ ((cokerHomOfLECongrIso hA hB hAB hAB').inv ≫ e)
      = (sCCMap R (SSet.Subcomplex.homOfLE hB.symm.le) ≫
          cokernel.π (sCCMap R (SSet.Subcomplex.homOfLE hAB))) ≫ e := by
  rw [← Category.assoc, pieceInv_cokerHomOfLECongrIso_inv_π]

/-- The `cokerInfSupChainIso` step of the composite, with the remaining tail `e`.  The
`homOfLE`-proof is kept explicit as a variable so that the lemma matches syntactically. -/
theorem pieceInv_cc4 {Z : SSet.{0}} (A M : Z.Subcomplex) (h : A ⊓ M ≤ M)
    {P' : ChainComplex (ModuleCat R) ℕ}
    (e : cokernel (sCCMap R (SSet.Subcomplex.homOfLE (le_sup_left : A ≤ A ⊔ M))) ⟶ P') :
    cokernel.π (sCCMap R (SSet.Subcomplex.homOfLE h))
      ≫ ((cokerInfSupChainIso Z A M).hom ≫ e)
      = (sCCMap R (SSet.Subcomplex.homOfLE (le_sup_right : M ≤ A ⊔ M))
          ≫ cokernel.π (sCCMap R (SSet.Subcomplex.homOfLE (le_sup_left : A ≤ A ⊔ M)))) ≫ e := by
  rw [← Category.assoc, pieceInv_cokerInfSupChainIso_hom_π]

/-- The composition of two inclusions of subcomplexes, with the remaining tail `e`. -/
theorem pieceInv_cc5 {Z : SSet.{0}} {A B C : Z.Subcomplex} (h : A ≤ B) (h' : B ≤ C)
    {P : ChainComplex (ModuleCat R) ℕ} (e : sCC R C ⟶ P) :
    sCCMap R (SSet.Subcomplex.homOfLE h) ≫ (sCCMap R (SSet.Subcomplex.homOfLE h') ≫ e)
      = sCCMap R (SSet.Subcomplex.homOfLE (h.trans h')) ≫ e := by
  rw [← Category.assoc, ← sCCMap_comp', SSet.Subcomplex.homOfLE_comp]

/-- **The inverse of `pieceBdryHornIsoIso` is the explicit last-face map.**  For a morphism of
simplicial sets `f : X ⟶ Y` and a simplex `σ : Δ[t+1] ⟶ Y`, the isomorphism
`Work.SSSR.pieceBdryHornIsoIso f t σ : C(∂T_σ)/C(Λ) ≅ C(T_{d_lastσ})/C(∂T_{d_lastσ})` is the
"identity on the last face": its inverse sends the class of a chain `w` of `T_{d_lastσ}` to the
class in `C(∂T_σ)/C(Λ)` of `lastFaceChain f t σ w`, the push-forward of `w` along the pasting map
`lastFaceMap f t σ` (whose range is the last face `pieceLastFace f σ ≤ ∂T_σ`).

Proof route: `pieceBdryHornIsoIso` is a composite of five isomorphisms, each of which is a
`CategoryTheory.Limits.cokernel.map`/`mapIso` of explicit chain maps of inclusions
(`Work.SSSR.cokerHomOfLECongrIso`, `Work.SSSR.cokerInfSupChainIso`, `Work.SSSR.cokerConjIso`,
`Work.SSSR.cokerIotaCongrIso`, all in `Submission/Work/SSS/serreE1PieceExplicit.lean`).  In the
direction of the inverse all of these are `cokernel.map`s of honest maps, so the composite can be
computed on the class of a chain by repeatedly applying
`CategoryTheory.Limits.cokernel.π_desc`
(`cokernel.π f ≫ cokernel.map f f' p q w = q ≫ cokernel.π f'`); the resulting chain map is then
identified with `lastFaceChain` using `Subfunctor.homOfLe_ι`, `Subfunctor.toRange_ι` and the
definition `Work.SSSR.lastFaceMap`. -/
theorem pieceBdryHornIsoIso_inv {X Y : SSet.{0}} (f : X ⟶ Y) (t : ℕ)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) ⟶ Y) :
    cokernel.π (Work.SSSR.TIncl f (SSet.stdSimplex.δ (n := t) (Fin.last (t+1)) ≫ σ))
        ≫ (Work.SSSR.pieceBdryHornIsoIso f t σ).inv
      = Work.SSSR.lastFaceChain f t σ ≫ Work.SSSR.bdryHornProj (R := R) f σ := by
  rw [pieceBdryHornIsoIso]
  simp only [Iso.trans_inv, Iso.symm_inv]
  simp only [TIncl, bdryHornProj, bdryIncl, lastFaceChain]
  simp only [Category.assoc]
  rw [pieceInv_cc1]
  rw [pieceInv_cc2]
  rw [Category.assoc]
  rw [pieceInv_cc3]
  rw [Category.assoc]
  set k5 := (cokerHomOfLECongrIso (R := R) (Z := pullAlong f σ) (A := pieceHorn f σ)
    (A' := pieceHorn f σ) (B := bdryAlong f σ) (B' := pieceHorn f σ ⊔ pieceLastFace f σ) rfl
    (bdryAlong_eq_horn_sup_lastFace f t σ).symm (pieceHorn_le_bdryAlong f σ) le_sup_left).inv
    with hk5
  rw [pieceInv_cc4 (Z := pullAlong f σ) (pieceHorn f σ) (pieceLastFace f σ) inf_le_right k5]
  rw [Category.assoc]
  rw [pieceInv_cokerHomOfLECongrIso_inv_π]
  rw [pieceInv_cc5]
  rw [pieceInv_cc5]

end Work.SSSR
