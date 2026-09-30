import Mathlib
import Submission.Work.SSSR.serreE1Piece
import Submission.Work.SSSR.cokerInfSupChain
import Submission.Work.SSSR.coker_conj_iso
import Submission.Work.SSSR.pieceAlongZeroCoker
import Submission.Work.SSSR.pieceBdryHornIso
import Submission.Work.SSSR.pieceConnectingIso
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

variable {R : Type} [CommRing R] [Nontrivial R]

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 800000
set_option linter.style.haveILetI false

namespace Work.SSSR

open CategoryTheory CategoryTheory.Limits Simplicial Opposite
noncomputable section

/-- **Explicit form of `Work.SSSR.coker_inf_sup_iso_chain`** (the second isomorphism theorem). -/
noncomputable def cokerInfSupChainIso (Z : SSet.{0}) (A M : Z.Subcomplex) :
    CategoryTheory.Limits.cokernel
        (sCCMap R (SSet.Subcomplex.homOfLE (inf_le_right : A ⊓ M ≤ M))) ≅
      CategoryTheory.Limits.cokernel
        (sCCMap R (SSet.Subcomplex.homOfLE (le_sup_left : A ≤ A ⊔ M))) := by
  letI : IsIso (CategoryTheory.Limits.cokernel.map
      (sCCMap R (SSet.Subcomplex.homOfLE (inf_le_right : A ⊓ M ≤ M)))
      (sCCMap R (SSet.Subcomplex.homOfLE (le_sup_left : A ≤ A ⊔ M)))
      (sCCMap R (SSet.Subcomplex.homOfLE (inf_le_left : A ⊓ M ≤ A)))
      (sCCMap R (SSet.Subcomplex.homOfLE (le_sup_right : M ≤ A ⊔ M)))
      (isPushout_sCC Z A M).w) :=
    CategoryTheory.Limits.isIso_cokernel_map_of_isPushout (isPushout_sCC Z A M)
  exact asIso (CategoryTheory.Limits.cokernel.map
      (sCCMap R (SSet.Subcomplex.homOfLE (inf_le_right : A ⊓ M ≤ M)))
      (sCCMap R (SSet.Subcomplex.homOfLE (le_sup_left : A ≤ A ⊔ M)))
      (sCCMap R (SSet.Subcomplex.homOfLE (inf_le_left : A ⊓ M ≤ A)))
      (sCCMap R (SSet.Subcomplex.homOfLE (le_sup_right : M ≤ A ⊔ M)))
      (isPushout_sCC Z A M).w)

/-- **Explicit form of `Work.SSSR.coker_conj_iso`.** -/
noncomputable def cokerConjIso {W Z : SSet.{0}} (Φ : W ⟶ Z) [CategoryTheory.Mono Φ]
    (P : W.Subcomplex) :
    CategoryTheory.Limits.cokernel
        (Work.SSSR.sCCMap R (SSet.Subcomplex.homOfLE (SSet.Subcomplex.image_le_range P Φ))) ≅
      CategoryTheory.Limits.cokernel (Work.SSSR.sCCMap R P.ι) := by
  have hcomp : ∀ {X Y Z : SSet.{0}} (f : X ⟶ Y) (g : Y ⟶ Z),
      sCCMap R (f ≫ g) = sCCMap R f ≫ sCCMap R g := by
    intro X Y Z f g
    simp only [sCCMap, Functor.map_comp]
  haveI : IsIso (SSet.Subcomplex.toRange Φ) := inferInstance
  haveI : IsIso (P.toImage Φ) := by
    haveI : Mono (P.toImage Φ) :=
      mono_of_mono_fac (SSet.Subcomplex.toImage_ι P Φ)
    exact CategoryTheory.isIso_of_mono_of_epi (P.toImage Φ)
  haveI : IsIso (sCCMap R (P.toImage Φ)) := inferInstance
  haveI : IsIso (sCCMap R (SSet.Subcomplex.toRange Φ)) := inferInstance
  have hsq : P.toImage Φ ≫ SSet.Subcomplex.homOfLE (SSet.Subcomplex.image_le_range P Φ)
      = P.ι ≫ SSet.Subcomplex.toRange Φ := by
    apply (cancel_mono (SSet.Subcomplex.range Φ).ι).1
    rw [Category.assoc, Category.assoc, SSet.Subcomplex.homOfLE_ι, SSet.Subcomplex.toRange_ι,
        SSet.Subcomplex.toImage_ι P Φ]
  refine (CategoryTheory.Limits.cokernel.mapIso (sCCMap R P.ι)
      (sCCMap R (SSet.Subcomplex.homOfLE (SSet.Subcomplex.image_le_range P Φ)))
      (asIso (sCCMap R (P.toImage Φ)))
      (asIso (sCCMap R (SSet.Subcomplex.toRange Φ))) ?_).symm
  simp only [asIso_hom]
  rw [← hcomp, ← hcomp, hsq]

/-- **Explicit form of `Work.SSSR.coker_homOfLE_congr`.** -/
noncomputable def cokerHomOfLECongrIso {Z : SSet.{0}} {A A' B B' : Z.Subcomplex} (hA : A = A')
    (hB : B = B') (hAB : A ≤ B) (hAB' : A' ≤ B') :
    cokernel (sCCMap R (SSet.Subcomplex.homOfLE hAB)) ≅
      cokernel (sCCMap R (SSet.Subcomplex.homOfLE hAB')) := by
  refine cokernel.mapIso _ _ (sCCFunctor.mapIso (SSet.Subcomplex.eqToIso hA))
    (sCCFunctor.mapIso (SSet.Subcomplex.eqToIso hB)) ?_
  simp only [CategoryTheory.Functor.mapIso_hom, SSet.Subcomplex.eqToIso_hom]
  rw [← sCCMap_comp', ← sCCMap_comp', SSet.Subcomplex.homOfLE_comp,
    SSet.Subcomplex.homOfLE_comp]

/-- **Explicit form of `Work.SSSR.coker_iota_congr`.** -/
noncomputable def cokerIotaCongrIso {Z : SSet.{0}} {P Q : Z.Subcomplex} (h : P = Q) :
    cokernel (sCCMap R P.ι) ≅ cokernel (sCCMap R Q.ι) := by
  subst h
  exact Iso.refl _

/-- **Explicit form of `Work.SSSR.pieceAlongZeroCoker`.** -/
noncomputable def pieceAlongZeroCokerIso {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B))
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk 0) : SSet.{0}) ⟶ Work.SSSR.sSing B) :
    Work.SSSR.pieceAlong R (Work.SSSR.sSingP p) σ ≅
      Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ) := by
  unfold pieceAlong
  haveI hπ : IsIso (cokernel.π (sCCMap R (bdryAlong (Work.SSSR.sSingP p) σ).ι)) :=
    CokernelCofork.IsColimit.isIso_π
      (CokernelCofork.ofπ (cokernel.π _) (cokernel.condition _))
      (cokernelIsCokernel _)
      (sCCMap_ι_eq_zero_of_eq_bot (bdryAlong_eq_bot_of_zero (Work.SSSR.sSingP p) σ))
  exact (asIso (cokernel.π (sCCMap R (bdryAlong (Work.SSSR.sSingP p) σ).ι))).symm

/-- **Explicit form of `Work.SSSR.pullAlong_vertex_iso`.** -/
noncomputable def pullAlongVertexIsoIso {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B))
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk 0) : SSet.{0}) ⟶ Work.SSSR.sSing B) :
    pullback σ (Work.SSSR.sSingP p) ≅ sSing (Work.SSSR.StemsB.fibre p (Work.SSSR.sigmaVert σ)) := by
  haveI := phiAlong_isIso p σ
  exact (asIso (phiAlong p σ)).symm

/-- **Explicit form of `Work.SSSR.pieceAlongZero`.** -/
noncomputable def pieceAlongZeroIso {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B))
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk 0) : SSet.{0}) ⟶ Work.SSSR.sSing B) :
    Work.SSSR.pieceAlong R (Work.SSSR.sSingP p) σ ≅
      Work.SSSR.Cohomology.singularChains R
        (TopCat.of (Work.SSSR.StemsB.fibre p (Work.SSSR.sigmaVert σ))) :=
  pieceAlongZeroCokerIso p σ ≪≫
    ((SSet.chainComplexFunctor (ModuleCat R)).obj (ModuleCat.of R R)).mapIso
      (pullAlongVertexIsoIso p σ) ≪≫
    eqToIso (show sCC R (sSing (Work.SSSR.StemsB.fibre p (Work.SSSR.sigmaVert σ))) =
      Work.SSSR.Cohomology.singularChains R
        (TopCat.of (Work.SSSR.StemsB.fibre p (Work.SSSR.sigmaVert σ))) from rfl)

/-- **Explicit form of `Work.SSSR.pieceBdryHornIso`.** -/
noncomputable def pieceBdryHornIsoIso {X Y : SSet.{0}} (f : X ⟶ Y) (t : ℕ)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) ⟶ Y) :
    Work.SSSR.pieceBdryHornC R f σ ≅
      Work.SSSR.pieceAlong R f (SSet.stdSimplex.δ (n := t) (Fin.last (t+1)) ≫ σ) := by
  haveI : Mono (lastFaceMap f t σ) := lastFaceMap_mono f t σ
  have himg : ((pieceHorn f σ).preimage (lastFaceMap f t σ)).image (lastFaceMap f t σ)
      = pieceHorn f σ ⊓ pieceLastFace f σ :=
    (image_preimage_eq_inf_range (pieceHorn f σ) (lastFaceMap f t σ)).trans
      (congrArg (fun S => pieceHorn f σ ⊓ S) (range_lastFaceMap f t σ))
  exact cokerHomOfLECongrIso (Z := pullAlong f σ) (A := pieceHorn f σ)
      (A' := pieceHorn f σ) (B := bdryAlong f σ) (B' := pieceHorn f σ ⊔ pieceLastFace f σ)
      rfl (bdryAlong_eq_horn_sup_lastFace f t σ).symm (pieceHorn_le_bdryAlong f σ) le_sup_left ≪≫
    (cokerInfSupChainIso (pullAlong f σ) (pieceHorn f σ) (pieceLastFace f σ)).symm ≪≫
    cokerHomOfLECongrIso (Z := pullAlong f σ)
      (A := pieceHorn f σ ⊓ pieceLastFace f σ)
      (A' := ((pieceHorn f σ).preimage (lastFaceMap f t σ)).image (lastFaceMap f t σ))
      (B := pieceLastFace f σ) (B' := SSet.Subcomplex.range (lastFaceMap f t σ))
      himg.symm (range_lastFaceMap f t σ).symm inf_le_right (SSet.Subcomplex.image_le_range _ _) ≪≫
    cokerConjIso (lastFaceMap f t σ) ((pieceHorn f σ).preimage (lastFaceMap f t σ)) ≪≫
    cokerIotaCongrIso (Z := pullAlong f (SSet.stdSimplex.δ (n := t) (Fin.last (t+1)) ≫ σ))
      (P := (pieceHorn f σ).preimage (lastFaceMap f t σ))
      (Q := bdryAlong f (SSet.stdSimplex.δ (n := t) (Fin.last (t+1)) ≫ σ))
      (preimage_lastFaceMap f t σ)

/-- **Explicit form of `Work.SSSR.pieceConnectingIso`.** -/
noncomputable def pieceConnectingIsoIso {X Y : SSet.{0}} (f : X ⟶ Y) (t : ℕ)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) ⟶ Y)
    (m : ℕ) (hm : 1 ≤ m)
    (hi : IsZero ((Work.SSSR.pieceHornC R f σ).homology m))
    (hj : IsZero ((Work.SSSR.pieceHornC R f σ).homology (m-1))) :
    (Work.SSSR.pieceAlong R f σ).homology m ≅ (Work.SSSR.pieceBdryHornC R f σ).homology (m-1) := by
  let i := Work.SSSR.sCCMap R (SSet.Subcomplex.homOfLE (Work.SSSR.pieceHorn_le_bdryAlong f σ))
  let j := Work.SSSR.sCCMap R (Work.SSSR.bdryAlong f σ).ι
  let k := Work.SSSR.sCCMap R (Work.SSSR.pieceHorn f σ).ι
  have hkey : i ≫ j = k := by
    show Work.SSSR.sCCMap R (SSet.Subcomplex.homOfLE (Work.SSSR.pieceHorn_le_bdryAlong f σ)) ≫
      Work.SSSR.sCCMap R (Work.SSSR.bdryAlong f σ).ι = Work.SSSR.sCCMap R (Work.SSSR.pieceHorn f σ).ι
    rw [Work.SSSR.sChainMap_comp R _ _]
    rw [Subfunctor.homOfLe_ι]
  have hmono : Mono j := by
    change Mono (Work.SSSR.sChainMap R (Work.SSSR.bdryAlong f σ).ι)
    exact Work.SSSR.sChainMap_mono R _ inferInstance
  haveI : Mono j := hmono
  have hS : (ShortComplex.SnakeInput.L₃ (kernelCokernelCompSequence.snakeInput i j)).ShortExact :=
    cokernelComp_shortExact i j
  have hi' : IsZero ((cokernel (i ≫ j)).homology m) :=
    IsZero.of_iso hi ((HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.down ℕ)
      m).mapIso (cokernelIsoOfEq hkey))
  have hj' : IsZero ((cokernel (i ≫ j)).homology (m-1)) :=
    IsZero.of_iso hj ((HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.down ℕ)
      (m-1)).mapIso (cokernelIsoOfEq hkey))
  exact hS.δIso m (m-1) (ComplexShape.down_mk m (m-1) (by omega)) hi' hj'

/-- **Explicit form of `Work.SSSR.serreE1Piece`**: the iterated face map
`ε_σ : H_{s+k}(T_σ, ∂T_σ) ≅ H_k(F_{σ(v₀)})`. -/
noncomputable def serreE1PieceIso {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (hfib : Work.SSSR.StemsB.IsSerreFibration p) (s k : ℕ)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0}) ⟶ Work.SSSR.sSing B) :
    (Work.SSSR.pieceAlong R (Work.SSSR.sSingP p) σ).homology (s + k) ≅
      (Work.SSSR.Cohomology.singularChains R
        (TopCat.of (Work.SSSR.StemsB.fibre p (Work.SSSR.sigmaVert σ)))).homology k := by
  induction s with
  | zero =>
    rw [Nat.zero_add]
    exact HomologicalComplex.homologyMapIso (pieceAlongZeroIso p σ) k
  | succ t ih =>
    have hcont := Work.SSSR.pieceContraction p hfib (Nat.succ_le_succ (Nat.zero_le t)) σ
    let g := Classical.choose hcont
    let H := Classical.choose (Classical.choose_spec hcont)
    have hspec := Classical.choose_spec (Classical.choose_spec hcont)
    have hZero : ∀ (j : ℕ), IsZero ((Work.SSSR.pieceHornC R (Work.SSSR.sSingP p) σ).homology j) :=
      fun j => ModuleCat.isZero_iff_subsingleton.mpr
        (Work.SSSR.pieceHornAcyclic R p σ g H hspec.1 hspec.2 j)
    have h1 : t + 1 + k - 1 = t + k := by omega
    have h2 : Fin.last (t+1) ≠ (0 : Fin (t+2)) := by
      intro h
      have hv := congrArg Fin.val h
      simp [Fin.last] at hv
    have hsv := Work.SSSR.sigmaVert_face (Fin.last (t+1)) h2 σ
    exact pieceConnectingIsoIso (Work.SSSR.sSingP p) t σ (t + 1 + k) (by omega)
        (hZero _) (hZero _) ≪≫
      eqToIso (congrArg (fun (m : ℕ) =>
        (Work.SSSR.pieceBdryHornC R (Work.SSSR.sSingP p) σ).homology m) h1) ≪≫
      HomologicalComplex.homologyMapIso
        (pieceBdryHornIsoIso (Work.SSSR.sSingP p) t σ) (t + k) ≪≫
      ih (SSet.stdSimplex.δ (n := t) (Fin.last (t+1)) ≫ σ) ≪≫
      eqToIso (congrArg (fun (x : B) =>
        (Work.SSSR.Cohomology.singularChains R (TopCat.of (Work.SSSR.StemsB.fibre p x))).homology k) hsv)

end

end Work.SSSR
