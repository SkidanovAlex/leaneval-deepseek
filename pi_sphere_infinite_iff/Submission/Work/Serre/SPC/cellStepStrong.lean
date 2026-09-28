import Mathlib
import Submission.Work.Serre.SPC.Defs
import Submission.Work.Serre.cellStep
import Submission.Work.Serre.SPC.cellPieceStrong

set_option synthInstance.maxHeartbeats 400000


/-!
# The strengthened cell step

`Work.Serre.SPC.CellStepHyp` is the *strengthened* cell step: the pair comparison
`(X, q⁻¹Γ) → (Γ', Γ)` of a Serre fibration over a cell attachment is an isomorphism on integral
homology in degrees `< D + φ` **and surjective in degree `D + φ`**.

The isomorphism part is `Work.Serre.cellStep` (proved in `Submission/Work/Serre/cellStep.lean`); the
surjectivity in the boundary degree is obtained here by replaying the same assembly (compression,
excision, decomposition over the open pieces) with surjectivity in place of `IsIso`, using the
per-piece surjectivity `Work.Serre.SPC.cellPieceSurj`.

The only new ingredient at the level of homological algebra is that the coproduct of a family of
chain maps which are surjective on `H_m` is surjective on `H_m`
(`Work.Serre.SPC.surjective_homologyMap_sigma`), together with the corresponding additivity
statement over a disjoint union of pairs (`Work.Serre.SPC.sigmaPairMap_surjective`).
-/

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open scoped Topology unitInterval
open CategoryTheory CategoryTheory.Limits
open Work.Serre
open Work.RatHurewicz

namespace Work.Serre.SPC

noncomputable section

/-! ## Surjectivity of a coproduct of chain maps on homology -/

/-- **Surjectivity is additive over a coproduct of chain complexes**: if a family of chain maps is
surjective on `H_n`, then so is the coproduct of the maps.  The mirror of
`Work.Serre.CellStep.isIso_homologyMap_sigma`. -/
theorem surjective_homologyMap_sigma {ι : Type} {K L : ι → ChainComplex (ModuleCat ℤ) ℕ}
    (f : ∀ i, K i ⟶ L i) (n : ℕ)
    (h : ∀ i, Function.Surjective (HomologicalComplex.homologyMap (f i) n).hom) :
    Function.Surjective (HomologicalComplex.homologyMap (Limits.Sigma.map f) n).hom := by
  rw [← ModuleCat.epi_iff_surjective]
  haveI hK : IsIso (Limits.Sigma.desc
      (fun i => HomologicalComplex.homologyMap (Limits.Sigma.ι K i) n)) :=
    Work.Serre.sigma_desc_sigmaι_isIso K n
  haveI hL : IsIso (Limits.Sigma.desc
      (fun i => HomologicalComplex.homologyMap (Limits.Sigma.ι L i) n)) :=
    Work.Serre.sigma_desc_sigmaι_isIso L n
  haveI hf : ∀ i, Epi (HomologicalComplex.homologyMap (f i) n) :=
    fun i => (ModuleCat.epi_iff_surjective _).mpr (h i)
  haveI hS : Epi (Limits.Sigma.map (fun i => HomologicalComplex.homologyMap (f i) n)) :=
    Limits.Sigma.map_epi _
  have hsq := Work.Serre.CellStep.sigma_desc_homologyMap_natural f n
  have hX : HomologicalComplex.homologyMap (Limits.Sigma.map f) n
      = (asIso (Limits.Sigma.desc
            (fun i => HomologicalComplex.homologyMap (Limits.Sigma.ι K i) n))).inv
        ≫ (Limits.Sigma.map (fun i => HomologicalComplex.homologyMap (f i) n)
            ≫ Limits.Sigma.desc
                (fun i => HomologicalComplex.homologyMap (Limits.Sigma.ι L i) n)) := by
    rw [← hsq]
    exact (Iso.inv_hom_id_assoc (asIso (Limits.Sigma.desc
      (fun i => HomologicalComplex.homologyMap (Limits.Sigma.ι K i) n))) _).symm
  rw [hX]
  infer_instance

/-! ## Additivity of surjectivity over a disjoint union of pairs -/

/-- **Additivity of surjectivity over a disjoint union of pairs.**  The mirror of
`Work.Serre.CellStep.sigmaAdditivity`. -/
theorem sigmaPairMap_surjective {ι : Type} {X Y : ι → Type} [∀ i, TopologicalSpace (X i)]
    [∀ i, TopologicalSpace (Y i)] (A : ∀ i, Set (X i)) (B : ∀ i, Set (Y i))
    (g : ∀ i, C(X i, Y i)) (hg : ∀ i, Set.MapsTo (g i) (A i) (B i)) (m : ℕ)
    (h : ∀ i, Function.Surjective (HomologicalComplex.homologyMap
      (Work.Serre.pairMap (A i) (B i) (g i) (hg i)) m).hom) :
    Function.Surjective (HomologicalComplex.homologyMap
      (Work.Serre.sigmaPairMap X Y A B g hg) m).hom := by
  obtain ⟨eX, eY, hsq⟩ := Work.Serre.CellStep.relChainsCoproductSquare A B g hg
  let pm : ∀ i, Work.Cohomology.relChains (TopCat.of (X i)) (A i) ⟶
      Work.Cohomology.relChains (TopCat.of (Y i)) (B i) :=
    fun i => Work.Serre.pairMap (A i) (B i) (g i) (hg i)
  have hs : Function.Surjective (HomologicalComplex.homologyMap
      (Limits.Sigma.map pm) m).hom :=
    surjective_homologyMap_sigma pm m h
  haveI heX : IsIso (HomologicalComplex.homologyMap eX.hom m) :=
    Iso.isIso_hom (HomologicalComplex.homologyMapIso eX m)
  haveI heY : IsIso (HomologicalComplex.homologyMap eY.hom m) :=
    Iso.isIso_hom (HomologicalComplex.homologyMapIso eY m)
  have hsq' : HomologicalComplex.homologyMap eX.hom m
        ≫ HomologicalComplex.homologyMap (Limits.Sigma.map pm) m
      = HomologicalComplex.homologyMap (Work.Serre.sigmaPairMap X Y A B g hg) m
        ≫ HomologicalComplex.homologyMap eY.hom m := by
    calc HomologicalComplex.homologyMap eX.hom m
          ≫ HomologicalComplex.homologyMap (Limits.Sigma.map pm) m
        = HomologicalComplex.homologyMap (eX.hom ≫ Limits.Sigma.map pm) m :=
          (HomologicalComplex.homologyMap_comp eX.hom (Limits.Sigma.map pm) m).symm
      _ = HomologicalComplex.homologyMap
            (Work.Serre.sigmaPairMap X Y A B g hg ≫ eY.hom) m := by rw [hsq]
      _ = HomologicalComplex.homologyMap (Work.Serre.sigmaPairMap X Y A B g hg) m
          ≫ HomologicalComplex.homologyMap eY.hom m :=
          HomologicalComplex.homologyMap_comp (Work.Serre.sigmaPairMap X Y A B g hg) eY.hom m
  exact (Work.Serre.SPC.surjective_iff_of_comm_square
    (HomologicalComplex.homologyMap (Limits.Sigma.map pm) m)
    (HomologicalComplex.homologyMap (Work.Serre.sigmaPairMap X Y A B g hg) m)
    (HomologicalComplex.homologyMap eX.hom m) (HomologicalComplex.homologyMap eY.hom m)
    hsq').mp hs

/-! ## The strengthened cell step -/

/-- **The strengthened cell step.**  `Work.Serre.SPC.CellStepHyp`: the pair comparison
`(X, q⁻¹Γ) → (Γ', Γ)` of a Serre fibration over an attachment of `D`-cells (`D ≥ 2`) with
homologically `φ`-connected fibres is an isomorphism on integral homology in degrees `< D + φ`
and surjective in degree `D + φ`.

The isomorphism part is `Work.Serre.cellStep` verbatim.  For the surjectivity in the boundary
degree, the same assembly is replayed with `Function.Surjective` in place of `IsIso`: the
compression, excision and piece-decomposition squares have horizontal maps which are homology
isomorphisms in *every* degree, so they transfer surjectivity
(`Work.Serre.SPC.surjective_homologyMap_iff_of_square`), and the coproduct of the per-piece maps is
surjective by `Work.Serre.SPC.sigmaPairMap_surjective` together with the per-piece surjectivity
`Work.Serre.SPC.cellPieceSurj` of the cell step. -/
theorem cellStepStrong : Work.Serre.SPC.CellStepHyp := by
  intro D hD Γ _ ι f X _ q hq φ hfib h0
  constructor
  · intro i hi
    exact Work.Serre.cellStep D hD Γ ι f X q hq φ hfib h0 i hi
  · -- the horizontal maps of the three squares, homology isomorphisms in every degree
    have hA : CategoryTheory.IsIso (HomologicalComplex.homologyMap
        (asmAX (D := D) (Γ := Γ) (ι := ι) (X := X) (f := f) (q := q)) (D + φ)) := by
      unfold asmAX
      exact Work.Serre.CellStep.isIso_relCokerMap_of_acyclic (TopCat.of X)
        (Set.preimage_mono (asmOld_subset_cellU f))
        (fun k => Work.Serre.isZero_relChains_preimage_of_compress q hq
          (asmOld_subset_cellU f)
          (fun d => Work.Serre.CellStep.compressRel_cellU (D - 2) Γ ι f (by norm_num)
            (by norm_num) d) k) (D + φ)
    have hB : CategoryTheory.IsIso (HomologicalComplex.homologyMap
        (asmAB (D := D) (Γ := Γ) (ι := ι) (f := f)) (D + φ)) := by
      unfold asmAB
      exact Work.Serre.CellStep.isIso_relCokerMap_of_acyclic
        (TopCat.of (attachCells (D - 2) Γ ι f)) (asmOld_subset_cellU f)
        (fun k => Work.Serre.isZero_relChains_of_compress
          (fun d => Work.Serre.CellStep.compressRel_cellU (D - 2) Γ ι f (by norm_num)
            (by norm_num) d) k) (D + φ)
    have hEX : CategoryTheory.IsIso (HomologicalComplex.homologyMap
        (asmEX (D := D) (Γ := Γ) (ι := ι) (X := X) (f := f) (q := q)) (D + φ)) := by
      unfold asmEX
      refine Work.Cohomology.excision_relChainsMap_isIso (TopCat.of X) (q ⁻¹' cellV f 1)
        (q ⁻¹' cellU f (3/4)) ((isOpen_cellV f le_rfl).preimage q.continuous)
        ((isOpen_cellU f (by norm_num)).preimage q.continuous) ?_ (D + φ)
      rw [← Set.preimage_union, (Set.union_comm (cellV f 1) (cellU f (3/4))).trans
        (cellU_union_cellV f (by norm_num)), Set.preimage_univ]
    have hEB : CategoryTheory.IsIso (HomologicalComplex.homologyMap
        (asmEB (D := D) (Γ := Γ) (ι := ι) (f := f)) (D + φ)) := by
      unfold asmEB
      refine Work.Cohomology.excision_relChainsMap_isIso
        (TopCat.of (attachCells (D - 2) Γ ι f)) (cellV f 1) (cellU f (3/4))
        (isOpen_cellV f le_rfl) (isOpen_cellU f (by norm_num)) ?_ (D + φ)
      exact (Set.union_comm (cellV f 1) (cellU f (3/4))).trans (cellU_union_cellV f (by norm_num))
    have hPhiB : CategoryTheory.IsIso (HomologicalComplex.homologyMap
        (asmPhiB (D := D) (Γ := Γ) (ι := ι) (f := f)) (D + φ)) := by
      haveI : CategoryTheory.IsIso (asmPhiB (D := D) (Γ := Γ) (ι := ι) (f := f)) := by
        unfold asmPhiB
        exact Work.StemsB.isIso_relChainsMapOf_homeomorph
          (X := TopCat.of ↥(cellV f 1))
          (Y := TopCat.of (Σ α, ↥(Work.Serre.pieceSet (D - 2) Γ ι f α))) (asmSigB f)
          (asmUV f) (asmPieceRelB f) (asmUV_rel f)
      exact Functor.map_isIso
        (HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) (D + φ)) _
    have hPhiX : CategoryTheory.IsIso (HomologicalComplex.homologyMap
        (asmPhiX (D := D) (Γ := Γ) (ι := ι) (X := X) (f := f) (q := q)) (D + φ)) := by
      haveI : CategoryTheory.IsIso (asmPhiX (D := D) (Γ := Γ) (ι := ι) (X := X) (f := f)
          (q := q)) := by
        unfold asmPhiX
        exact Work.StemsB.isIso_relChainsMapOf_homeomorph
          (X := TopCat.of ↥(q ⁻¹' cellV f 1))
          (Y := TopCat.of (Σ α, ↥(q ⁻¹' Work.Serre.pieceSet (D - 2) Γ ι f α))) (asmSigX f q)
          (asmUVx f q) (asmPieceRelX f q) (asmUVx_rel f q)
      exact Functor.map_isIso
        (HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) (D + φ)) _
    -- the coproduct of the per-piece maps is surjective in the boundary degree
    have hP' : Function.Surjective (HomologicalComplex.homologyMap
        (asmP (D := D) (Γ := Γ) (ι := ι) (X := X) (f := f) (q := q))
        ((D - 2) + 2 + φ)).hom := by
      unfold asmP
      refine Work.Serre.SPC.sigmaPairMap_surjective
        (fun α => Work.Serre.CellStep.cpSrcRel f α q)
        (fun α => Work.Serre.CellStep.cpTarRel f α)
        (fun α => asmPieceFun f q α) (fun α => asmPieceFun_mem f q α) ((D - 2) + 2 + φ) ?_
      intro α
      rw [asmPairMap_eq f q α]
      exact (Work.Serre.SPC.cellPieceStrong (D - 2) Γ ι f α q hq φ hfib h0).2
    have hP : Function.Surjective (HomologicalComplex.homologyMap
        (asmP (D := D) (Γ := Γ) (ι := ι) (X := X) (f := f) (q := q)) (D + φ)).hom := by
      rwa [show (D - 2) + 2 + φ = D + φ from by omega] at hP'
    -- the three squares
    have h1 : Function.Surjective (HomologicalComplex.homologyMap
          (asmCs (D := D) (Γ := Γ) (ι := ι) (X := X) (f := f) (q := q)) (D + φ)).hom
        ↔ Function.Surjective (HomologicalComplex.homologyMap
          (asmUmap (D := D) (Γ := Γ) (ι := ι) (X := X) (f := f) (q := q)) (D + φ)).hom :=
      Work.Serre.SPC.surjective_homologyMap_iff_of_square
        (asmAX (D := D) (Γ := Γ) (ι := ι) (X := X) (f := f) (q := q))
        (asmAB (D := D) (Γ := Γ) (ι := ι) (f := f))
        (asmCs (D := D) (Γ := Γ) (ι := ι) (X := X) (f := f) (q := q))
        (asmUmap (D := D) (Γ := Γ) (ι := ι) (X := X) (f := f) (q := q))
        (asmSq1 (D := D) (Γ := Γ) (ι := ι) (X := X) (f := f) (q := q)) (D + φ) hA hB
    have h2 : Function.Surjective (HomologicalComplex.homologyMap
          (asmW (D := D) (Γ := Γ) (ι := ι) (X := X) (f := f) (q := q)) (D + φ)).hom
        ↔ Function.Surjective (HomologicalComplex.homologyMap
          (asmUmap (D := D) (Γ := Γ) (ι := ι) (X := X) (f := f) (q := q)) (D + φ)).hom :=
      Work.Serre.SPC.surjective_homologyMap_iff_of_square
        (asmEX (D := D) (Γ := Γ) (ι := ι) (X := X) (f := f) (q := q))
        (asmEB (D := D) (Γ := Γ) (ι := ι) (f := f))
        (asmW (D := D) (Γ := Γ) (ι := ι) (X := X) (f := f) (q := q))
        (asmUmap (D := D) (Γ := Γ) (ι := ι) (X := X) (f := f) (q := q))
        (asmSq2 (D := D) (Γ := Γ) (ι := ι) (X := X) (f := f) (q := q)) (D + φ) hEX hEB
    have h3 : Function.Surjective (HomologicalComplex.homologyMap
          (asmW (D := D) (Γ := Γ) (ι := ι) (X := X) (f := f) (q := q)) (D + φ)).hom
        ↔ Function.Surjective (HomologicalComplex.homologyMap
          (asmP (D := D) (Γ := Γ) (ι := ι) (X := X) (f := f) (q := q)) (D + φ)).hom :=
      Work.Serre.SPC.surjective_homologyMap_iff_of_square
        (asmPhiX (D := D) (Γ := Γ) (ι := ι) (X := X) (f := f) (q := q))
        (asmPhiB (D := D) (Γ := Γ) (ι := ι) (f := f))
        (asmW (D := D) (Γ := Γ) (ι := ι) (X := X) (f := f) (q := q))
        (asmP (D := D) (Γ := Γ) (ι := ι) (X := X) (f := f) (q := q))
        (asmSq3 (D := D) (Γ := Γ) (ι := ι) (X := X) (f := f) (q := q)) (D + φ) hPhiX hPhiB
    show Function.Surjective (HomologicalComplex.homologyMap
      (asmCs (D := D) (Γ := Γ) (ι := ι) (X := X) (f := f) (q := q)) (D + φ)).hom
    exact h1.mpr (h2.mp (h3.mpr hP))
