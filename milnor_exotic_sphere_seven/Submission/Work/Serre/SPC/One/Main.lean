import Mathlib
import Submission.Work.Serre.SPC.One.Assembly
import Submission.Work.Serre.SPC.One.pieceChainMap_strong

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The integral `1`-cell step

The `1`-cell step `Work.Serre.SPC.CellStepHypOne` is assembled here from the four commuting squares
of `Submission.Work.Serre.SPC.One.Assembly`:

`C_*(X, q⁻¹Y') → C_*(X, q⁻¹(Z∖P)) → C_*(q⁻¹V, q⁻¹(V∖P)) ⟶ C_*(V, V∖P) ← ⊕ᵢ C_*(Pᵢ, Pᵢ∖{cᵢ})`.

The first two arrows are quasi-isomorphisms (the compression of the complement of the centres onto
the old part, and excision for the open cover `(V, Z∖P)` of `Z`), the third is the map of pairs
induced by `q` over the union of the open cells, and the last is the coproduct decomposition.  Since
the maps `coprodTotal`, `coprodBase` are isomorphisms, the per-piece comparison
`pieceChainMap_strong` transfers to the comparison `oneCellStepMap`.
-/

set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

open scoped Topology unitInterval
open CategoryTheory CategoryTheory.Limits

namespace Work.Serre.SPC.One

noncomputable section

variable {Y : Type} [TopologicalSpace Y] {ι : Type} {f : ι → C(cellS0, Y)}
variable {X : Type} [TopologicalSpace X]

/-! ## Generalities -/

/-- **Transfer along a commuting square of chain complexes**, on homology. -/
theorem homologyMap_square {P Q R S : ChainComplex (ModuleCat ℤ) ℕ} {h : P ⟶ Q} {g : R ⟶ S}
    {u : R ⟶ P} {v : S ⟶ Q} (hsq : u ≫ h = g ≫ v) (m : ℕ) :
    HomologicalComplex.homologyMap u m ≫ HomologicalComplex.homologyMap h m
      = HomologicalComplex.homologyMap g m ≫ HomologicalComplex.homologyMap v m := by
  rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp, hsq]

/-- A homeomorphism of topological spaces induces an isomorphism of singular chain complexes. -/
theorem isIso_chainMap_homeo {A B : Type} [TopologicalSpace A] [TopologicalSpace B]
    (e : A ≃ₜ B) :
    IsIso (Work.Cohomology.chainMap ℤ (TopCat.of A) (TopCat.of B)
      (TopCat.ofHom ⟨e.toFun, e.continuous_toFun⟩)) :=
  Work.StemsB.isIso_chainMap_sphHomeoHom (X := TopCat.of A) (Y := TopCat.of B) e

/-! ## The cover by the open cells and the complement of the centres -/

/-- The open cells together with the complement of the centres cover the attached space. -/
theorem cellInnerUnionOne_union_cellCompl (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(cellS0, Y)) :
    cellInnerUnionOne Y ι f ∪ cellCompl Y ι f = Set.univ := by
  rw [Set.eq_univ_iff_forall]
  intro z
  by_cases h : z ∈ cellInnerUnionOne Y ι f
  · exact Or.inl h
  · exact Or.inr (oldPart_subset_cellCompl Y ι f (by rw [oneCellOldPart_eq_compl]; exact h))

theorem isOpen_cellInnerUnionOne (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(cellS0, Y)) : IsOpen (cellInnerUnionOne Y ι f) :=
  isOpen_cellUnionOne (Y := Y) (ι := ι) f (U := cellInnerOne) (fun _ hx => hx) isOpen_cellInnerOne

theorem isOpen_cellCompl (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(cellS0, Y)) : IsOpen (cellCompl Y ι f) :=
  (isClosed_oneCellCentresOne Y ι f).isOpen_compl

/-! ## The coproduct decompositions are quasi-isomorphisms -/

/-- The coproduct decomposition of the total space is a quasi-isomorphism in every degree. -/
theorem isIso_homologyMap_coprodTotal (q : C(X, attachOneCells Y ι f)) (m : ℕ) :
    IsIso (HomologicalComplex.homologyMap (coprodTotal q) m) := by
  haveI hf : IsIso (Work.Cohomology.chainMap ℤ (TopCat.of ↥(q ⁻¹' cellInnerUnionOne Y ι f))
      (TopCat.of (Σ i, pieceX Y ι f q i)) (TopCat.ofHom (piX q))) :=
    isIso_chainMap_homeo (piX q)
  haveI hg : IsIso (Work.Cohomology.chainMap ℤ
      (TopCat.of ↥{z : ↥(q ⁻¹' cellInnerUnionOne Y ι f) | (z : X) ∈ q ⁻¹' cellCompl Y ι f})
      (TopCat.of ↥{x : Σ i, pieceX Y ι f q i | x.2 ∈ pieceXrel Y ι f q x.1})
      (TopCat.ofHom (piXrel q))) :=
    isIso_chainMap_homeo (piXrel q)
  have hf' : ∀ k, IsIso (HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ
      (TopCat.of ↥(q ⁻¹' cellInnerUnionOne Y ι f)) (TopCat.of (Σ i, pieceX Y ι f q i))
      (TopCat.ofHom (piX q))) k) := by
    intro k
    haveI := hf
    infer_instance
  have hg' : ∀ k, IsIso (HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ
      (TopCat.of ↥{z : ↥(q ⁻¹' cellInnerUnionOne Y ι f) | (z : X) ∈ q ⁻¹' cellCompl Y ι f})
      (TopCat.of ↥{x : Σ i, pieceX Y ι f q i | x.2 ∈ pieceXrel Y ι f q x.1})
      (TopCat.ofHom (piXrel q))) k) := by
    intro k
    haveI := hg
    infer_instance
  simp only [coprodTotal]
  exact Work.Cohomology.relChainsMapOf_homologyMap_isIso _ _ _ _ _ m hf' hg'

/-- The coproduct decomposition of the base is a quasi-isomorphism in every degree. -/
theorem isIso_homologyMap_coprodBase (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(cellS0, Y)) (m : ℕ) :
    IsIso (HomologicalComplex.homologyMap (coprodBase Y ι f) m) := by
  haveI hf : IsIso (Work.Cohomology.chainMap ℤ (TopCat.of ↥(cellInnerUnionOne Y ι f))
      (TopCat.of (Σ i, pieceY Y ι f i)) (TopCat.ofHom (piZ Y ι f))) :=
    isIso_chainMap_homeo (piZ Y ι f)
  haveI hg : IsIso (Work.Cohomology.chainMap ℤ
      (TopCat.of ↥{y : ↥(cellInnerUnionOne Y ι f) | (y : attachOneCells Y ι f) ∈ cellCompl Y ι f})
      (TopCat.of ↥{x : Σ i, pieceY Y ι f i | x.2 ∈ pieceYrel Y ι f x.1})
      (TopCat.ofHom (piZrel Y ι f))) :=
    isIso_chainMap_homeo (piZrel Y ι f)
  have hf' : ∀ k, IsIso (HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ
      (TopCat.of ↥(cellInnerUnionOne Y ι f)) (TopCat.of (Σ i, pieceY Y ι f i))
      (TopCat.ofHom (piZ Y ι f))) k) := by
    intro k
    haveI := hf
    infer_instance
  have hg' : ∀ k, IsIso (HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ
      (TopCat.of ↥{y : ↥(cellInnerUnionOne Y ι f) |
        (y : attachOneCells Y ι f) ∈ cellCompl Y ι f})
      (TopCat.of ↥{x : Σ i, pieceY Y ι f i | x.2 ∈ pieceYrel Y ι f x.1})
      (TopCat.ofHom (piZrel Y ι f))) k) := by
    intro k
    haveI := hg
    infer_instance
  simp only [coprodBase]
  exact Work.Cohomology.relChainsMapOf_homologyMap_isIso _ _ _ _ _ m hf' hg'

/-! ## Excision -/

theorem isIso_homologyMap_excisionX (q : C(X, attachOneCells Y ι f)) (m : ℕ) :
    IsIso (HomologicalComplex.homologyMap (Work.Cohomology.relChainsMap (TopCat.of X)
      (q ⁻¹' cellInnerUnionOne Y ι f) (q ⁻¹' cellCompl Y ι f)) m) :=
  Work.Cohomology.excision_relChainsMap_isIso (TopCat.of X) (q ⁻¹' cellInnerUnionOne Y ι f)
    (q ⁻¹' cellCompl Y ι f) ((isOpen_cellInnerUnionOne Y ι f).preimage q.continuous)
    ((isOpen_cellCompl Y ι f).preimage q.continuous)
    (by rw [← Set.preimage_union, cellInnerUnionOne_union_cellCompl Y ι f, Set.preimage_univ]) m

theorem isIso_homologyMap_excisionZ (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(cellS0, Y)) (m : ℕ) :
    IsIso (HomologicalComplex.homologyMap (Work.Cohomology.relChainsMap
      (TopCat.of (attachOneCells Y ι f)) (cellInnerUnionOne Y ι f) (cellCompl Y ι f)) m) :=
  Work.Cohomology.excision_relChainsMap_isIso (TopCat.of (attachOneCells Y ι f))
    (cellInnerUnionOne Y ι f) (cellCompl Y ι f) (isOpen_cellInnerUnionOne Y ι f)
    (isOpen_cellCompl Y ι f) (cellInnerUnionOne_union_cellCompl Y ι f) m

/-! ## The compressions -/

/-- The compression of the complement of the centres onto the old part, on the base. -/
theorem isIso_homologyMap_relCokerMap_base (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(cellS0, Y)) (m : ℕ) :
    IsIso (HomologicalComplex.homologyMap (Work.Cohomology.relCokerMap
      (TopCat.of (attachOneCells Y ι f)) (oneCellOldPart Y ι f) (cellCompl Y ι f)
      (oldPart_subset_cellCompl Y ι f)) m) :=
  Work.Serre.CellStep.isIso_relCokerMap_of_acyclic (TopCat.of (attachOneCells Y ι f))
    (oldPart_subset_cellCompl Y ι f)
    (fun k => Work.Serre.isZero_relChains_of_compress (compressRel_cellCompl Y ι f) k) m

/-- The compression of the complement of the centres onto the old part, on the total space. -/
theorem isIso_homologyMap_relCokerMap_preimage (q : C(X, attachOneCells Y ι f))
    (hq : Work.StemsB.IsSerreFibration q) (m : ℕ) :
    IsIso (HomologicalComplex.homologyMap (Work.Cohomology.relCokerMap (TopCat.of X)
      (q ⁻¹' oneCellOldPart Y ι f) (q ⁻¹' cellCompl Y ι f)
      (Set.preimage_mono (oldPart_subset_cellCompl Y ι f))) m) :=
  Work.Serre.CellStep.isIso_relCokerMap_of_acyclic (TopCat.of X)
    (Set.preimage_mono (oldPart_subset_cellCompl Y ι f))
    (fun k => Work.Serre.isZero_relChains_preimage_of_compress q hq
      (oldPart_subset_cellCompl Y ι f) (compressRel_cellCompl Y ι f) k) m

/-! ## The coproduct of the per-piece comparisons -/

theorem isIso_homologyMap_sigmaPieceMap (q : C(X, attachOneCells Y ι f))
    (hq : Work.StemsB.IsSerreFibration q) (φ : ℕ)
    (hfib : ∀ y : attachOneCells Y ι f, ∀ j : ℕ, 0 < j → j < φ →
      IsZero ((Work.Cohomology.singularChains ℤ (TopCat.of (Work.StemsB.fibre q y))).homology j))
    (h0 : ∀ y : attachOneCells Y ι f,
      IsIso (TopCat.singularHomology₀ε (TopCat.of (Work.StemsB.fibre q y)) (ModuleCat.of ℤ ℤ)))
    (m : ℕ) (hm : m < 1 + φ) :
    IsIso (HomologicalComplex.homologyMap (sigmaPieceMap Y ι f q) m) :=
  (sigmaPairMapAdditivity (fun i => pieceXrel Y ι f q i) (fun i => pieceYrel Y ι f i)
    (fun i => pieceMap Y ι f q i) (fun i => pieceMap_mapsTo Y ι f q i)).1 m
    (fun i => (pieceChainMap_strong Y ι f X q hq φ hfib h0 i).1 m hm)

theorem surjective_homologyMap_sigmaPieceMap (q : C(X, attachOneCells Y ι f))
    (hq : Work.StemsB.IsSerreFibration q) (φ : ℕ)
    (hfib : ∀ y : attachOneCells Y ι f, ∀ j : ℕ, 0 < j → j < φ →
      IsZero ((Work.Cohomology.singularChains ℤ (TopCat.of (Work.StemsB.fibre q y))).homology j))
    (h0 : ∀ y : attachOneCells Y ι f,
      IsIso (TopCat.singularHomology₀ε (TopCat.of (Work.StemsB.fibre q y)) (ModuleCat.of ℤ ℤ))) :
    Function.Surjective (HomologicalComplex.homologyMap
      (sigmaPieceMap Y ι f q) (1 + φ)).hom :=
  (sigmaPairMapAdditivity (fun i => pieceXrel Y ι f q i) (fun i => pieceYrel Y ι f i)
    (fun i => pieceMap Y ι f q i) (fun i => pieceMap_mapsTo Y ι f q i)).2 (1 + φ)
    (fun i => (pieceChainMap_strong Y ι f X q hq φ hfib h0 i).2)

/-! ## The transfer of the comparison along the four squares -/

/-- The comparison over the union of the open cells is an isomorphism as soon as the coproduct of
the per-piece comparisons is. -/
theorem isIso_midMap_of_sigma (q : C(X, attachOneCells Y ι f)) (m : ℕ)
    (hσ : IsIso (HomologicalComplex.homologyMap (sigmaPieceMap Y ι f q) m)) :
    IsIso (HomologicalComplex.homologyMap (midMap q) m) := by
  haveI hct : IsIso (HomologicalComplex.homologyMap (coprodTotal q) m) :=
    isIso_homologyMap_coprodTotal q m
  haveI hcb : IsIso (HomologicalComplex.homologyMap (coprodBase Y ι f) m) :=
    isIso_homologyMap_coprodBase Y ι f m
  haveI hmv : IsIso (HomologicalComplex.homologyMap (midMapV q) m) :=
    (isIso_iff_of_comm_square (HomologicalComplex.homologyMap (sigmaPieceMap Y ι f q) m)
      (HomologicalComplex.homologyMap (midMapV q) m)
      (HomologicalComplex.homologyMap (coprodTotal q) m)
      (HomologicalComplex.homologyMap (coprodBase Y ι f) m)
      (homologyMap_square (square_coprod q) m)).mp hσ
  haveI hexX : IsIso (HomologicalComplex.homologyMap (Work.Cohomology.relChainsMap (TopCat.of X)
      (q ⁻¹' cellInnerUnionOne Y ι f) (q ⁻¹' cellCompl Y ι f)) m) :=
    isIso_homologyMap_excisionX q m
  haveI hexZ : IsIso (HomologicalComplex.homologyMap (Work.Cohomology.relChainsMap
      (TopCat.of (attachOneCells Y ι f)) (cellInnerUnionOne Y ι f) (cellCompl Y ι f)) m) :=
    isIso_homologyMap_excisionZ Y ι f m
  exact (isIso_iff_of_comm_square (HomologicalComplex.homologyMap (midMap q) m)
    (HomologicalComplex.homologyMap (midMapV q) m)
    (HomologicalComplex.homologyMap (Work.Cohomology.relChainsMap (TopCat.of X)
      (q ⁻¹' cellInnerUnionOne Y ι f) (q ⁻¹' cellCompl Y ι f)) m)
    (HomologicalComplex.homologyMap (Work.Cohomology.relChainsMap
      (TopCat.of (attachOneCells Y ι f)) (cellInnerUnionOne Y ι f) (cellCompl Y ι f)) m)
    (homologyMap_square (square_excision q) m)).mpr hmv

/-- The same, for surjectivity. -/
theorem surjective_midMap_of_sigma (q : C(X, attachOneCells Y ι f)) (m : ℕ)
    (hσ : Function.Surjective (HomologicalComplex.homologyMap
      (sigmaPieceMap Y ι f q) m).hom) :
    Function.Surjective (HomologicalComplex.homologyMap (midMap q) m).hom := by
  haveI hct : IsIso (HomologicalComplex.homologyMap (coprodTotal q) m) :=
    isIso_homologyMap_coprodTotal q m
  haveI hcb : IsIso (HomologicalComplex.homologyMap (coprodBase Y ι f) m) :=
    isIso_homologyMap_coprodBase Y ι f m
  haveI hmv : Function.Surjective (HomologicalComplex.homologyMap (midMapV q) m).hom :=
    (surjective_iff_of_comm_square (HomologicalComplex.homologyMap (sigmaPieceMap Y ι f q) m)
      (HomologicalComplex.homologyMap (midMapV q) m)
      (HomologicalComplex.homologyMap (coprodTotal q) m)
      (HomologicalComplex.homologyMap (coprodBase Y ι f) m)
      (homologyMap_square (square_coprod q) m)).mp hσ
  haveI hexX : IsIso (HomologicalComplex.homologyMap (Work.Cohomology.relChainsMap (TopCat.of X)
      (q ⁻¹' cellInnerUnionOne Y ι f) (q ⁻¹' cellCompl Y ι f)) m) :=
    isIso_homologyMap_excisionX q m
  haveI hexZ : IsIso (HomologicalComplex.homologyMap (Work.Cohomology.relChainsMap
      (TopCat.of (attachOneCells Y ι f)) (cellInnerUnionOne Y ι f) (cellCompl Y ι f)) m) :=
    isIso_homologyMap_excisionZ Y ι f m
  exact (surjective_iff_of_comm_square (HomologicalComplex.homologyMap (midMap q) m)
    (HomologicalComplex.homologyMap (midMapV q) m)
    (HomologicalComplex.homologyMap (Work.Cohomology.relChainsMap (TopCat.of X)
      (q ⁻¹' cellInnerUnionOne Y ι f) (q ⁻¹' cellCompl Y ι f)) m)
    (HomologicalComplex.homologyMap (Work.Cohomology.relChainsMap
      (TopCat.of (attachOneCells Y ι f)) (cellInnerUnionOne Y ι f) (cellCompl Y ι f)) m)
    (homologyMap_square (square_excision q) m)).mpr hmv

/-- **The `1`-cell comparison is an isomorphism in degree `m`** as soon as the coproduct of the
per-piece comparisons is. -/
theorem oneCellStepMap_iso_of_sigma (q : C(X, attachOneCells Y ι f))
    (hq : Work.StemsB.IsSerreFibration q) (m : ℕ)
    (hσ : IsIso (HomologicalComplex.homologyMap (sigmaPieceMap Y ι f q) m)) :
    IsIso (HomologicalComplex.homologyMap (oneCellStepMap ι f q) m) := by
  have hmid : IsIso (HomologicalComplex.homologyMap (midMap q) m) :=
    isIso_midMap_of_sigma q m hσ
  have hrX : IsIso (HomologicalComplex.homologyMap (Work.Cohomology.relCokerMap (TopCat.of X)
      (q ⁻¹' oneCellOldPart Y ι f) (q ⁻¹' cellCompl Y ι f)
      (Set.preimage_mono (oldPart_subset_cellCompl Y ι f))) m) :=
    isIso_homologyMap_relCokerMap_preimage q hq m
  have hrZ : IsIso (HomologicalComplex.homologyMap (Work.Cohomology.relCokerMap
      (TopCat.of (attachOneCells Y ι f)) (oneCellOldPart Y ι f) (cellCompl Y ι f)
      (oldPart_subset_cellCompl Y ι f)) m) :=
    isIso_homologyMap_relCokerMap_base Y ι f m
  exact (@isIso_iff_of_comm_square _ _ _ _
    (HomologicalComplex.homologyMap (midMap q) m)
    (HomologicalComplex.homologyMap (oneCellStepMap ι f q) m)
    (HomologicalComplex.homologyMap (Work.Cohomology.relCokerMap (TopCat.of X)
      (q ⁻¹' oneCellOldPart Y ι f) (q ⁻¹' cellCompl Y ι f)
      (Set.preimage_mono (oldPart_subset_cellCompl Y ι f))) m)
    (HomologicalComplex.homologyMap (Work.Cohomology.relCokerMap
      (TopCat.of (attachOneCells Y ι f)) (oneCellOldPart Y ι f) (cellCompl Y ι f)
      (oldPart_subset_cellCompl Y ι f)) m)
    (homologyMap_square (square_compress q) m).symm hrX hrZ).mp hmid

/-- **The `1`-cell comparison is surjective in degree `m`** as soon as the coproduct of the
per-piece comparisons is. -/
theorem oneCellStepMap_surjective_of_sigma (q : C(X, attachOneCells Y ι f))
    (hq : Work.StemsB.IsSerreFibration q) (m : ℕ)
    (hσ : Function.Surjective (HomologicalComplex.homologyMap
      (sigmaPieceMap Y ι f q) m).hom) :
    Function.Surjective (HomologicalComplex.homologyMap (oneCellStepMap ι f q) m).hom := by
  have hmid : Function.Surjective (HomologicalComplex.homologyMap (midMap q) m).hom :=
    surjective_midMap_of_sigma q m hσ
  have hrX : IsIso (HomologicalComplex.homologyMap (Work.Cohomology.relCokerMap (TopCat.of X)
      (q ⁻¹' oneCellOldPart Y ι f) (q ⁻¹' cellCompl Y ι f)
      (Set.preimage_mono (oldPart_subset_cellCompl Y ι f))) m) :=
    isIso_homologyMap_relCokerMap_preimage q hq m
  have hrZ : IsIso (HomologicalComplex.homologyMap (Work.Cohomology.relCokerMap
      (TopCat.of (attachOneCells Y ι f)) (oneCellOldPart Y ι f) (cellCompl Y ι f)
      (oldPart_subset_cellCompl Y ι f)) m) :=
    isIso_homologyMap_relCokerMap_base Y ι f m
  exact (@surjective_iff_of_comm_square _ _ _ _
    (HomologicalComplex.homologyMap (midMap q) m)
    (HomologicalComplex.homologyMap (oneCellStepMap ι f q) m)
    (HomologicalComplex.homologyMap (Work.Cohomology.relCokerMap (TopCat.of X)
      (q ⁻¹' oneCellOldPart Y ι f) (q ⁻¹' cellCompl Y ι f)
      (Set.preimage_mono (oldPart_subset_cellCompl Y ι f))) m)
    (HomologicalComplex.homologyMap (Work.Cohomology.relCokerMap
      (TopCat.of (attachOneCells Y ι f)) (oneCellOldPart Y ι f) (cellCompl Y ι f)
      (oldPart_subset_cellCompl Y ι f)) m)
    (homologyMap_square (square_compress q) m).symm hrX hrZ).mp hmid

/-! ## The `1`-cell step -/

/-- **The integral `1`-cell step.** -/
theorem cellStepHypOne_aux : Work.Serre.SPC.CellStepHypOne := by
  intro Y _instY ι f X _instX q hq φ hfib h0
  exact ⟨fun m hm => oneCellStepMap_iso_of_sigma q hq m
      (isIso_homologyMap_sigmaPieceMap q hq φ hfib h0 m hm),
    oneCellStepMap_surjective_of_sigma q hq (1 + φ)
      (surjective_homologyMap_sigmaPieceMap q hq φ hfib h0)⟩

end

end Work.Serre.SPC.One
