import Mathlib
import Submission.Work.Serre.cellStepDefs
import Submission.Work.Serre.CellStep.Geom
import Submission.Work.Serre.CellStep.Model
import Submission.Work.Serre.CellStep.Piece
import Submission.Work.Serre.CellStep.ModelReduction
import Submission.Work.Serre.CellStep.csModelIso
import Submission.Work.Serre.CellStep.cellPieceIso
import Submission.Work.Serre.CellStep.compressRel_cellU
import Submission.Work.Serre.CellStep.sigmaHomeo
import Submission.Work.Serre.CellStep.sigmaAdditivity
import Submission.Work.Cohomology.localHomology
import Submission.Work.RatHurewicz.ExcisionSetup

set_option synthInstance.maxHeartbeats 400000


set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open scoped Topology unitInterval
open CategoryTheory CategoryTheory.Limits

namespace Work.Serre

noncomputable section

open Work.RatHurewicz

variable {n : ℕ} {Γ : Type} [TopologicalSpace Γ] {ι : Type}

/-! ## The maps of the cell step -/

/-- The map `q` as a morphism of `TopCat`. -/
def aqMap (n : ℕ) (Γ : Type) [TopologicalSpace Γ] (ι : Type)
    (f : ι → C(cellSphere n, Γ)) {X : Type} [TopologicalSpace X]
    (q : C(X, attachCells n Γ ι f)) : TopCat.of X ⟶ TopCat.of (attachCells n Γ ι f) :=
  TopCat.ofHom q

/-- The restriction of `q` to the preimage of `S`, as a morphism of `TopCat`. -/
def aqPre (n : ℕ) (Γ : Type) [TopologicalSpace Γ] (ι : Type)
    (f : ι → C(cellSphere n, Γ)) {X : Type} [TopologicalSpace X]
    (q : C(X, attachCells n Γ ι f)) (S : Set (attachCells n Γ ι f)) :
    TopCat.of ↥(q ⁻¹' S) ⟶ TopCat.of ↥S :=
  TopCat.ofHom ⟨fun z => ⟨q z.1, z.2⟩,
    Continuous.subtype_mk (q.continuous.comp continuous_subtype_val) (fun z => z.2)⟩

/-- The map of relative chain complexes induced by `q` on the pairs over `(S,A)`, in the "global"
presentation (`X` relative to `q⁻¹A`, `Γ'` relative to `A`). -/
def aqRelMap (n : ℕ) (Γ : Type) [TopologicalSpace Γ] (ι : Type)
    (f : ι → C(cellSphere n, Γ)) {X : Type} [TopologicalSpace X]
    (q : C(X, attachCells n Γ ι f)) (A : Set (attachCells n Γ ι f)) :
    Work.Cohomology.relChains (TopCat.of X) (q ⁻¹' A) ⟶
      Work.Cohomology.relChains (TopCat.of (attachCells n Γ ι f)) A :=
  Work.StemsB.relChainsMapOf (aqMap n Γ ι f q) (q ⁻¹' A) A (fun x hx => hx)

/-- The map of relative chain complexes induced by `q` on the pairs over `(S,A)`, in the
"restricted" presentation (both sides as subspaces). -/
def aqRelMapSub (n : ℕ) (Γ : Type) [TopologicalSpace Γ] (ι : Type)
    (f : ι → C(cellSphere n, Γ)) {X : Type} [TopologicalSpace X]
    (q : C(X, attachCells n Γ ι f)) (S A : Set (attachCells n Γ ι f)) :
    Work.Cohomology.relChains (TopCat.of ↥(q ⁻¹' S))
        {z : ↥(q ⁻¹' S) | (z : X) ∈ q ⁻¹' A} ⟶
      Work.Cohomology.relChains (TopCat.of ↥S) {z : ↥S | (z : attachCells n Γ ι f) ∈ A} :=
  Work.StemsB.relChainsMapOf (aqPre n Γ ι f q S) _ _ (fun z hz => hz)

/-- **The square lemma.**  Two composites of maps of relative chain complexes agree as soon as the
composites of the underlying maps of spaces agree. -/
theorem aqSquare {X Y Z W : TopCat} (A : Set X) (B : Set Y) (C : Set Z) (D : Set W)
    {u : Work.Cohomology.relChains X A ⟶ Work.Cohomology.relChains Y B}
    {v : Work.Cohomology.relChains Y B ⟶ Work.Cohomology.relChains Z C}
    {u' : Work.Cohomology.relChains X A ⟶ Work.Cohomology.relChains W D}
    {v' : Work.Cohomology.relChains W D ⟶ Work.Cohomology.relChains Z C}
    {f : X ⟶ Y} {g : Y ⟶ Z} {f' : X ⟶ W} {g' : W ⟶ Z}
    (hu : cokernel.π (Work.Cohomology.inclChains X A) ≫ u
      = Work.Cohomology.chainMap ℤ X Y f ≫ cokernel.π (Work.Cohomology.inclChains Y B))
    (hv : cokernel.π (Work.Cohomology.inclChains Y B) ≫ v
      = Work.Cohomology.chainMap ℤ Y Z g ≫ cokernel.π (Work.Cohomology.inclChains Z C))
    (hu' : cokernel.π (Work.Cohomology.inclChains X A) ≫ u'
      = Work.Cohomology.chainMap ℤ X W f' ≫ cokernel.π (Work.Cohomology.inclChains W D))
    (hv' : cokernel.π (Work.Cohomology.inclChains W D) ≫ v'
      = Work.Cohomology.chainMap ℤ W Z g' ≫ cokernel.π (Work.Cohomology.inclChains Z C))
    (h : f ≫ g = f' ≫ g') : u ≫ v = u' ≫ v' := by
  apply (cancel_epi (cokernel.π (Work.Cohomology.inclChains X A))).1
  calc cokernel.π (Work.Cohomology.inclChains X A) ≫ (u ≫ v)
      = (cokernel.π (Work.Cohomology.inclChains X A) ≫ u) ≫ v := (Category.assoc _ _ _).symm
    _ = (Work.Cohomology.chainMap ℤ X Y f
          ≫ cokernel.π (Work.Cohomology.inclChains Y B)) ≫ v := by rw [hu]
    _ = Work.Cohomology.chainMap ℤ X Y f
          ≫ (cokernel.π (Work.Cohomology.inclChains Y B) ≫ v) := Category.assoc _ _ _
    _ = Work.Cohomology.chainMap ℤ X Y f
          ≫ (Work.Cohomology.chainMap ℤ Y Z g
              ≫ cokernel.π (Work.Cohomology.inclChains Z C)) := by rw [hv]
    _ = (Work.Cohomology.chainMap ℤ X Y f ≫ Work.Cohomology.chainMap ℤ Y Z g)
          ≫ cokernel.π (Work.Cohomology.inclChains Z C) := (Category.assoc _ _ _).symm
    _ = Work.Cohomology.chainMap ℤ X Z (f ≫ g)
          ≫ cokernel.π (Work.Cohomology.inclChains Z C) := by
          rw [Work.Cohomology.chainMap_compPD]
    _ = Work.Cohomology.chainMap ℤ X Z (f' ≫ g')
          ≫ cokernel.π (Work.Cohomology.inclChains Z C) := by rw [h]
    _ = (Work.Cohomology.chainMap ℤ X W f' ≫ Work.Cohomology.chainMap ℤ W Z g')
          ≫ cokernel.π (Work.Cohomology.inclChains Z C) := by
          rw [Work.Cohomology.chainMap_compPD]
    _ = Work.Cohomology.chainMap ℤ X W f'
          ≫ (Work.Cohomology.chainMap ℤ W Z g'
              ≫ cokernel.π (Work.Cohomology.inclChains Z C)) := Category.assoc _ _ _
    _ = Work.Cohomology.chainMap ℤ X W f'
          ≫ (cokernel.π (Work.Cohomology.inclChains W D) ≫ v') := by rw [hv']
    _ = (Work.Cohomology.chainMap ℤ X W f'
          ≫ cokernel.π (Work.Cohomology.inclChains W D)) ≫ v' := (Category.assoc _ _ _).symm
    _ = (cokernel.π (Work.Cohomology.inclChains X A) ≫ u') ≫ v' := by rw [hu']
    _ = cokernel.π (Work.Cohomology.inclChains X A) ≫ (u' ≫ v') := Category.assoc _ _ _

/-! ## The disjoint-union decomposition of a covered space -/

/-- **The index of a point in a disjoint cover**: for a family of pairwise disjoint subsets `P i`
of `S` covering `S`, every point of `S` lies in exactly one `P i`. -/
theorem aqIndex_unique {Z : Type} [TopologicalSpace Z] {ι : Type} (S : Set Z) (P : ι → Set Z)
    (hdisj : Pairwise fun i j => Disjoint (P i) (P j)) (hcover : (⋃ i, P i) = S) (z : ↥S) :
    ∃! i, (z : Z) ∈ P i := by
  have hz : (z : Z) ∈ ⋃ i, P i := by rw [hcover]; exact z.2
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hz
  refine ⟨i, hi, fun j hj => ?_⟩
  by_contra hne
  have hmem : (z : Z) ∈ P i ∩ P j := ⟨hi, hj⟩
  have hd : P i ∩ P j = ∅ :=
    Set.disjoint_iff_inter_eq_empty.mp (hdisj (Ne.symm hne))
  rw [hd] at hmem
  exact hmem

/-- The index of a point of `S` in the disjoint cover by the `P i`. -/
noncomputable def aqIdx {Z : Type} [TopologicalSpace Z] {ι : Type} (S : Set Z) (P : ι → Set Z)
    (hdisj : Pairwise fun i j => Disjoint (P i) (P j)) (hcover : (⋃ i, P i) = S)
    (z : ↥S) : ι :=
  Classical.choose (aqIndex_unique S P hdisj hcover z)

theorem aqIdx_spec {Z : Type} [TopologicalSpace Z] {ι : Type} (S : Set Z) (P : ι → Set Z)
    (hdisj : Pairwise fun i j => Disjoint (P i) (P j)) (hcover : (⋃ i, P i) = S) (z : ↥S) :
    (z : Z) ∈ P (aqIdx S P hdisj hcover z) :=
  (Classical.choose_spec (aqIndex_unique S P hdisj hcover z)).1

theorem aqIdx_eq {Z : Type} [TopologicalSpace Z] {ι : Type} (S : Set Z) (P : ι → Set Z)
    (hdisj : Pairwise fun i j => Disjoint (P i) (P j)) (hcover : (⋃ i, P i) = S) (z : ↥S)
    {i : ι} (hi : (z : Z) ∈ P i) : aqIdx S P hdisj hcover z = i :=
  ((Classical.choose_spec (aqIndex_unique S P hdisj hcover z)).2 i hi).symm

/-- **The index homeomorphism** of a disjoint open cover: `S` is the disjoint union of the pieces
`P i`.  The second component of the image of `z` is `z` itself. -/
noncomputable def aqSigmaIso {Z : Type} [TopologicalSpace Z] {ι : Type} (S : Set Z)
    (P : ι → Set Z) (hsub : ∀ i, P i ⊆ S) (hopen : ∀ i, IsOpen (P i))
    (hdisj : Pairwise fun i j => Disjoint (P i) (P j)) (hcover : (⋃ i, P i) = S) :
    ↥S ≃ₜ (Σ i, ↥(P i)) where
  toFun z := ⟨aqIdx S P hdisj hcover z, ⟨(z : Z), aqIdx_spec S P hdisj hcover z⟩⟩
  invFun x := ⟨(x.2 : Z), hsub x.1 x.2.2⟩
  left_inv z := Subtype.ext rfl
  right_inv x := by
    rcases x with ⟨i, y⟩
    have hidx : aqIdx S P hdisj hcover (⟨(y : Z), hsub i y.2⟩ : ↥S) = i :=
      aqIdx_eq S P hdisj hcover ⟨(y : Z), hsub i y.2⟩ y.2
    refine Sigma.ext hidx ?_
    exact (Subtype.heq_iff_coe_eq (fun w => by
      show w ∈ P (aqIdx S P hdisj hcover (⟨(y : Z), hsub i y.2⟩ : ↥S)) ↔ w ∈ P i
      rw [hidx])).mpr rfl
  continuous_toFun := by
    refine continuous_of_cover_nhds (s := fun i => {z : ↥S | (z : Z) ∈ P i}) (fun z => ?_)
      (fun i => ?_)
    · have hz : (z : Z) ∈ ⋃ i, P i := by rw [hcover]; exact z.2
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hz
      exact ⟨i, ((hopen i).preimage continuous_subtype_val).mem_nhds hi⟩
    · rw [continuousOn_iff_continuous_domRestrict]
      have h1 : Continuous fun z : ↥{z : ↥S | (z : Z) ∈ P i} =>
          (⟨(z : Z), z.2⟩ : ↥(P i)) :=
        Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val)
          (fun z => z.2)
      have h2 : Continuous (@Sigma.mk ι (fun j => ↥(P j)) i) := continuous_sigmaMk
      refine (h2.comp h1).congr (fun z => ?_)
      have hidx : aqIdx S P hdisj hcover (z : ↥S) = i :=
        aqIdx_eq S P hdisj hcover (z : ↥S) z.2
      refine Sigma.ext hidx.symm ?_
      exact (Subtype.heq_iff_coe_eq (fun w => by
        show w ∈ P i ↔ w ∈ P (aqIdx S P hdisj hcover (z : ↥S))
        rw [hidx])).mpr rfl
  continuous_invFun := by
    refine continuous_sigma (f := fun x : (Σ i, ↥(P i)) =>
      (⟨(x.2 : Z), hsub x.1 x.2.2⟩ : ↥S)) ?_
    intro i
    exact Continuous.subtype_mk (continuous_subtype_val (p := fun z : Z => z ∈ P i))
      (fun a => hsub i a.2)

theorem aqSigmaIso_index {Z : Type} [TopologicalSpace Z] {ι : Type} (S : Set Z) (P : ι → Set Z)
    (hsub : ∀ i, P i ⊆ S) (hopen : ∀ i, IsOpen (P i))
    (hdisj : Pairwise fun i j => Disjoint (P i) (P j)) (hcover : (⋃ i, P i) = S)
    (z : ↥S) (i : ι) : (aqSigmaIso S P hsub hopen hdisj hcover z).1 = i ↔ (z : Z) ∈ P i := by
  show aqIdx S P hdisj hcover z = i ↔ (z : Z) ∈ P i
  exact ⟨fun h => h ▸ aqIdx_spec S P hdisj hcover z,
    fun h => aqIdx_eq S P hdisj hcover z h⟩

theorem aqSigmaIso_val {Z : Type} [TopologicalSpace Z] {ι : Type} (S : Set Z) (P : ι → Set Z)
    (hsub : ∀ i, P i ⊆ S) (hopen : ∀ i, IsOpen (P i))
    (hdisj : Pairwise fun i j => Disjoint (P i) (P j)) (hcover : (⋃ i, P i) = S)
    (z : ↥S) : ((aqSigmaIso S P hsub hopen hdisj hcover z).2 : Z) = (z : Z) := rfl

/-- The homeomorphism of `Sigma` types induced by a family of homeomorphisms. -/
noncomputable def aqSigmaCongr {ι : Type} {A B : ι → Type} [∀ i, TopologicalSpace (A i)]
    [∀ i, TopologicalSpace (B i)] (e : ∀ i, A i ≃ₜ B i) :
    (Σ i, A i) ≃ₜ (Σ i, B i) where
  toFun x := ⟨x.1, e x.1 x.2⟩
  invFun x := ⟨x.1, (e x.1).symm x.2⟩
  left_inv x := by rcases x with ⟨i, a⟩; simp
  right_inv x := by rcases x with ⟨i, b⟩; simp
  continuous_toFun := by
    refine continuous_sigma fun i => ?_
    exact continuous_sigmaMk.comp (e i).continuous
  continuous_invFun := by
    refine continuous_sigma fun i => ?_
    exact continuous_sigmaMk.comp (e i).symm.continuous

theorem aqSigmaCongr_fst {ι : Type} {A B : ι → Type} [∀ i, TopologicalSpace (A i)]
    [∀ i, TopologicalSpace (B i)] (e : ∀ i, A i ≃ₜ B i) (x : Σ i, A i) :
    (aqSigmaCongr e x).1 = x.1 := rfl

theorem aqSigmaCongr_snd {ι : Type} {A B : ι → Type} [∀ i, TopologicalSpace (A i)]
    [∀ i, TopologicalSpace (B i)] (e : ∀ i, A i ≃ₜ B i) (x : Σ i, A i) :
    ((aqSigmaCongr e x).2 : B x.1) = e x.1 x.2 := rfl

/-! ## The pieces of the cell cover -/

section Pieces

variable {D : ℕ} {Γ : Type} [TopologicalSpace Γ] {ι : Type} {X : Type} [TopologicalSpace X]
variable {f : ι → C(cellSphere (D - 2), Γ)} {q : C(X, attachCells (D - 2) Γ ι f)}

theorem asmV_iUnion_piece (f : ι → C(cellSphere (D - 2), Γ)) :
    (⋃ α, Work.Serre.pieceSet (D - 2) Γ ι f α) = cellV f 1 := rfl

theorem pieceSet_subset_cellV (f : ι → C(cellSphere (D - 2), Γ)) (α : ι) :
    Work.Serre.pieceSet (D - 2) Γ ι f α ⊆ cellV f 1 := by
  rw [← asmV_iUnion_piece f]; exact Set.subset_iUnion _ α

theorem isOpen_pieceSet (f : ι → C(cellSphere (D - 2), Γ)) (α : ι) :
    IsOpen (Work.Serre.pieceSet (D - 2) Γ ι f α) :=
  Work.Serre.AttachCompress.isOpen_cellInterior f α

theorem disjoint_pieceSet (f : ι → C(cellSphere (D - 2), Γ)) :
    Pairwise fun i j => Disjoint (Work.Serre.pieceSet (D - 2) Γ ι f i)
      (Work.Serre.pieceSet (D - 2) Γ ι f j) :=
  fun i j hij => disjoint_cellInterior i j hij

theorem asmX_iUnion_piece (f : ι → C(cellSphere (D - 2), Γ))
    (q : C(X, attachCells (D - 2) Γ ι f)) :
    (⋃ α, q ⁻¹' Work.Serre.pieceSet (D - 2) Γ ι f α) = q ⁻¹' cellV f 1 := by
  rw [← asmV_iUnion_piece f, Set.preimage_iUnion]

/-- **The base-side piece homeomorphism**: the union of the open cells is the disjoint union of the
pieces. -/
noncomputable def asmSigB (f : ι → C(cellSphere (D - 2), Γ)) :
    ↥(cellV f 1) ≃ₜ (Σ α, ↥(Work.Serre.pieceSet (D - 2) Γ ι f α)) :=
  aqSigmaIso (cellV f 1) (fun α => Work.Serre.pieceSet (D - 2) Γ ι f α)
    (fun α => pieceSet_subset_cellV f α) (fun α => isOpen_pieceSet f α)
    (disjoint_pieceSet f) (asmV_iUnion_piece f)

/-- **The total-side piece homeomorphism**. -/
noncomputable def asmSigX (f : ι → C(cellSphere (D - 2), Γ))
    (q : C(X, attachCells (D - 2) Γ ι f)) :
    ↥(q ⁻¹' cellV f 1) ≃ₜ (Σ α, ↥(q ⁻¹' Work.Serre.pieceSet (D - 2) Γ ι f α)) :=
  aqSigmaIso (q ⁻¹' cellV f 1) (fun α => q ⁻¹' Work.Serre.pieceSet (D - 2) Γ ι f α)
    (fun α => Set.preimage_mono (pieceSet_subset_cellV f α))
    (fun α => (isOpen_pieceSet f α).preimage q.continuous)
    (fun i j hij => by
      show Disjoint (q ⁻¹' Work.Serre.pieceSet (D - 2) Γ ι f i)
        (q ⁻¹' Work.Serre.pieceSet (D - 2) Γ ι f j)
      rw [Set.disjoint_left]
      intro z hz1 hz2
      exact (Set.disjoint_left.mp (disjoint_pieceSet f hij)) hz1 hz2)
    (asmX_iUnion_piece f q)

theorem asmSigB_index (f : ι → C(cellSphere (D - 2), Γ)) (z : ↥(cellV f 1)) (α : ι) :
    (asmSigB f z).1 = α ↔ (z : attachCells (D - 2) Γ ι f) ∈
      Work.Serre.pieceSet (D - 2) Γ ι f α :=
  aqSigmaIso_index (cellV f 1) (fun α => Work.Serre.pieceSet (D - 2) Γ ι f α)
    (fun α => pieceSet_subset_cellV f α) (fun α => isOpen_pieceSet f α)
    (disjoint_pieceSet f) (asmV_iUnion_piece f) z α

theorem asmSigB_val (f : ι → C(cellSphere (D - 2), Γ)) (z : ↥(cellV f 1)) :
    ((asmSigB f z).2 : attachCells (D - 2) Γ ι f) = (z : attachCells (D - 2) Γ ι f) :=
  aqSigmaIso_val (cellV f 1) (fun α => Work.Serre.pieceSet (D - 2) Γ ι f α)
    (fun α => pieceSet_subset_cellV f α) (fun α => isOpen_pieceSet f α)
    (disjoint_pieceSet f) (asmV_iUnion_piece f) z

theorem asmSigX_index (f : ι → C(cellSphere (D - 2), Γ))
    (q : C(X, attachCells (D - 2) Γ ι f)) (z : ↥(q ⁻¹' cellV f 1)) (α : ι) :
    (asmSigX f q z).1 = α ↔ (z : X) ∈ q ⁻¹' Work.Serre.pieceSet (D - 2) Γ ι f α :=
  aqSigmaIso_index (q ⁻¹' cellV f 1) (fun α => q ⁻¹' Work.Serre.pieceSet (D - 2) Γ ι f α)
    (fun α => Set.preimage_mono (pieceSet_subset_cellV f α))
    (fun α => (isOpen_pieceSet f α).preimage q.continuous)
    (fun i j hij => by
      show Disjoint (q ⁻¹' Work.Serre.pieceSet (D - 2) Γ ι f i)
        (q ⁻¹' Work.Serre.pieceSet (D - 2) Γ ι f j)
      rw [Set.disjoint_left]
      intro z hz1 hz2
      exact (Set.disjoint_left.mp (disjoint_pieceSet f hij)) hz1 hz2)
    (asmX_iUnion_piece f q) z α

theorem asmSigX_val (f : ι → C(cellSphere (D - 2), Γ))
    (q : C(X, attachCells (D - 2) Γ ι f)) (z : ↥(q ⁻¹' cellV f 1)) :
    ((asmSigX f q z).2 : X) = (z : X) :=
  aqSigmaIso_val (q ⁻¹' cellV f 1) (fun α => q ⁻¹' Work.Serre.pieceSet (D - 2) Γ ι f α)
    (fun α => Set.preimage_mono (pieceSet_subset_cellV f α))
    (fun α => (isOpen_pieceSet f α).preimage q.continuous)
    (fun i j hij => by
      show Disjoint (q ⁻¹' Work.Serre.pieceSet (D - 2) Γ ι f i)
        (q ⁻¹' Work.Serre.pieceSet (D - 2) Γ ι f j)
      rw [Set.disjoint_left]
      intro z hz1 hz2
      exact (Set.disjoint_left.mp (disjoint_pieceSet f hij)) hz1 hz2)
    (asmX_iUnion_piece f q) z

/-- The relative part of the base side, at the `V` level. -/
abbrev asmUV (f : ι → C(cellSphere (D - 2), Γ)) : Set ↥(cellV f 1) :=
  {z : ↥(cellV f 1) | (z : attachCells (D - 2) Γ ι f) ∈ cellU f (3/4)}

/-- The relative part of the total side, at the `V` level. -/
abbrev asmUVx (f : ι → C(cellSphere (D - 2), Γ)) (q : C(X, attachCells (D - 2) Γ ι f)) :
    Set ↥(q ⁻¹' cellV f 1) :=
  {z : ↥(q ⁻¹' cellV f 1) | (z : X) ∈ q ⁻¹' cellU f (3/4)}

/-- The relative part of the base side, at the piece level. -/
abbrev asmPieceRelB (f : ι → C(cellSphere (D - 2), Γ)) :
    Set (Σ α, ↥(Work.Serre.pieceSet (D - 2) Γ ι f α)) :=
  {z | z.2 ∈ Work.Serre.CellStep.cpTarRel f z.1}

/-- The relative part of the total side, at the piece level. -/
abbrev asmPieceRelX (f : ι → C(cellSphere (D - 2), Γ))
    (q : C(X, attachCells (D - 2) Γ ι f)) :
    Set (Σ α, ↥(q ⁻¹' Work.Serre.pieceSet (D - 2) Γ ι f α)) :=
  {z | z.2 ∈ Work.Serre.CellStep.cpSrcRel f z.1 q}

end Pieces

/-! ## The chain maps of the cell step -/

section Assembly

variable {D : ℕ} {Γ : Type} [TopologicalSpace Γ] {ι : Type} {X : Type} [TopologicalSpace X]
variable {f : ι → C(cellSphere (D - 2), Γ)} {q : C(X, attachCells (D - 2) Γ ι f)}

/-- The relative part of a piece, as a shell: `U ∩ V` is the shell `cellShellImg f (3/4) 1`. -/
theorem asm_cellU_inter_cellV :
    cellU f (3/4) ∩ cellV f 1 = cellShellImg f (3/4) 1 :=
  cellU_inter_cellV f le_rfl (by norm_num)

theorem asmOld_subset_cellU (f : ι → C(cellSphere (D - 2), Γ)) :
    attachOld D Γ ι f ⊆ cellU f (3/4) := by
  intro x hx
  rw [Work.Serre.cellU, Set.mem_compl_iff]
  exact fun hb => (Set.disjoint_left.mp (disjoint_cellBallImg_range f (by norm_num))) hb hx

theorem asmUV_rel (f : ι → C(cellSphere (D - 2), Γ)) :
    ∀ z : ↥(cellV f 1), z ∈ asmUV f ↔ asmSigB f z ∈ asmPieceRelB f := by
  intro z
  show (z : attachCells (D - 2) Γ ι f) ∈ cellU f (3/4) ↔
    ((asmSigB f z).2 : attachCells (D - 2) Γ ι f) ∈ cellShellImg f (3/4) 1
  rw [asmSigB_val]
  have hshell := asm_cellU_inter_cellV (D := D) (Γ := Γ) (ι := ι) (f := f)
  constructor
  · intro hz
    have hmem : (z : attachCells (D - 2) Γ ι f) ∈ cellU f (3/4) ∩ cellV f 1 := ⟨hz, z.2⟩
    rw [hshell] at hmem
    exact hmem
  · intro hz
    have hmem : (z : attachCells (D - 2) Γ ι f) ∈ cellU f (3/4) ∩ cellV f 1 := by
      rw [hshell]; exact hz
    exact hmem.1

theorem asmUVx_rel (f : ι → C(cellSphere (D - 2), Γ))
    (q : C(X, attachCells (D - 2) Γ ι f)) :
    ∀ z : ↥(q ⁻¹' cellV f 1), z ∈ asmUVx f q ↔ asmSigX f q z ∈ asmPieceRelX f q := by
  intro z
  show (z : X) ∈ q ⁻¹' cellU f (3/4) ↔
    ((asmSigX f q z).2 : X) ∈ q ⁻¹' cellShellImg f (3/4) 1
  rw [asmSigX_val]
  have hshell := asm_cellU_inter_cellV (D := D) (Γ := Γ) (ι := ι) (f := f)
  constructor
  · intro hz
    have hmem : q (z : X) ∈ cellU f (3/4) ∩ cellV f 1 := ⟨hz, z.2⟩
    rw [hshell] at hmem
    exact hmem
  · intro hz
    have hmem : q (z : X) ∈ cellU f (3/4) ∩ cellV f 1 := by
      rw [hshell]; exact hz
    exact hmem.1

/-- The chain map of the base side induced by the piece decomposition. -/
noncomputable def asmPhiB {f : ι → C(cellSphere (D - 2), Γ)} :
    Work.Cohomology.relChains (TopCat.of ↥(cellV f 1)) (asmUV f) ⟶
      Work.Cohomology.relChains
        (TopCat.of (Σ α, ↥(Work.Serre.pieceSet (D - 2) Γ ι f α))) (asmPieceRelB f) :=
  Work.StemsB.relChainsMapOf
    (Work.StemsB.sphHomeoHom (X := TopCat.of ↥(cellV f 1))
      (Y := TopCat.of (Σ α, ↥(Work.Serre.pieceSet (D - 2) Γ ι f α))) (asmSigB f))
    (asmUV f) (asmPieceRelB f) (Work.StemsB.homeoPairMem (asmUV_rel f))

/-- The chain map of the total side induced by the piece decomposition. -/
noncomputable def asmPhiX {f : ι → C(cellSphere (D - 2), Γ)}
    {q : C(X, attachCells (D - 2) Γ ι f)} :
    Work.Cohomology.relChains (TopCat.of ↥(q ⁻¹' cellV f 1)) (asmUVx f q) ⟶
      Work.Cohomology.relChains
        (TopCat.of (Σ α, ↥(q ⁻¹' Work.Serre.pieceSet (D - 2) Γ ι f α)))
        (asmPieceRelX f q) :=
  Work.StemsB.relChainsMapOf
    (Work.StemsB.sphHomeoHom (X := TopCat.of ↥(q ⁻¹' cellV f 1))
      (Y := TopCat.of (Σ α, ↥(q ⁻¹' Work.Serre.pieceSet (D - 2) Γ ι f α))) (asmSigX f q))
    (asmUVx f q) (asmPieceRelX f q) (Work.StemsB.homeoPairMem (asmUVx_rel f q))

/-- The comparison map `(X, X|Γ) → (Γ', Γ)` of the cell step. -/
noncomputable def asmCs : Work.Cohomology.relChains (TopCat.of X) (q ⁻¹' attachOld D Γ ι f) ⟶
    Work.Cohomology.relChains (TopCat.of (attachCells (D - 2) Γ ι f)) (attachOld D Γ ι f) :=
  cellStepAttachMap D Γ ι f X q

/-- The compression map on the total side. -/
noncomputable def asmAX :
    Work.Cohomology.relChains (TopCat.of X) (q ⁻¹' attachOld D Γ ι f) ⟶
      Work.Cohomology.relChains (TopCat.of X) (q ⁻¹' cellU f (3/4)) :=
  Work.Cohomology.relCokerMap (TopCat.of X) _ _
    (Set.preimage_mono (asmOld_subset_cellU f))

/-- The compression map on the base side. -/
noncomputable def asmAB :
    Work.Cohomology.relChains (TopCat.of (attachCells (D - 2) Γ ι f)) (attachOld D Γ ι f) ⟶
      Work.Cohomology.relChains (TopCat.of (attachCells (D - 2) Γ ι f)) (cellU f (3/4)) :=
  Work.Cohomology.relCokerMap _ _ _ (asmOld_subset_cellU f)

/-- The map of pairs over `(X, X|_{q⁻¹U}) → (Γ', U)`. -/
noncomputable def asmUmap :
    Work.Cohomology.relChains (TopCat.of X) (q ⁻¹' cellU f (3/4)) ⟶
      Work.Cohomology.relChains (TopCat.of (attachCells (D - 2) Γ ι f)) (cellU f (3/4)) :=
  aqRelMap (D - 2) Γ ι f q (cellU f (3/4))

/-- Excision on the total side. -/
noncomputable def asmEX :
    Work.Cohomology.relChains (TopCat.of ↥(q ⁻¹' cellV f 1)) (asmUVx f q) ⟶
      Work.Cohomology.relChains (TopCat.of X) (q ⁻¹' cellU f (3/4)) :=
  Work.Cohomology.relChainsMap (TopCat.of X) (q ⁻¹' cellV f 1) (q ⁻¹' cellU f (3/4))

/-- Excision on the base side. -/
noncomputable def asmEB :
    Work.Cohomology.relChains (TopCat.of ↥(cellV f 1)) (asmUV f) ⟶
      Work.Cohomology.relChains (TopCat.of (attachCells (D - 2) Γ ι f)) (cellU f (3/4)) :=
  Work.Cohomology.relChainsMap (TopCat.of (attachCells (D - 2) Γ ι f)) (cellV f 1) (cellU f (3/4))

/-- The map of pairs induced by `q` on the excised pairs. -/
noncomputable def asmW :
    Work.Cohomology.relChains (TopCat.of ↥(q ⁻¹' cellV f 1)) (asmUVx f q) ⟶
      Work.Cohomology.relChains (TopCat.of ↥(cellV f 1)) (asmUV f) :=
  aqRelMapSub (D - 2) Γ ι f q (cellV f 1) (cellU f (3/4))

/-- The per-cell map `q⁻¹(piece) → piece`. -/
def asmPieceFun (f : ι → C(cellSphere (D - 2), Γ)) (q : C(X, attachCells (D - 2) Γ ι f))
    (α : ι) : C(↥(q ⁻¹' Work.Serre.pieceSet (D - 2) Γ ι f α),
      ↥(Work.Serre.pieceSet (D - 2) Γ ι f α)) :=
  ⟨fun z => ⟨q z.1, z.2⟩, Continuous.subtype_mk (q.continuous.comp continuous_subtype_val)
    (fun z => z.2)⟩

theorem asmPieceFun_mem (f : ι → C(cellSphere (D - 2), Γ))
    (q : C(X, attachCells (D - 2) Γ ι f)) (α : ι) :
    Set.MapsTo (asmPieceFun f q α) (Work.Serre.CellStep.cpSrcRel f α q)
      (Work.Serre.CellStep.cpTarRel f α) :=
  fun z hz => hz

/-- The coproduct of the per-cell maps. -/
noncomputable def asmP :
    Work.Cohomology.relChains
        (TopCat.of (Σ α, ↥(q ⁻¹' Work.Serre.pieceSet (D - 2) Γ ι f α)))
        (asmPieceRelX f q) ⟶
      Work.Cohomology.relChains
        (TopCat.of (Σ α, ↥(Work.Serre.pieceSet (D - 2) Γ ι f α))) (asmPieceRelB f) :=
  Work.Serre.sigmaPairMap _ _ (fun α => Work.Serre.CellStep.cpSrcRel f α q)
    (fun α => Work.Serre.CellStep.cpTarRel f α) (fun α => asmPieceFun f q α)
    (fun α => asmPieceFun_mem f q α)

/-- The total map underlying the coproduct of the per-cell maps. -/
def asmPtotal : TopCat.of (Σ α, ↥(q ⁻¹' Work.Serre.pieceSet (D - 2) Γ ι f α)) ⟶
    TopCat.of (Σ α, ↥(Work.Serre.pieceSet (D - 2) Γ ι f α)) :=
  TopCat.ofHom ⟨Sigma.map id (fun i => asmPieceFun f q i),
    continuous_sigma_map.2 fun i => (asmPieceFun f q i).continuous⟩

end Assembly

/-! ## The commuting squares of the cell step -/

section Squares

variable {D : ℕ} {Γ : Type} [TopologicalSpace Γ] {ι : Type} {X : Type} [TopologicalSpace X]
variable {f : ι → C(cellSphere (D - 2), Γ)} {q : C(X, attachCells (D - 2) Γ ι f)}

theorem asmCs_pi :
    cokernel.π (Work.Cohomology.inclChains (TopCat.of X) (q ⁻¹' attachOld D Γ ι f)) ≫ asmCs
      = Work.Cohomology.chainMap ℤ (TopCat.of X) (TopCat.of (attachCells (D - 2) Γ ι f))
          (TopCat.ofHom q)
        ≫ cokernel.π (Work.Cohomology.inclChains (TopCat.of (attachCells (D - 2) Γ ι f))
            (attachOld D Γ ι f)) := by
  unfold asmCs Work.Serre.cellStepAttachMap
  exact Work.Serre.CellStep.pi_comp_relChainsMapOfCo _ _ _ _ _

theorem asmAX_pi :
    cokernel.π (Work.Cohomology.inclChains (TopCat.of X) (q ⁻¹' attachOld D Γ ι f)) ≫ asmAX
      = Work.Cohomology.chainMap ℤ (TopCat.of X) (TopCat.of X) (𝟙 (TopCat.of X))
        ≫ cokernel.π (Work.Cohomology.inclChains (TopCat.of X) (q ⁻¹' cellU f (3/4))) := by
  unfold asmAX
  rw [Work.Cohomology.relCokerMap_comp_π, Work.Serre.CellStep.chainMap_id_self,
    Category.id_comp]

theorem asmAB_pi :
    cokernel.π (Work.Cohomology.inclChains (TopCat.of (attachCells (D - 2) Γ ι f))
        (attachOld D Γ ι f)) ≫ asmAB
      = Work.Cohomology.chainMap ℤ (TopCat.of (attachCells (D - 2) Γ ι f))
          (TopCat.of (attachCells (D - 2) Γ ι f)) (𝟙 (TopCat.of (attachCells (D - 2) Γ ι f)))
        ≫ cokernel.π (Work.Cohomology.inclChains (TopCat.of (attachCells (D - 2) Γ ι f))
            (cellU f (3/4))) := by
  unfold asmAB
  rw [Work.Cohomology.relCokerMap_comp_π, Work.Serre.CellStep.chainMap_id_self,
    Category.id_comp]

theorem asmUmap_pi :
    cokernel.π (Work.Cohomology.inclChains (TopCat.of X) (q ⁻¹' cellU f (3/4))) ≫ asmUmap
      = Work.Cohomology.chainMap ℤ (TopCat.of X) (TopCat.of (attachCells (D - 2) Γ ι f))
          (TopCat.ofHom q)
        ≫ cokernel.π (Work.Cohomology.inclChains (TopCat.of (attachCells (D - 2) Γ ι f))
            (cellU f (3/4))) := by
  unfold asmUmap aqRelMap
  exact Work.StemsB.π_comp_relChainsMapOf _ _ _ _

theorem asmEX_pi :
    cokernel.π (Work.Cohomology.inclChains (TopCat.of ↥(q ⁻¹' cellV f 1)) (asmUVx f q)) ≫ asmEX
      = Work.Cohomology.chainMap ℤ (TopCat.of ↥(q ⁻¹' cellV f 1)) (TopCat.of X)
          (Work.Cohomology.subtypeIncl (TopCat.of X) (q ⁻¹' cellV f 1))
        ≫ cokernel.π (Work.Cohomology.inclChains (TopCat.of X) (q ⁻¹' cellU f (3/4))) := by
  unfold asmEX Work.Cohomology.relChainsMap
  exact Work.Cohomology.cokernel_π_relChainsMap (TopCat.of X) (q ⁻¹' cellV f 1)
    (q ⁻¹' cellU f (3/4))

theorem asmEB_pi :
    cokernel.π (Work.Cohomology.inclChains (TopCat.of ↥(cellV f 1)) (asmUV f)) ≫ asmEB
      = Work.Cohomology.chainMap ℤ (TopCat.of ↥(cellV f 1))
          (TopCat.of (attachCells (D - 2) Γ ι f))
          (Work.Cohomology.subtypeIncl (TopCat.of (attachCells (D - 2) Γ ι f)) (cellV f 1))
        ≫ cokernel.π (Work.Cohomology.inclChains (TopCat.of (attachCells (D - 2) Γ ι f))
            (cellU f (3/4))) := by
  unfold asmEB Work.Cohomology.relChainsMap
  exact Work.Cohomology.cokernel_π_relChainsMap (TopCat.of (attachCells (D - 2) Γ ι f))
    (cellV f 1) (cellU f (3/4))

theorem asmW_pi :
    cokernel.π (Work.Cohomology.inclChains (TopCat.of ↥(q ⁻¹' cellV f 1)) (asmUVx f q)) ≫ asmW
      = Work.Cohomology.chainMap ℤ (TopCat.of ↥(q ⁻¹' cellV f 1)) (TopCat.of ↥(cellV f 1))
          (aqPre (D - 2) Γ ι f q (cellV f 1))
        ≫ cokernel.π (Work.Cohomology.inclChains (TopCat.of ↥(cellV f 1)) (asmUV f)) := by
  unfold asmW aqRelMapSub
  exact Work.StemsB.π_comp_relChainsMapOf _ _ _ _

theorem asmPhiB_pi :
    cokernel.π (Work.Cohomology.inclChains (TopCat.of ↥(cellV f 1)) (asmUV f)) ≫ asmPhiB
      = Work.Cohomology.chainMap ℤ (TopCat.of ↥(cellV f 1))
          (TopCat.of (Σ α, ↥(Work.Serre.pieceSet (D - 2) Γ ι f α)))
          (Work.StemsB.sphHomeoHom (X := TopCat.of ↥(cellV f 1))
            (Y := TopCat.of (Σ α, ↥(Work.Serre.pieceSet (D - 2) Γ ι f α))) (asmSigB f))
        ≫ cokernel.π (Work.Cohomology.inclChains
            (TopCat.of (Σ α, ↥(Work.Serre.pieceSet (D - 2) Γ ι f α))) (asmPieceRelB f)) := by
  unfold asmPhiB
  exact Work.StemsB.π_comp_relChainsMapOf _ _ _ _

theorem asmPhiX_pi :
    cokernel.π (Work.Cohomology.inclChains (TopCat.of ↥(q ⁻¹' cellV f 1)) (asmUVx f q))
        ≫ asmPhiX
      = Work.Cohomology.chainMap ℤ (TopCat.of ↥(q ⁻¹' cellV f 1))
          (TopCat.of (Σ α, ↥(q ⁻¹' Work.Serre.pieceSet (D - 2) Γ ι f α)))
          (Work.StemsB.sphHomeoHom (X := TopCat.of ↥(q ⁻¹' cellV f 1))
            (Y := TopCat.of (Σ α, ↥(q ⁻¹' Work.Serre.pieceSet (D - 2) Γ ι f α)))
            (asmSigX f q))
        ≫ cokernel.π (Work.Cohomology.inclChains
            (TopCat.of (Σ α, ↥(q ⁻¹' Work.Serre.pieceSet (D - 2) Γ ι f α)))
            (asmPieceRelX f q)) := by
  unfold asmPhiX
  exact Work.StemsB.π_comp_relChainsMapOf _ _ _ _

theorem asmP_pi :
    cokernel.π (Work.Cohomology.inclChains
        (TopCat.of (Σ α, ↥(q ⁻¹' Work.Serre.pieceSet (D - 2) Γ ι f α))) (asmPieceRelX f q))
        ≫ asmP
      = Work.Cohomology.chainMap ℤ
          (TopCat.of (Σ α, ↥(q ⁻¹' Work.Serre.pieceSet (D - 2) Γ ι f α)))
          (TopCat.of (Σ α, ↥(Work.Serre.pieceSet (D - 2) Γ ι f α))) asmPtotal
        ≫ cokernel.π (Work.Cohomology.inclChains
            (TopCat.of (Σ α, ↥(Work.Serre.pieceSet (D - 2) Γ ι f α))) (asmPieceRelB f)) := by
  unfold asmP Work.Serre.sigmaPairMap asmPtotal
  exact Work.Serre.CellStep.pi_comp_relChainsMapOfCo _ _ _ _ _

/-- **The first square**: compressing the relative part `Γ ⊆ U`. -/
theorem asmSq1 :
    (asmAX ≫ asmUmap : Work.Cohomology.relChains (TopCat.of X) (q ⁻¹' attachOld D Γ ι f)
      ⟶ Work.Cohomology.relChains (TopCat.of (attachCells (D - 2) Γ ι f)) (cellU f (3/4)))
      = asmCs ≫ asmAB := by
  refine aqSquare _ _ _ _ asmAX_pi asmUmap_pi asmCs_pi asmAB_pi ?_
  rw [Category.id_comp, Category.comp_id]

/-- **The second square**: excision. -/
theorem asmSq2 :
    (asmEX ≫ asmUmap : Work.Cohomology.relChains (TopCat.of ↥(q ⁻¹' cellV f 1)) (asmUVx f q)
      ⟶ Work.Cohomology.relChains (TopCat.of (attachCells (D - 2) Γ ι f)) (cellU f (3/4)))
      = asmW ≫ asmEB := by
  refine aqSquare _ _ _ _ asmEX_pi asmUmap_pi asmW_pi asmEB_pi ?_
  apply TopCat.ext
  intro x
  rfl

theorem asmPtotal_apply
    (y : Σ α, ↥(q ⁻¹' Work.Serre.pieceSet (D - 2) Γ ι f α)) :
    asmPtotal y = (⟨y.1, asmPieceFun f q y.1 y.2⟩ :
      Σ α, ↥(Work.Serre.pieceSet (D - 2) Γ ι f α)) := rfl

theorem aqPre_apply (z : ↥(q ⁻¹' cellV f 1)) :
    aqPre (D - 2) Γ ι f q (cellV f 1) z = (⟨q z.1, z.2⟩ : ↥(cellV f 1)) := rfl

/-- The two piece homeomorphisms intertwine the projection with the coproduct of the per-cell
maps. -/
theorem asmSq3_map :
    Work.StemsB.sphHomeoHom (asmSigX f q) ≫ asmPtotal
      = aqPre (D - 2) Γ ι f q (cellV f 1) ≫ Work.StemsB.sphHomeoHom (asmSigB f) := by
  apply TopCat.ext
  intro x
  show asmPtotal (Work.StemsB.sphHomeoHom (asmSigX f q) x)
    = Work.StemsB.sphHomeoHom (asmSigB f) (aqPre (D - 2) Γ ι f q (cellV f 1) x)
  rw [Work.StemsB.sphHomeoHom_apply, Work.StemsB.sphHomeoHom_apply, asmPtotal_apply,
    aqPre_apply]
  have hx : (x : X) ∈ q ⁻¹' Work.Serre.pieceSet (D - 2) Γ ι f (asmSigX f q x).1 :=
    (asmSigX_index f q x (asmSigX f q x).1).mp rfl
  have hidxB : (asmSigB f (⟨q x.1, x.2⟩ : ↥(cellV f 1))).1 = (asmSigX f q x).1 :=
    (asmSigB_index f (⟨q x.1, x.2⟩ : ↥(cellV f 1)) (asmSigX f q x).1).mpr hx
  refine Sigma.ext hidxB.symm ?_
  refine (Subtype.heq_iff_coe_eq (fun w => by rw [hidxB])).mpr ?_
  show q ((asmSigX f q x).2 : X)
    = ((asmSigB f (⟨q x.1, x.2⟩ : ↥(cellV f 1))).2 : attachCells (D - 2) Γ ι f)
  rw [asmSigX_val f q x, asmSigB_val f (⟨q x.1, x.2⟩ : ↥(cellV f 1))]

/-- **The third square**: the piece decomposition. -/
theorem asmSq3 :
    (asmPhiX ≫ asmP : Work.Cohomology.relChains (TopCat.of ↥(q ⁻¹' cellV f 1)) (asmUVx f q)
      ⟶ Work.Cohomology.relChains
          (TopCat.of (Σ α, ↥(Work.Serre.pieceSet (D - 2) Γ ι f α))) (asmPieceRelB f))
      = asmW ≫ asmPhiB := by
  refine aqSquare _ _ _ _ asmPhiX_pi asmP_pi asmW_pi asmPhiB_pi ?_
  exact asmSq3_map

end Squares

/-! ## The per-cell maps and the final assembly -/

section Final

variable {D : ℕ} {Γ : Type} [TopologicalSpace Γ] {ι : Type} {X : Type} [TopologicalSpace X]
variable {f : ι → C(cellSphere (D - 2), Γ)} {q : C(X, attachCells (D - 2) Γ ι f)}

/-- The per-cell map of `sigmaPairMap` is the per-cell map of the cell step. -/
theorem asmPairMap_eq (f : ι → C(cellSphere (D - 2), Γ))
    (q : C(X, attachCells (D - 2) Γ ι f)) (α : ι) :
    Work.Serre.pairMap (Work.Serre.CellStep.cpSrcRel f α q)
        (Work.Serre.CellStep.cpTarRel f α) (asmPieceFun f q α) (asmPieceFun_mem f q α)
      = Work.Serre.cellPieceMap (D - 2) Γ ι f α q := by
  rw [Work.Serre.pairMap, Work.Serre.cellPieceMap]
  exact Work.Serre.CellStep.relChainsMapOf_congrStems _ _ _ _

end Final

/-- **The cell step.**  Let `Γ' = attachCells (D-2) Γ ι f` be obtained from `Γ` by attaching a
family of `D`-cells (`D ≥ 2`), with `Γ` embedded as `Set.range attachIncl`, and let `q : X → Γ'`
be a Serre fibration whose fibres over every point of `Γ'` are homologically `φ`-connected.  Then
the map of pairs `(X, q⁻¹(Γ)) → (Γ', Γ)` induced by `q` (`Work.Serre.cellStepAttachMap D Γ ι f X q`) is an
isomorphism on integral homology in degrees `< D + φ`.  See
`Submission/Work/Serre/STABLE_EXACT_PLAN.md` for the proof strategy (compression, excision,
additivity over the disjoint cells, and the per-cell `Work.Serre.cubeRelIso`). -/
theorem cellStep (D : ℕ) (hD : 2 ≤ D) (Γ : Type) [TopologicalSpace Γ] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere (D-2), Γ))
    (X : Type) [TopologicalSpace X]
    (q : C(X, Work.RatHurewicz.attachCells (D-2) Γ ι f))
    (hq : Work.StemsB.IsSerreFibration q) (φ : ℕ)
    (hfib : ∀ (y : Work.RatHurewicz.attachCells (D-2) Γ ι f), ∀ j : ℕ, 0 < j → j < φ →
      IsZero ((Work.Cohomology.singularChains ℤ
        (TopCat.of (Work.StemsB.fibre q y))).homology j))
    (h0 : ∀ y : Work.RatHurewicz.attachCells (D-2) Γ ι f,
      IsIso (TopCat.singularHomology₀ε (TopCat.of (Work.StemsB.fibre q y)) (ModuleCat.of ℤ ℤ)))
    (i : ℕ) (hi : i < D + φ) :
    IsIso (HomologicalComplex.homologyMap
      (Work.Serre.cellStepAttachMap D Γ ι f X q) i) := by
  have hi' : i < ((D - 2) + 2) + φ := by omega
  -- the two compressions
  have hA : CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (asmAX (D := D) (Γ := Γ) (ι := ι) (X := X) (f := f) (q := q)) i) := by
    unfold asmAX
    exact Work.Serre.CellStep.isIso_relCokerMap_of_acyclic (TopCat.of X)
      (Set.preimage_mono (asmOld_subset_cellU f))
      (fun k => Work.Serre.isZero_relChains_preimage_of_compress q hq
        (asmOld_subset_cellU f)
        (fun d => Work.Serre.CellStep.compressRel_cellU (D - 2) Γ ι f (by norm_num) (by norm_num) d) k) i
  have hB : CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (asmAB (D := D) (Γ := Γ) (ι := ι) (f := f)) i) := by
    unfold asmAB
    exact Work.Serre.CellStep.isIso_relCokerMap_of_acyclic
      (TopCat.of (attachCells (D - 2) Γ ι f)) (asmOld_subset_cellU f)
      (fun k => Work.Serre.isZero_relChains_of_compress
        (fun d => Work.Serre.CellStep.compressRel_cellU (D - 2) Γ ι f (by norm_num) (by norm_num) d) k) i
  -- the excisions
  have hEX : CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (asmEX (D := D) (Γ := Γ) (ι := ι) (X := X) (f := f) (q := q)) i) := by
    unfold asmEX
    refine Work.Cohomology.excision_relChainsMap_isIso (TopCat.of X) (q ⁻¹' cellV f 1)
      (q ⁻¹' cellU f (3/4)) ((isOpen_cellV f le_rfl).preimage q.continuous)
      ((isOpen_cellU f (by norm_num)).preimage q.continuous) ?_ i
    rw [← Set.preimage_union, (Set.union_comm (cellV f 1) (cellU f (3/4))).trans
      (cellU_union_cellV f (by norm_num)), Set.preimage_univ]
  have hEB : CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (asmEB (D := D) (Γ := Γ) (ι := ι) (f := f)) i) := by
    unfold asmEB
    refine Work.Cohomology.excision_relChainsMap_isIso
      (TopCat.of (attachCells (D - 2) Γ ι f)) (cellV f 1) (cellU f (3/4))
      (isOpen_cellV f le_rfl) (isOpen_cellU f (by norm_num)) ?_ i
    exact (Set.union_comm (cellV f 1) (cellU f (3/4))).trans (cellU_union_cellV f (by norm_num))
  -- the piece decompositions
  have hPhiB : CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (asmPhiB (D := D) (Γ := Γ) (ι := ι) (f := f)) i) := by
    haveI : CategoryTheory.IsIso (asmPhiB (D := D) (Γ := Γ) (ι := ι) (f := f)) := by
      unfold asmPhiB
      exact Work.StemsB.isIso_relChainsMapOf_homeomorph
        (X := TopCat.of ↥(cellV f 1))
        (Y := TopCat.of (Σ α, ↥(Work.Serre.pieceSet (D - 2) Γ ι f α))) (asmSigB f)
        (asmUV f) (asmPieceRelB f) (asmUV_rel f)
    exact Functor.map_isIso
      (HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) i) _
  have hPhiX : CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (asmPhiX (D := D) (Γ := Γ) (ι := ι) (X := X) (f := f) (q := q)) i) := by
    haveI : CategoryTheory.IsIso (asmPhiX (D := D) (Γ := Γ) (ι := ι) (X := X) (f := f) (q := q)) := by
      unfold asmPhiX
      exact Work.StemsB.isIso_relChainsMapOf_homeomorph
        (X := TopCat.of ↥(q ⁻¹' cellV f 1))
        (Y := TopCat.of (Σ α, ↥(q ⁻¹' Work.Serre.pieceSet (D - 2) Γ ι f α))) (asmSigX f q)
        (asmUVx f q) (asmPieceRelX f q) (asmUVx_rel f q)
    exact Functor.map_isIso
      (HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) i) _
  -- the coproduct of the per-cell maps
  have hP : CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (asmP (D := D) (Γ := Γ) (ι := ι) (X := X) (f := f) (q := q)) i) := by
    unfold asmP
    refine Work.Serre.CellStep.sigmaAdditivity
      (fun α => Work.Serre.CellStep.cpSrcRel f α q)
      (fun α => Work.Serre.CellStep.cpTarRel f α)
      (fun α => asmPieceFun f q α) (fun α => asmPieceFun_mem f q α) i ?_
    intro α
    rw [asmPairMap_eq f q α]
    exact Work.Serre.CellStep.cellPieceIso (D - 2) Γ ι f α q hq φ hfib h0 i hi'
  -- the chain of squares
  have h1 : CategoryTheory.IsIso (HomologicalComplex.homologyMap
        (asmCs (D := D) (Γ := Γ) (ι := ι) (X := X) (f := f) (q := q)) i)
      ↔ CategoryTheory.IsIso (HomologicalComplex.homologyMap
        (asmUmap (D := D) (Γ := Γ) (ι := ι) (X := X) (f := f) (q := q)) i) :=
    Work.Serre.CellStep.isIso_homologyMap_iff_of_square
      (asmAX (D := D) (Γ := Γ) (ι := ι) (X := X) (f := f) (q := q))
      (asmAB (D := D) (Γ := Γ) (ι := ι) (f := f))
      (asmCs (D := D) (Γ := Γ) (ι := ι) (X := X) (f := f) (q := q))
      (asmUmap (D := D) (Γ := Γ) (ι := ι) (X := X) (f := f) (q := q))
      (asmSq1 (D := D) (Γ := Γ) (ι := ι) (X := X) (f := f) (q := q)) i hA hB
  have h2 : CategoryTheory.IsIso (HomologicalComplex.homologyMap
        (asmW (D := D) (Γ := Γ) (ι := ι) (X := X) (f := f) (q := q)) i)
      ↔ CategoryTheory.IsIso (HomologicalComplex.homologyMap
        (asmUmap (D := D) (Γ := Γ) (ι := ι) (X := X) (f := f) (q := q)) i) :=
    Work.Serre.CellStep.isIso_homologyMap_iff_of_square
      (asmEX (D := D) (Γ := Γ) (ι := ι) (X := X) (f := f) (q := q))
      (asmEB (D := D) (Γ := Γ) (ι := ι) (f := f))
      (asmW (D := D) (Γ := Γ) (ι := ι) (X := X) (f := f) (q := q))
      (asmUmap (D := D) (Γ := Γ) (ι := ι) (X := X) (f := f) (q := q))
      (asmSq2 (D := D) (Γ := Γ) (ι := ι) (X := X) (f := f) (q := q)) i hEX hEB
  have h3 : CategoryTheory.IsIso (HomologicalComplex.homologyMap
        (asmW (D := D) (Γ := Γ) (ι := ι) (X := X) (f := f) (q := q)) i)
      ↔ CategoryTheory.IsIso (HomologicalComplex.homologyMap
        (asmP (D := D) (Γ := Γ) (ι := ι) (X := X) (f := f) (q := q)) i) :=
    Work.Serre.CellStep.isIso_homologyMap_iff_of_square
      (asmPhiX (D := D) (Γ := Γ) (ι := ι) (X := X) (f := f) (q := q))
      (asmPhiB (D := D) (Γ := Γ) (ι := ι) (f := f))
      (asmW (D := D) (Γ := Γ) (ι := ι) (X := X) (f := f) (q := q))
      (asmP (D := D) (Γ := Γ) (ι := ι) (X := X) (f := f) (q := q))
      (asmSq3 (D := D) (Γ := Γ) (ι := ι) (X := X) (f := f) (q := q)) i hPhiX hPhiB
  show CategoryTheory.IsIso (HomologicalComplex.homologyMap
    (asmCs (D := D) (Γ := Γ) (ι := ι) (X := X) (f := f) (q := q)) i)
  exact h1.mpr (h2.mp (h3.mpr hP))

end

end Work.Serre

