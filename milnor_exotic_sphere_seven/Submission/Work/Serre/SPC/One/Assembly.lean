import Mathlib
import Submission.Work.Serre.SPC.One.Pieces
import Submission.Work.Serre.SPC.One.compressRel_cellCompl
import Submission.Work.Serre.SPC.One.sigmaPairMapAdditivity
import Submission.Work.Serre.SPC.discDefs
import Submission.Work.Serre.CellStep.sigmaHomeo
import Submission.Work.Serre.CellStep.ModelReduction

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Assembly of the `1`-cell step

This file reduces the `1`-cell step `Work.Serre.SPC.CellStepHypOne` to

* the compression of the complement of the centres onto the old part
  (`Work.Serre.SPC.One.compressRel_cellCompl`),
* the additivity of relative homology over the disjoint union of the pieces
  (`Work.Serre.SPC.One.sigmaPairMapAdditivity`), and
* the per-piece comparison (`Work.Serre.SPC.One.pieceChainMap`).

The chain of maps is

`C_*(X,q⁻¹Y') → C_*(X,q⁻¹(Z∖P)) → C_*(q⁻¹V, q⁻¹(V∖P)) ⟶ C_*(V, V∖P) ← ⊕ᵢ C_*(Pᵢ, Pᵢ∖{cᵢ})`,

where the first two arrows are quasi-isomorphisms (compression, excision), the third is the map
induced by `q` over the union of the open cells and the last is the coproduct decomposition.
-/

set_option maxHeartbeats 1000000

open scoped Topology unitInterval
open CategoryTheory CategoryTheory.Limits

namespace Work.Serre.SPC.One

noncomputable section

variable {X : Type} [TopologicalSpace X]

/-! ## The maps of the assembly -/

/-- The complement of the cell centres. -/
abbrev cellCompl (Y : Type) [TopologicalSpace Y] (ι : Type) (f : ι → C(cellS0, Y)) :
    Set (attachOneCells Y ι f) := (oneCellCentresOne Y ι f)ᶜ

/-- The restriction of `q` to the preimage of a subset, as a map onto that subset. -/
def restrictCm {X : Type} [TopologicalSpace X] {Z : Type} [TopologicalSpace Z]
    (q : C(X, Z)) (W : Set Z) :
    C(↥(q ⁻¹' W), ↥W) :=
  ⟨fun x => ⟨q x.1, x.2⟩,
    Continuous.subtype_mk (q.continuous.comp continuous_subtype_val) (fun x => x.2)⟩

/-- The map of pairs over the complement of the centres induced by `q`. -/
noncomputable def midMap {Y : Type} [TopologicalSpace Y] {ι : Type} {f : ι → C(cellS0, Y)}
    {X : Type} [TopologicalSpace X] (q : C(X, attachOneCells Y ι f)) :
    Work.Cohomology.relChains (TopCat.of X) (q ⁻¹' cellCompl Y ι f) ⟶
      Work.Cohomology.relChains (TopCat.of (attachOneCells Y ι f)) (cellCompl Y ι f) :=
  Work.Cohomology.relChainsMapOf (TopCat.of X) (TopCat.of (attachOneCells Y ι f))
    (q ⁻¹' cellCompl Y ι f) (cellCompl Y ι f) (TopCat.ofHom q)
    (TopCat.ofHom (restrictCm q (cellCompl Y ι f)))
    (by ext x; rfl)

/-- The map of pairs over the union of the open cells induced by `q`. -/
noncomputable def midMapV {Y : Type} [TopologicalSpace Y] {ι : Type} {f : ι → C(cellS0, Y)}
    {X : Type} [TopologicalSpace X] (q : C(X, attachOneCells Y ι f)) :
    Work.Cohomology.relChains (TopCat.of ↥(q ⁻¹' cellInnerUnionOne Y ι f))
        {x : ↥(q ⁻¹' cellInnerUnionOne Y ι f) | (x : X) ∈ q ⁻¹' cellCompl Y ι f} ⟶
      Work.Cohomology.relChains (TopCat.of ↥(cellInnerUnionOne Y ι f))
        {y : ↥(cellInnerUnionOne Y ι f) | (y : attachOneCells Y ι f) ∈ cellCompl Y ι f} :=
  Work.Cohomology.relChainsMapOf
    (TopCat.of ↥(q ⁻¹' cellInnerUnionOne Y ι f)) (TopCat.of ↥(cellInnerUnionOne Y ι f))
    {x : ↥(q ⁻¹' cellInnerUnionOne Y ι f) | (x : X) ∈ q ⁻¹' cellCompl Y ι f}
    {y : ↥(cellInnerUnionOne Y ι f) | (y : attachOneCells Y ι f) ∈ cellCompl Y ι f}
    (TopCat.ofHom (restrictCm q (cellInnerUnionOne Y ι f)))
    (TopCat.ofHom ⟨fun x => ⟨⟨q x.1.1, x.1.2⟩, x.2⟩, by
      refine Continuous.subtype_mk (Continuous.subtype_mk ?_ _) _
      exact q.continuous.comp (continuous_subtype_val.comp continuous_subtype_val)⟩)
    (by ext x; rfl)


/-- The open model interval is open in the model interval. -/
theorem isOpen_cellInnerOne : IsOpen (cellInnerOne : Set cellD1) :=
  isOpen_lt (by fun_prop : Continuous fun x : cellD1 => ‖((x : cellD1) : ℝ)‖) continuous_const

theorem isOpen_cellInteriorOne {Y : Type} [TopologicalSpace Y] {ι : Type}
    {f : ι → C(cellS0, Y)} (i : ι) : IsOpen (cellInteriorOne Y ι f i) :=
  isOpen_cellImage f (U := cellInnerOne) i (fun _ hx => hx) isOpen_cellInnerOne

theorem disjoint_cellInteriorOne' {Y : Type} [TopologicalSpace Y] {ι : Type}
    {f : ι → C(cellS0, Y)} : Pairwise fun i j : ι => Disjoint (cellInteriorOne Y ι f i)
      (cellInteriorOne Y ι f j) :=
  fun _ _ hij => disjoint_cellInteriorOne f hij

/-! ## The cell decomposition of the union of the open cells -/

/-- The `i`-th piece of the union of the open cells, as a subset of the union. -/
def pieceYZ (Y : Type) [TopologicalSpace Y] (ι : Type) (f : ι → C(cellS0, Y)) (i : ι) :
    Set ↥(cellInnerUnionOne Y ι f) :=
  {z | (z : attachOneCells Y ι f) ∈ cellInteriorOne Y ι f i}

/-- The `i`-th piece of the preimage of the union of the open cells. -/
def pieceXZ {Y : Type} [TopologicalSpace Y] {ι : Type} {f : ι → C(cellS0, Y)}
    {X : Type} [TopologicalSpace X] (q : C(X, attachOneCells Y ι f)) (i : ι) :
    Set ↥(q ⁻¹' cellInnerUnionOne Y ι f) :=
  {z | (z : X) ∈ q ⁻¹' cellInteriorOne Y ι f i}

theorem isOpen_pieceYZ (Y : Type) [TopologicalSpace Y] (ι : Type) (f : ι → C(cellS0, Y))
    (i : ι) : IsOpen (pieceYZ Y ι f i) :=
  (isOpen_cellInteriorOne i).preimage continuous_subtype_val

theorem disjoint_pieceYZ (Y : Type) [TopologicalSpace Y] (ι : Type) (f : ι → C(cellS0, Y)) :
    Pairwise fun i j : ι => Disjoint (pieceYZ Y ι f i) (pieceYZ Y ι f j) :=
  fun i j hij => Set.disjoint_left.mpr (fun z hz1 hz2 =>
    Set.disjoint_left.mp (disjoint_cellInteriorOne f hij) hz1 hz2)

theorem iUnion_pieceYZ (Y : Type) [TopologicalSpace Y] (ι : Type) (f : ι → C(cellS0, Y)) :
    (⋃ i, pieceYZ Y ι f i) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro z
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp z.2
  exact Set.mem_iUnion.mpr ⟨i, hi⟩

theorem isOpen_pieceXZ {Y : Type} [TopologicalSpace Y] {ι : Type} {f : ι → C(cellS0, Y)}
    {X : Type} [TopologicalSpace X] (q : C(X, attachOneCells Y ι f)) (i : ι) :
    IsOpen (pieceXZ (Y := Y) q i) :=
  ((isOpen_cellInteriorOne i).preimage q.continuous).preimage continuous_subtype_val

theorem disjoint_pieceXZ {Y : Type} [TopologicalSpace Y] {ι : Type} {f : ι → C(cellS0, Y)}
    {X : Type} [TopologicalSpace X] (q : C(X, attachOneCells Y ι f)) :
    Pairwise fun i j : ι => Disjoint (pieceXZ (Y := Y) q i) (pieceXZ (Y := Y) q j) :=
  fun i j hij => Set.disjoint_left.mpr (fun z hz1 hz2 => by
    exact Set.disjoint_left.mp (disjoint_cellInteriorOne (f := f) hij) (show
      q (z : X) ∈ cellInteriorOne Y ι f i from hz1) (show
      q (z : X) ∈ cellInteriorOne Y ι f j from hz2))

theorem iUnion_pieceXZ {Y : Type} [TopologicalSpace Y] {ι : Type} {f : ι → C(cellS0, Y)}
    {X : Type} [TopologicalSpace X] (q : C(X, attachOneCells Y ι f)) :
    (⋃ i, pieceXZ (Y := Y) q i) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro z
  have hz : q (z : X) ∈ ⋃ i, cellInteriorOne Y ι f i := z.2
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hz
  exact Set.mem_iUnion.mpr ⟨i, hi⟩

/-- A family of homeomorphisms induces a homeomorphism of the disjoint unions. -/
def sigmaHomeoCongr {ι : Type} {α β : ι → Type} [∀ i, TopologicalSpace (α i)]
    [∀ i, TopologicalSpace (β i)] (e : ∀ i, α i ≃ₜ β i) :
    (Σ i, α i) ≃ₜ (Σ i, β i) where
  toFun x := ⟨x.1, e x.1 x.2⟩
  invFun x := ⟨x.1, (e x.1).symm x.2⟩
  left_inv x := by simp
  right_inv x := by simp
  continuous_toFun := continuous_sigma fun i =>
    continuous_sigmaMk.comp (e i).continuous
  continuous_invFun := continuous_sigma fun i =>
    continuous_sigmaMk.comp (e i).symm.continuous

@[simp] theorem sigmaHomeoCongr_apply_snd {ι : Type} {α β : ι → Type}
    [∀ i, TopologicalSpace (α i)] [∀ i, TopologicalSpace (β i)] (e : ∀ i, α i ≃ₜ β i)
    (x : Σ i, α i) : (sigmaHomeoCongr e x).2 = e x.1 x.2 := rfl

/-- The canonical homeomorphism of a piece of the union with the piece itself. -/
def pieceHomeoYZ (Y : Type) [TopologicalSpace Y] (ι : Type) (f : ι → C(cellS0, Y)) (i : ι) :
    ↥(pieceYZ Y ι f i) ≃ₜ pieceY Y ι f i where
  toFun z := ⟨z.1.1, z.2⟩
  invFun y := ⟨⟨y.1, Set.mem_iUnion.mpr ⟨i, y.2⟩⟩, y.2⟩
  left_inv z := Subtype.ext (Subtype.ext rfl)
  right_inv y := Subtype.ext rfl
  continuous_toFun := Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) _
  continuous_invFun := Continuous.subtype_mk
    (Continuous.subtype_mk continuous_subtype_val _) _

/-- The canonical homeomorphism of a piece of the preimage of the union with the piece itself. -/
def pieceHomeoXZ {Y : Type} [TopologicalSpace Y] {ι : Type} {f : ι → C(cellS0, Y)}
    {X : Type} [TopologicalSpace X] (q : C(X, attachOneCells Y ι f)) (i : ι) :
    ↥(pieceXZ (Y := Y) q i) ≃ₜ pieceX Y ι f q i where
  toFun z := ⟨z.1.1, z.2⟩
  invFun y := ⟨⟨y.1, Set.mem_iUnion.mpr ⟨i, y.2⟩⟩, y.2⟩
  left_inv z := Subtype.ext (Subtype.ext rfl)
  right_inv y := Subtype.ext rfl
  continuous_toFun := Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) _
  continuous_invFun := Continuous.subtype_mk
    (Continuous.subtype_mk continuous_subtype_val _) _

@[simp] theorem pieceHomeoYZ_apply_val (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(cellS0, Y)) (i : ι) (x : ↥(pieceYZ Y ι f i)) :
    (((pieceHomeoYZ Y ι f i x : pieceY Y ι f i)) : attachOneCells Y ι f)
      = ((x : ↥(pieceYZ Y ι f i)) : attachOneCells Y ι f) := rfl

@[simp] theorem pieceHomeoXZ_apply_val {Y : Type} [TopologicalSpace Y] {ι : Type}
    {f : ι → C(cellS0, Y)} {X : Type} [TopologicalSpace X]
    (q : C(X, attachOneCells Y ι f)) (i : ι) (x : ↥(pieceXZ (Y := Y) q i)) :
    (((pieceHomeoXZ q i x : pieceX Y ι f q i)) : X)
      = ((x : ↥(pieceXZ (Y := Y) q i)) : X) := rfl

/-- **The coproduct decomposition of a space covered by pairwise disjoint open sets**, with the
explicit description of the homeomorphism: the first component of the image of `z` is the (unique)
index with `z ∈ P i`, and the underlying point of the second component is `z` itself. -/
theorem sigmaHomeo' {Z : Type} [TopologicalSpace Z] {ι : Type} (P : ι → Set Z)
    (hopen : ∀ i, IsOpen (P i)) (hdisj : Pairwise fun i j => Disjoint (P i) (P j))
    (hcover : (⋃ i, P i) = Set.univ) :
    ∃ e : Z ≃ₜ (Σ i, ↥(P i)),
      (∀ (z : Z) (i : ι), (e z).1 = i ↔ z ∈ P i) ∧ (∀ z : Z, ((e z).2 : Z) = z) := by
  classical
  have heq_subtype : ∀ {a b : ι} (h : a = b) {x : Z} (ha : x ∈ P a) (hb : x ∈ P b),
      HEq (⟨x, ha⟩ : ↥(P a)) (⟨x, hb⟩ : ↥(P b)) := by
    intro a b h x ha hb
    subst h
    exact heq_of_eq (Subtype.ext rfl)
  have huniq : ∀ z : Z, ∃! i, z ∈ P i := by
    intro z
    have hz : z ∈ ⋃ i, P i := by rw [hcover]; exact Set.mem_univ z
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hz
    refine ⟨i, hi, ?_⟩
    intro j hj
    by_contra hne
    have hmem : z ∈ P i ∩ P j := ⟨hi, hj⟩
    have hd : Disjoint (P i) (P j) := hdisj (Ne.symm hne)
    rw [Set.disjoint_iff_inter_eq_empty] at hd
    rw [hd] at hmem
    exact hmem
  choose idx hidx using fun z => (huniq z).exists
  have hidxuniq : ∀ z (i : ι), z ∈ P i → idx z = i :=
    fun z i hi => (huniq z).unique (hidx z) hi
  let f : Z → (Σ i, ↥(P i)) := fun z => ⟨idx z, ⟨z, hidx z⟩⟩
  have hf_eq : ∀ (x : Z) (i : ι) (hx : x ∈ P i), f x = (⟨i, ⟨x, hx⟩⟩ : Σ j, ↥(P j)) := by
    intro x i hx
    exact Sigma.ext (hidxuniq x i hx) (heq_subtype (hidxuniq x i hx) (hidx x) hx)
  have hfcont : Continuous f := by
    refine continuous_of_cover_nhds (s := P) (fun x => ?_) (fun i => ?_)
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (by rw [hcover]; exact Set.mem_univ x)
      exact ⟨i, (hopen i).mem_nhds hi⟩
    · rw [continuousOn_iff_continuous_domRestrict]
      exact (continuous_sigmaMk (i := i)).congr (fun x : ↥(P i) => (hf_eq x.1 i x.2).symm)
  let g : (Σ i, ↥(P i)) → Z := fun x => x.2.val
  have hgcont : Continuous g := continuous_sigma (fun i => continuous_subtype_val)
  have hleft : Function.LeftInverse g f := fun z => rfl
  have hright : Function.RightInverse g f := by
    intro x
    rcases x with ⟨i, ⟨z, hz⟩⟩
    exact hf_eq z i hz
  refine ⟨{ toFun := f, invFun := g, left_inv := hleft, right_inv := hright,
            continuous_toFun := hfcont, continuous_invFun := hgcont }, ?_, ?_⟩
  · intro z i
    show idx z = i ↔ z ∈ P i
    exact ⟨fun h => h ▸ hidx z, fun h => hidxuniq z i h⟩
  · intro z
    rfl

/-- **The coproduct decomposition of the union of the open cells.** -/
def piZ (Y : Type) [TopologicalSpace Y] (ι : Type) (f : ι → C(cellS0, Y)) :
    ↥(cellInnerUnionOne Y ι f) ≃ₜ (Σ i, pieceY Y ι f i) :=
  Homeomorph.trans (Classical.choose (sigmaHomeo' (pieceYZ Y ι f)
      (isOpen_pieceYZ Y ι f) (disjoint_pieceYZ Y ι f) (iUnion_pieceYZ Y ι f)))
    (sigmaHomeoCongr (pieceHomeoYZ Y ι f))

/-- **The coproduct decomposition of the preimage of the union of the open cells.** -/
def piX {Y : Type} [TopologicalSpace Y] {ι : Type} {f : ι → C(cellS0, Y)}
    {X : Type} [TopologicalSpace X] (q : C(X, attachOneCells Y ι f)) :
    ↥(q ⁻¹' cellInnerUnionOne Y ι f) ≃ₜ (Σ i, pieceX Y ι f q i) :=
  Homeomorph.trans (Classical.choose (sigmaHomeo' (pieceXZ (Y := Y) q)
      (isOpen_pieceXZ q) (disjoint_pieceXZ q) (iUnion_pieceXZ q)))
    (sigmaHomeoCongr (pieceHomeoXZ q))

theorem piZ_apply_fst (Y : Type) [TopologicalSpace Y] (ι : Type) (f : ι → C(cellS0, Y))
    (z : ↥(cellInnerUnionOne Y ι f)) (i : ι) :
    (piZ Y ι f z).1 = i ↔ (z : attachOneCells Y ι f) ∈ cellInteriorOne Y ι f i := by
  have h := (Classical.choose_spec (sigmaHomeo' (pieceYZ Y ι f)
    (isOpen_pieceYZ Y ι f) (disjoint_pieceYZ Y ι f) (iUnion_pieceYZ Y ι f))).1 z i
  simp only [piZ, Homeomorph.trans_apply]
  exact h

theorem piX_apply_fst {Y : Type} [TopologicalSpace Y] {ι : Type} {f : ι → C(cellS0, Y)}
    {X : Type} [TopologicalSpace X] (q : C(X, attachOneCells Y ι f))
    (z : ↥(q ⁻¹' cellInnerUnionOne Y ι f)) (i : ι) :
    (piX q z).1 = i ↔ (z : X) ∈ q ⁻¹' cellInteriorOne Y ι f i := by
  have h := (Classical.choose_spec (sigmaHomeo' (pieceXZ (Y := Y) q)
    (isOpen_pieceXZ q) (disjoint_pieceXZ q) (iUnion_pieceXZ q))).1 z i
  simp only [piX, Homeomorph.trans_apply]
  exact h

/-- The underlying point of the second component of the coproduct decomposition is the point
itself. -/
theorem piZ_apply_snd (Y : Type) [TopologicalSpace Y] (ι : Type) (f : ι → C(cellS0, Y))
    (z : ↥(cellInnerUnionOne Y ι f)) :
    (((piZ Y ι f z).2 : pieceY Y ι f (piZ Y ι f z).1) : attachOneCells Y ι f)
      = (z : attachOneCells Y ι f) := by
  have h := (Classical.choose_spec (sigmaHomeo' (pieceYZ Y ι f)
    (isOpen_pieceYZ Y ι f) (disjoint_pieceYZ Y ι f) (iUnion_pieceYZ Y ι f))).2 z
  exact congrArg (fun w : ↥(cellInnerUnionOne Y ι f) => (w : attachOneCells Y ι f)) h

/-- The underlying point of the second component of the coproduct decomposition is the point
itself. -/
theorem piX_apply_snd {Y : Type} [TopologicalSpace Y] {ι : Type} {f : ι → C(cellS0, Y)}
    {X : Type} [TopologicalSpace X] (q : C(X, attachOneCells Y ι f))
    (z : ↥(q ⁻¹' cellInnerUnionOne Y ι f)) :
    (((piX q z).2 : pieceX Y ι f q (piX q z).1) : X) = (z : X) := by
  have h := (Classical.choose_spec (sigmaHomeo' (pieceXZ (Y := Y) q)
    (isOpen_pieceXZ q) (disjoint_pieceXZ q) (iUnion_pieceXZ q))).2 z
  exact congrArg (fun w : ↥(q ⁻¹' cellInnerUnionOne Y ι f) => (w : X)) h


/-! ## The relative parts correspond under the coproduct decomposition -/

theorem piZ_mem_rel (Y : Type) [TopologicalSpace Y] (ι : Type) (f : ι → C(cellS0, Y))
    (z : ↥(cellInnerUnionOne Y ι f)) :
    (piZ Y ι f z).2 ∈ pieceYrel Y ι f (piZ Y ι f z).1 ↔
      (z : attachOneCells Y ι f) ∈ cellCompl Y ι f := by
  have hfst : (z : attachOneCells Y ι f) ∈ cellInteriorOne Y ι f (piZ Y ι f z).1 :=
    (piZ_apply_fst Y ι f z (piZ Y ι f z).1).mp rfl
  have hsnd : (((piZ Y ι f z).2 : pieceY Y ι f (piZ Y ι f z).1) : attachOneCells Y ι f)
      = (z : attachOneCells Y ι f) := piZ_apply_snd Y ι f z
  constructor
  · intro h
    rw [mem_compl_centres]
    intro j hji
    by_cases hj : j = (piZ Y ι f z).1
    · subst hj
      exact h.2 (hsnd.trans hji.symm)
    · have hc : oneCellCentreOne Y ι f j ∈ cellInteriorOne Y ι f j :=
        oneCellCentreOne_mem_cellInteriorOne f j
      have hmem : (z : attachOneCells Y ι f) ∈ cellInteriorOne Y ι f j := hji ▸ hc
      exact Set.disjoint_left.mp
        (disjoint_cellInteriorOne f (Ne.symm hj)) hfst hmem
  · intro h
    rw [mem_compl_centres] at h
    have hne : (z : attachOneCells Y ι f) ≠ oneCellCentreOne Y ι f (piZ Y ι f z).1 :=
      fun hc => (h _) hc.symm
    exact ⟨hsnd.symm ▸ hfst, fun hc => hne (hsnd.symm.trans hc)⟩

theorem piX_mem_rel {Y : Type} [TopologicalSpace Y] {ι : Type} {f : ι → C(cellS0, Y)}
    {X : Type} [TopologicalSpace X] (q : C(X, attachOneCells Y ι f))
    (z : ↥(q ⁻¹' cellInnerUnionOne Y ι f)) :
    (piX q z).2 ∈ pieceXrel Y ι f q (piX q z).1 ↔
      (z : X) ∈ q ⁻¹' cellCompl Y ι f := by
  have hfst : q (z : X) ∈ cellInteriorOne Y ι f (piX q z).1 :=
    (piX_apply_fst q z (piX q z).1).mp rfl
  have hsnd : (((piX q z).2 : pieceX Y ι f q (piX q z).1) : X) = (z : X) := piX_apply_snd q z
  constructor
  · intro h
    rw [Set.mem_preimage, mem_compl_centres]
    intro j hji
    by_cases hj : j = (piX q z).1
    · subst hj
      exact h.2 ((congrArg q hsnd).trans hji.symm)
    · have hc : oneCellCentreOne Y ι f j ∈ cellInteriorOne Y ι f j :=
        oneCellCentreOne_mem_cellInteriorOne f j
      have hmem : q (z : X) ∈ cellInteriorOne Y ι f j := hji ▸ hc
      exact Set.disjoint_left.mp
        (disjoint_cellInteriorOne f (Ne.symm hj)) hfst hmem
  · intro h
    rw [Set.mem_preimage, mem_compl_centres] at h
    have hne : q (z : X) ≠ oneCellCentreOne Y ι f (piX q z).1 :=
      fun hc => (h _) hc.symm
    exact ⟨(congrArg q hsnd).symm ▸ hfst,
      fun hc => hne ((congrArg q hsnd).symm.trans hc)⟩

/-- **The coproduct decomposition restricts to the relative parts.** -/
def piZrel (Y : Type) [TopologicalSpace Y] (ι : Type) (f : ι → C(cellS0, Y)) :
    ↥{y : ↥(cellInnerUnionOne Y ι f) | (y : attachOneCells Y ι f) ∈ cellCompl Y ι f} ≃ₜ
      ↥{x : Σ i, pieceY Y ι f i | x.2 ∈ pieceYrel Y ι f x.1} where
  toFun y := ⟨piZ Y ι f y.1, (piZ_mem_rel Y ι f y.1).mpr y.2⟩
  invFun x := ⟨(piZ Y ι f).symm x.1,
    (piZ_mem_rel Y ι f ((piZ Y ι f).symm x.1)).mp (by
      rw [Homeomorph.apply_symm_apply]; exact x.2)⟩
  left_inv y := Subtype.ext (by simp)
  right_inv x := Subtype.ext (by simp)
  continuous_toFun := Continuous.subtype_mk
    ((piZ Y ι f).continuous.comp continuous_subtype_val)
    (fun y => (piZ_mem_rel Y ι f y.1).mpr y.2)
  continuous_invFun := Continuous.subtype_mk
    (((piZ Y ι f).symm.continuous.comp continuous_subtype_val))
    (fun x => (piZ_mem_rel Y ι f ((piZ Y ι f).symm x.1)).mp (by
      rw [Homeomorph.apply_symm_apply]; exact x.2))

/-- **The coproduct decomposition restricts to the relative parts.** -/
def piXrel {Y : Type} [TopologicalSpace Y] {ι : Type} {f : ι → C(cellS0, Y)}
    {X : Type} [TopologicalSpace X] (q : C(X, attachOneCells Y ι f)) :
    ↥{z : ↥(q ⁻¹' cellInnerUnionOne Y ι f) | (z : X) ∈ q ⁻¹' cellCompl Y ι f} ≃ₜ
      ↥{x : Σ i, pieceX Y ι f q i | x.2 ∈ pieceXrel Y ι f q x.1} where
  toFun y := ⟨piX q y.1, (piX_mem_rel q y.1).mpr y.2⟩
  invFun x := ⟨(piX q).symm x.1,
    (piX_mem_rel q ((piX q).symm x.1)).mp (by
      rw [Homeomorph.apply_symm_apply]; exact x.2)⟩
  left_inv y := Subtype.ext (by simp)
  right_inv x := Subtype.ext (by simp)
  continuous_toFun := Continuous.subtype_mk
    ((piX q).continuous.comp continuous_subtype_val)
    (fun y => (piX_mem_rel q y.1).mpr y.2)
  continuous_invFun := Continuous.subtype_mk
    (((piX q).symm.continuous.comp continuous_subtype_val))
    (fun x => (piX_mem_rel q ((piX q).symm x.1)).mp (by
      rw [Homeomorph.apply_symm_apply]; exact x.2))

theorem piZ_piZrel_apply (Y : Type) [TopologicalSpace Y] (ι : Type) (f : ι → C(cellS0, Y))
    (x : ↥{y : ↥(cellInnerUnionOne Y ι f) | (y : attachOneCells Y ι f) ∈ cellCompl Y ι f}) :
    piZ Y ι f (x : ↥(cellInnerUnionOne Y ι f))
      = (((piZrel Y ι f x : ↥{x : Σ i, pieceY Y ι f i | x.2 ∈ pieceYrel Y ι f x.1}) :
          Σ i, pieceY Y ι f i)) := rfl

theorem piX_piXrel_apply {Y : Type} [TopologicalSpace Y] {ι : Type} {f : ι → C(cellS0, Y)}
    {X : Type} [TopologicalSpace X] (q : C(X, attachOneCells Y ι f))
    (x : ↥{z : ↥(q ⁻¹' cellInnerUnionOne Y ι f) | (z : X) ∈ q ⁻¹' cellCompl Y ι f}) :
    piX q (x : ↥(q ⁻¹' cellInnerUnionOne Y ι f))
      = (((piXrel q x : ↥{x : Σ i, pieceX Y ι f q i | x.2 ∈ pieceXrel Y ι f q x.1}) :
          Σ i, pieceX Y ι f q i)) := rfl

/-- The isomorphism of relative chain complexes induced by the coproduct decomposition of the
base. -/
noncomputable def coprodBase (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(cellS0, Y)) :
    Work.Cohomology.relChains (TopCat.of ↥(cellInnerUnionOne Y ι f))
        {y : ↥(cellInnerUnionOne Y ι f) | (y : attachOneCells Y ι f) ∈ cellCompl Y ι f} ⟶
      Work.Cohomology.relChains (TopCat.of (Σ i, pieceY Y ι f i))
        {x : Σ i, pieceY Y ι f i | x.2 ∈ pieceYrel Y ι f x.1} :=
  Work.Cohomology.relChainsMapOf (TopCat.of ↥(cellInnerUnionOne Y ι f))
    (TopCat.of (Σ i, pieceY Y ι f i))
    {y : ↥(cellInnerUnionOne Y ι f) | (y : attachOneCells Y ι f) ∈ cellCompl Y ι f}
    {x : Σ i, pieceY Y ι f i | x.2 ∈ pieceYrel Y ι f x.1}
    (TopCat.ofHom (piZ Y ι f)) (TopCat.ofHom (piZrel Y ι f))
    (by
      ext x : 1
      show piZ Y ι f (x : ↥(cellInnerUnionOne Y ι f)) = _
      exact piZ_piZrel_apply Y ι f x)

/-- The isomorphism of relative chain complexes induced by the coproduct decomposition of the
total space. -/
noncomputable def coprodTotal {Y : Type} [TopologicalSpace Y] {ι : Type}
    {f : ι → C(cellS0, Y)} {X : Type} [TopologicalSpace X]
    (q : C(X, attachOneCells Y ι f)) :
    Work.Cohomology.relChains (TopCat.of ↥(q ⁻¹' cellInnerUnionOne Y ι f))
        {z : ↥(q ⁻¹' cellInnerUnionOne Y ι f) | (z : X) ∈ q ⁻¹' cellCompl Y ι f} ⟶
      Work.Cohomology.relChains (TopCat.of (Σ i, pieceX Y ι f q i))
        {x : Σ i, pieceX Y ι f q i | x.2 ∈ pieceXrel Y ι f q x.1} :=
  Work.Cohomology.relChainsMapOf (TopCat.of ↥(q ⁻¹' cellInnerUnionOne Y ι f))
    (TopCat.of (Σ i, pieceX Y ι f q i))
    {z : ↥(q ⁻¹' cellInnerUnionOne Y ι f) | (z : X) ∈ q ⁻¹' cellCompl Y ι f}
    {x : Σ i, pieceX Y ι f q i | x.2 ∈ pieceXrel Y ι f q x.1}
    (TopCat.ofHom (piX q)) (TopCat.ofHom (piXrel q))
    (by
      ext x : 1
      show piX q (x : ↥(q ⁻¹' cellInnerUnionOne Y ι f)) = _
      exact piX_piXrel_apply q x)


/-! ## The commuting squares of the assembly -/

theorem oldPart_subset_cellCompl (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(cellS0, Y)) : oneCellOldPart Y ι f ⊆ cellCompl Y ι f :=
  oldPart_subset_compl_centres

/-- The projection of the cell step map onto the pair of the old parts. -/
theorem cokernel_π_oneCellStepMap {Y : Type} [TopologicalSpace Y] {ι : Type}
    {f : ι → C(cellS0, Y)} {X : Type} [TopologicalSpace X] (q : C(X, attachOneCells Y ι f)) :
    cokernel.π (Work.Cohomology.inclChains (TopCat.of X) (q ⁻¹' oneCellOldPart Y ι f))
        ≫ oneCellStepMap ι f q
      = Work.Cohomology.chainMap ℤ (TopCat.of X) (TopCat.of (attachOneCells Y ι f))
          (TopCat.ofHom q)
        ≫ cokernel.π (Work.Cohomology.inclChains (TopCat.of (attachOneCells Y ι f))
            (oneCellOldPart Y ι f)) := by
  unfold oneCellStepMap Work.Cohomology.relChainsMapOf
  exact Work.Cohomology.cokernel_π_map _ _ _ _ _

theorem cokernel_π_midMap {Y : Type} [TopologicalSpace Y] {ι : Type} {f : ι → C(cellS0, Y)}
    {X : Type} [TopologicalSpace X] (q : C(X, attachOneCells Y ι f)) :
    cokernel.π (Work.Cohomology.inclChains (TopCat.of X) (q ⁻¹' cellCompl Y ι f))
        ≫ midMap q
      = Work.Cohomology.chainMap ℤ (TopCat.of X) (TopCat.of (attachOneCells Y ι f))
          (TopCat.ofHom q)
        ≫ cokernel.π (Work.Cohomology.inclChains (TopCat.of (attachOneCells Y ι f))
            (cellCompl Y ι f)) := by
  unfold midMap Work.Cohomology.relChainsMapOf
  exact Work.Cohomology.cokernel_π_map _ _ _ _ _

theorem cokernel_π_midMapV {Y : Type} [TopologicalSpace Y] {ι : Type} {f : ι → C(cellS0, Y)}
    {X : Type} [TopologicalSpace X] (q : C(X, attachOneCells Y ι f)) :
    cokernel.π (Work.Cohomology.inclChains (TopCat.of ↥(q ⁻¹' cellInnerUnionOne Y ι f))
        {x : ↥(q ⁻¹' cellInnerUnionOne Y ι f) | (x : X) ∈ q ⁻¹' cellCompl Y ι f})
        ≫ midMapV q
      = Work.Cohomology.chainMap ℤ (TopCat.of ↥(q ⁻¹' cellInnerUnionOne Y ι f))
          (TopCat.of ↥(cellInnerUnionOne Y ι f))
          (TopCat.ofHom (restrictCm q (cellInnerUnionOne Y ι f)))
        ≫ cokernel.π (Work.Cohomology.inclChains (TopCat.of ↥(cellInnerUnionOne Y ι f))
            {y : ↥(cellInnerUnionOne Y ι f) | (y : attachOneCells Y ι f) ∈ cellCompl Y ι f}) := by
  unfold midMapV Work.Cohomology.relChainsMapOf
  exact Work.Cohomology.cokernel_π_map _ _ _ _ _

theorem cokernel_π_coprodBase (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(cellS0, Y)) :
    cokernel.π (Work.Cohomology.inclChains (TopCat.of ↥(cellInnerUnionOne Y ι f))
        {y : ↥(cellInnerUnionOne Y ι f) | (y : attachOneCells Y ι f) ∈ cellCompl Y ι f})
        ≫ coprodBase Y ι f
      = Work.Cohomology.chainMap ℤ (TopCat.of ↥(cellInnerUnionOne Y ι f))
          (TopCat.of (Σ i, pieceY Y ι f i)) (TopCat.ofHom (piZ Y ι f))
        ≫ cokernel.π (Work.Cohomology.inclChains (TopCat.of (Σ i, pieceY Y ι f i))
            {x : Σ i, pieceY Y ι f i | x.2 ∈ pieceYrel Y ι f x.1}) := by
  unfold coprodBase Work.Cohomology.relChainsMapOf
  exact Work.Cohomology.cokernel_π_map _ _ _ _ _

theorem cokernel_π_coprodTotal {Y : Type} [TopologicalSpace Y] {ι : Type}
    {f : ι → C(cellS0, Y)} {X : Type} [TopologicalSpace X]
    (q : C(X, attachOneCells Y ι f)) :
    cokernel.π (Work.Cohomology.inclChains (TopCat.of ↥(q ⁻¹' cellInnerUnionOne Y ι f))
        {z : ↥(q ⁻¹' cellInnerUnionOne Y ι f) | (z : X) ∈ q ⁻¹' cellCompl Y ι f})
        ≫ coprodTotal q
      = Work.Cohomology.chainMap ℤ (TopCat.of ↥(q ⁻¹' cellInnerUnionOne Y ι f))
          (TopCat.of (Σ i, pieceX Y ι f q i)) (TopCat.ofHom (piX q))
        ≫ cokernel.π (Work.Cohomology.inclChains (TopCat.of (Σ i, pieceX Y ι f q i))
            {x : Σ i, pieceX Y ι f q i | x.2 ∈ pieceXrel Y ι f q x.1}) := by
  unfold coprodTotal Work.Cohomology.relChainsMapOf
  exact Work.Cohomology.cokernel_π_map _ _ _ _ _

/-- The projection of the coproduct of the piece maps. -/
theorem cokernel_π_sigmaPieceMap (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(cellS0, Y)) {X : Type} [TopologicalSpace X]
    (q : C(X, attachOneCells Y ι f)) :
    cokernel.π (Work.Cohomology.inclChains (TopCat.of (Σ i, pieceX Y ι f q i))
        {x : Σ i, pieceX Y ι f q i | x.2 ∈ pieceXrel Y ι f q x.1})
        ≫ sigmaPieceMap Y ι f q
      = Work.Cohomology.chainMap ℤ (TopCat.of (Σ i, pieceX Y ι f q i))
          (TopCat.of (Σ i, pieceY Y ι f i))
          (TopCat.ofHom ⟨Sigma.map id (fun i => pieceMap Y ι f q i),
            continuous_sigma_map.2 fun i => (pieceMap Y ι f q i).continuous⟩)
        ≫ cokernel.π (Work.Cohomology.inclChains (TopCat.of (Σ i, pieceY Y ι f i))
            {x : Σ i, pieceY Y ι f i | x.2 ∈ pieceYrel Y ι f x.1}) := by
  unfold sigmaPieceMap sigmaPairMap Work.Cohomology.relChainsMapOf
  exact Work.Cohomology.cokernel_π_map _ _ _ _ _


/-- **The compression square**: the cell step map factors through the map over the complement of
the centres. -/
theorem square_compress {Y : Type} [TopologicalSpace Y] {ι : Type} {f : ι → C(cellS0, Y)}
    {X : Type} [TopologicalSpace X] (q : C(X, attachOneCells Y ι f)) :
    oneCellStepMap ι f q ≫
        Work.Cohomology.relCokerMap (TopCat.of (attachOneCells Y ι f)) (oneCellOldPart Y ι f)
          (cellCompl Y ι f) (oldPart_subset_cellCompl Y ι f)
      = Work.Cohomology.relCokerMap (TopCat.of X) (q ⁻¹' oneCellOldPart Y ι f)
          (q ⁻¹' cellCompl Y ι f) (Set.preimage_mono (oldPart_subset_cellCompl Y ι f))
        ≫ midMap q := by
  have hM := cokernel_π_oneCellStepMap q
  have hZ := Work.Cohomology.relCokerMap_comp_π (TopCat.of (attachOneCells Y ι f))
    (oneCellOldPart Y ι f) (cellCompl Y ι f) (oldPart_subset_cellCompl Y ι f)
  have hX := Work.Cohomology.relCokerMap_comp_π (TopCat.of X) (q ⁻¹' oneCellOldPart Y ι f)
    (q ⁻¹' cellCompl Y ι f) (Set.preimage_mono (oldPart_subset_cellCompl Y ι f))
  have hmid := cokernel_π_midMap q
  apply (cancel_epi (cokernel.π (Work.Cohomology.inclChains (TopCat.of X)
    (q ⁻¹' oneCellOldPart Y ι f)))).1
  have h1 : cokernel.π (Work.Cohomology.inclChains (TopCat.of X) (q ⁻¹' oneCellOldPart Y ι f))
        ≫ (oneCellStepMap ι f q ≫
            Work.Cohomology.relCokerMap (TopCat.of (attachOneCells Y ι f))
              (oneCellOldPart Y ι f) (cellCompl Y ι f) (oldPart_subset_cellCompl Y ι f))
      = (cokernel.π (Work.Cohomology.inclChains (TopCat.of X) (q ⁻¹' oneCellOldPart Y ι f))
          ≫ oneCellStepMap ι f q)
        ≫ Work.Cohomology.relCokerMap (TopCat.of (attachOneCells Y ι f))
            (oneCellOldPart Y ι f) (cellCompl Y ι f) (oldPart_subset_cellCompl Y ι f) :=
    (Category.assoc _ _ _).symm
  have h2 : (cokernel.π (Work.Cohomology.inclChains (TopCat.of X) (q ⁻¹' oneCellOldPart Y ι f))
          ≫ oneCellStepMap ι f q)
        ≫ Work.Cohomology.relCokerMap (TopCat.of (attachOneCells Y ι f))
            (oneCellOldPart Y ι f) (cellCompl Y ι f) (oldPart_subset_cellCompl Y ι f)
      = (Work.Cohomology.chainMap ℤ (TopCat.of X) (TopCat.of (attachOneCells Y ι f))
            (TopCat.ofHom q)
          ≫ cokernel.π (Work.Cohomology.inclChains (TopCat.of (attachOneCells Y ι f))
              (oneCellOldPart Y ι f)))
        ≫ Work.Cohomology.relCokerMap (TopCat.of (attachOneCells Y ι f))
            (oneCellOldPart Y ι f) (cellCompl Y ι f) (oldPart_subset_cellCompl Y ι f) :=
    congrArg (fun t => t ≫ Work.Cohomology.relCokerMap (TopCat.of (attachOneCells Y ι f))
        (oneCellOldPart Y ι f) (cellCompl Y ι f) (oldPart_subset_cellCompl Y ι f)) hM
  have h3 : (Work.Cohomology.chainMap ℤ (TopCat.of X) (TopCat.of (attachOneCells Y ι f))
            (TopCat.ofHom q)
          ≫ cokernel.π (Work.Cohomology.inclChains (TopCat.of (attachOneCells Y ι f))
              (oneCellOldPart Y ι f)))
        ≫ Work.Cohomology.relCokerMap (TopCat.of (attachOneCells Y ι f))
            (oneCellOldPart Y ι f) (cellCompl Y ι f) (oldPart_subset_cellCompl Y ι f)
      = Work.Cohomology.chainMap ℤ (TopCat.of X) (TopCat.of (attachOneCells Y ι f))
            (TopCat.ofHom q)
          ≫ (cokernel.π (Work.Cohomology.inclChains (TopCat.of (attachOneCells Y ι f))
              (oneCellOldPart Y ι f))
            ≫ Work.Cohomology.relCokerMap (TopCat.of (attachOneCells Y ι f))
                (oneCellOldPart Y ι f) (cellCompl Y ι f)
                (oldPart_subset_cellCompl Y ι f)) := Category.assoc _ _ _
  have h4 : Work.Cohomology.chainMap ℤ (TopCat.of X) (TopCat.of (attachOneCells Y ι f))
            (TopCat.ofHom q)
          ≫ (cokernel.π (Work.Cohomology.inclChains (TopCat.of (attachOneCells Y ι f))
              (oneCellOldPart Y ι f))
            ≫ Work.Cohomology.relCokerMap (TopCat.of (attachOneCells Y ι f))
                (oneCellOldPart Y ι f) (cellCompl Y ι f)
                (oldPart_subset_cellCompl Y ι f))
      = Work.Cohomology.chainMap ℤ (TopCat.of X) (TopCat.of (attachOneCells Y ι f))
            (TopCat.ofHom q)
          ≫ cokernel.π (Work.Cohomology.inclChains (TopCat.of (attachOneCells Y ι f))
              (cellCompl Y ι f)) :=
    congrArg (fun t => Work.Cohomology.chainMap ℤ (TopCat.of X)
        (TopCat.of (attachOneCells Y ι f)) (TopCat.ofHom q) ≫ t) hZ
  have h5 : Work.Cohomology.chainMap ℤ (TopCat.of X) (TopCat.of (attachOneCells Y ι f))
            (TopCat.ofHom q)
          ≫ cokernel.π (Work.Cohomology.inclChains (TopCat.of (attachOneCells Y ι f))
              (cellCompl Y ι f))
      = cokernel.π (Work.Cohomology.inclChains (TopCat.of X) (q ⁻¹' cellCompl Y ι f))
        ≫ midMap q := hmid.symm
  have h6 : cokernel.π (Work.Cohomology.inclChains (TopCat.of X) (q ⁻¹' cellCompl Y ι f))
        ≫ midMap q
      = (cokernel.π (Work.Cohomology.inclChains (TopCat.of X) (q ⁻¹' oneCellOldPart Y ι f))
          ≫ Work.Cohomology.relCokerMap (TopCat.of X) (q ⁻¹' oneCellOldPart Y ι f)
              (q ⁻¹' cellCompl Y ι f) (Set.preimage_mono (oldPart_subset_cellCompl Y ι f)))
        ≫ midMap q := congrArg (fun t => t ≫ midMap q) hX.symm
  have h7 : (cokernel.π (Work.Cohomology.inclChains (TopCat.of X) (q ⁻¹' oneCellOldPart Y ι f))
          ≫ Work.Cohomology.relCokerMap (TopCat.of X) (q ⁻¹' oneCellOldPart Y ι f)
              (q ⁻¹' cellCompl Y ι f) (Set.preimage_mono (oldPart_subset_cellCompl Y ι f)))
        ≫ midMap q
      = cokernel.π (Work.Cohomology.inclChains (TopCat.of X) (q ⁻¹' oneCellOldPart Y ι f))
        ≫ (Work.Cohomology.relCokerMap (TopCat.of X) (q ⁻¹' oneCellOldPart Y ι f)
              (q ⁻¹' cellCompl Y ι f) (Set.preimage_mono (oldPart_subset_cellCompl Y ι f))
            ≫ midMap q) := Category.assoc _ _ _
  exact h1.trans (h2.trans (h3.trans (h4.trans (h5.trans (h6.trans h7)))))


/-- **The excision square**: the comparison over the complement of the centres is the comparison
over the union of the open cells. -/
theorem square_excision {Y : Type} [TopologicalSpace Y] {ι : Type} {f : ι → C(cellS0, Y)}
    {X : Type} [TopologicalSpace X] (q : C(X, attachOneCells Y ι f)) :
    Work.Cohomology.relChainsMap (TopCat.of X) (q ⁻¹' cellInnerUnionOne Y ι f)
        (q ⁻¹' cellCompl Y ι f)
      ≫ midMap q
      = midMapV q
        ≫ Work.Cohomology.relChainsMap (TopCat.of (attachOneCells Y ι f))
            (cellInnerUnionOne Y ι f) (cellCompl Y ι f) := by
  have h₁ := Work.Cohomology.cokernel_π_relChainsMap (TopCat.of X) (q ⁻¹' cellInnerUnionOne Y ι f)
    (q ⁻¹' cellCompl Y ι f)
  have h₂ := cokernel_π_midMap q
  have h₃ := cokernel_π_midMapV q
  have h₄ := Work.Cohomology.cokernel_π_relChainsMap (TopCat.of (attachOneCells Y ι f))
    (cellInnerUnionOne Y ι f) (cellCompl Y ι f)
  have hmap : Work.Cohomology.subtypeIncl (TopCat.of X) (q ⁻¹' cellInnerUnionOne Y ι f)
        ≫ TopCat.ofHom q
      = TopCat.ofHom (restrictCm q (cellInnerUnionOne Y ι f))
        ≫ Work.Cohomology.subtypeIncl (TopCat.of (attachOneCells Y ι f))
            (cellInnerUnionOne Y ι f) := by
    ext x
    rfl
  have hmid : Work.Cohomology.chainMap ℤ (TopCat.of ↥(q ⁻¹' cellInnerUnionOne Y ι f))
          (TopCat.of X) (Work.Cohomology.subtypeIncl (TopCat.of X)
            (q ⁻¹' cellInnerUnionOne Y ι f))
        ≫ Work.Cohomology.chainMap ℤ (TopCat.of X) (TopCat.of (attachOneCells Y ι f))
            (TopCat.ofHom q)
      = Work.Cohomology.chainMap ℤ (TopCat.of ↥(q ⁻¹' cellInnerUnionOne Y ι f))
          (TopCat.of ↥(cellInnerUnionOne Y ι f))
          (TopCat.ofHom (restrictCm q (cellInnerUnionOne Y ι f)))
        ≫ Work.Cohomology.chainMap ℤ (TopCat.of ↥(cellInnerUnionOne Y ι f))
            (TopCat.of (attachOneCells Y ι f))
            (Work.Cohomology.subtypeIncl (TopCat.of (attachOneCells Y ι f))
              (cellInnerUnionOne Y ι f)) := by
    rw [← Work.Cohomology.chainMap_comp_relChains, ← Work.Cohomology.chainMap_comp_relChains,
      hmap]
  apply (cancel_epi (cokernel.π (Work.Cohomology.inclChains
    (TopCat.of ↥(q ⁻¹' cellInnerUnionOne Y ι f))
    {x : ↥(q ⁻¹' cellInnerUnionOne Y ι f) | (x : X) ∈ q ⁻¹' cellCompl Y ι f}))).1
  have k2 : (cokernel.π (Work.Cohomology.inclChains (TopCat.of ↥(q ⁻¹' cellInnerUnionOne Y ι f))
            {x : ↥(q ⁻¹' cellInnerUnionOne Y ι f) | (x : X) ∈ q ⁻¹' cellCompl Y ι f})
          ≫ Work.Cohomology.relChainsMap (TopCat.of X) (q ⁻¹' cellInnerUnionOne Y ι f)
              (q ⁻¹' cellCompl Y ι f))
        ≫ midMap q
      = (Work.Cohomology.chainMap ℤ (TopCat.of ↥(q ⁻¹' cellInnerUnionOne Y ι f))
            (TopCat.of X) (Work.Cohomology.subtypeIncl (TopCat.of X)
              (q ⁻¹' cellInnerUnionOne Y ι f))
          ≫ cokernel.π (Work.Cohomology.inclChains (TopCat.of X) (q ⁻¹' cellCompl Y ι f)))
        ≫ midMap q := congrArg (fun t => t ≫ midMap q) h₁
  have k5 : Work.Cohomology.chainMap ℤ (TopCat.of ↥(q ⁻¹' cellInnerUnionOne Y ι f))
            (TopCat.of X) (Work.Cohomology.subtypeIncl (TopCat.of X)
              (q ⁻¹' cellInnerUnionOne Y ι f))
          ≫ (Work.Cohomology.chainMap ℤ (TopCat.of X)
                (TopCat.of (attachOneCells Y ι f)) (TopCat.ofHom q)
            ≫ cokernel.π (Work.Cohomology.inclChains (TopCat.of (attachOneCells Y ι f))
                (cellCompl Y ι f)))
      = (Work.Cohomology.chainMap ℤ (TopCat.of ↥(q ⁻¹' cellInnerUnionOne Y ι f))
            (TopCat.of X) (Work.Cohomology.subtypeIncl (TopCat.of X)
              (q ⁻¹' cellInnerUnionOne Y ι f))
          ≫ Work.Cohomology.chainMap ℤ (TopCat.of X) (TopCat.of (attachOneCells Y ι f))
              (TopCat.ofHom q))
        ≫ cokernel.π (Work.Cohomology.inclChains (TopCat.of (attachOneCells Y ι f))
            (cellCompl Y ι f)) := (Category.assoc _ _ _).symm
  have k6 : (Work.Cohomology.chainMap ℤ (TopCat.of ↥(q ⁻¹' cellInnerUnionOne Y ι f))
            (TopCat.of X) (Work.Cohomology.subtypeIncl (TopCat.of X)
              (q ⁻¹' cellInnerUnionOne Y ι f))
          ≫ Work.Cohomology.chainMap ℤ (TopCat.of X) (TopCat.of (attachOneCells Y ι f))
              (TopCat.ofHom q))
        ≫ cokernel.π (Work.Cohomology.inclChains (TopCat.of (attachOneCells Y ι f))
            (cellCompl Y ι f))
      = (Work.Cohomology.chainMap ℤ (TopCat.of ↥(q ⁻¹' cellInnerUnionOne Y ι f))
            (TopCat.of ↥(cellInnerUnionOne Y ι f))
            (TopCat.ofHom (restrictCm q (cellInnerUnionOne Y ι f)))
          ≫ Work.Cohomology.chainMap ℤ (TopCat.of ↥(cellInnerUnionOne Y ι f))
              (TopCat.of (attachOneCells Y ι f))
              (Work.Cohomology.subtypeIncl (TopCat.of (attachOneCells Y ι f))
                (cellInnerUnionOne Y ι f)))
        ≫ cokernel.π (Work.Cohomology.inclChains (TopCat.of (attachOneCells Y ι f))
            (cellCompl Y ι f)) := congrArg (fun t => t ≫ cokernel.π (Work.Cohomology.inclChains
              (TopCat.of (attachOneCells Y ι f)) (cellCompl Y ι f))) hmid
  have k12 : Work.Cohomology.chainMap ℤ (TopCat.of ↥(q ⁻¹' cellInnerUnionOne Y ι f))
            (TopCat.of ↥(cellInnerUnionOne Y ι f))
            (TopCat.ofHom (restrictCm q (cellInnerUnionOne Y ι f)))
          ≫ (cokernel.π (Work.Cohomology.inclChains (TopCat.of ↥(cellInnerUnionOne Y ι f))
                {y : ↥(cellInnerUnionOne Y ι f) | (y : attachOneCells Y ι f) ∈ cellCompl Y ι f})
            ≫ Work.Cohomology.relChainsMap (TopCat.of (attachOneCells Y ι f))
                (cellInnerUnionOne Y ι f) (cellCompl Y ι f))
      = (Work.Cohomology.chainMap ℤ (TopCat.of ↥(q ⁻¹' cellInnerUnionOne Y ι f))
            (TopCat.of ↥(cellInnerUnionOne Y ι f))
            (TopCat.ofHom (restrictCm q (cellInnerUnionOne Y ι f)))
          ≫ cokernel.π (Work.Cohomology.inclChains (TopCat.of ↥(cellInnerUnionOne Y ι f))
                {y : ↥(cellInnerUnionOne Y ι f) |
                  (y : attachOneCells Y ι f) ∈ cellCompl Y ι f}))
        ≫ Work.Cohomology.relChainsMap (TopCat.of (attachOneCells Y ι f))
            (cellInnerUnionOne Y ι f) (cellCompl Y ι f) := (Category.assoc _ _ _).symm
  have k13 : (Work.Cohomology.chainMap ℤ (TopCat.of ↥(q ⁻¹' cellInnerUnionOne Y ι f))
            (TopCat.of ↥(cellInnerUnionOne Y ι f))
            (TopCat.ofHom (restrictCm q (cellInnerUnionOne Y ι f)))
          ≫ cokernel.π (Work.Cohomology.inclChains (TopCat.of ↥(cellInnerUnionOne Y ι f))
                {y : ↥(cellInnerUnionOne Y ι f) |
                  (y : attachOneCells Y ι f) ∈ cellCompl Y ι f}))
        ≫ Work.Cohomology.relChainsMap (TopCat.of (attachOneCells Y ι f))
            (cellInnerUnionOne Y ι f) (cellCompl Y ι f)
      = (cokernel.π (Work.Cohomology.inclChains (TopCat.of ↥(q ⁻¹' cellInnerUnionOne Y ι f))
            {x : ↥(q ⁻¹' cellInnerUnionOne Y ι f) | (x : X) ∈ q ⁻¹' cellCompl Y ι f})
          ≫ midMapV q)
        ≫ Work.Cohomology.relChainsMap (TopCat.of (attachOneCells Y ι f))
            (cellInnerUnionOne Y ι f) (cellCompl Y ι f) := congrArg (fun t => t ≫
          Work.Cohomology.relChainsMap (TopCat.of (attachOneCells Y ι f))
            (cellInnerUnionOne Y ι f) (cellCompl Y ι f)) h₃.symm
  have k1 : cokernel.π (Work.Cohomology.inclChains (TopCat.of ↥(q ⁻¹' cellInnerUnionOne Y ι f))
        {x : ↥(q ⁻¹' cellInnerUnionOne Y ι f) | (x : X) ∈ q ⁻¹' cellCompl Y ι f})
        ≫ (Work.Cohomology.relChainsMap (TopCat.of X) (q ⁻¹' cellInnerUnionOne Y ι f)
            (q ⁻¹' cellCompl Y ι f) ≫ midMap q)
      = (cokernel.π (Work.Cohomology.inclChains (TopCat.of ↥(q ⁻¹' cellInnerUnionOne Y ι f))
            {x : ↥(q ⁻¹' cellInnerUnionOne Y ι f) | (x : X) ∈ q ⁻¹' cellCompl Y ι f})
          ≫ Work.Cohomology.relChainsMap (TopCat.of X) (q ⁻¹' cellInnerUnionOne Y ι f)
              (q ⁻¹' cellCompl Y ι f))
        ≫ midMap q := (Category.assoc _ _ _).symm
  have k3 : (Work.Cohomology.chainMap ℤ (TopCat.of ↥(q ⁻¹' cellInnerUnionOne Y ι f))
            (TopCat.of X) (Work.Cohomology.subtypeIncl (TopCat.of X)
              (q ⁻¹' cellInnerUnionOne Y ι f))
          ≫ cokernel.π (Work.Cohomology.inclChains (TopCat.of X) (q ⁻¹' cellCompl Y ι f)))
        ≫ midMap q
      = Work.Cohomology.chainMap ℤ (TopCat.of ↥(q ⁻¹' cellInnerUnionOne Y ι f))
            (TopCat.of X) (Work.Cohomology.subtypeIncl (TopCat.of X)
              (q ⁻¹' cellInnerUnionOne Y ι f))
          ≫ (cokernel.π (Work.Cohomology.inclChains (TopCat.of X) (q ⁻¹' cellCompl Y ι f))
            ≫ midMap q) := Category.assoc _ _ _
  have k4 : Work.Cohomology.chainMap ℤ (TopCat.of ↥(q ⁻¹' cellInnerUnionOne Y ι f))
            (TopCat.of X) (Work.Cohomology.subtypeIncl (TopCat.of X)
              (q ⁻¹' cellInnerUnionOne Y ι f))
          ≫ (cokernel.π (Work.Cohomology.inclChains (TopCat.of X) (q ⁻¹' cellCompl Y ι f))
            ≫ midMap q)
      = Work.Cohomology.chainMap ℤ (TopCat.of ↥(q ⁻¹' cellInnerUnionOne Y ι f))
            (TopCat.of X) (Work.Cohomology.subtypeIncl (TopCat.of X)
              (q ⁻¹' cellInnerUnionOne Y ι f))
          ≫ (Work.Cohomology.chainMap ℤ (TopCat.of X)
                (TopCat.of (attachOneCells Y ι f)) (TopCat.ofHom q)
            ≫ cokernel.π (Work.Cohomology.inclChains (TopCat.of (attachOneCells Y ι f))
                (cellCompl Y ι f))) :=
    congrArg (fun t => Work.Cohomology.chainMap ℤ
        (TopCat.of ↥(q ⁻¹' cellInnerUnionOne Y ι f)) (TopCat.of X)
        (Work.Cohomology.subtypeIncl (TopCat.of X) (q ⁻¹' cellInnerUnionOne Y ι f)) ≫ t) h₂
  have k7 : (Work.Cohomology.chainMap ℤ (TopCat.of ↥(q ⁻¹' cellInnerUnionOne Y ι f))
            (TopCat.of ↥(cellInnerUnionOne Y ι f))
            (TopCat.ofHom (restrictCm q (cellInnerUnionOne Y ι f)))
          ≫ Work.Cohomology.chainMap ℤ (TopCat.of ↥(cellInnerUnionOne Y ι f))
              (TopCat.of (attachOneCells Y ι f))
              (Work.Cohomology.subtypeIncl (TopCat.of (attachOneCells Y ι f))
                (cellInnerUnionOne Y ι f)))
        ≫ cokernel.π (Work.Cohomology.inclChains (TopCat.of (attachOneCells Y ι f))
            (cellCompl Y ι f))
      = Work.Cohomology.chainMap ℤ (TopCat.of ↥(q ⁻¹' cellInnerUnionOne Y ι f))
            (TopCat.of ↥(cellInnerUnionOne Y ι f))
            (TopCat.ofHom (restrictCm q (cellInnerUnionOne Y ι f)))
          ≫ (Work.Cohomology.chainMap ℤ (TopCat.of ↥(cellInnerUnionOne Y ι f))
                (TopCat.of (attachOneCells Y ι f))
                (Work.Cohomology.subtypeIncl (TopCat.of (attachOneCells Y ι f))
                  (cellInnerUnionOne Y ι f))
            ≫ cokernel.π (Work.Cohomology.inclChains (TopCat.of (attachOneCells Y ι f))
                (cellCompl Y ι f))) := Category.assoc _ _ _
  have k8 : Work.Cohomology.chainMap ℤ (TopCat.of ↥(q ⁻¹' cellInnerUnionOne Y ι f))
            (TopCat.of ↥(cellInnerUnionOne Y ι f))
            (TopCat.ofHom (restrictCm q (cellInnerUnionOne Y ι f)))
          ≫ (Work.Cohomology.chainMap ℤ (TopCat.of ↥(cellInnerUnionOne Y ι f))
                (TopCat.of (attachOneCells Y ι f))
                (Work.Cohomology.subtypeIncl (TopCat.of (attachOneCells Y ι f))
                  (cellInnerUnionOne Y ι f))
            ≫ cokernel.π (Work.Cohomology.inclChains (TopCat.of (attachOneCells Y ι f))
                (cellCompl Y ι f)))
      = Work.Cohomology.chainMap ℤ (TopCat.of ↥(q ⁻¹' cellInnerUnionOne Y ι f))
            (TopCat.of ↥(cellInnerUnionOne Y ι f))
            (TopCat.ofHom (restrictCm q (cellInnerUnionOne Y ι f)))
          ≫ (cokernel.π (Work.Cohomology.inclChains (TopCat.of ↥(cellInnerUnionOne Y ι f))
                {y : ↥(cellInnerUnionOne Y ι f) |
                  (y : attachOneCells Y ι f) ∈ cellCompl Y ι f})
            ≫ Work.Cohomology.relChainsMap (TopCat.of (attachOneCells Y ι f))
                (cellInnerUnionOne Y ι f) (cellCompl Y ι f)) :=
    congrArg (fun t => Work.Cohomology.chainMap ℤ
        (TopCat.of ↥(q ⁻¹' cellInnerUnionOne Y ι f)) (TopCat.of ↥(cellInnerUnionOne Y ι f))
        (TopCat.ofHom (restrictCm q (cellInnerUnionOne Y ι f))) ≫ t) h₄.symm
  exact k1.trans (k2.trans (k3.trans (k4.trans (k5.trans (k6.trans (k7.trans
    (k8.trans (k12.trans k13))))))))

/-- **The coproduct square**: the comparison over the union of the open cells corresponds to the
coproduct of the comparisons over the pieces. -/
theorem square_coprod {Y : Type} [TopologicalSpace Y] {ι : Type} {f : ι → C(cellS0, Y)}
    {X : Type} [TopologicalSpace X] (q : C(X, attachOneCells Y ι f)) :
    coprodTotal q ≫ sigmaPieceMap Y ι f q
      = midMapV q ≫ coprodBase Y ι f := by
  have g₁ := cokernel_π_coprodTotal q
  have g₂ := cokernel_π_sigmaPieceMap Y ι f q
  have g₃ := cokernel_π_midMapV q
  have g₄ := cokernel_π_coprodBase Y ι f
  have hmap : (TopCat.ofHom (piX q) : TopCat.of ↥(q ⁻¹' cellInnerUnionOne Y ι f) ⟶
        TopCat.of (Σ i, pieceX Y ι f q i))
      ≫ TopCat.ofHom ⟨Sigma.map id (fun i => pieceMap Y ι f q i),
          continuous_sigma_map.2 fun i => (pieceMap Y ι f q i).continuous⟩
      = (TopCat.ofHom (restrictCm q (cellInnerUnionOne Y ι f)) :
          TopCat.of ↥(q ⁻¹' cellInnerUnionOne Y ι f) ⟶ TopCat.of ↥(cellInnerUnionOne Y ι f))
        ≫ TopCat.ofHom (piZ Y ι f) := by
    ext x : 1
    have hmem : (x : X) ∈ q ⁻¹' cellInnerUnionOne Y ι f := x.2
    have hidx : (piX q x).1 = (piZ Y ι f ⟨q (x : X), hmem⟩).1 :=
      (piX_apply_fst q x _).mpr ((piZ_apply_fst Y ι f ⟨q (x : X), hmem⟩ _).mp rfl)
    show (⟨(piX q x).1, pieceMap Y ι f q (piX q x).1 (piX q x).2⟩ : Σ i, pieceY Y ι f i)
      = (piZ Y ι f ⟨q (x : X), hmem⟩)
    refine Sigma.ext hidx ?_
    refine (Subtype.heq_iff_coe_eq (fun z => by rw [hidx])).mpr ?_
    simp only [pieceMap, ContinuousMap.coe_mk]
    rw [piX_apply_snd, piZ_apply_snd]
  have hchain : Work.Cohomology.chainMap ℤ (TopCat.of ↥(q ⁻¹' cellInnerUnionOne Y ι f))
          (TopCat.of (Σ i, pieceX Y ι f q i)) (TopCat.ofHom (piX q))
        ≫ Work.Cohomology.chainMap ℤ (TopCat.of (Σ i, pieceX Y ι f q i))
            (TopCat.of (Σ i, pieceY Y ι f i))
            (TopCat.ofHom ⟨Sigma.map id (fun i => pieceMap Y ι f q i),
              continuous_sigma_map.2 fun i => (pieceMap Y ι f q i).continuous⟩)
      = Work.Cohomology.chainMap ℤ (TopCat.of ↥(q ⁻¹' cellInnerUnionOne Y ι f))
          (TopCat.of ↥(cellInnerUnionOne Y ι f))
          (TopCat.ofHom (restrictCm q (cellInnerUnionOne Y ι f)))
        ≫ Work.Cohomology.chainMap ℤ (TopCat.of ↥(cellInnerUnionOne Y ι f))
            (TopCat.of (Σ i, pieceY Y ι f i)) (TopCat.ofHom (piZ Y ι f)) := by
    rw [← Work.Cohomology.chainMap_comp_relChains, ← Work.Cohomology.chainMap_comp_relChains,
      hmap]
  apply (cancel_epi (cokernel.π (Work.Cohomology.inclChains
    (TopCat.of ↥(q ⁻¹' cellInnerUnionOne Y ι f))
    {z : ↥(q ⁻¹' cellInnerUnionOne Y ι f) | (z : X) ∈ q ⁻¹' cellCompl Y ι f}))).1
  have m1 : cokernel.π (Work.Cohomology.inclChains (TopCat.of ↥(q ⁻¹' cellInnerUnionOne Y ι f))
        {z : ↥(q ⁻¹' cellInnerUnionOne Y ι f) | (z : X) ∈ q ⁻¹' cellCompl Y ι f})
        ≫ (coprodTotal q ≫ sigmaPieceMap Y ι f q)
      = (cokernel.π (Work.Cohomology.inclChains (TopCat.of ↥(q ⁻¹' cellInnerUnionOne Y ι f))
            {z : ↥(q ⁻¹' cellInnerUnionOne Y ι f) | (z : X) ∈ q ⁻¹' cellCompl Y ι f})
          ≫ coprodTotal q) ≫ sigmaPieceMap Y ι f q := (Category.assoc _ _ _).symm
  have m2 : (cokernel.π (Work.Cohomology.inclChains (TopCat.of ↥(q ⁻¹' cellInnerUnionOne Y ι f))
            {z : ↥(q ⁻¹' cellInnerUnionOne Y ι f) | (z : X) ∈ q ⁻¹' cellCompl Y ι f})
          ≫ coprodTotal q) ≫ sigmaPieceMap Y ι f q
      = (Work.Cohomology.chainMap ℤ (TopCat.of ↥(q ⁻¹' cellInnerUnionOne Y ι f))
            (TopCat.of (Σ i, pieceX Y ι f q i)) (TopCat.ofHom (piX q))
          ≫ cokernel.π (Work.Cohomology.inclChains (TopCat.of (Σ i, pieceX Y ι f q i))
              {x : Σ i, pieceX Y ι f q i | x.2 ∈ pieceXrel Y ι f q x.1}))
        ≫ sigmaPieceMap Y ι f q := congrArg (fun t => t ≫ sigmaPieceMap Y ι f q) g₁
  have m3 : (Work.Cohomology.chainMap ℤ (TopCat.of ↥(q ⁻¹' cellInnerUnionOne Y ι f))
            (TopCat.of (Σ i, pieceX Y ι f q i)) (TopCat.ofHom (piX q))
          ≫ cokernel.π (Work.Cohomology.inclChains (TopCat.of (Σ i, pieceX Y ι f q i))
              {x : Σ i, pieceX Y ι f q i | x.2 ∈ pieceXrel Y ι f q x.1}))
        ≫ sigmaPieceMap Y ι f q
      = Work.Cohomology.chainMap ℤ (TopCat.of ↥(q ⁻¹' cellInnerUnionOne Y ι f))
            (TopCat.of (Σ i, pieceX Y ι f q i)) (TopCat.ofHom (piX q))
          ≫ (cokernel.π (Work.Cohomology.inclChains (TopCat.of (Σ i, pieceX Y ι f q i))
              {x : Σ i, pieceX Y ι f q i | x.2 ∈ pieceXrel Y ι f q x.1})
            ≫ sigmaPieceMap Y ι f q) := Category.assoc _ _ _
  have m4 : Work.Cohomology.chainMap ℤ (TopCat.of ↥(q ⁻¹' cellInnerUnionOne Y ι f))
            (TopCat.of (Σ i, pieceX Y ι f q i)) (TopCat.ofHom (piX q))
          ≫ (cokernel.π (Work.Cohomology.inclChains (TopCat.of (Σ i, pieceX Y ι f q i))
              {x : Σ i, pieceX Y ι f q i | x.2 ∈ pieceXrel Y ι f q x.1})
            ≫ sigmaPieceMap Y ι f q)
      = Work.Cohomology.chainMap ℤ (TopCat.of ↥(q ⁻¹' cellInnerUnionOne Y ι f))
            (TopCat.of (Σ i, pieceX Y ι f q i)) (TopCat.ofHom (piX q))
          ≫ (Work.Cohomology.chainMap ℤ (TopCat.of (Σ i, pieceX Y ι f q i))
                (TopCat.of (Σ i, pieceY Y ι f i))
                (TopCat.ofHom ⟨Sigma.map id (fun i => pieceMap Y ι f q i),
                  continuous_sigma_map.2 fun i => (pieceMap Y ι f q i).continuous⟩)
            ≫ cokernel.π (Work.Cohomology.inclChains (TopCat.of (Σ i, pieceY Y ι f i))
                {x : Σ i, pieceY Y ι f i | x.2 ∈ pieceYrel Y ι f x.1})) :=
    congrArg (fun t => Work.Cohomology.chainMap ℤ
        (TopCat.of ↥(q ⁻¹' cellInnerUnionOne Y ι f)) (TopCat.of (Σ i, pieceX Y ι f q i))
        (TopCat.ofHom (piX q)) ≫ t) g₂
  have m5 : Work.Cohomology.chainMap ℤ (TopCat.of ↥(q ⁻¹' cellInnerUnionOne Y ι f))
            (TopCat.of (Σ i, pieceX Y ι f q i)) (TopCat.ofHom (piX q))
          ≫ (Work.Cohomology.chainMap ℤ (TopCat.of (Σ i, pieceX Y ι f q i))
                (TopCat.of (Σ i, pieceY Y ι f i))
                (TopCat.ofHom ⟨Sigma.map id (fun i => pieceMap Y ι f q i),
                  continuous_sigma_map.2 fun i => (pieceMap Y ι f q i).continuous⟩)
            ≫ cokernel.π (Work.Cohomology.inclChains (TopCat.of (Σ i, pieceY Y ι f i))
                {x : Σ i, pieceY Y ι f i | x.2 ∈ pieceYrel Y ι f x.1}))
      = (Work.Cohomology.chainMap ℤ (TopCat.of ↥(q ⁻¹' cellInnerUnionOne Y ι f))
            (TopCat.of (Σ i, pieceX Y ι f q i)) (TopCat.ofHom (piX q))
          ≫ Work.Cohomology.chainMap ℤ (TopCat.of (Σ i, pieceX Y ι f q i))
              (TopCat.of (Σ i, pieceY Y ι f i))
              (TopCat.ofHom ⟨Sigma.map id (fun i => pieceMap Y ι f q i),
                continuous_sigma_map.2 fun i => (pieceMap Y ι f q i).continuous⟩))
        ≫ cokernel.π (Work.Cohomology.inclChains (TopCat.of (Σ i, pieceY Y ι f i))
            {x : Σ i, pieceY Y ι f i | x.2 ∈ pieceYrel Y ι f x.1}) :=
        (Category.assoc _ _ _).symm
  have m6 : (Work.Cohomology.chainMap ℤ (TopCat.of ↥(q ⁻¹' cellInnerUnionOne Y ι f))
            (TopCat.of (Σ i, pieceX Y ι f q i)) (TopCat.ofHom (piX q))
          ≫ Work.Cohomology.chainMap ℤ (TopCat.of (Σ i, pieceX Y ι f q i))
              (TopCat.of (Σ i, pieceY Y ι f i))
              (TopCat.ofHom ⟨Sigma.map id (fun i => pieceMap Y ι f q i),
                continuous_sigma_map.2 fun i => (pieceMap Y ι f q i).continuous⟩))
        ≫ cokernel.π (Work.Cohomology.inclChains (TopCat.of (Σ i, pieceY Y ι f i))
            {x : Σ i, pieceY Y ι f i | x.2 ∈ pieceYrel Y ι f x.1})
      = (Work.Cohomology.chainMap ℤ (TopCat.of ↥(q ⁻¹' cellInnerUnionOne Y ι f))
            (TopCat.of ↥(cellInnerUnionOne Y ι f))
            (TopCat.ofHom (restrictCm q (cellInnerUnionOne Y ι f)))
          ≫ Work.Cohomology.chainMap ℤ (TopCat.of ↥(cellInnerUnionOne Y ι f))
              (TopCat.of (Σ i, pieceY Y ι f i)) (TopCat.ofHom (piZ Y ι f)))
        ≫ cokernel.π (Work.Cohomology.inclChains (TopCat.of (Σ i, pieceY Y ι f i))
            {x : Σ i, pieceY Y ι f i | x.2 ∈ pieceYrel Y ι f x.1}) :=
    congrArg (fun t => t ≫ cokernel.π (Work.Cohomology.inclChains
        (TopCat.of (Σ i, pieceY Y ι f i)) {x : Σ i, pieceY Y ι f i |
          x.2 ∈ pieceYrel Y ι f x.1})) hchain
  have m7 : (Work.Cohomology.chainMap ℤ (TopCat.of ↥(q ⁻¹' cellInnerUnionOne Y ι f))
            (TopCat.of ↥(cellInnerUnionOne Y ι f))
            (TopCat.ofHom (restrictCm q (cellInnerUnionOne Y ι f)))
          ≫ Work.Cohomology.chainMap ℤ (TopCat.of ↥(cellInnerUnionOne Y ι f))
              (TopCat.of (Σ i, pieceY Y ι f i)) (TopCat.ofHom (piZ Y ι f)))
        ≫ cokernel.π (Work.Cohomology.inclChains (TopCat.of (Σ i, pieceY Y ι f i))
            {x : Σ i, pieceY Y ι f i | x.2 ∈ pieceYrel Y ι f x.1})
      = Work.Cohomology.chainMap ℤ (TopCat.of ↥(q ⁻¹' cellInnerUnionOne Y ι f))
            (TopCat.of ↥(cellInnerUnionOne Y ι f))
            (TopCat.ofHom (restrictCm q (cellInnerUnionOne Y ι f)))
          ≫ (Work.Cohomology.chainMap ℤ (TopCat.of ↥(cellInnerUnionOne Y ι f))
                (TopCat.of (Σ i, pieceY Y ι f i)) (TopCat.ofHom (piZ Y ι f))
            ≫ cokernel.π (Work.Cohomology.inclChains (TopCat.of (Σ i, pieceY Y ι f i))
                {x : Σ i, pieceY Y ι f i | x.2 ∈ pieceYrel Y ι f x.1})) :=
        Category.assoc _ _ _
  have m8 : Work.Cohomology.chainMap ℤ (TopCat.of ↥(q ⁻¹' cellInnerUnionOne Y ι f))
            (TopCat.of ↥(cellInnerUnionOne Y ι f))
            (TopCat.ofHom (restrictCm q (cellInnerUnionOne Y ι f)))
          ≫ (Work.Cohomology.chainMap ℤ (TopCat.of ↥(cellInnerUnionOne Y ι f))
                (TopCat.of (Σ i, pieceY Y ι f i)) (TopCat.ofHom (piZ Y ι f))
            ≫ cokernel.π (Work.Cohomology.inclChains (TopCat.of (Σ i, pieceY Y ι f i))
                {x : Σ i, pieceY Y ι f i | x.2 ∈ pieceYrel Y ι f x.1}))
      = Work.Cohomology.chainMap ℤ (TopCat.of ↥(q ⁻¹' cellInnerUnionOne Y ι f))
            (TopCat.of ↥(cellInnerUnionOne Y ι f))
            (TopCat.ofHom (restrictCm q (cellInnerUnionOne Y ι f)))
          ≫ (cokernel.π (Work.Cohomology.inclChains (TopCat.of ↥(cellInnerUnionOne Y ι f))
                {y : ↥(cellInnerUnionOne Y ι f) |
                  (y : attachOneCells Y ι f) ∈ cellCompl Y ι f})
            ≫ coprodBase Y ι f) :=
    congrArg (fun t => Work.Cohomology.chainMap ℤ
        (TopCat.of ↥(q ⁻¹' cellInnerUnionOne Y ι f)) (TopCat.of ↥(cellInnerUnionOne Y ι f))
        (TopCat.ofHom (restrictCm q (cellInnerUnionOne Y ι f))) ≫ t) g₄.symm
  have m9 : Work.Cohomology.chainMap ℤ (TopCat.of ↥(q ⁻¹' cellInnerUnionOne Y ι f))
            (TopCat.of ↥(cellInnerUnionOne Y ι f))
            (TopCat.ofHom (restrictCm q (cellInnerUnionOne Y ι f)))
          ≫ (cokernel.π (Work.Cohomology.inclChains (TopCat.of ↥(cellInnerUnionOne Y ι f))
                {y : ↥(cellInnerUnionOne Y ι f) |
                  (y : attachOneCells Y ι f) ∈ cellCompl Y ι f})
            ≫ coprodBase Y ι f)
      = (Work.Cohomology.chainMap ℤ (TopCat.of ↥(q ⁻¹' cellInnerUnionOne Y ι f))
            (TopCat.of ↥(cellInnerUnionOne Y ι f))
            (TopCat.ofHom (restrictCm q (cellInnerUnionOne Y ι f)))
          ≫ cokernel.π (Work.Cohomology.inclChains (TopCat.of ↥(cellInnerUnionOne Y ι f))
                {y : ↥(cellInnerUnionOne Y ι f) |
                  (y : attachOneCells Y ι f) ∈ cellCompl Y ι f}))
        ≫ coprodBase Y ι f := (Category.assoc _ _ _).symm
  have m10 : (Work.Cohomology.chainMap ℤ (TopCat.of ↥(q ⁻¹' cellInnerUnionOne Y ι f))
            (TopCat.of ↥(cellInnerUnionOne Y ι f))
            (TopCat.ofHom (restrictCm q (cellInnerUnionOne Y ι f)))
          ≫ cokernel.π (Work.Cohomology.inclChains (TopCat.of ↥(cellInnerUnionOne Y ι f))
                {y : ↥(cellInnerUnionOne Y ι f) |
                  (y : attachOneCells Y ι f) ∈ cellCompl Y ι f}))
        ≫ coprodBase Y ι f
      = (cokernel.π (Work.Cohomology.inclChains (TopCat.of ↥(q ⁻¹' cellInnerUnionOne Y ι f))
            {z : ↥(q ⁻¹' cellInnerUnionOne Y ι f) | (z : X) ∈ q ⁻¹' cellCompl Y ι f})
          ≫ midMapV q)
        ≫ coprodBase Y ι f := congrArg (fun t => t ≫ coprodBase Y ι f) g₃.symm
  have m11 : (cokernel.π (Work.Cohomology.inclChains (TopCat.of ↥(q ⁻¹' cellInnerUnionOne Y ι f))
            {z : ↥(q ⁻¹' cellInnerUnionOne Y ι f) | (z : X) ∈ q ⁻¹' cellCompl Y ι f})
          ≫ midMapV q)
        ≫ coprodBase Y ι f
      = cokernel.π (Work.Cohomology.inclChains (TopCat.of ↥(q ⁻¹' cellInnerUnionOne Y ι f))
            {z : ↥(q ⁻¹' cellInnerUnionOne Y ι f) | (z : X) ∈ q ⁻¹' cellCompl Y ι f})
        ≫ (midMapV q ≫ coprodBase Y ι f) := Category.assoc _ _ _
  exact m1.trans (m2.trans (m3.trans (m4.trans (m5.trans (m6.trans (m7.trans
    (m8.trans (m9.trans (m10.trans m11)))))))))

end

end Work.Serre.SPC.One
