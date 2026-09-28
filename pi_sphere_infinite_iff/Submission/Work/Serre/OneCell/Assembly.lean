import Mathlib
import Submission.Work.Serre.OneCell.Prelim
import Submission.Work.Serre.OneCell.Halves
import Submission.Work.Serre.OneCell.HalfVanishing
import Submission.Work.Serre.OneCell.compressRel_oneCellHalf
import Submission.Work.Serre.OneCell.iUnion_oneCellHalf
import Submission.Work.Serre.OneCell.isZeroRatH_iUnion_open
import Submission.Work.Serre.OneCell.isZero_ratH_cellInteriorOne
import Submission.Work.Serre.OneCell.isZero_ratH_preimage_cellInteriorOne
import Submission.Work.Serre.OneCell.isIso_ratH_zero_of_fibration
import Submission.Work.Serre.OneCell.pathConnectedSpace_of_ratH_zero_iso
import Submission.Work.Serre.OneCell.Transfer
import Submission.Work.Serre.CellStep.Tools

set_option synthInstance.maxHeartbeats 400000


/-!
# The absolute comparisons of the local model of the `1`-cell step

The local model `Work.Serre.OneCell.oneCellPerCell` compares the map of pairs
`(q⁻¹B, q⁻¹(B∖P)) ⟶ (B, B∖P)`, where `B = cellInnerUnionOne` is the union of the open cells and
`P = oneCellCentresOne` the set of their centres.  Here we assemble the two absolute comparisons
`H_k(q⁻¹B) ≅ H_k(B)` and `H_k(q⁻¹(B∖P)) ≅ H_k(B∖P)` needed by the five lemma:

* in degree `0` they are the `π₀`-bijections of `isIso_ratH_zero_of_fibration` (the fibres over `B`
  are path connected, because `H₀(fibre;ℚ) ≅ ℚ`);
* in positive degrees both sides vanish: `B` is the disjoint union of the open cells and `B∖P` of
  the halves of the cells, and each piece (and its preimage) is rationally acyclic — the cells by
  contractibility, the halves by the compression onto their midpoint, and the preimages by the
  compression engine for Serre fibrations.
-/

open CategoryTheory CategoryTheory.Limits
open scoped Topology

namespace Work.Serre.OneCell

open Work.Serre

noncomputable section

variable {Y : Type} [TopologicalSpace Y] {ι : Type} {f : ι → C(cellSphereZero, Y)}

/-- The union of the open cells with the cell centres removed. -/
def cellPunctured (Y : Type) [TopologicalSpace Y] (ι : Type) (f : ι → C(cellSphereZero, Y)) :
    Set (attachOneCells Y ι f) := cellInnerUnionOne Y ι f \ oneCellCentresOne Y ι f

/-- The acyclicity hypothesis on the fibres of a Serre fibration. -/
def FibreAcyclic (E : Type) [TopologicalSpace E] (q : C(E, attachOneCells Y ι f)) (N : ℕ) : Prop :=
  ∀ z : attachOneCells Y ι f,
    (∀ k : ℕ, 0 < k → k ≤ N → IsZero ((Work.Cohomology.singularChains ℚ
      (TopCat.of (Work.StemsB.fibre q z))).homology k)) ∧
    Nonempty ((Work.Cohomology.singularChains ℚ
      (TopCat.of (Work.StemsB.fibre q z))).homology 0 ≅ ModuleCat.of ℚ ℚ)

/-! ## The vanishing of `H_k` on the two sides -/

theorem isZero_ratH_cellInnerUnionOne (k : ℕ) (hk : 0 < k) :
    IsZero (ratH (TopCat.of ↥(cellInnerUnionOne Y ι f)) k) := by
  rw [cellInnerUnionOne_eq_iUnion_cellInteriorOne]
  exact isZeroRatH_iUnion_open (fun i => cellInteriorOne Y ι f i)
    (fun i => isOpen_cellInteriorOne Y ι f i)
    (fun i j hij => disjoint_cellInteriorOne f hij) k
    (fun i => isZero_ratH_cellInteriorOne Y ι f i k hk)

theorem isZero_ratH_preimage_cellInnerUnionOne {E : Type} [TopologicalSpace E]
    (q : C(E, attachOneCells Y ι f)) (hq : Work.StemsB.IsSerreFibration q) (N : ℕ)
    (hacyc : FibreAcyclic (Y := Y) (ι := ι) (f := f) E q N)
    (k : ℕ) (hk0 : 0 < k) (hkN : k ≤ N) :
    IsZero (ratH (TopCat.of ↥(q ⁻¹' cellInnerUnionOne Y ι f)) k) := by
  have hset : (⋃ i, q ⁻¹' cellInteriorOne Y ι f i) = q ⁻¹' cellInnerUnionOne Y ι f := by
    rw [← Set.preimage_iUnion, cellInnerUnionOne_eq_iUnion_cellInteriorOne]
  refine isZero_ratH_setCongr hset k ?_
  exact isZeroRatH_iUnion_open (fun i => q ⁻¹' cellInteriorOne Y ι f i)
    (fun i => (isOpen_cellInteriorOne Y ι f i).preimage q.continuous)
    (fun i j hij => Set.disjoint_left.mpr
      (fun x hx hx' => Set.disjoint_left.mp (disjoint_cellInteriorOne f hij) hx hx')) k
    (fun i => isZero_ratH_preimage_cellInteriorOne Y ι f q hq N hacyc i k hk0 hkN)

theorem isZero_ratH_cellPunctured (k : ℕ) (hk : 0 < k) :
    IsZero (ratH (TopCat.of ↥(cellPunctured Y ι f)) k) := by
  have hset : (⋃ p : ι × Bool, oneCellHalfPiece Y ι f p) = cellPunctured Y ι f :=
    iUnion_oneCellHalf Y ι f
  refine isZero_ratH_setCongr hset k ?_
  exact isZeroRatH_iUnion_open (fun p : ι × Bool => oneCellHalfPiece Y ι f p)
    (fun p => isOpen_oneCellHalf Y ι f p.1 p.2)
    (pairwiseDisjoint_oneCellHalf Y ι f) k
    (fun p => isZero_ratH_oneCellHalf Y ι f p.1 p.2 k hk)

theorem isZero_ratH_preimage_cellPunctured {E : Type} [TopologicalSpace E]
    (q : C(E, attachOneCells Y ι f)) (hq : Work.StemsB.IsSerreFibration q) (N : ℕ)
    (hacyc : FibreAcyclic (Y := Y) (ι := ι) (f := f) E q N)
    (k : ℕ) (hk0 : 0 < k) (hkN : k ≤ N) :
    IsZero (ratH (TopCat.of ↥(q ⁻¹' cellPunctured Y ι f)) k) := by
  have hset : (⋃ p : ι × Bool, q ⁻¹' oneCellHalfPiece Y ι f p) = q ⁻¹' cellPunctured Y ι f := by
    rw [← Set.preimage_iUnion, iUnion_oneCellHalf]
    rfl
  refine isZero_ratH_setCongr hset k ?_
  exact isZeroRatH_iUnion_open (fun p : ι × Bool => q ⁻¹' oneCellHalfPiece Y ι f p)
    (fun p => (isOpen_oneCellHalf Y ι f p.1 p.2).preimage q.continuous)
    (fun p r hpr => Set.disjoint_left.mpr
      (fun x hx hx' =>
        Set.disjoint_left.mp (pairwiseDisjoint_oneCellHalf Y ι f hpr) hx hx')) k
    (fun p => isZero_ratH_preimage_oneCellHalf Y ι f q hq N hacyc p.1 p.2 k hk0 hkN)

/-! ## The absolute comparisons -/

theorem isIso_ratHomologyMap_restrictTo_cellInnerUnionOne {E : Type} [TopologicalSpace E]
    (q : C(E, attachOneCells Y ι f)) (hq : Work.StemsB.IsSerreFibration q) (N : ℕ)
    (hacyc : FibreAcyclic (Y := Y) (ι := ι) (f := f) E q N) (k : ℕ) (hk : k ≤ N) :
    IsIso (ratHomologyMap (restrictTo q (cellInnerUnionOne Y ι f)) k) := by
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · subst hk0
    exact isIso_ratH_zero_of_fibration q hq (cellInnerUnionOne Y ι f)
      (fun z _ => pathConnectedSpace_of_ratH_zero_iso ((hacyc z).2))
  · exact Work.StemsB.isIso_of_isZero_of_isZero
      (isZero_ratH_preimage_cellInnerUnionOne q hq N hacyc k hkpos hk)
      (isZero_ratH_cellInnerUnionOne (Y := Y) (ι := ι) (f := f) k hkpos)

theorem isIso_ratHomologyMap_restrictTo_cellPunctured {E : Type} [TopologicalSpace E]
    (q : C(E, attachOneCells Y ι f)) (hq : Work.StemsB.IsSerreFibration q) (N : ℕ)
    (hacyc : FibreAcyclic (Y := Y) (ι := ι) (f := f) E q N) (k : ℕ) (hk : k ≤ N) :
    IsIso (ratHomologyMap (restrictTo q (cellPunctured Y ι f)) k) := by
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · subst hk0
    exact isIso_ratH_zero_of_fibration q hq (cellPunctured Y ι f)
      (fun z _ => pathConnectedSpace_of_ratH_zero_iso ((hacyc z).2))
  · exact Work.StemsB.isIso_of_isZero_of_isZero
      (isZero_ratH_preimage_cellPunctured q hq N hacyc k hkpos hk)
      (isZero_ratH_cellPunctured (Y := Y) (ι := ι) (f := f) k hkpos)

/-! ## The comparison in the sub-pair form -/

/-- The explicit form of `Work.Serre.OneCell.pairMapQ`: the relative chain map of the map of pairs
`(X,A) → (Y,B)` induced by `g`, written as a `relChainsRMapOf` so that it can be fed to the five
lemma `isIso_homologyMap_relChainsRMapOf_range`. -/
def pairMapExplicit {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (A : Set X) (B' : Set Y) (g : C(X, Y)) (hg : Set.MapsTo g A B') :
    Work.StemsB.relChainsR ℚ (TopCat.of X) A ⟶ Work.StemsB.relChainsR ℚ (TopCat.of Y) B' :=
  Work.Serre.relChainsRMapOf (R := ℚ) (TopCat.of X) (TopCat.of Y) A B' (TopCat.ofHom g)
    (TopCat.ofHom ⟨fun x => ⟨g x.1, hg x.2⟩, by fun_prop⟩) (by ext x; rfl)

def subPairMap {E : Type} [TopologicalSpace E] (q : C(E, attachOneCells Y ι f)) :
    C(↥{x : ↥(q ⁻¹' cellInnerUnionOne Y ι f) | (x : E) ∈ q ⁻¹' cellPunctured Y ι f},
      ↥{x : ↥(cellInnerUnionOne Y ι f) |
        (x : attachOneCells Y ι f) ∈ cellPunctured Y ι f}) :=
  ⟨fun x => ⟨⟨q x.1.1, x.1.2⟩, x.2⟩, by fun_prop⟩

theorem isIso_ratHomologyMap_subPair {E : Type} [TopologicalSpace E]
    (q : C(E, attachOneCells Y ι f)) (hq : Work.StemsB.IsSerreFibration q) (N : ℕ)
    (hacyc : FibreAcyclic (Y := Y) (ι := ι) (f := f) E q N) (k : ℕ) (hk : k ≤ N) :
    IsIso (ratHomologyMap (subPairMap q) k) := by
  have hUB : cellPunctured Y ι f ⊆ cellInnerUnionOne Y ι f := Set.sdiff_subset
  have hpre : q ⁻¹' cellPunctured Y ι f ⊆ q ⁻¹' cellInnerUnionOne Y ι f :=
    Set.preimage_mono hUB
  refine isIso_ratHomologyMap_of_homeo_square
    (eX := homeoSubtypeSubtype (X := E) hpre)
    (eY := homeoSubtypeSubtype (X := attachOneCells Y ι f) hUB)
    (g' := subPairMap q) (g := restrictTo q (cellPunctured Y ι f))
    (h := fun x => rfl) k ?_
  exact isIso_ratHomologyMap_restrictTo_cellPunctured q hq N hacyc k hk

/-- **The five lemma in the `pairMapQ` form**: the relative comparison of a map of pairs is an
isomorphism in degree `n` as soon as the two absolute comparisons are. -/
theorem isIso_pairMapQ_of {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (A : Set X)
    (B' : Set Y) (g : C(X, Y)) (hg : Set.MapsTo g A B') (n : ℕ)
    (hf : ∀ k : ℕ, k ≤ n →
      IsIso (HomologicalComplex.homologyMap
        (Work.Cohomology.chainMap ℚ (TopCat.of X) (TopCat.of Y) (TopCat.ofHom g)) k))
    (hg' : ∀ k : ℕ, k ≤ n →
      IsIso (ratHomologyMap (⟨fun x => ⟨g x.1, hg x.2⟩, by fun_prop⟩ : C(↥A, ↥B')) k)) :
    IsIso (HomologicalComplex.homologyMap (pairMapExplicit A B' g hg) n) := by
  unfold pairMapExplicit
  exact isIso_homologyMap_relChainsRMapOf_range A B' (TopCat.ofHom g)
    (TopCat.ofHom ⟨fun x => ⟨g x.1, hg x.2⟩, by fun_prop⟩) (by ext x; rfl) n hf hg'

end

end Work.Serre.OneCell
