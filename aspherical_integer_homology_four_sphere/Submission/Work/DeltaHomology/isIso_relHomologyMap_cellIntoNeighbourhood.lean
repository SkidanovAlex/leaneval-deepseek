import Mathlib
import Submission.Work.DeltaHomology.isIso_fold_cellClassMap
import Submission.Work.DeltaHomology.openCoverInclPair
import Submission.Work.HomologyExtra.isIso_relHomologyMap_pairHomOfHomeomorph
import Submission.Work.HomologyExtra.RelChainMapFunctor

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The cell pair inside the skeleton pair is a local neighbourhood pair

For a realized `Δ`-complex `R : DeltaRealization K X`, an `n`-simplex `σ` and the closed cell
`C = cell n σ ⊆ W = skelSet n`, the map of pairs

`cellIntoNeighbourhood R n σ : (C, C ∖ {b_σ}) ⟶ (W, W ∖ {b_σ})`

(the inclusion of the closed cell into the `n`-skeleton) induces an isomorphism on relative
homology in degree `n`.  Both pairs compute the local homology of the barycentre `b_σ` of `σ`,
so the map is an isomorphism.

The proof factors the inclusion through the *open* cell.  Write

* `U = {x : ↥W | (x : X) ∈ intCell n σ}` — the open cell of `σ`, viewed inside the skeleton; it
  is open in `↥W` (`isOpen_intCell_skelSet`), its complement being the union of the other closed
  cells of the skeleton and of the lower skeleta;
* `A = punctNeighbourhood n σ = {x : ↥W | (x : X) ≠ b_σ}`, also open.

Then `U ∪ A = ↥W`, so the open-cover excision `isIso_relHomologyMap_inclOpenCover` shows that the
inclusion `(U, U ∩ A) ⟶ (W, A)` is an isomorphism on relative homology; the same for the cell,
`isIso_relHomologyMap_inclOpenCover_cell`; and the two "open pieces" are identified by the
homeomorphism `↥(cellIntPiece) ≃ₜ ↥U`.  The composite of isomorphisms computes
`relHomologyMap ZMod n (cellIntoNeighbourhood R n σ)`.
-/

namespace Work.DeltaHomology

open CategoryTheory AlgebraicTopology CategoryTheory.Limits Convexity Work.Homology

noncomputable section

variable {K : DeltaCx} {X : TopCat}

/-! ## Two cells of the same dimension have disjoint interiors -/

/-- The (closed) cell of `τ` is disjoint from the *open* cell of `σ` when `σ ≠ τ`: the open cell
of `σ` is disjoint from the `(n-1)`-skeleton, and the closed cell of `τ` is covered by its open
cell together with the `(n-1)`-skeleton. -/
theorem intCell_disjoint_cell (R : DeltaRealization K X)
    (n : ℕ) {σ τ : Fin (K.card n)} (h : σ ≠ τ) :
    Disjoint (R.toDeltaSimplexMap.intCell n σ) (R.toDeltaSimplexMap.cell n τ) := by
  rw [Set.disjoint_left]
  intro x hx hx'
  have hxint : x ∈ R.toDeltaSimplexMap.intCell n σ := hx
  rw [DeltaSimplexMap.intCell_eq_sdiff] at hx
  by_cases hint : x ∈ R.toDeltaSimplexMap.intCell n τ
  · exact Set.disjoint_left.mp (intCell_disjoint R n h) hxint hint
  · have hmem : x ∈ ⋃ (j : {j : ℕ // j < n}), R.toDeltaSimplexMap.skelSet j.1 := by
      by_contra hcon
      exact hint (by rw [DeltaSimplexMap.intCell_eq_sdiff]; exact ⟨hx', hcon⟩)
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hmem
    exact hx.2 (Set.mem_iUnion.mpr ⟨j, hj⟩)

/-! ## A point off the lower skeleta lies in a top cell -/

/-- A point of the `n`-skeleton which lies in no lower skeleton lies in the closed cell of some
`n`-simplex. -/
theorem exists_cell_of_mem_skelSet (R : DeltaRealization K X) (n : ℕ) (x : X)
    (hx : x ∈ R.toDeltaSimplexMap.skelSet n)
    (hnot : ∀ j, j < n → x ∉ R.toDeltaSimplexMap.skelSet j) :
    ∃ σ : Fin (K.card n), x ∈ R.toDeltaSimplexMap.cell n σ := by
  obtain ⟨p, hp, hpd⟩ := (mem_skelSet_iff R n x).mp hx
  obtain ⟨d, idx, pt, hpos⟩ := p
  have hd : d = n := by
    rcases lt_or_eq_of_le hpd with hlt | heq
    · have hmem : x ∈ R.toDeltaSimplexMap.skelSet d := by
        rw [← hp]
        exact DeltaSimplexMap.real_mem_skelSet R.toDeltaSimplexMap ⟨d, idx, pt, hpos⟩
      exact absurd hmem (hnot d hlt)
    · exact heq
  obtain rfl : d = n := hd
  exact ⟨idx, ⟨pt, hp⟩⟩

/-- A point of the `n`-skeleton which lies in no lower skeleton and in no cell of another
`n`-simplex lies in the open cell of `σ`. -/
theorem mem_intCell_of_mem_skelSet (R : DeltaRealization K X) (n : ℕ) (σ : Fin (K.card n)) (x : X)
    (hx : x ∈ R.toDeltaSimplexMap.skelSet n)
    (hnot : ∀ j, j < n → x ∉ R.toDeltaSimplexMap.skelSet j)
    (hD : ∀ τ : Fin (K.card n), τ ≠ σ → x ∉ R.toDeltaSimplexMap.cell n τ) :
    x ∈ R.toDeltaSimplexMap.intCell n σ := by
  rw [DeltaSimplexMap.mem_intCell_iff]
  refine ⟨?_, hnot⟩
  obtain ⟨σ', hσ'⟩ := exists_cell_of_mem_skelSet R n x hx hnot
  by_cases h : σ' = σ
  · rwa [h] at hσ'
  · exact absurd hσ' (hD σ' h)

/-! ## The open cell is open in the skeleton -/

/-- The open cell of `σ`, viewed inside the `n`-skeleton, is open there: its complement in
`skelSet n` is the union of the other closed `n`-cells together with the `(n-1)`-skeleton, a
finite union of closed sets. -/
theorem isOpen_intCell_skelSet (R : DeltaRealization K X) (n : ℕ) (σ : Fin (K.card n)) :
    IsOpen {x : ↥(R.toDeltaSimplexMap.skelSet n) | (x : X) ∈ R.toDeltaSimplexMap.intCell n σ} := by
  haveI : T2Space X := R.t2
  have hD : IsClosed (⋃ (τ : {τ : Fin (K.card n) // τ ≠ σ}),
      {x : ↥(R.toDeltaSimplexMap.skelSet n) | (x : X) ∈ R.toDeltaSimplexMap.cell n τ.1}) :=
    isClosed_iUnion_of_finite (fun τ =>
      (isCompact_range (R.toDeltaSimplexMap.cls n τ.1).continuous).isClosed.preimage
        continuous_subtype_val)
  haveI : Finite {j : ℕ // j < n} := Set.finite_Iio n
  have hE : IsClosed (⋃ (j : {j : ℕ // j < n}),
      {x : ↥(R.toDeltaSimplexMap.skelSet n) | (x : X) ∈ R.toDeltaSimplexMap.skelSet j.1}) :=
    isClosed_iUnion_of_finite (fun j => (isClosed_skelSet R j.1).preimage continuous_subtype_val)
  have hset : {x : ↥(R.toDeltaSimplexMap.skelSet n) | (x : X) ∈ R.toDeltaSimplexMap.intCell n σ} =
      ((⋃ (τ : {τ : Fin (K.card n) // τ ≠ σ}),
          {x : ↥(R.toDeltaSimplexMap.skelSet n) | (x : X) ∈ R.toDeltaSimplexMap.cell n τ.1})
       ∪ (⋃ (j : {j : ℕ // j < n}),
          {x : ↥(R.toDeltaSimplexMap.skelSet n) | (x : X) ∈ R.toDeltaSimplexMap.skelSet j.1}))ᶜ := by
    ext x
    constructor
    · intro hx
      rw [Set.mem_compl_iff, Set.mem_union, not_or]
      constructor
      · rw [Set.mem_iUnion]
        rintro ⟨τ, hτ⟩
        exact Set.disjoint_left.mp
          (intCell_disjoint_cell (R := R) (n := n) (σ := σ) (τ := τ.1) (Ne.symm τ.2)) hx hτ
      · rw [Set.mem_iUnion]
        rintro ⟨j, hj⟩
        exact R.toDeltaSimplexMap.intCell_subset_compl_skelSet j.2 σ hx hj
    · intro hx
      rw [Set.mem_compl_iff, Set.mem_union, not_or] at hx
      obtain ⟨hxD, hxE⟩ := hx
      exact mem_intCell_of_mem_skelSet R n σ (x : X) x.2
        (fun j hj h => hxE (Set.mem_iUnion.mpr ⟨⟨j, hj⟩, h⟩))
        (fun τ hτ h => hxD (Set.mem_iUnion.mpr ⟨⟨τ, hτ⟩, h⟩))
  rw [hset]
  exact (hD.union hE).isOpen_compl

/-! ## Maps of pairs with the same underlying map -/

/-- Two maps of pairs with the same underlying continuous map are equal (the `mapsTo` field is a
proposition). -/
theorem pairHom_ext_of_hom_eq {X Y : TopCat} {A : Set X} {B : Set Y}
    {Φ Ψ : PairHom X Y A B} (h : Φ.hom = Ψ.hom) : Φ = Ψ := by
  obtain ⟨f, hf⟩ := Φ
  obtain ⟨g, hg⟩ := Ψ
  subst h
  rw [Subsingleton.elim hf hg]

/-! ## The local pair of the cell inside the local pair of the skeleton -/

/-- **The inclusion of the cell pair into the local neighbourhood pair of the skeleton is an
isomorphism on relative homology.**  The inclusion `cellIntoNeighbourhood R n σ` factors through
the open cell of `σ` (inside the skeleton), where it becomes an excision inclusion, and the cell
pair is homeomorphic to the open-cell pair by `cellIntPiece`. -/
theorem isIso_relHomologyMap_cellIntoNeighbourhood {K : Work.DeltaHomology.DeltaCx} {X : TopCat}
    (R : Work.DeltaHomology.DeltaRealization K X) (n : ℕ) (σ : Fin (K.card n)) :
    CategoryTheory.IsIso (Work.Homology.relHomologyMap Work.Homology.ZMod n
      (Work.DeltaHomology.DeltaRealization.cellIntoNeighbourhood R n σ)) := by
  haveI : T1Space X := R.t2.t1Space
  let U : Set ↥(R.toDeltaSimplexMap.skelSet n) :=
    {x | (x : X) ∈ R.toDeltaSimplexMap.intCell n σ}
  let A : Set ↥(R.toDeltaSimplexMap.skelSet n) := R.punctNeighbourhood n σ
  have hU : IsOpen U := isOpen_intCell_skelSet R n σ
  have hA : IsOpen A := by
    have h : A = (fun x : ↥(R.toDeltaSimplexMap.skelSet n) => (x : X)) ⁻¹'
        ({R.toDeltaSimplexMap.cellBarycenter n σ}ᶜ : Set X) := by
      ext x; rfl
    rw [h]
    exact (isOpen_compl_singleton (x := R.toDeltaSimplexMap.cellBarycenter n σ)).preimage
      continuous_subtype_val
  have hcov : U ∪ A = Set.univ := by
    ext x
    simp only [Set.mem_union, Set.mem_univ, iff_true]
    by_cases hx : (x : X) = R.toDeltaSimplexMap.cellBarycenter n σ
    · left; show (x : X) ∈ R.toDeltaSimplexMap.intCell n σ; rw [hx]
      exact DeltaSimplexMap.cellBarycenter_mem_intCell R n σ
    · right; exact hx
  let B : Set ↥U := {y | (y : ↥(R.toDeltaSimplexMap.skelSet n)) ∈ A}
  -- the two excision inclusions
  have hβ : IsIso (relHomologyMap ZMod n
      (PairHom.inclOpenCover (X := TopCat.of (R.toDeltaSimplexMap.skelSet n)) U A)) :=
    isIso_relHomologyMap_inclOpenCover hU hA hcov n
  have hγ : IsIso (relHomologyMap ZMod n
      (PairHom.inclOpenCover (X := TopCat.of (R.toDeltaSimplexMap.cell n σ))
        (cellIntPiece R n σ) (cellPunctPiece R n σ))) :=
    isIso_relHomologyMap_inclOpenCover_cell R n n σ
  -- the homeomorphism between the two "open cell" pieces
  let κe : ↥(cellIntPiece R n σ) ≃ₜ ↥U :=
    { toFun := fun x => ⟨⟨(x.1.1 : X), R.toDeltaSimplexMap.cell_subset_skelSet σ x.1.2⟩, x.2⟩
      invFun := fun y =>
        ⟨⟨(y.1.1 : X), DeltaSimplexMap.intCell_subset_cell R.toDeltaSimplexMap n σ y.2⟩, y.2⟩
      left_inv := fun x => Subtype.ext (Subtype.ext rfl)
      right_inv := fun y => Subtype.ext (Subtype.ext rfl)
      continuous_toFun := Continuous.subtype_mk
        (Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) fun _ => _)
        fun _ => _
      continuous_invFun := Continuous.subtype_mk
        (Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) fun _ => _)
        fun _ => _ }
  have he : ∀ x : ↥(cellIntPiece R n σ),
      x ∈ {y : ↥(cellIntPiece R n σ) |
        (y : ↥(R.toDeltaSimplexMap.cell n σ)) ∈ cellPunctPiece R n σ} ↔ κe x ∈ B := by
    intro x
    rw [cellPunctPiece_eq_compl_singleton]
    rfl
  let κpair : PairHom (TopCat.of ↥(cellIntPiece R n σ)) (TopCat.of ↥U)
      {y : ↥(cellIntPiece R n σ) |
        (y : ↥(R.toDeltaSimplexMap.cell n σ)) ∈ cellPunctPiece R n σ} B :=
    Work.HomologyExtra.pairHomOfHomeomorph
      (X := TopCat.of ↥(cellIntPiece R n σ)) (Y := TopCat.of ↥U) κe he
  have hκ : IsIso (relHomologyMap ZMod n κpair) :=
    Work.HomologyExtra.isIso_relHomologyMap_pairHomOfHomeomorph
      (X := TopCat.of ↥(cellIntPiece R n σ)) (Y := TopCat.of ↥U) κe he n
  -- both ways round are the same map of pairs
  have hsq : (DeltaRealization.cellIntoNeighbourhood R n σ).comp
        (PairHom.inclOpenCover (X := TopCat.of (R.toDeltaSimplexMap.cell n σ))
          (cellIntPiece R n σ) (cellPunctPiece R n σ))
      = (PairHom.inclOpenCover (X := TopCat.of (R.toDeltaSimplexMap.skelSet n)) U A).comp κpair := by
    apply pairHom_ext_of_hom_eq
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro x
    apply Subtype.ext
    rfl
  have hcomm : relHomologyMap ZMod n
        (PairHom.inclOpenCover (X := TopCat.of (R.toDeltaSimplexMap.cell n σ))
          (cellIntPiece R n σ) (cellPunctPiece R n σ))
      ≫ relHomologyMap ZMod n (DeltaRealization.cellIntoNeighbourhood R n σ)
      = relHomologyMap ZMod n κpair
        ≫ relHomologyMap ZMod n
            (PairHom.inclOpenCover (X := TopCat.of (R.toDeltaSimplexMap.skelSet n)) U A) := by
    rw [← Work.HomologyExtra.relHomologyMap_comp, ← Work.HomologyExtra.relHomologyMap_comp, hsq]
  have key : relHomologyMap ZMod n (DeltaRealization.cellIntoNeighbourhood R n σ)
      = inv (relHomologyMap ZMod n
          (PairHom.inclOpenCover (X := TopCat.of (R.toDeltaSimplexMap.cell n σ))
            (cellIntPiece R n σ) (cellPunctPiece R n σ)))
        ≫ relHomologyMap ZMod n κpair
        ≫ relHomologyMap ZMod n
            (PairHom.inclOpenCover (X := TopCat.of (R.toDeltaSimplexMap.skelSet n)) U A) := by
    rw [← Category.id_comp (relHomologyMap ZMod n (DeltaRealization.cellIntoNeighbourhood R n σ)),
      ← IsIso.inv_hom_id (relHomologyMap ZMod n
          (PairHom.inclOpenCover (X := TopCat.of (R.toDeltaSimplexMap.cell n σ))
            (cellIntPiece R n σ) (cellPunctPiece R n σ))),
      Category.assoc, hcomm]
  rw [key]
  haveI := hγ
  haveI := hκ
  haveI := hβ
  infer_instance

end

end Work.DeltaHomology
