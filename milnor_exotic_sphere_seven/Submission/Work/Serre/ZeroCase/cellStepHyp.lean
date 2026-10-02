import Mathlib
import Submission.Work.Serre.SPC.Defs
import Submission.Work.Serre.SPC.asmDefs
import Submission.Work.Serre.SPC.cellPieceStrong
import Submission.Work.Serre.SPC.cubeStrong
import Submission.Work.Serre.SPC.discStrong
import Submission.Work.Serre.cellStep
import Submission.Work.Serre.CellStep.cellPieceIso
import Submission.Work.Serre.CellStep.csModelIso
import Submission.Work.Serre.CellStep.sigmaAdditivity
import Submission.Work.Serre.CellStep.Geom
import Submission.Work.Serre.CellStep.Tools
import Submission.Work.Serre.CellStep.Model
import Submission.Work.Serre.CellStep.Piece
import Submission.Work.Serre.CellStep.compressRel_cellU
import Submission.Work.Serre.CellStep.sigmaHomeo
import Submission.Work.Serre.SPC.One.sigmaPairMapAdditivity

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The strengthened cell step `Work.Serre.SPC.CellStepHyp`

This file proves the contract `Work.Serre.SPC.CellStepHyp`: for a Serre fibration `q : X → Γ'`
over a space `Γ'` obtained from `Γ` by attaching cells of dimension `D ≥ 2`, with fibres
homologically `φ`-connected, the map of pairs `(X, q⁻¹Γ) → (Γ', Γ)` induced by `q`
(`Work.Serre.cellStepAttachMap D Γ ι f X q`) is an isomorphism on integral homology in degrees `< D + φ`
**and surjective in degree `D + φ`**.

The isomorphism statement in the stable range is `Work.Serre.cellStep`, whose proof is independent
of this file.  Here we add the surjectivity in the boundary degree, by assembling the *per-piece*
statement `Work.Serre.SPC.cellPieceSurj` along the cover decomposition of
`Submission/Work/Serre/SPC/asmDefs.lean`:

* the map `asmCs` of the cell step sits in the commutative diagram of `asmDefs` whose other maps
  are `asmAX`/`asmAB` (the compressions of the relative part from `Γ` to `cellU f (3/4)`),
  `asmEX`/`asmEB` (excision for the open cover `{cellV f 1, cellU f (3/4)}`) and
  `asmPhiX`/`asmPhiB` (the splitting of the union of the open cells into the disjoint union of the
  pieces), with `asmP` the coproduct of the per-piece maps;
* all these maps except `asmCs`, `asmUmap`, `asmW` and `asmP` are quasi-isomorphisms, so
  surjectivity in any degree transfers along the three squares `asmSq1`, `asmSq2`, `asmSq3`
  (`Work.Serre.SPC.surjective_homologyMap_iff_of_square`);
* a coproduct of surjections is surjective
  (`Work.Serre.SPC.One.sigmaPairMapAdditivity`).

The whole computation is carried out in degree `(D - 2) + 2 + φ`, which is the degree delivered by
the per-piece statement; at the end the substitution `D = (D - 2) + 2` (available since `D ≥ 2`)
makes it definitionally equal to the degree `D + φ` of the contract.  The `unfold`s are needed
because the `whnf` of the composite definitions `asmAX`, …, `asmPhiB` is expensive, and the
explicit `TopCat.of ↥…` arguments of `Work.StemsB.isIso_relChainsMapOf_homeomorph` avoid the
coercion inference that otherwise diverges.
-/

set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open scoped Topology unitInterval
open CategoryTheory CategoryTheory.Limits

namespace Work.Serre.ZeroCase

noncomputable section

open Work.RatHurewicz

/-! ## The per-piece map as a map of pairs -/

/-- The per-piece map `Work.Serre.cellPieceMap` is the relative chain map of the projection of the
piece, in the `Work.Serre.pairMap` presentation: the two definitions only differ in the bookkeeping
of the relative parts (the underlying maps of spaces are the same). -/
theorem cellPieceMap_eq_pairMap (D : ℕ) (Γ : Type) [TopologicalSpace Γ] (ι : Type)
    (f : ι → C(cellSphere (D - 2), Γ)) (α : ι) {X : Type} [TopologicalSpace X]
    (q : C(X, attachCells (D - 2) Γ ι f)) :
    Work.Serre.cellPieceMap (D - 2) Γ ι f α q
      = Work.Serre.pairMap (Work.Serre.CellStep.cpSrcRel f α q)
          (Work.Serre.CellStep.cpTarRel f α) (Work.Serre.SPC.asmPieceFun (D := D) f q α)
          (Work.Serre.SPC.asmPieceFun_mem (D := D) f q α) := by
  have hmap : Work.Serre.CellStep.cpProj f α q
      = TopCat.ofHom (Work.Serre.SPC.asmPieceFun (D := D) f q α) := by
    apply TopCat.ext
    intro x
    rfl
  rw [Work.Serre.CellStep.cellPieceMap_eq_stems, Work.Serre.pairMap,
    Work.Serre.CellStep.stems_eq_cohom]
  exact Work.Serre.SPC.relChainsMapOf_congr' _ _ hmap (by
    apply TopCat.ext
    intro x
    rfl) _ _

/-! ## Surjectivity of a coproduct of maps of pairs -/

/-- **A coproduct of surjections is surjective.**  The surjectivity half of
`Work.Serre.SPC.One.sigmaPairMapAdditivity`, restated for the relative chain map
`Work.Serre.sigmaPairMap` of a family of maps of pairs (the two definitions are the same, and the
additivity theorem is stated for the `SPC.One` copy). -/
theorem sigmaPairMap_surjective_of_pieces {ι : Type} {X Y : ι → Type} [∀ i, TopologicalSpace (X i)]
    [∀ i, TopologicalSpace (Y i)] (A : ∀ i, Set (X i)) (B : ∀ i, Set (Y i))
    (g : ∀ i, C(X i, Y i)) (hg : ∀ i, Set.MapsTo (g i) (A i) (B i)) (m : ℕ)
    (h : ∀ i, Function.Surjective (HomologicalComplex.homologyMap
      (Work.Serre.pairMap (A i) (B i) (g i) (hg i)) m).hom) :
    Function.Surjective (HomologicalComplex.homologyMap
      (Work.Serre.sigmaPairMap X Y A B g hg) m).hom := by
  have h' : ∀ i, Function.Surjective (HomologicalComplex.homologyMap
      (Work.Serre.SPC.One.pairMap (A i) (B i) (g i) (hg i)) m).hom := fun i => by
    rw [Work.Serre.SPC.One.pairMap_eq]
    exact h i
  have hσ := (Work.Serre.SPC.One.sigmaPairMapAdditivity A B g hg).2 m h'
  rwa [Work.Serre.SPC.One.sigmaPairMap_eq] at hσ

/-! ## The per-piece surjectivity, in the `pairMap` presentation -/

/-- The per-piece statement `Work.Serre.SPC.cellPieceSurj`, transported to the `Work.Serre.pairMap`
presentation used by the assembly (`Work.Serre.SPC.asmP`).  The degree is the one delivered by
`cellPieceSurj`, namely `(D - 2) + 2 + φ`. -/
theorem cellPieceMap_pairMap_surj (D : ℕ) (Γ : Type) [TopologicalSpace Γ] (ι : Type)
    (f : ι → C(cellSphere (D - 2), Γ)) (α : ι) {X : Type} [TopologicalSpace X]
    (q : C(X, attachCells (D - 2) Γ ι f)) (hq : Work.StemsB.IsSerreFibration q) (φ : ℕ)
    (hfib : ∀ y : attachCells (D - 2) Γ ι f, ∀ j : ℕ, 0 < j → j < φ →
      CategoryTheory.Limits.IsZero ((Work.Cohomology.singularChains ℤ
        (TopCat.of (Work.StemsB.fibre q y))).homology j))
    (h0 : ∀ y : attachCells (D - 2) Γ ι f,
      CategoryTheory.IsIso (TopCat.singularHomology₀ε (TopCat.of (Work.StemsB.fibre q y))
        (ModuleCat.of ℤ ℤ))) :
    Function.Surjective (HomologicalComplex.homologyMap
      (Work.Serre.pairMap (Work.Serre.CellStep.cpSrcRel f α q)
        (Work.Serre.CellStep.cpTarRel f α) (Work.Serre.SPC.asmPieceFun (D := D) f q α)
        (Work.Serre.SPC.asmPieceFun_mem (D := D) f q α)) (((D - 2) + 2) + φ)).hom := by
  rw [← cellPieceMap_eq_pairMap (D := D) (Γ := Γ) (ι := ι) (f := f) (α := α) (q := q)]
  exact Work.Serre.SPC.cellPieceSurj (D - 2) Γ ι f α q hq φ hfib h0

/-! ## The surjectivity of the cell-step map in the boundary degree -/

/-- **The cell-step map is surjective in degree `D + φ`.**  Assembled from the per-piece statements
`Work.Serre.SPC.cellPieceSurj` along the cover decomposition of
`Submission/Work/Serre/SPC/asmDefs.lean`.  The degree is written `(D - 2) + 2 + φ`, which the
caller converts into `D + φ` using `D ≥ 2`. -/
theorem cellStepMap_surjective (D : ℕ) (hD : 2 ≤ D) (Γ : Type) [TopologicalSpace Γ] (ι : Type)
    (f : ι → C(cellSphere (D - 2), Γ)) (X : Type) [TopologicalSpace X]
    (q : C(X, attachCells (D - 2) Γ ι f)) (hq : Work.StemsB.IsSerreFibration q) (φ : ℕ)
    (hfib : ∀ y : attachCells (D - 2) Γ ι f, ∀ j : ℕ, 0 < j → j < φ →
      CategoryTheory.Limits.IsZero ((Work.Cohomology.singularChains ℤ
        (TopCat.of (Work.StemsB.fibre q y))).homology j))
    (h0 : ∀ y : attachCells (D - 2) Γ ι f,
      CategoryTheory.IsIso (TopCat.singularHomology₀ε (TopCat.of (Work.StemsB.fibre q y))
        (ModuleCat.of ℤ ℤ))) :
    Function.Surjective (HomologicalComplex.homologyMap
      (Work.Serre.cellStepAttachMap D Γ ι f X q) ((D - 2) + 2 + φ)).hom := by
  -- the radial compression of `cellU f (3/4)` onto the old part
  have hcomp : ∀ d, Work.RatHurewicz.CompressRel ↥(cellU f (3/4))
      {x : ↥(cellU f (3/4)) | (x : attachCells (D - 2) Γ ι f) ∈
        Set.range (attachIncl (D - 2) Γ ι f)} d :=
    fun d => Work.Serre.CellStep.compressRel_cellU (D - 2) Γ ι f (ρ := 3/4)
      (by norm_num) (by norm_num) d
  -- ### the vertical maps of the assembly diagram are quasi-isomorphisms
  have hAX : CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (Work.Serre.SPC.asmAX (D := D) (Γ := Γ) (ι := ι) (X := X) (f := f) (q := q))
      ((D - 2) + 2 + φ)) := by
    unfold Work.Serre.SPC.asmAX
    exact Work.Serre.CellStep.isIso_relCokerMap_of_acyclic (X := TopCat.of X)
      (Set.preimage_mono (Work.Serre.SPC.asmOld_subset_cellU f))
      (fun j => Work.Serre.isZero_relChains_preimage_of_compress q hq
        (Work.Serre.SPC.asmOld_subset_cellU f) hcomp j) ((D - 2) + 2 + φ)
  have hAB : CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (Work.Serre.SPC.asmAB (D := D) (Γ := Γ) (ι := ι) (f := f)) ((D - 2) + 2 + φ)) := by
    unfold Work.Serre.SPC.asmAB
    exact Work.Serre.CellStep.isIso_relCokerMap_of_acyclic
      (X := TopCat.of (attachCells (D - 2) Γ ι f))
      (Work.Serre.SPC.asmOld_subset_cellU f)
      (fun j => Work.Serre.isZero_relChains_of_compress hcomp j) ((D - 2) + 2 + φ)
  have hEX : CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (Work.Serre.SPC.asmEX (D := D) (Γ := Γ) (ι := ι) (X := X) (f := f) (q := q))
      ((D - 2) + 2 + φ)) := by
    unfold Work.Serre.SPC.asmEX
    have hcov : q ⁻¹' cellV f 1 ∪ q ⁻¹' cellU f (3/4) = Set.univ := by
      rw [← Set.preimage_union, Set.union_comm,
        cellU_union_cellV (f := f) (ρ := 3/4) (R := 1) (by norm_num), Set.preimage_univ]
    exact Work.Cohomology.excision_relChainsMap_isIso (TopCat.of X) (q ⁻¹' cellV f 1)
      (q ⁻¹' cellU f (3/4)) ((isOpen_cellV (f := f) (R := 1) (by norm_num)).preimage q.continuous)
      ((isOpen_cellU (f := f) (ρ := 3/4) (by norm_num)).preimage q.continuous) hcov ((D - 2) + 2 + φ)
  have hEB : CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (Work.Serre.SPC.asmEB (D := D) (Γ := Γ) (ι := ι) (f := f)) ((D - 2) + 2 + φ)) := by
    unfold Work.Serre.SPC.asmEB
    have hcov : cellV f 1 ∪ cellU f (3/4) = Set.univ := by
      rw [Set.union_comm, cellU_union_cellV (f := f) (ρ := 3/4) (R := 1) (by norm_num)]
    exact Work.Cohomology.excision_relChainsMap_isIso
      (TopCat.of (attachCells (D - 2) Γ ι f)) (cellV f 1) (cellU f (3/4))
      (isOpen_cellV (f := f) (R := 1) (by norm_num))
      (isOpen_cellU (f := f) (ρ := 3/4) (by norm_num)) hcov ((D - 2) + 2 + φ)
  have hPhiX : CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (Work.Serre.SPC.asmPhiX (D := D) (Γ := Γ) (ι := ι) (X := X) (f := f) (q := q))
      ((D - 2) + 2 + φ)) := by
    haveI : CategoryTheory.IsIso
        (Work.Serre.SPC.asmPhiX (D := D) (Γ := Γ) (ι := ι) (X := X) (f := f) (q := q)) := by
      unfold Work.Serre.SPC.asmPhiX
      exact Work.StemsB.isIso_relChainsMapOf_homeomorph
        (X := TopCat.of ↥(q ⁻¹' cellV f 1))
        (Y := TopCat.of (Σ α, ↥(q ⁻¹' Work.Serre.pieceSet (D - 2) Γ ι f α)))
        (Work.Serre.SPC.asmSigX f q) (Work.Serre.SPC.asmUVx f q) (Work.Serre.SPC.asmPieceRelX f q)
        (Work.Serre.SPC.asmUVx_rel f q)
    exact Functor.map_isIso (HomologicalComplex.homologyFunctor (ModuleCat ℤ)
      (ComplexShape.down ℕ) ((D - 2) + 2 + φ))
      (Work.Serre.SPC.asmPhiX (D := D) (Γ := Γ) (ι := ι) (X := X) (f := f) (q := q))
  have hPhiB : CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (Work.Serre.SPC.asmPhiB (D := D) (Γ := Γ) (ι := ι) (f := f)) ((D - 2) + 2 + φ)) := by
    haveI : CategoryTheory.IsIso
        (Work.Serre.SPC.asmPhiB (D := D) (Γ := Γ) (ι := ι) (f := f)) := by
      unfold Work.Serre.SPC.asmPhiB
      exact Work.StemsB.isIso_relChainsMapOf_homeomorph
        (X := TopCat.of ↥(cellV f 1))
        (Y := TopCat.of (Σ α, ↥(Work.Serre.pieceSet (D - 2) Γ ι f α)))
        (Work.Serre.SPC.asmSigB f) (Work.Serre.SPC.asmUV f) (Work.Serre.SPC.asmPieceRelB f)
        (Work.Serre.SPC.asmUV_rel f)
    exact Functor.map_isIso (HomologicalComplex.homologyFunctor (ModuleCat ℤ)
      (ComplexShape.down ℕ) ((D - 2) + 2 + φ))
      (Work.Serre.SPC.asmPhiB (D := D) (Γ := Γ) (ι := ι) (f := f))
  -- ### surjectivity of the coproduct of the per-piece maps
  have hP : Function.Surjective (HomologicalComplex.homologyMap
      (Work.Serre.SPC.asmP (D := D) (Γ := Γ) (ι := ι) (X := X) (f := f) (q := q))
      ((D - 2) + 2 + φ)).hom := by
    unfold Work.Serre.SPC.asmP
    refine sigmaPairMap_surjective_of_pieces
      (X := fun α => ↥(q ⁻¹' Work.Serre.pieceSet (D - 2) Γ ι f α))
      (Y := fun α => ↥(Work.Serre.pieceSet (D - 2) Γ ι f α))
      (A := fun α => Work.Serre.CellStep.cpSrcRel f α q)
      (B := fun α => Work.Serre.CellStep.cpTarRel f α)
      (g := fun α => Work.Serre.SPC.asmPieceFun (D := D) f q α)
      (hg := fun α => Work.Serre.SPC.asmPieceFun_mem (D := D) f q α)
      ((D - 2) + 2 + φ) ?_
    intro α
    exact cellPieceMap_pairMap_surj D Γ ι f α q hq φ hfib h0
  -- ### the transfer along the three squares
  have hW : Function.Surjective (HomologicalComplex.homologyMap
      (Work.Serre.SPC.asmW (D := D) (Γ := Γ) (ι := ι) (X := X) (f := f) (q := q))
      ((D - 2) + 2 + φ)).hom :=
    (Work.Serre.SPC.surjective_homologyMap_iff_of_square
      (Work.Serre.SPC.asmPhiX (D := D) (Γ := Γ) (ι := ι) (X := X) (f := f) (q := q))
      (Work.Serre.SPC.asmPhiB (D := D) (Γ := Γ) (ι := ι) (f := f))
      (Work.Serre.SPC.asmW (D := D) (Γ := Γ) (ι := ι) (X := X) (f := f) (q := q))
      (Work.Serre.SPC.asmP (D := D) (Γ := Γ) (ι := ι) (X := X) (f := f) (q := q))
      (Work.Serre.SPC.asmSq3 (D := D) (Γ := Γ) (ι := ι) (X := X) (f := f) (q := q))
      ((D - 2) + 2 + φ) hPhiX hPhiB).mpr hP
  have hU : Function.Surjective (HomologicalComplex.homologyMap
      (Work.Serre.SPC.asmUmap (D := D) (Γ := Γ) (ι := ι) (X := X) (f := f) (q := q))
      ((D - 2) + 2 + φ)).hom :=
    (Work.Serre.SPC.surjective_homologyMap_iff_of_square
      (Work.Serre.SPC.asmEX (D := D) (Γ := Γ) (ι := ι) (X := X) (f := f) (q := q))
      (Work.Serre.SPC.asmEB (D := D) (Γ := Γ) (ι := ι) (f := f))
      (Work.Serre.SPC.asmW (D := D) (Γ := Γ) (ι := ι) (X := X) (f := f) (q := q))
      (Work.Serre.SPC.asmUmap (D := D) (Γ := Γ) (ι := ι) (X := X) (f := f) (q := q))
      (Work.Serre.SPC.asmSq2 (D := D) (Γ := Γ) (ι := ι) (X := X) (f := f) (q := q))
      ((D - 2) + 2 + φ) hEX hEB).mp hW
  have hCs : Function.Surjective (HomologicalComplex.homologyMap
      (Work.Serre.SPC.asmCs (D := D) (Γ := Γ) (ι := ι) (X := X) (f := f) (q := q))
      ((D - 2) + 2 + φ)).hom :=
    (Work.Serre.SPC.surjective_homologyMap_iff_of_square
      (Work.Serre.SPC.asmAX (D := D) (Γ := Γ) (ι := ι) (X := X) (f := f) (q := q))
      (Work.Serre.SPC.asmAB (D := D) (Γ := Γ) (ι := ι) (f := f))
      (Work.Serre.SPC.asmCs (D := D) (Γ := Γ) (ι := ι) (X := X) (f := f) (q := q))
      (Work.Serre.SPC.asmUmap (D := D) (Γ := Γ) (ι := ι) (X := X) (f := f) (q := q))
      (Work.Serre.SPC.asmSq1 (D := D) (Γ := Γ) (ι := ι) (X := X) (f := f) (q := q))
      ((D - 2) + 2 + φ) hAX hAB).mpr hU
  simpa [Work.Serre.SPC.asmCs] using hCs

/-! ## The contract -/

theorem cellStepHyp : Work.Serre.SPC.CellStepHyp := by
  intro D hD Γ _ ι f X _ q hq φ hfib h0
  -- replace `D` by `n + 2`, which makes the degree `(D - 2) + 2 + φ` definitionally `D + φ`
  obtain ⟨n, hn⟩ : ∃ n, D = n + 2 := ⟨D - 2, (Nat.sub_add_cancel hD).symm⟩
  subst hn
  exact ⟨fun i hi => Work.Serre.cellStep (n + 2) (by omega) Γ ι f X q hq φ hfib h0 i hi,
    cellStepMap_surjective (n + 2) (by omega) Γ ι f X q hq φ hfib h0⟩

end

end Work.Serre.ZeroCase
