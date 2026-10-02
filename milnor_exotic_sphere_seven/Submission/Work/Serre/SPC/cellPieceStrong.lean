import Mathlib
import Submission.Work.Serre.CellStep.cellPieceIso
import Submission.Work.Serre.CellStep.ModelReduction
import Submission.Work.Serre.SPC.modelPiece
import Submission.Work.Serre.SPC.discDefs
import Submission.Work.Serre.SPC.discStrong

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The strong per-piece statement of the cell step

The per-piece map `Work.Serre.cellPieceMap n Γ ι f α q` of the cell cover is an isomorphism on
integral homology in degrees `< (n+2) + φ` and *surjective* in degree `(n+2) + φ`, for a Serre
fibration `q` whose fibre is homologically `φ`-connected.

The isomorphism part in degrees below `(n+2)+φ` is `Work.Serre.CellStep.cellPieceIso`; here we add
the surjectivity in the boundary degree.  The route is the same one: the disc statement
`Work.Serre.SPC.discPairStrong` (in its surjectivity half) is transported to the model per-cell map
`csModelMap` by the chain of relative-part compressions of `CellStep/ModelReduction.lean`, and then
to `cellPieceMap` along the characteristic-map homeomorphism of pairs
(`Work.Serre.CellStep.cpSrcRelMap`/`cpTarRelMap`).

The only new ingredient is the transfer of surjectivity across a commutative square of chain
complexes whose vertical maps are homology isomorphisms, the exact analogue of
`Work.Serre.CellStep.isIso_homologyMap_iff_of_square`.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open scoped Topology unitInterval
open CategoryTheory CategoryTheory.Limits

namespace Work.Serre.SPC

noncomputable section

open Work.RatHurewicz

/-! ## Transfer of surjectivity along a commutative square -/

/-- **Surjectivity transfers across a commutative square of chain complexes** whose vertical maps
are homology isomorphisms in the given degree.  The exact analogue of
`Work.Serre.CellStep.isIso_homologyMap_iff_of_square`. -/
theorem surjective_homologyMap_iff_of_square {C₁ C₂ B₁ B₂ : ChainComplex (ModuleCat ℤ) ℕ}
    (h : C₁ ⟶ C₂) (g : B₁ ⟶ B₂) (u : C₁ ⟶ B₁) (v : C₂ ⟶ B₂)
    (hsq : h ≫ v = u ≫ g) (k : ℕ)
    (hh : IsIso (HomologicalComplex.homologyMap h k))
    (hg : IsIso (HomologicalComplex.homologyMap g k)) :
    Function.Surjective (HomologicalComplex.homologyMap u k).hom ↔
      Function.Surjective (HomologicalComplex.homologyMap v k).hom := by
  have hw : HomologicalComplex.homologyMap h k ≫ HomologicalComplex.homologyMap v k
      = HomologicalComplex.homologyMap u k ≫ HomologicalComplex.homologyMap g k := by
    rw [← HomologicalComplex.homologyMap_comp, hsq, HomologicalComplex.homologyMap_comp]
  haveI := hh
  haveI := hg
  exact (surjective_iff_of_comm_square (h := HomologicalComplex.homologyMap v k)
    (f := HomologicalComplex.homologyMap u k) (u := HomologicalComplex.homologyMap h k)
    (v := HomologicalComplex.homologyMap g k) hw).symm

/-! ## The surjectivity form of the model per-cell statement -/

/-- **The model per-cell map is surjective in the boundary degree** when the disc pair map is.
The mirror of `Work.Serre.CellStep.csModelIso_of_discIso` for surjectivity. -/
theorem csModelSurj_of_discSurj {n : ℕ} {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (hp : Work.StemsB.IsSerreFibration p)
    (τ : C(cellDisk n, B)) (k : ℕ)
    (hDisc : Function.Surjective
      (HomologicalComplex.homologyMap (Work.Serre.discPairMap n p τ) k).hom) :
    Function.Surjective
      (HomologicalComplex.homologyMap (Work.Serre.csModelMap n p τ) k).hom := by
  have hsub1 : Work.Serre.CellStep.Tp p τ (Work.Serre.csS (n := n)) ⊆
      Work.Serre.CellStep.Tp p τ (Work.Serre.csSh (n := n)) :=
    fun x hx => Work.Serre.csS_subset_csSh (n := n) hx
  have hsub2 : Work.Serre.CellStep.Tp p τ (Work.Serre.csS (n := n)) ⊆
      Work.Serre.CellStep.Tp p τ (Work.Serre.csQ (n := n)) :=
    fun x hx => Work.Serre.csS_subset_csQ (n := n) hx
  have hsub3 : Work.Serre.CellStep.Tp p τ (Work.Serre.cellSphereSet n) ⊆
      Work.Serre.CellStep.Tp p τ (Work.Serre.csQ (n := n)) :=
    fun x hx => Work.Serre.cellSphereSet_subset_csQ (n := n) hx
  have hsub4 : Work.Serre.CellStep.Tp p τ (Work.Serre.csSh (n := n)) ⊆
      Work.Serre.CellStep.Tp p τ (Work.Serre.csB (n := n)) :=
    fun x hx => Work.Serre.csSh_subset_csB (n := n) hx
  have h3 : Function.Surjective (HomologicalComplex.homologyMap
      (Work.Serre.CellStep.Pa3 p τ) k).hom :=
    (surjective_homologyMap_iff_of_square
      (h := Work.Cohomology.relCokerMap (Work.Serre.CellStep.Pb p τ)
        (Work.Serre.CellStep.Tp p τ (Work.Serre.cellSphereSet n))
        (Work.Serre.CellStep.Tp p τ (Work.Serre.csQ (n := n))) hsub3)
      (g := Work.Cohomology.relCokerMap (Work.Serre.CellStep.Dc n)
        (Work.Serre.cellSphereSet n) (Work.Serre.csQ (n := n))
        (Work.Serre.cellSphereSet_subset_csQ (n := n)))
      (u := Work.Serre.CellStep.Pa4 p τ) (v := Work.Serre.CellStep.Pa3 p τ)
      (Work.Serre.CellStep.square5 p τ) k
      (Work.Serre.CellStep.isIso_relCokerMap_of_acyclic (X := Work.Serre.CellStep.Pb p τ) hsub3
        (fun j => Work.Serre.CellStep.isZero_TotRel (W₀ := Work.Serre.cellSphereSet n)
          (W := Work.Serre.csQ (n := n)) p hp τ
          (Work.Serre.cellSphereSet_subset_csQ (n := n))
          (Work.Serre.CellStep.compressRel_csQ_cellSphereSet n) j) k)
      (Work.Serre.CellStep.isIso_relCokerMap_of_acyclic (X := Work.Serre.CellStep.Dc n)
        (Work.Serre.cellSphereSet_subset_csQ (n := n))
        (fun j => Work.Serre.isZero_relChains_of_compress
          (Work.Serre.CellStep.compressRel_csQ_cellSphereSet n) j) k)).mp hDisc
  have h2 : Function.Surjective (HomologicalComplex.homologyMap
      (Work.Serre.CellStep.Pa2 p τ) k).hom :=
    (surjective_homologyMap_iff_of_square
      (h := Work.Cohomology.relCokerMap (Work.Serre.CellStep.Pb p τ)
        (Work.Serre.CellStep.Tp p τ (Work.Serre.csS (n := n)))
        (Work.Serre.CellStep.Tp p τ (Work.Serre.csQ (n := n))) hsub2)
      (g := Work.Cohomology.relCokerMap (Work.Serre.CellStep.Dc n)
        (Work.Serre.csS (n := n)) (Work.Serre.csQ (n := n))
        (Work.Serre.csS_subset_csQ (n := n)))
      (u := Work.Serre.CellStep.Pa2 p τ) (v := Work.Serre.CellStep.Pa3 p τ)
      (Work.Serre.CellStep.square4 p τ) k
      (Work.Serre.CellStep.isIso_relCokerMap_of_acyclic (X := Work.Serre.CellStep.Pb p τ) hsub2
        (fun j => Work.Serre.CellStep.isZero_TotRel (W₀ := Work.Serre.csS (n := n))
          (W := Work.Serre.csQ (n := n)) p hp τ (Work.Serre.csS_subset_csQ (n := n))
          (Work.Serre.CellStep.compressRel_csQ_csS n) j) k)
      (Work.Serre.CellStep.isIso_relCokerMap_of_acyclic (X := Work.Serre.CellStep.Dc n)
        (Work.Serre.csS_subset_csQ (n := n))
        (fun j => Work.Serre.isZero_relChains_of_compress
          (Work.Serre.CellStep.compressRel_csQ_csS n) j) k)).mpr h3
  have h1 : Function.Surjective (HomologicalComplex.homologyMap
      (Work.Serre.CellStep.Pa1 p τ) k).hom :=
    (surjective_homologyMap_iff_of_square
      (h := Work.Cohomology.relCokerMap (Work.Serre.CellStep.Pb p τ)
        (Work.Serre.CellStep.Tp p τ (Work.Serre.csS (n := n)))
        (Work.Serre.CellStep.Tp p τ (Work.Serre.csSh (n := n))) hsub1)
      (g := Work.Cohomology.relCokerMap (Work.Serre.CellStep.Dc n)
        (Work.Serre.csS (n := n)) (Work.Serre.csSh (n := n))
        (Work.Serre.csS_subset_csSh (n := n)))
      (u := Work.Serre.CellStep.Pa2 p τ) (v := Work.Serre.CellStep.Pa1 p τ)
      (Work.Serre.CellStep.square3 p τ) k
      (Work.Serre.CellStep.isIso_relCokerMap_of_acyclic (X := Work.Serre.CellStep.Pb p τ) hsub1
        (fun j => Work.Serre.CellStep.isZero_TotRel (W₀ := Work.Serre.csS (n := n))
          (W := Work.Serre.csSh (n := n)) p hp τ (Work.Serre.csS_subset_csSh (n := n))
          (Work.Serre.CellStep.compressRel_csSh_csS n) j) k)
      (Work.Serre.CellStep.isIso_relCokerMap_of_acyclic (X := Work.Serre.CellStep.Dc n)
        (Work.Serre.csS_subset_csSh (n := n))
        (fun j => Work.Serre.isZero_relChains_of_compress
          (Work.Serre.CellStep.compressRel_csSh_csS n) j) k)).mp h2
  have h0' : Function.Surjective (HomologicalComplex.homologyMap
      (Work.Serre.CellStep.Pa0' p τ) k).hom :=
    (surjective_homologyMap_iff_of_square
      (h := Work.Cohomology.relChainsMap (Work.Serre.CellStep.Pb p τ)
        (Work.Serre.CellStep.Tp p τ (Work.Serre.csB (n := n)))
        (Work.Serre.CellStep.Tp p τ (Work.Serre.csSh (n := n))))
      (g := 𝟙 (Work.Cohomology.relChains (Work.Serre.CellStep.Dc n)
        (Work.Serre.csSh (n := n))))
      (u := Work.Serre.CellStep.Pa0' p τ) (v := Work.Serre.CellStep.Pa1 p τ)
      (Work.Serre.CellStep.square2 p τ) k
      (Work.Serre.CellStep.relChainsMap_isIso (Work.Serre.CellStep.Pb p τ)
        (Work.Serre.CellStep.Tp p τ (Work.Serre.csB (n := n)))
        (Work.Serre.CellStep.Tp p τ (Work.Serre.csSh (n := n))) hsub4
        (Work.Serre.CellStep.isZero_relChains_Pb_csB p hp τ) k)
      (Work.Serre.CellStep.isIso_homologyMap_id
        (Work.Cohomology.relChains (Work.Serre.CellStep.Dc n) (Work.Serre.csSh (n := n)))
        k)).mpr h1
  exact (surjective_homologyMap_iff_of_square
    (h := 𝟙 _)
    (g := Work.Cohomology.relChainsMap (Work.Serre.CellStep.Dc n)
      (Work.Serre.csB (n := n)) (Work.Serre.csSh (n := n)))
    (u := Work.Serre.csModelMap n p τ) (v := Work.Serre.CellStep.Pa0' p τ)
    (by rw [Category.id_comp]; exact Work.Serre.CellStep.square1 p τ) k
    (Work.Serre.CellStep.isIso_homologyMap_id _ k)
    (Work.Serre.CellStep.relChainsMap_isIso (Work.Serre.CellStep.Dc n)
      (Work.Serre.csB (n := n)) (Work.Serre.csSh (n := n))
      (Work.Serre.csSh_subset_csB (n := n)) (Work.Serre.CellStep.isZero_relChains_Dc_csB n) k)).mpr
    h0'

/-! ## The surjectivity part of the per-piece statement -/

/-- **The per-piece map is surjective in the boundary degree.**  The mirror of
`Work.Serre.CellStep.cellPieceIso`. -/
theorem cellPieceSurj (n : ℕ) (Γ : Type) [TopologicalSpace Γ] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere n, Γ)) (α : ι) {X : Type} [TopologicalSpace X]
    (q : C(X, Work.RatHurewicz.attachCells n Γ ι f)) (hq : Work.StemsB.IsSerreFibration q)
    (φ : ℕ)
    (hfib : ∀ y : Work.RatHurewicz.attachCells n Γ ι f, ∀ j : ℕ, 0 < j → j < φ →
      CategoryTheory.Limits.IsZero ((Work.Cohomology.singularChains ℤ
        (TopCat.of (Work.StemsB.fibre q y))).homology j))
    (h0 : ∀ y : Work.RatHurewicz.attachCells n Γ ι f,
      CategoryTheory.IsIso (TopCat.singularHomology₀ε (TopCat.of (Work.StemsB.fibre q y))
        (ModuleCat.of ℤ ℤ))) :
    Function.Surjective (HomologicalComplex.homologyMap
      (Work.Serre.cellPieceMap n Γ ι f α q) ((n + 2) + φ)).hom := by
  haveI hhIso : CategoryTheory.IsIso (Work.Serre.CellStep.cpSrcRelMap f α q) := by
    unfold Work.Serre.CellStep.cpSrcRelMap
    exact Work.StemsB.isIso_relChainsMapOf_homeomorph
      (X := TopCat.of ↥(q ⁻¹' Work.Serre.pieceSet n Γ ι f α))
      (Y := TopCat.of ↥(Work.Serre.CellStep.Tp q (Work.RatHurewicz.cellMap n Γ ι f α)
        (Work.Serre.csB (n := n))))
      (Work.Serre.CellStep.cpTotalHomeo f α q) (Work.Serre.CellStep.cpSrcRel f α q)
      (Work.Serre.CellStep.SrcRel q (Work.RatHurewicz.cellMap n Γ ι f α))
      (Work.Serre.CellStep.cpTotalHomeo_relIff f α q)
  haveI hgIso : CategoryTheory.IsIso (Work.Serre.CellStep.cpTarRelMap f α) := by
    unfold Work.Serre.CellStep.cpTarRelMap
    exact Work.StemsB.isIso_relChainsMapOf_homeomorph
      (X := TopCat.of ↥(Work.Serre.pieceSet n Γ ι f α))
      (Y := TopCat.of ↥(Work.Serre.csB (n := n))) (Work.Serre.CellStep.cpBaseHomeo f α)
      (Work.Serre.CellStep.cpTarRel f α) (Work.Serre.CellStep.TrSh n)
      (Work.Serre.CellStep.cpBaseHomeo_relIff f α)
  have hh : CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (Work.Serre.CellStep.cpSrcRelMap f α q) ((n + 2) + φ)) :=
    Functor.map_isIso (HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ)
      ((n + 2) + φ)) (Work.Serre.CellStep.cpSrcRelMap f α q)
  have hg : CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (Work.Serre.CellStep.cpTarRelMap f α) ((n + 2) + φ)) :=
    Functor.map_isIso (HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ)
      ((n + 2) + φ)) (Work.Serre.CellStep.cpTarRelMap f α)
  have hsq : Work.Serre.CellStep.cpSrcRelMap f α q ≫
        (Work.Serre.csModelMap n q (Work.RatHurewicz.cellMap n Γ ι f α))
      = (Work.Serre.cellPieceMap n Γ ι f α q) ≫ Work.Serre.CellStep.cpTarRelMap f α := by
    unfold Work.Serre.CellStep.cpSrcRelMap Work.Serre.CellStep.cpTarRelMap
    rw [Work.Serre.CellStep.csModelMap_eq_stems, Work.Serre.CellStep.cellPieceMap_eq_stems,
      Work.Serre.CellStep.relChainsMapOfStems_comp,
      Work.Serre.CellStep.relChainsMapOfStems_comp]
    exact Work.Serre.CellStep.relChainsMapOfStems_congr' (Work.Serre.CellStep.cpSquare f α q)
  refine (surjective_homologyMap_iff_of_square (Work.Serre.CellStep.cpSrcRelMap f α q)
    (Work.Serre.CellStep.cpTarRelMap f α) (Work.Serre.cellPieceMap n Γ ι f α q)
    (Work.Serre.csModelMap n q (Work.RatHurewicz.cellMap n Γ ι f α)) hsq ((n + 2) + φ) hh hg).mpr ?_
  exact csModelSurj_of_discSurj q hq (Work.RatHurewicz.cellMap n Γ ι f α) ((n + 2) + φ)
    (discPairStrong n X (Work.RatHurewicz.attachCells n Γ ι f) q hq
      (Work.RatHurewicz.cellMap n Γ ι f α) φ
      (fun y j hj1 hj2 => hfib (Work.RatHurewicz.cellMap n Γ ι f α y) j hj1 hj2)
      (fun y => h0 (Work.RatHurewicz.cellMap n Γ ι f α y))).2

/-! ## The per-piece statement -/

theorem cellPieceStrong (n : ℕ) (Γ : Type) [TopologicalSpace Γ] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere n, Γ)) (α : ι) {X : Type} [TopologicalSpace X]
    (q : C(X, Work.RatHurewicz.attachCells n Γ ι f)) (hq : Work.StemsB.IsSerreFibration q)
    (φ : ℕ)
    (hfib : ∀ y : Work.RatHurewicz.attachCells n Γ ι f, ∀ j : ℕ, 0 < j → j < φ →
      CategoryTheory.Limits.IsZero ((Work.Cohomology.singularChains ℤ
        (TopCat.of (Work.StemsB.fibre q y))).homology j))
    (h0 : ∀ y : Work.RatHurewicz.attachCells n Γ ι f,
      CategoryTheory.IsIso (TopCat.singularHomology₀ε (TopCat.of (Work.StemsB.fibre q y))
        (ModuleCat.of ℤ ℤ))) :
    (∀ i : ℕ, i < (n + 2) + φ → CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (Work.Serre.cellPieceMap n Γ ι f α q) i)) ∧
    Function.Surjective (HomologicalComplex.homologyMap
      (Work.Serre.cellPieceMap n Γ ι f α q) ((n + 2) + φ)).hom := by
  constructor
  · intro i hi
    exact Work.Serre.CellStep.cellPieceIso n Γ ι f α q hq φ hfib h0 i hi
  · exact cellPieceSurj n Γ ι f α q hq φ hfib h0

end

end Work.Serre.SPC
