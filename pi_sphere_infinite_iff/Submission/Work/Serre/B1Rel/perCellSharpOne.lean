import Mathlib
import Submission.Work.Serre.B1Rel.Defs
import Submission.Work.Serre.B1Rel.oneCellSection
import Submission.Work.Serre.B1Rel.oneCellSourceIso
import Submission.Work.Serre.B1Rel.targetGroupsSelf
import Submission.Work.Serre.CsrSharp.Cell.perCellSharp
import Submission.Work.Serre.CsrSharp.Tools
import Submission.Work.Serre.csrPairFunctoriality

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The sharp rational per-cell computation for a `1`-cell

`Work.Serre.B1Rel.perCellSharpOne` computes the per-cell comparison
`Work.Serre.B1Rel.perCellMapOne` of the `i`-th open `1`-cell in the sharp range: it is an
isomorphism on rational homology in degrees `< 1 + φ` and surjective in degree `1 + φ`, when the
Serre fibration has fibres acyclic in degrees `0 < j < φ` and rationally connected.

The proof is the `1`-dimensional instance of the pattern of
`Work.Serre.CsrSharp.Cell.perCellSharp_of_groups`: the target pair `(oᵢ, oᵢ∖{cᵢ})` has relative
homology `ℚ` only in degree `1`, the source pair has the shifted fibre homology
(`oneCellSourceIso`), the map is surjective in every degree because the fibration admits a section
over the contractible open cell (`oneCellSection`), and the three descriptions of the homology
give the isomorphism in each degree.
-/

set_option maxHeartbeats 1600000

open CategoryTheory CategoryTheory.Limits
open scoped Topology

namespace Work.Serre.B1Rel

noncomputable section

open Work.Serre

/-! ## Surjectivity from a section -/

/-- **The per-cell map is surjective on homology in every degree** as soon as the restriction of
the fibration to the open cell `oᵢ` admits a section: the section is a map of pairs
`(oᵢ, oᵢ∖{cᵢ}) → (q⁻¹'oᵢ, q⁻¹'(oᵢ∖{cᵢ}))` whose composite with the per-cell map is the identity,
so the composite of the induced maps on relative chains is the identity. -/
theorem perCellMapOne_surjective (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(Work.Serre.cellSphereZero, Y)) {E : Type} [TopologicalSpace E]
    (q : C(E, Work.Serre.attachOneCells Y ι f)) (i : ι)
    (s : C(↥(OneCell.cellInteriorOne Y ι f i),
        ↥(q ⁻¹' OneCell.cellInteriorOne Y ι f i)))
    (hs : (Work.Serre.csrRestrict q (OneCell.cellInteriorOne Y ι f i)).comp s
      = ContinuousMap.id ↥(OneCell.cellInteriorOne Y ι f i)) (m : ℕ) :
    Function.Surjective
      (HomologicalComplex.homologyMap (perCellMapOne Y ι f q i) m).hom := by
  have hmap : ∀ x : ↥(OneCell.cellInteriorOne Y ι f i),
      (Work.Serre.csrRestrict q (OneCell.cellInteriorOne Y ι f i)) (s x) = x :=
    fun x => congrFun (congrArg DFunLike.coe hs) x
  have hval : ∀ x : ↥(OneCell.cellInteriorOne Y ι f i),
      q ((s x : ↥(q ⁻¹' OneCell.cellInteriorOne Y ι f i)) : E)
        = (x : Work.Serre.attachOneCells Y ι f) :=
    fun x => congrArg Subtype.val (hmap x)
  have hs' : Set.MapsTo s (tgtRelOne Y ι f i) (srcRelOne Y ι f q i) := by
    intro x hx
    show q ((s x : ↥(q ⁻¹' OneCell.cellInteriorOne Y ι f i)) : E) ∈
      OneCell.cellInteriorOne Y ι f i \ {OneCell.oneCellCentreOne Y ι f i}
    rw [hval x]
    exact hx
  have hAA : Set.MapsTo ((Work.Serre.csrRestrict q (OneCell.cellInteriorOne Y ι f i)).comp s)
      (tgtRelOne Y ι f i) (tgtRelOne Y ι f i) := fun x hx => by
    show (Work.Serre.csrRestrict q (OneCell.cellInteriorOne Y ι f i)) (s x) ∈ tgtRelOne Y ι f i
    rw [hmap x]
    exact hx
  have hcomp : Work.Serre.relChainsRPairMap (tgtRelOne Y ι f i) (srcRelOne Y ι f q i) s hs' ≫
      perCellMapOne Y ι f q i = 𝟙 _ := by
    rw [show perCellMapOne Y ι f q i
        = Work.Serre.relChainsRPairMap (srcRelOne Y ι f q i) (tgtRelOne Y ι f i)
            (Work.Serre.csrRestrict q (OneCell.cellInteriorOne Y ι f i)) (fun _ hx => hx)
        from rfl]
    rw [Work.Serre.csrPairFunctoriality s
      (Work.Serre.csrRestrict q (OneCell.cellInteriorOne Y ι f i)) hs' (fun _ hx => hx)]
    refine (Work.Serre.CsrSharp.Tools.relChainsRPairMap_congr hs hAA (fun x hx => hx)).trans ?_
    exact Work.Serre.CsrSharp.Tools.relChainsRPairMap_id' _ _
  have h1 : HomologicalComplex.homologyMap
        (Work.Serre.relChainsRPairMap (tgtRelOne Y ι f i) (srcRelOne Y ι f q i) s hs') m
      ≫ HomologicalComplex.homologyMap (perCellMapOne Y ι f q i) m = 𝟙 _ := by
    rw [← HomologicalComplex.homologyMap_comp, hcomp, HomologicalComplex.homologyMap_id]
  intro y
  refine ⟨(HomologicalComplex.homologyMap
      (Work.Serre.relChainsRPairMap (tgtRelOne Y ι f i) (srcRelOne Y ι f q i) s hs') m).hom y, ?_⟩
  have h2 := congrArg ModuleCat.Hom.hom h1
  rw [ModuleCat.hom_comp, ModuleCat.hom_id] at h2
  exact LinearMap.congr_fun h2 y

/-! ## The per-cell computation -/

/-- **The sharp rational per-cell computation for a `1`-cell.** -/
theorem perCellSharpOne (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(Work.Serre.cellSphereZero, Y)) {E : Type} [TopologicalSpace E]
    (q : C(E, Work.Serre.attachOneCells Y ι f)) (hq : Work.StemsB.IsSerreFibration q) (φ : ℕ)
    (hfib : ∀ z : Work.Serre.attachOneCells Y ι f, ∀ j : ℕ, 0 < j → j < φ →
      CategoryTheory.Limits.IsZero ((Work.Cohomology.singularChains ℚ
        (TopCat.of (Work.StemsB.fibre q z))).homology j))
    (h0 : ∀ z : Work.Serre.attachOneCells Y ι f,
      Nonempty ((Work.Cohomology.singularChains ℚ
        (TopCat.of (Work.StemsB.fibre q z))).homology 0 ≅ ModuleCat.of ℚ ℚ)) (i : ι) :
    (∀ m : ℕ, m < 1 + φ → CategoryTheory.IsIso
      (HomologicalComplex.homologyMap (perCellMapOne Y ι f q i) m)) ∧
    Function.Surjective (HomologicalComplex.homologyMap (perCellMapOne Y ι f q i) (1 + φ)).hom := by
  obtain ⟨hTz, hTtop⟩ := oneCellTargetGroupsSelf Y ι f i
  obtain ⟨hSiso, hSzero⟩ := oneCellSourceIso Y ι f q hq i
  have hne : Nonempty (Work.StemsB.fibre q (OneCell.oneCellCentreOne Y ι f i)) :=
    Work.Serre.Csr.nonempty_of_nonempty_homologyZeroIso _
      (h0 (OneCell.oneCellCentreOne Y ι f i))
  obtain ⟨s, hs⟩ := oneCellSection Y ι f q hq i hne
  have hsurj := perCellMapOne_surjective Y ι f q i s hs
  refine ⟨fun m hm => ?_, fun y => hsurj (1 + φ) y⟩
  rcases lt_trichotomy m 1 with hlt | heq | hgt
  · -- below the cell dimension both sides vanish
    haveI hzS : IsZero ((srcOne Y ι f q i).homology m) := hSzero m hlt
    haveI hzT : IsZero ((tgtOne Y ι f i).homology m) := hTz m (by omega)
    haveI : Subsingleton ((srcOne Y ι f q i).homology m) := ModuleCat.subsingleton_of_isZero hzS
    haveI : Subsingleton ((tgtOne Y ι f i).homology m) := ModuleCat.subsingleton_of_isZero hzT
    haveI : Mono (HomologicalComplex.homologyMap (perCellMapOne Y ι f q i) m) :=
      (ModuleCat.mono_iff_injective _).mpr (fun a b _ => Subsingleton.elim a b)
    haveI : Epi (HomologicalComplex.homologyMap (perCellMapOne Y ι f q i) m) :=
      (ModuleCat.epi_iff_surjective _).mpr (fun b => ⟨0, Subsingleton.elim _ b⟩)
    exact isIso_of_mono_of_epi _
  · -- in the cell dimension both sides are one dimensional over `ℚ` and the map is surjective
    subst heq
    obtain ⟨eS⟩ := hSiso 0
    rw [Nat.zero_add] at eS
    obtain ⟨eF⟩ := h0 (OneCell.oneCellCentreOne Y ι f i)
    obtain ⟨eT⟩ := hTtop
    exact Work.Serre.Csr.isIso_of_epi_of_ratIso (eS ≪≫ eF) eT
      (HomologicalComplex.homologyMap (perCellMapOne Y ι f q i) 1)
      ((ModuleCat.epi_iff_surjective _).mpr (hsurj 1))
  · -- above the cell dimension (and below `1 + φ`) the fibre homology vanishes
    haveI hzT : IsZero ((tgtOne Y ι f i).homology m) := hTz m (by omega)
    have hk : m - 1 + 1 = m := Nat.sub_add_cancel (by omega)
    obtain ⟨eS⟩ := hSiso (m - 1)
    haveI hzF : IsZero ((Work.Cohomology.singularChains ℚ
        (TopCat.of (Work.StemsB.fibre q (OneCell.oneCellCentreOne Y ι f i)))).homology
          (m - 1)) := hfib (OneCell.oneCellCentreOne Y ι f i) (m - 1) (by omega) (by omega)
    haveI hzS' : IsZero ((srcOne Y ι f q i).homology (m - 1 + 1)) := hzF.of_iso eS
    haveI hzS : IsZero ((srcOne Y ι f q i).homology m) := by rwa [hk] at hzS'
    haveI : Subsingleton ((srcOne Y ι f q i).homology m) := ModuleCat.subsingleton_of_isZero hzS
    haveI : Subsingleton ((tgtOne Y ι f i).homology m) := ModuleCat.subsingleton_of_isZero hzT
    haveI : Mono (HomologicalComplex.homologyMap (perCellMapOne Y ι f q i) m) :=
      (ModuleCat.mono_iff_injective _).mpr (fun a b _ => Subsingleton.elim a b)
    haveI : Epi (HomologicalComplex.homologyMap (perCellMapOne Y ι f q i) m) :=
      (ModuleCat.epi_iff_surjective _).mpr (fun b => ⟨0, Subsingleton.elim _ b⟩)
    exact isIso_of_mono_of_epi _

end

end Work.Serre.B1Rel
