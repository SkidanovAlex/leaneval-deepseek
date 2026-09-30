import Mathlib
import Submission.Work.Serre.B1Rel.Propagate
import Submission.Work.Serre.B1Rel.oneCellStepSharp
import Submission.Work.Serre.E3aModel
import Submission.Work.Serre.cellStepSharp
import Submission.Work.Serre.RatTower.Base
import Submission.Work.Serre.RatTower.Attach
import Submission.Work.Serre.ratFibreTransport
import Submission.Work.Serre.Assembly.pullbackFst_serre

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 4000000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

/-!
# The `b = 1` model of the base for the rational pair comparison

`Work.Serre.B1Rel.RelGoodQ p N γ₀ g` (the invariant of `Work.Serre.B1Rel.Propagate`) is
established for the model of a path connected base built in `Work.Serre.E3aModel` (the `1`-skeleton
with the `π₁`-killing `2`-cells, followed by the generator/killing tower `towerB`), when the fibres
of `p` are rationally acyclic *below* `φ` and rationally connected, and the invariant range `N`
satisfies `N ≤ φ + 1`.

The base cases are the one-point base (`relGoodQ_punit`), the `1`-skeleton
(`relGoodQ_skeleton`, from the sharp `1`-cell step `Work.Serre.B1Rel.oneCellStepSharp`) and the
base stage (`relGoodQ_base`, from the sharp `(n+2)`-cell step `Work.Serre.cellStepSharp` with
`n = 0`); the induction along the tower is `relGoodQ_tower`.  Every step is the propagation
`Work.Serre.B1Rel.propagateRelQ`.
-/

open CategoryTheory CategoryTheory.Limits
open scoped Topology unitInterval

namespace Work.Serre.B1Rel

noncomputable section

variable {B E : Type} [TopologicalSpace B] [TopologicalSpace E]

/-! ## The fibre data, in the sharp (`< φ`) range -/

/-- **The sharp fibre data of a Serre fibration at every point of a path connected base**, from the
data at one point. -/
theorem fibreDataBelow_all (p : C(E, B)) (hp : Work.StemsB.IsSerreFibration p) (b₀ : B)
    [PathConnectedSpace B] (φ : ℕ)
    (hfib : ∀ j : ℕ, 0 < j → j < φ →
      CategoryTheory.Limits.IsZero (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre p b₀)) j))
    (h0 : Nonempty (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre p b₀)) 0
      ≅ ModuleCat.of ℚ ℚ)) :
    (∀ y : B, ∀ j : ℕ, 0 < j → j < φ →
      CategoryTheory.Limits.IsZero (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre p y)) j)) ∧
    (∀ y : B, Nonempty (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre p y)) 0
      ≅ ModuleCat.of ℚ ℚ)) := by
  refine ⟨fun y j hj hjφ => ?_, fun y => ?_⟩
  · obtain ⟨P⟩ := PathConnectedSpace.joined b₀ y
    exact Work.Serre.isZero_ratH_fibre_of_path p hp b₀ y P.toContinuousMap P.source P.target φ
      hfib j hj hjφ
  · obtain ⟨P⟩ := PathConnectedSpace.joined b₀ y
    obtain ⟨e⟩ := Work.Serre.ratH_fibre_iso_of_path p hp P.toContinuousMap 0
    rw [show P.toContinuousMap 0 = b₀ from P.source,
      show P.toContinuousMap 1 = y from P.target] at e
    exact ⟨e.symm ≪≫ h0.some⟩

/-- **The sharp fibre data of the pullback of `p` along `g`**, from the fibre data of `p`. -/
theorem fibreData_pullback_below {Γ : Type} [TopologicalSpace Γ] (g : C(Γ, B)) (p : C(E, B))
    (y : Γ) (φ : ℕ)
    (hfib : ∀ y' : B, ∀ j : ℕ, 0 < j → j < φ →
      CategoryTheory.Limits.IsZero (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre p y')) j))
    (h0 : ∀ y' : B, Nonempty (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre p y')) 0
      ≅ ModuleCat.of ℚ ℚ)) :
    (∀ k : ℕ, 0 < k → k < φ → CategoryTheory.Limits.IsZero
      (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre (Work.StemsB.pullbackFst g p) y)) k)) ∧
    Nonempty (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre (Work.StemsB.pullbackFst g p) y)) 0
      ≅ ModuleCat.of ℚ ℚ) :=
  ⟨fun k hk hkφ => Work.Serre.RatTower.isZero_ratH_of_homeomorph
      (X := TopCat.of (Work.StemsB.fibre (Work.StemsB.pullbackFst g p) y))
      (Y := TopCat.of (Work.StemsB.fibre p (g y)))
      (Work.Serre.RatTower.fibrePullbackFstHomeo g p y) k (hfib (g y) k hk hkφ),
    Work.Serre.RatTower.nonempty_ratH_zero_of_homeomorph
      (X := TopCat.of (Work.StemsB.fibre (Work.StemsB.pullbackFst g p) y))
      (Y := TopCat.of (Work.StemsB.fibre p (g y)))
      (Work.Serre.RatTower.fibrePullbackFstHomeo g p y) (h0 (g y))⟩

/-! ## The base case: the one-point base -/

/-- **The invariant at the one-point base.** -/
theorem relGoodQ_punit (p : C(E, B)) (b₀ : B) (N : ℕ) :
    RelGoodQ p N (⟨⟩ : PUnit) (ContinuousMap.const PUnit b₀) := by
  have hsrc : ((Work.StemsB.pullbackFst (ContinuousMap.const PUnit b₀) p) ⁻¹'
      ({⟨⟩} : Set PUnit)) = Set.univ := by
    ext x; simp
  have htgt : ({⟨⟩} : Set PUnit) = (Set.univ : Set PUnit) := by
    ext x; simp
  have hX : ∀ i : ℕ, IsZero ((Work.StemsB.relChainsR ℚ
      (TopCat.of (Work.StemsB.Pullback (ContinuousMap.const PUnit b₀) p))
      ((Work.StemsB.pullbackFst (ContinuousMap.const PUnit b₀) p) ⁻¹'
        ({⟨⟩} : Set PUnit))).homology i) := by
    intro i
    rw [hsrc]
    exact (HomologicalComplex.homologyFunctor (ModuleCat ℚ) (ComplexShape.down ℕ) i).map_isZero
      (Work.Serre.RatTower.rt_isZero_relChainsR_univ _)
  have hY : ∀ i : ℕ, IsZero ((Work.StemsB.relChainsR ℚ (TopCat.of PUnit)
      ({⟨⟩} : Set PUnit)).homology i) := by
    intro i
    rw [htgt]
    exact (HomologicalComplex.homologyFunctor (ModuleCat ℚ) (ComplexShape.down ℕ) i).map_isZero
      (Work.Serre.RatTower.rt_isZero_relChainsR_univ _)
  constructor
  · intro i _
    have he := IsZero.eq_of_src (hX i) (HomologicalComplex.homologyMap
      (Work.Serre.stagePairMapRat (ContinuousMap.const PUnit b₀) p ⟨⟩) i)
      (IsZero.iso (hX i) (hY i)).hom
    rw [he]
    infer_instance
  · change Epi (HomologicalComplex.homologyMap
      (Work.Serre.stagePairMapRat (ContinuousMap.const PUnit b₀) p ⟨⟩) N)
    rw [ModuleCat.epi_iff_surjective]
    haveI : Subsingleton (↥((Work.StemsB.relChainsR ℚ (TopCat.of PUnit)
        ({⟨⟩} : Set PUnit)).homology N)) :=
      ModuleCat.subsingleton_of_isZero (hY N)
    intro y
    exact ⟨0, Subsingleton.elim _ _⟩

/-! ## The `1`-skeleton -/

/-- **The invariant at the `1`-skeleton**, propagated from the one-point base along the `1`-cells. -/
theorem relGoodQ_skeleton (p : C(E, B)) (hp : Work.StemsB.IsSerreFibration p) (b₀ : B)
    [PathConnectedSpace B] (N φ : ℕ) (hNφ : N ≤ φ + 1)
    (hfib : ∀ y : B, ∀ j : ℕ, 0 < j → j < φ →
      CategoryTheory.Limits.IsZero (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre p y)) j))
    (h0 : ∀ y : B, Nonempty (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre p y)) 0
      ≅ ModuleCat.of ℚ ℚ)) :
    RelGoodQ p N (Work.Serre.E3aSk.skeletonBase B b₀) (Work.Serre.E3aModel.skelMap B b₀) := by
  haveI : PathConnectedSpace (Work.Serre.E3aSk.Skeleton B b₀) :=
    Work.Serre.E3aModel.pathConnectedSpace_skeleton B b₀
  refine propagateRelQ p N (⟨⟩ : PUnit) (ContinuousMap.const PUnit b₀)
    (relGoodQ_punit p b₀ N)
    (Work.Serre.oneIncl PUnit _ (Work.Serre.E3aSk.skeletonAttach B b₀))
    (Work.Serre.E3aModel.injective_oneIncl_punit _ _)
    (Work.Serre.E3aModel.isInducing_oneIncl_punit _ _)
    (Work.Serre.E3aModel.skelMap B b₀) ?_ ?_
  · intro x
    exact Work.Serre.E3aModel.skelMap_base B b₀
  · rw [Work.Serre.E3aModel.stepMapQ_oneIncl_eq_oneCellStepMap p PUnit
      (↥(GenLoop (Fin 1) B b₀)) (Work.Serre.E3aSk.skeletonAttach B b₀)
      (Work.Serre.E3aModel.skelMap B b₀)]
    obtain ⟨hstepIso, hstepSurj⟩ :=
      oneCellStepSharp PUnit (↥(GenLoop (Fin 1) B b₀))
        (Work.Serre.E3aSk.skeletonAttach B b₀)
        (Work.StemsB.pullbackFst (Work.Serre.E3aModel.skelMap B b₀) p)
        (Work.Serre.Assembly.pullbackFst_serre _ p hp) φ
        (fun z => (fibreData_pullback_below (Work.Serre.E3aModel.skelMap B b₀) p z φ
          hfib h0).1)
        (fun z => (fibreData_pullback_below (Work.Serre.E3aModel.skelMap B b₀) p z φ
          hfib h0).2)
    have h1φ : N ≤ 1 + φ := by omega
    constructor
    · intro i hi
      exact hstepIso i (by omega)
    · rcases lt_or_eq_of_le h1φ with h | h
      · haveI : IsIso (HomologicalComplex.homologyMap
            (Work.Serre.oneCellStepMap (↥(GenLoop (Fin 1) B b₀))
              (Work.Serre.E3aSk.skeletonAttach B b₀)
              (Work.StemsB.pullbackFst (Work.Serre.E3aModel.skelMap B b₀) p)) N) :=
          hstepIso N h
        exact IsIso.epi_of_iso _
      · rw [h]
        exact (ModuleCat.epi_iff_surjective _).mpr hstepSurj

/-! ## The base stage: the skeleton with the `π₁`-killing `2`-cells -/

/-- **The invariant at the base stage**, propagated from the skeleton along the `2`-cells killing
the kernel of `π₁`. -/
theorem relGoodQ_base (p : C(E, B)) (hp : Work.StemsB.IsSerreFibration p) (b₀ : B)
    [PathConnectedSpace B] (N φ : ℕ) (hNφ : N ≤ φ + 1)
    (hfib : ∀ y : B, ∀ j : ℕ, 0 < j → j < φ →
      CategoryTheory.Limits.IsZero (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre p y)) j))
    (h0 : ∀ y : B, Nonempty (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre p y)) 0
      ≅ ModuleCat.of ℚ ℚ)) :
    RelGoodQ p N (Work.Serre.E3aModel.basePt B b₀) (Work.Serre.E3aModel.baseMap B b₀) := by
  refine propagateRelQ p N (Work.Serre.E3aSk.skeletonBase B b₀)
    (Work.Serre.E3aModel.skelMap B b₀)
    (relGoodQ_skeleton p hp b₀ N φ hNφ hfib h0)
    (Work.RatHurewicz.attachIncl 0 (Work.Serre.E3aSk.Skeleton B b₀)
      (Work.Serre.E3aModel.KilIdx B b₀) (Work.Serre.E3aModel.KilFam B b₀))
    (Work.RatHurewicz.AttachRange.attachIncl_injective 0 _ _ _)
    (Work.RatHurewicz.isInducing_attachIncl 0 _ _ _)
    (Work.Serre.E3aModel.baseMap B b₀) ?_ ?_
  · intro x
    exact Work.Serre.E3aModel.baseMap_incl B b₀ x
  · rw [Work.Serre.E3aModel.stepMapQ_attachIncl_eq_cellStepMap p
      (Work.Serre.E3aSk.Skeleton B b₀) 0 (Work.Serre.E3aModel.KilIdx B b₀)
      (Work.Serre.E3aModel.KilFam B b₀) (Work.Serre.E3aModel.baseMap B b₀)]
    obtain ⟨hstepIso, hstepSurj⟩ :=
      Work.Serre.cellStepSharp 0 (Work.Serre.E3aSk.Skeleton B b₀) (Work.Serre.E3aModel.KilIdx B b₀)
        (Work.Serre.E3aModel.KilFam B b₀)
        (Work.StemsB.pullbackFst (Work.Serre.E3aModel.baseMap B b₀) p)
        (Work.Serre.Assembly.pullbackFst_serre _ p hp) φ
        (fun z => (fibreData_pullback_below (Work.Serre.E3aModel.baseMap B b₀) p z φ
          hfib h0).1)
        (fun z => (fibreData_pullback_below (Work.Serre.E3aModel.baseMap B b₀) p z φ
          hfib h0).2)
    constructor
    · intro i hi
      exact hstepIso i (by omega)
    · rcases lt_or_eq_of_le (show N ≤ (0 + 2) + φ by omega) with h | h
      · haveI : IsIso (HomologicalComplex.homologyMap
            (Work.Serre.cellStepMap 0
              (Work.Serre.E3aModel.KilIdx B b₀) (Work.Serre.E3aModel.KilFam B b₀)
              (Work.StemsB.pullbackFst (Work.Serre.E3aModel.baseMap B b₀) p)) N) :=
          hstepIso N h
        exact IsIso.epi_of_iso _
      · rw [h]
        exact (ModuleCat.epi_iff_surjective _).mpr hstepSurj

/-! ## The tower -/

/-- **The invariant propagates along the model tower** `Work.Serre.E3aModel.towerB`. -/
theorem relGoodQ_tower (p : C(E, B)) (hp : Work.StemsB.IsSerreFibration p) (b₀ : B)
    [PathConnectedSpace B] (N φ : ℕ) (hNφ : N ≤ φ + 1)
    (hfib : ∀ y : B, ∀ j : ℕ, 0 < j → j < φ →
      CategoryTheory.Limits.IsZero (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre p y)) j))
    (h0 : ∀ y : B, Nonempty (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre p y)) 0
      ≅ ModuleCat.of ℚ ℚ))
    (s₀ : Work.Serre.CWModel.StA B b₀ 0) (h₀ : RelGoodQ p N s₀.y₀ s₀.g) (k : ℕ) :
    RelGoodQ p N (Work.Serre.E3aModel.towerB B b₀ s₀ k).y₀
      (Work.Serre.E3aModel.towerB B b₀ s₀ k).g := by
  induction k with
  | zero => exact h₀
  | succ k ih =>
    haveI hpc : PathConnectedSpace (Work.Serre.E3aModel.towerB B b₀ s₀ k).Y :=
      (Work.Serre.E3aModel.towerB B b₀ s₀ k).conn
    -- the generator step
    have hstepG : (∀ i : ℕ, i < N → IsIso (HomologicalComplex.homologyMap
        (Work.Serre.E3aStep.stepMapQ p
          (Work.RatHurewicz.attachIncl k (Work.Serre.E3aModel.towerB B b₀ s₀ k).Y
            (Work.Serre.E3aModel.GenIdx (Work.Serre.E3aModel.towerB B b₀ s₀ k))
            (Work.Serre.E3aModel.GenFr (Work.Serre.E3aModel.towerB B b₀ s₀ k)))
          (Work.Serre.CWModel.genStep (Work.Serre.E3aModel.towerB B b₀ s₀ k)).g) i)) ∧
        Epi (HomologicalComplex.homologyMap
        (Work.Serre.E3aStep.stepMapQ p
          (Work.RatHurewicz.attachIncl k (Work.Serre.E3aModel.towerB B b₀ s₀ k).Y
            (Work.Serre.E3aModel.GenIdx (Work.Serre.E3aModel.towerB B b₀ s₀ k))
            (Work.Serre.E3aModel.GenFr (Work.Serre.E3aModel.towerB B b₀ s₀ k)))
          (Work.Serre.CWModel.genStep (Work.Serre.E3aModel.towerB B b₀ s₀ k)).g) N) := by
      rw [Work.Serre.E3aModel.stepMapQ_attachIncl_eq_cellStepMap p
        (Work.Serre.E3aModel.towerB B b₀ s₀ k).Y k
        (Work.Serre.E3aModel.GenIdx (Work.Serre.E3aModel.towerB B b₀ s₀ k))
        (Work.Serre.E3aModel.GenFr (Work.Serre.E3aModel.towerB B b₀ s₀ k))
        (Work.Serre.CWModel.genStep (Work.Serre.E3aModel.towerB B b₀ s₀ k)).g]
      obtain ⟨hstepIso, hstepSurj⟩ :=
        Work.Serre.cellStepSharp k (Work.Serre.E3aModel.towerB B b₀ s₀ k).Y
          (Work.Serre.E3aModel.GenIdx (Work.Serre.E3aModel.towerB B b₀ s₀ k))
          (Work.Serre.E3aModel.GenFr (Work.Serre.E3aModel.towerB B b₀ s₀ k))
          (Work.StemsB.pullbackFst
            (Work.Serre.CWModel.genStep (Work.Serre.E3aModel.towerB B b₀ s₀ k)).g p)
          (Work.Serre.Assembly.pullbackFst_serre _ p hp) φ
          (fun z => (fibreData_pullback_below _
            p z φ hfib h0).1)
          (fun z => (fibreData_pullback_below _ p z φ hfib h0).2)
      constructor
      · intro i hi
        exact hstepIso i (by omega)
      · rcases lt_or_eq_of_le (show N ≤ (k + 2) + φ by omega) with h | h
        · haveI : IsIso (HomologicalComplex.homologyMap
              (Work.Serre.cellStepMap k
                (Work.Serre.E3aModel.GenIdx (Work.Serre.E3aModel.towerB B b₀ s₀ k))
                (Work.Serre.E3aModel.GenFr (Work.Serre.E3aModel.towerB B b₀ s₀ k))
                (Work.StemsB.pullbackFst
                  (Work.Serre.CWModel.genStep (Work.Serre.E3aModel.towerB B b₀ s₀ k)).g p)) N) :=
            hstepIso N h
          exact IsIso.epi_of_iso _
        · rw [h]
          exact (ModuleCat.epi_iff_surjective _).mpr hstepSurj
    have hG : RelGoodQ p N (Work.Serre.CWModel.genStep
        (Work.Serre.E3aModel.towerB B b₀ s₀ k)).y₀
        (Work.Serre.CWModel.genStep (Work.Serre.E3aModel.towerB B b₀ s₀ k)).g :=
      propagateRelQ p N (Work.Serre.E3aModel.towerB B b₀ s₀ k).y₀
        (Work.Serre.E3aModel.towerB B b₀ s₀ k).g ih
        (Work.RatHurewicz.attachIncl k (Work.Serre.E3aModel.towerB B b₀ s₀ k).Y
          (Work.Serre.E3aModel.GenIdx (Work.Serre.E3aModel.towerB B b₀ s₀ k))
          (Work.Serre.E3aModel.GenFr (Work.Serre.E3aModel.towerB B b₀ s₀ k)))
        (Work.RatHurewicz.AttachRange.attachIncl_injective k _ _ _)
        (Work.RatHurewicz.isInducing_attachIncl k _ _ _)
        (Work.Serre.CWModel.genStep (Work.Serre.E3aModel.towerB B b₀ s₀ k)).g
        (fun x => rfl) hstepG
    -- the killing step
    have hstepK : (∀ i : ℕ, i < N → IsIso (HomologicalComplex.homologyMap
        (Work.Serre.E3aStep.stepMapQ p
          (Work.RatHurewicz.attachIncl (k + 1) (Work.Serre.CWModel.genStep
            (Work.Serre.E3aModel.towerB B b₀ s₀ k)).Y
            (Work.Serre.E3aModel.KillIdx2 (Work.Serre.CWModel.genStep
              (Work.Serre.E3aModel.towerB B b₀ s₀ k)))
            (Work.Serre.E3aModel.KillFr (Work.Serre.CWModel.genStep
              (Work.Serre.E3aModel.towerB B b₀ s₀ k))))
          (Work.Serre.CWModel.killStep (Work.Serre.CWModel.genStep
            (Work.Serre.E3aModel.towerB B b₀ s₀ k))).g) i)) ∧
        Epi (HomologicalComplex.homologyMap
        (Work.Serre.E3aStep.stepMapQ p
          (Work.RatHurewicz.attachIncl (k + 1) (Work.Serre.CWModel.genStep
            (Work.Serre.E3aModel.towerB B b₀ s₀ k)).Y
            (Work.Serre.E3aModel.KillIdx2 (Work.Serre.CWModel.genStep
              (Work.Serre.E3aModel.towerB B b₀ s₀ k)))
            (Work.Serre.E3aModel.KillFr (Work.Serre.CWModel.genStep
              (Work.Serre.E3aModel.towerB B b₀ s₀ k))))
          (Work.Serre.CWModel.killStep (Work.Serre.CWModel.genStep
            (Work.Serre.E3aModel.towerB B b₀ s₀ k))).g) N) := by
      rw [Work.Serre.E3aModel.stepMapQ_attachIncl_eq_cellStepMap p
        (Work.Serre.CWModel.genStep (Work.Serre.E3aModel.towerB B b₀ s₀ k)).Y (k + 1)
        (Work.Serre.E3aModel.KillIdx2 (Work.Serre.CWModel.genStep
          (Work.Serre.E3aModel.towerB B b₀ s₀ k)))
        (Work.Serre.E3aModel.KillFr (Work.Serre.CWModel.genStep
          (Work.Serre.E3aModel.towerB B b₀ s₀ k)))
        (Work.Serre.CWModel.killStep (Work.Serre.CWModel.genStep
          (Work.Serre.E3aModel.towerB B b₀ s₀ k))).g]
      obtain ⟨hstepIso, hstepSurj⟩ :=
        Work.Serre.cellStepSharp (k + 1) (Work.Serre.CWModel.genStep
          (Work.Serre.E3aModel.towerB B b₀ s₀ k)).Y
          (Work.Serre.E3aModel.KillIdx2 (Work.Serre.CWModel.genStep
            (Work.Serre.E3aModel.towerB B b₀ s₀ k)))
          (Work.Serre.E3aModel.KillFr (Work.Serre.CWModel.genStep
            (Work.Serre.E3aModel.towerB B b₀ s₀ k)))
          (Work.StemsB.pullbackFst (Work.Serre.CWModel.killStep
            (Work.Serre.CWModel.genStep (Work.Serre.E3aModel.towerB B b₀ s₀ k))).g p)
          (Work.Serre.Assembly.pullbackFst_serre _ p hp) φ
          (fun z => (fibreData_pullback_below _ p z φ hfib h0).1)
          (fun z => (fibreData_pullback_below _ p z φ hfib h0).2)
      constructor
      · intro i hi
        exact hstepIso i (by omega)
      · rcases lt_or_eq_of_le (show N ≤ ((k + 1) + 2) + φ by omega) with h | h
        · haveI : IsIso (HomologicalComplex.homologyMap
              (Work.Serre.cellStepMap (k + 1)
                (Work.Serre.E3aModel.KillIdx2 (Work.Serre.CWModel.genStep
                  (Work.Serre.E3aModel.towerB B b₀ s₀ k)))
                (Work.Serre.E3aModel.KillFr (Work.Serre.CWModel.genStep
                  (Work.Serre.E3aModel.towerB B b₀ s₀ k)))
                (Work.StemsB.pullbackFst (Work.Serre.CWModel.killStep
                  (Work.Serre.CWModel.genStep (Work.Serre.E3aModel.towerB B b₀ s₀ k))).g p)) N) :=
            hstepIso N h
          exact IsIso.epi_of_iso _
        · rw [h]
          exact (ModuleCat.epi_iff_surjective _).mpr hstepSurj
    change RelGoodQ p N (Work.Serre.CWModel.killStep
      (Work.Serre.CWModel.genStep (Work.Serre.E3aModel.towerB B b₀ s₀ k))).y₀
      (Work.Serre.CWModel.killStep (Work.Serre.CWModel.genStep
        (Work.Serre.E3aModel.towerB B b₀ s₀ k))).g
    exact propagateRelQ p N (Work.Serre.CWModel.genStep
        (Work.Serre.E3aModel.towerB B b₀ s₀ k)).y₀
      (Work.Serre.CWModel.genStep (Work.Serre.E3aModel.towerB B b₀ s₀ k)).g hG
      (Work.RatHurewicz.attachIncl (k + 1) (Work.Serre.CWModel.genStep
        (Work.Serre.E3aModel.towerB B b₀ s₀ k)).Y
        (Work.Serre.E3aModel.KillIdx2 (Work.Serre.CWModel.genStep
          (Work.Serre.E3aModel.towerB B b₀ s₀ k)))
        (Work.Serre.E3aModel.KillFr (Work.Serre.CWModel.genStep
          (Work.Serre.E3aModel.towerB B b₀ s₀ k))))
      (Work.RatHurewicz.AttachRange.attachIncl_injective (k + 1) _ _ _)
      (Work.RatHurewicz.isInducing_attachIncl (k + 1) _ _ _)
      (Work.Serre.CWModel.killStep (Work.Serre.CWModel.genStep
        (Work.Serre.E3aModel.towerB B b₀ s₀ k))).g
      (fun x => rfl) hstepK

/-! ## The invariant at the top stage of the model -/

/-- **The relative invariant at the top stage of the `b = 1` model of `B`.** -/
theorem relGoodQ_model (p : C(E, B)) (hp : Work.StemsB.IsSerreFibration p) (b₀ : B)
    [PathConnectedSpace B] (N φ : ℕ) (hNφ : N ≤ φ + 1)
    (hfib : ∀ y : B, ∀ j : ℕ, 0 < j → j < φ →
      CategoryTheory.Limits.IsZero (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre p y)) j))
    (h0 : ∀ y : B, Nonempty (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre p y)) 0
      ≅ ModuleCat.of ℚ ℚ)) :
    RelGoodQ p N
      (Work.Serre.E3aModel.towerB B b₀ (Work.Serre.E3aModel.baseState B b₀) (N + 1)).y₀
      (Work.Serre.E3aModel.towerB B b₀ (Work.Serre.E3aModel.baseState B b₀) (N + 1)).g :=
  relGoodQ_tower p hp b₀ N φ hNφ hfib h0 (Work.Serre.E3aModel.baseState B b₀)
    (relGoodQ_base p hp b₀ N φ hNφ hfib h0) (N + 1)

end

end Work.Serre.B1Rel
