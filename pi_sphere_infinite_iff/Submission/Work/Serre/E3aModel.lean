import Mathlib
import Submission.Work.Serre.E3aDefs
import Submission.Work.Serre.E3aStepDefs
import Submission.Work.Serre.E3aSkDefs
import Submission.Work.Serre.serreRangeEMVanAll
import Submission.Work.Serre.propagateAbsQ
import Submission.Work.Serre.exists_skeletonMap
import Submission.Work.Serre.pathConnectedSpace_attachOneCells
import Submission.Work.Serre.RatTower.fiveLemmaTau2
import Submission.Work.Serre.RatTower.pullbackFstRangeHomeo
import Submission.Work.Serre.RatTower.Attach
import Submission.Work.Serre.SPC.piOne_killStep
import Submission.Work.Serre.ratFibreTransport
import Submission.Work.Serre.ratPairBasic
import Submission.Work.Serre.oneCellStepRelHomologyIso
import Submission.Work.Serre.cellStepRelHomologyIso
import Submission.Work.Serre.Assembly.pullbackSnd_piMapN_bijective
import Submission.Work.Serre.Assembly.pullbackFst_serre
import Submission.Work.Serre.pullbackFst_piMapN_bijective
import Submission.Work.Serre.serreK2Proved
import Submission.Work.Serre.serreE3aStepA
import Submission.Work.Cohomology.relChainsMapOf_comp
import Submission.Work.Serre.CWModel.Tower
import Submission.Work.Serre.CWModel.Gen
import Submission.Work.Serre.CWModel.Kill
import Submission.Work.RatHurewicz.AttachRange.AttachInclInj

set_option synthInstance.maxHeartbeats 400000


/-!
# `E3(a)`: the model of the base and the cellular induction

This file assembles `Work.Serre.SerreE3aFibreAcyclic` from

* the `1`-skeleton `Work.Serre.E3aSk.Skeleton` with its structure map
  (`Work.Serre.exists_skeletonMap`) and the `π₁`-killing step `Work.Serre.SPC.piOne_killStep`,
  giving the base stage `Work.Serre.E3aModel.baseState` of the model with `π₁` bijective;
* the generator and killing steps `Work.Serre.CWModel.genStep`/`killStep`, iterated along
  `Work.Serre.E3aModel.towerB`;
* the cellular induction `Work.Serre.propagateAbsQ` for the invariant
  `Work.Serre.E3aStep.AbsGoodQ`, with the cell steps supplied by
  `Work.Serre.oneCellStepRelHomologyIso` and `Work.Serre.cellStepRelHomologyIso`
  (and the fibre data transported along paths in `B` by
  `Work.Serre.isZero_ratH_fibre_of_path`).
-/

open CategoryTheory CategoryTheory.Limits
open scoped Topology

namespace Work.Serre.E3aModel

noncomputable section

/-! ## The skeleton and the base stage -/

/-- The structure map of the `1`-skeleton. -/
noncomputable def skelMap (B : Type) [TopologicalSpace B] (b₀ : B) :
    C(Work.Serre.E3aSk.Skeleton B b₀, B) :=
  Classical.choose (Work.Serre.exists_skeletonMap B b₀)

theorem skelMap_base (B : Type) [TopologicalSpace B] (b₀ : B) :
    skelMap B b₀ (Work.Serre.E3aSk.skeletonBase B b₀) = b₀ :=
  (Classical.choose_spec (Work.Serre.exists_skeletonMap B b₀)).1

theorem skelMap_surj (B : Type) [TopologicalSpace B] (b₀ : B) :
    Function.Surjective
      (Work.Serre.piMapN (skelMap B b₀) 1 (Work.Serre.E3aSk.skeletonBase B b₀)) :=
  (Classical.choose_spec (Work.Serre.exists_skeletonMap B b₀)).2

/-- The index type of the `2`-cells killing the kernel of `π₁` of the skeleton map. -/
abbrev KilIdx (B : Type) [TopologicalSpace B] (b₀ : B) : Type :=
  {α : HomotopyGroup (Fin 1) (Work.Serre.E3aSk.Skeleton B b₀)
      (Work.Serre.E3aSk.skeletonBase B b₀) //
    Work.Serre.piMapN (skelMap B b₀) 1 (Work.Serre.E3aSk.skeletonBase B b₀) α = 1}

/-- The attaching maps of the killing `2`-cells. -/
abbrev KilFam (B : Type) [TopologicalSpace B] (b₀ : B) :
    KilIdx B b₀ → C(Work.RatHurewicz.cellSphere 0, Work.Serre.E3aSk.Skeleton B b₀) :=
  fun k => Work.RatHurewicz.killFamily 0 (Work.Serre.E3aSk.Skeleton B b₀)
    (Work.Serre.E3aSk.skeletonBase B b₀) k.1

/-- The extensions of the skeleton map over the killing cells. -/
noncomputable def kilG (B : Type) [TopologicalSpace B] (b₀ : B) :
    KilIdx B b₀ → C(Work.RatHurewicz.cellDisk 0, B) :=
  Classical.choose (Work.Serre.SPC.piOne_killStep b₀ (Work.Serre.E3aSk.skeletonBase B b₀)
    (skelMap B b₀) (skelMap_base B b₀) (skelMap_surj B b₀))

theorem kilG_spec (B : Type) [TopologicalSpace B] (b₀ : B) :
    ∀ (k : KilIdx B b₀) (z : Work.RatHurewicz.cellSphere 0),
      kilG B b₀ k (Work.RatHurewicz.cellSphereToDisk 0 z) = skelMap B b₀ (KilFam B b₀ k z) :=
  (Classical.choose_spec (Work.Serre.SPC.piOne_killStep b₀ (Work.Serre.E3aSk.skeletonBase B b₀)
    (skelMap B b₀) (skelMap_base B b₀) (skelMap_surj B b₀))).1

/-- The space of the base stage of the model. -/
abbrev BaseSpace (B : Type) [TopologicalSpace B] (b₀ : B) : Type :=
  Work.RatHurewicz.attachCells 0 (Work.Serre.E3aSk.Skeleton B b₀) (KilIdx B b₀) (KilFam B b₀)

/-- The base point of the base stage. -/
def basePt (B : Type) [TopologicalSpace B] (b₀ : B) : BaseSpace B b₀ :=
  Work.RatHurewicz.attachIncl 0 _ _ _ (Work.Serre.E3aSk.skeletonBase B b₀)

/-- The structure map of the base stage. -/
noncomputable def baseMap (B : Type) [TopologicalSpace B] (b₀ : B) : C(BaseSpace B b₀, B) :=
  Work.Serre.CWModel.attachG 0 _ _ _ (skelMap B b₀) (kilG B b₀) (kilG_spec B b₀)

theorem baseMap_incl (B : Type) [TopologicalSpace B] (b₀ : B)
    (y : Work.Serre.E3aSk.Skeleton B b₀) :
    baseMap B b₀ (Work.RatHurewicz.attachIncl 0 _ _ _ y) = skelMap B b₀ y := rfl

theorem baseMap_base (B : Type) [TopologicalSpace B] (b₀ : B) :
    baseMap B b₀ (basePt B b₀) = b₀ :=
  skelMap_base B b₀

theorem baseMap_pi1_bij (B : Type) [TopologicalSpace B] (b₀ : B) :
    Function.Bijective (Work.Serre.piMapN (baseMap B b₀) 1 (basePt B b₀)) :=
  (Classical.choose_spec (Work.Serre.SPC.piOne_killStep b₀ (Work.Serre.E3aSk.skeletonBase B b₀)
    (skelMap B b₀) (skelMap_base B b₀) (skelMap_surj B b₀))).2

theorem pathConnectedSpace_skeleton (B : Type) [TopologicalSpace B] (b₀ : B) :
    PathConnectedSpace (Work.Serre.E3aSk.Skeleton B b₀) :=
  Work.Serre.pathConnectedSpace_attachOneCells PUnit _ (Work.Serre.E3aSk.skeletonAttach B b₀)

theorem pathConnectedSpace_baseSpace (B : Type) [TopologicalSpace B] (b₀ : B) :
    PathConnectedSpace (BaseSpace B b₀) := by
  haveI := pathConnectedSpace_skeleton B b₀
  exact Work.Serre.CWModel.pathConnectedSpace_attachCells 0 _ _ _

/-- **The base stage of the model**: `B` replaced by a space with `π₁` bijective. -/
noncomputable def baseState (B : Type) [TopologicalSpace B] (b₀ : B) :
    Work.Serre.CWModel.StA B b₀ 0 where
  Y := BaseSpace B b₀
  inst := inferInstance
  y₀ := basePt B b₀
  g := baseMap B b₀
  gbase := baseMap_base B b₀
  conn := pathConnectedSpace_baseSpace B b₀
  bij := by
    intro j hj
    have hj0 : j = 0 := by omega
    subst hj0
    exact baseMap_pi1_bij B b₀

/-! ## The tower of the model -/

/-- The index type of the generator step at level `n`. -/
abbrev GenIdx {B : Type} [TopologicalSpace B] {b₀ : B} {n : ℕ}
    (s : Work.Serre.CWModel.StA B b₀ n) : Type :=
  HomotopyGroup (Fin (n + 2)) B (s.g s.y₀)

/-- The attaching maps of the generator step (all constant at the base point). -/
abbrev GenFr {B : Type} [TopologicalSpace B] {b₀ : B} {n : ℕ}
    (s : Work.Serre.CWModel.StA B b₀ n) :
    GenIdx s → C(Work.RatHurewicz.cellSphere n, s.Y) :=
  fun _ => ContinuousMap.const _ s.y₀

/-- The index type of the killing step at level `n`. -/
abbrev KillIdx2 {B : Type} [TopologicalSpace B] {b₀ : B} {n : ℕ}
    (s : Work.Serre.CWModel.StG B b₀ n) : Type :=
  {α : HomotopyGroup (Fin (n + 2)) s.Y s.y₀ // Work.Serre.piMapN s.g (n + 2) s.y₀ α = 1}

/-- The attaching maps of the killing step. -/
abbrev KillFr {B : Type} [TopologicalSpace B] {b₀ : B} {n : ℕ}
    (s : Work.Serre.CWModel.StG B b₀ n) :
    KillIdx2 s → C(Work.RatHurewicz.cellSphere (n + 1), s.Y) :=
  fun k => Work.RatHurewicz.killFamily (n + 1) s.Y s.y₀ k.1

/-- The embedding of the old stage into the new one, for the generator step. -/
theorem isEmbedding_attachIncl_gen {B : Type} [TopologicalSpace B] {b₀ : B} {n : ℕ}
    (s : Work.Serre.CWModel.StA B b₀ n) :
    Topology.IsEmbedding (Work.RatHurewicz.attachIncl n s.Y (GenIdx s) (GenFr s)) :=
  Topology.IsEmbedding.mk (Work.RatHurewicz.isInducing_attachIncl n s.Y (GenIdx s) (GenFr s))
    (Work.RatHurewicz.AttachRange.attachIncl_injective n s.Y (GenIdx s) (GenFr s))

/-- The embedding of the old stage into the new one, for the killing step. -/
theorem isEmbedding_attachIncl_kill {B : Type} [TopologicalSpace B] {b₀ : B} {n : ℕ}
    (s : Work.Serre.CWModel.StG B b₀ n) :
    Topology.IsEmbedding (Work.RatHurewicz.attachIncl (n + 1) s.Y (KillIdx2 s) (KillFr s)) :=
  Topology.IsEmbedding.mk
    (Work.RatHurewicz.isInducing_attachIncl (n + 1) s.Y (KillIdx2 s) (KillFr s))
    (Work.RatHurewicz.AttachRange.attachIncl_injective (n + 1) s.Y (KillIdx2 s) (KillFr s))

/-- **The model tower**, starting from the base stage of `B`. -/
noncomputable def towerB (B : Type) [TopologicalSpace B] (b₀ : B)
    (s₀ : Work.Serre.CWModel.StA B b₀ 0) : (k : ℕ) → Work.Serre.CWModel.StA B b₀ k
  | 0 => s₀
  | (k + 1) => Work.Serre.CWModel.killStep (Work.Serre.CWModel.genStep (towerB B b₀ s₀ k))

theorem towerB_zero (B : Type) [TopologicalSpace B] (b₀ : B)
    (s₀ : Work.Serre.CWModel.StA B b₀ 0) : towerB B b₀ s₀ 0 = s₀ := rfl

theorem towerB_succ (B : Type) [TopologicalSpace B] (b₀ : B)
    (s₀ : Work.Serre.CWModel.StA B b₀ 0) (k : ℕ) :
    towerB B b₀ s₀ (k + 1)
      = Work.Serre.CWModel.killStep (Work.Serre.CWModel.genStep (towerB B b₀ s₀ k)) := rfl

/-- **The `π`-facts of the top stage of the tower**, at every base point. -/
theorem towerB_piMapN_bijective (B : Type) [TopologicalSpace B] [PathConnectedSpace B] (b₀ : B)
    (s₀ : Work.Serre.CWModel.StA B b₀ 0) (N : ℕ) :
    ∀ i : ℕ, i ≤ N → ∀ x : (towerB B b₀ s₀ (N + 1)).Y,
      Function.Bijective (Work.Serre.piMapN (towerB B b₀ s₀ (N + 1)).g i x) := by
  set s := towerB B b₀ s₀ (N + 1) with hs
  haveI hΓ : PathConnectedSpace s.Y := s.conn
  intro i hi x
  rcases Nat.eq_zero_or_pos i with h0 | hpos
  · subst h0
    haveI h1 : Subsingleton (HomotopyGroup (Fin 0) s.Y x) :=
      (HomotopyGroup.pi0EquivZerothHomotopy (X := s.Y) (x := x)).injective.subsingleton
    haveI hZB : Subsingleton (ZerothHomotopy B) :=
      ⟨fun a c => by
        obtain ⟨y, rfl⟩ := ZerothHomotopy.mk_surjective a
        obtain ⟨z, rfl⟩ := ZerothHomotopy.mk_surjective c
        obtain ⟨p⟩ := PathConnectedSpace.joined y z
        exact ZerothHomotopy.sound p⟩
    have h2 : Subsingleton (HomotopyGroup (Fin 0) B (s.g x)) :=
      (HomotopyGroup.pi0EquivZerothHomotopy (X := B) (x := s.g x)).injective.subsingleton
    exact ⟨fun a c _ => h1.elim a c, fun y => ⟨default, h2.elim _ _⟩⟩
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
    exact Work.Serre.bijective_piMapN_of_joined s.g (PathConnectedSpace.joined s.y₀ x) (j + 1)
      (s.bij j (by omega))

/-! ## The cell step is the step map of the induction -/

/-- The step map of the induction for a `(n+2)`-cell attachment is the cell step map
`Work.Serre.cellStepMap`. -/
theorem stepMapQ_attachIncl_eq_cellStepMap {B E : Type} [TopologicalSpace B] [TopologicalSpace E]
    (p : C(E, B)) (Y : Type) [TopologicalSpace Y] (n : ℕ) (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere n, Y)) (g' : C(Work.RatHurewicz.attachCells n Y ι f, B)) :
    Work.Serre.E3aStep.stepMapQ p (Work.RatHurewicz.attachIncl n Y ι f) g'
      = Work.Serre.cellStepMap n ι f (Work.StemsB.pullbackFst g' p) := by
  unfold Work.Serre.E3aStep.stepMapQ Work.Serre.E3aStep.stepRestrict
  unfold Work.Serre.cellStepMap Work.Serre.cellStepRestrict Work.Serre.relChainsRMapOf
  congr 1

/-- The step map of the induction for a `1`-cell attachment is the `1`-cell step map
`Work.Serre.oneCellStepMap`. -/
theorem stepMapQ_oneIncl_eq_oneCellStepMap {B E : Type} [TopologicalSpace B] [TopologicalSpace E]
    (p : C(E, B)) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(Work.Serre.cellSphereZero, Y)) (g' : C(Work.Serre.attachOneCells Y ι f, B)) :
    Work.Serre.E3aStep.stepMapQ p (Work.Serre.oneIncl Y ι f) g'
      = Work.Serre.oneCellStepMap ι f (Work.StemsB.pullbackFst g' p) := by
  unfold Work.Serre.E3aStep.stepMapQ Work.Serre.E3aStep.stepRestrict
  unfold Work.Serre.oneCellStepMap Work.Serre.oneCellStepRestrict Work.Serre.relChainsRMapOf
  congr 1

/-! ## The `1`-skeleton attaches along a trivial embedding -/

theorem injective_oneIncl_punit (ι : Type) (f : ι → C(Work.Serre.cellSphereZero, PUnit)) :
    Function.Injective (Work.Serre.oneIncl PUnit ι f) :=
  fun x y _ => Subsingleton.elim x y

theorem isInducing_oneIncl_punit (ι : Type) (f : ι → C(Work.Serre.cellSphereZero, PUnit)) :
    Topology.IsInducing (Work.Serre.oneIncl PUnit ι f) := by
  rw [Topology.isInducing_iff]
  exact Subsingleton.elim _ _


/-! ## The fibre data transfers along paths in the base -/

/-- The rational acyclicity of the fibres of a Serre fibration transfers along a path in the
base. -/
theorem fibreAcyclic_of_path {B E : Type} [TopologicalSpace B] [TopologicalSpace E]
    (p : C(E, B)) (hp : Work.StemsB.IsSerreFibration p) (b₀ y : B) (γ : C(unitInterval, B))
    (h0 : γ 0 = b₀) (h1 : γ 1 = y) (N : ℕ)
    (hfib : ∀ j : ℕ, 0 < j → j ≤ N → IsZero (ratH (TopCat.of (Work.StemsB.fibre p b₀)) j)) :
    ∀ j : ℕ, 0 < j → j ≤ N → IsZero (ratH (TopCat.of (Work.StemsB.fibre p y)) j) :=
  fun j hj hjN =>
    Work.Serre.isZero_ratH_fibre_of_path p hp b₀ y γ h0 h1 (N + 1)
      (fun j hj hjN => hfib j hj (by omega)) j hj (by omega)

/-- `H₀` of the fibre transfers along a path in the base. -/
theorem fibreH0_of_path {B E : Type} [TopologicalSpace B] [TopologicalSpace E]
    (p : C(E, B)) (hp : Work.StemsB.IsSerreFibration p) (b₀ y : B) (γ : C(unitInterval, B))
    (h0 : γ 0 = b₀) (h1 : γ 1 = y)
    (h : Nonempty (ratH (TopCat.of (Work.StemsB.fibre p b₀)) 0 ≅ ModuleCat.of ℚ ℚ)) :
    Nonempty (ratH (TopCat.of (Work.StemsB.fibre p y)) 0 ≅ ModuleCat.of ℚ ℚ) := by
  obtain ⟨e⟩ := Work.Serre.ratH_fibre_iso_of_path p hp γ 0
  rw [h0] at e
  rw [h1] at e
  exact ⟨e.symm ≪≫ h.some⟩


/-- The fibre data of the pullback of `p` along `g`, from the fibre data of `p`. -/
theorem fibreData_pullback {B E Γ : Type} [TopologicalSpace B] [TopologicalSpace E]
    [TopologicalSpace Γ] (g : C(Γ, B)) (p : C(E, B)) (y : Γ) (N : ℕ)
    (hfib : ∀ y' : B, ∀ j : ℕ, 0 < j → j ≤ N →
      IsZero (ratH (TopCat.of (Work.StemsB.fibre p y')) j))
    (h0 : ∀ y' : B, Nonempty (ratH (TopCat.of (Work.StemsB.fibre p y')) 0
      ≅ ModuleCat.of ℚ ℚ)) :
    (∀ k : ℕ, 0 < k → k ≤ N → IsZero
      (ratH (TopCat.of (Work.StemsB.fibre (Work.StemsB.pullbackFst g p) y)) k)) ∧
    Nonempty (ratH (TopCat.of (Work.StemsB.fibre (Work.StemsB.pullbackFst g p) y)) 0
      ≅ ModuleCat.of ℚ ℚ) :=
  ⟨fun k hk hkN => Work.Serre.RatTower.isZero_ratH_of_homeomorph
      (X := TopCat.of (Work.StemsB.fibre (Work.StemsB.pullbackFst g p) y))
      (Y := TopCat.of (Work.StemsB.fibre p (g y)))
      (Work.Serre.RatTower.fibrePullbackFstHomeo g p y) k (hfib (g y) k hk hkN),
    Work.Serre.RatTower.nonempty_ratH_zero_of_homeomorph
      (X := TopCat.of (Work.StemsB.fibre (Work.StemsB.pullbackFst g p) y))
      (Y := TopCat.of (Work.StemsB.fibre p (g y)))
      (Work.Serre.RatTower.fibrePullbackFstHomeo g p y) (h0 (g y))⟩

/-! ## The base case of the induction: the one-point base -/

/-- The pullback of `p` along the constant map at `b₀` is the fibre of `p` over `b₀`. -/
def pullbackConstHomeo {B E : Type} [TopologicalSpace B] [TopologicalSpace E] (p : C(E, B))
    (b₀ : B) :
    Work.StemsB.Pullback (ContinuousMap.const PUnit b₀) p ≃ₜ Work.StemsB.fibre p b₀ where
  toFun x := ⟨x.1.2, x.2.symm⟩
  invFun e := ⟨(⟨⟩, e.1), e.2.symm⟩
  left_inv x := Subtype.ext (Prod.ext (Subsingleton.elim ⟨⟩ x.1.1) rfl)
  right_inv e := Subtype.ext rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- `X → *` is a rational isomorphism in degrees `≤ N` when `H_j(X;ℚ) = 0` for `0 < j ≤ N` and
`H₀(X;ℚ) ≅ ℚ`. -/
theorem isIso_toPoint_of_acyclic {X : Type} [TopologicalSpace X] (N : ℕ)
    (hfib : ∀ j : ℕ, 0 < j → j ≤ N → IsZero (ratH (TopCat.of X) j))
    (h0 : Nonempty (ratH (TopCat.of X) 0 ≅ ModuleCat.of ℚ ℚ)) :
    ∀ j : ℕ, j ≤ N → IsIso (ratHomologyMap (toPoint X) j) := by
  intro j hj
  rcases Nat.eq_zero_or_pos j with h0j | hpos
  · subst h0j
    haveI : PathConnectedSpace X := Work.Serre.OneCell.pathConnectedSpace_of_ratH_zero_iso h0
    exact Work.Serre.isIso_ratHomologyMap_toPoint_zero_of_subsingleton_pi0 X
      (Classical.arbitrary X) (subsingleton_pi0_of_pathConnectedSpace X _)
  · exact IsZero.isIso (hfib j hpos hj)
      (Work.Cohomology.homologyContractible_ring ℚ (X := TopCat.of PUnit) j hpos)
      (ratHomologyMap (toPoint X) j)

/-- **The base case of the cellular induction**: for the one-point base, the invariant holds
whenever the fibre over `b₀` is rationally acyclic below `N` and connected. -/
theorem absGoodQ_punit {B E : Type} [TopologicalSpace B] [TopologicalSpace E] (p : C(E, B))
    (b₀ : B) (N : ℕ)
    (hfib : ∀ j : ℕ, 0 < j → j ≤ N → IsZero (ratH (TopCat.of (Work.StemsB.fibre p b₀)) j))
    (h0 : Nonempty (ratH (TopCat.of (Work.StemsB.fibre p b₀)) 0 ≅ ModuleCat.of ℚ ℚ)) :
    Work.Serre.E3aStep.AbsGoodQ p N (ContinuousMap.const PUnit b₀) := by
  have hiso := isIso_toPoint_of_acyclic N hfib h0
  have hfac : ∀ j : ℕ,
      ratHomologyMap (Work.StemsB.pullbackFst (ContinuousMap.const PUnit b₀) p) j
        = ratHomologyMap (pullbackConstHomeo p b₀ : C(_, _)) j
          ≫ ratHomologyMap (toPoint (Work.StemsB.fibre p b₀)) j := by
    intro j
    have hfun : Work.StemsB.pullbackFst (ContinuousMap.const PUnit b₀) p
        = (toPoint (Work.StemsB.fibre p b₀)).comp (pullbackConstHomeo p b₀ : C(_, _)) := by
      ext x
    rw [hfun, Work.Serre.ratHomologyMap_comp]
  constructor
  · intro j hj
    rw [hfac j]
    haveI := Work.Serre.OneCell.isIso_ratHomologyMap_homeo (pullbackConstHomeo p b₀) j
    haveI := hiso j (le_of_lt hj)
    infer_instance
  · rw [hfac N]
    haveI := Work.Serre.OneCell.isIso_ratHomologyMap_homeo (pullbackConstHomeo p b₀) N
    haveI := hiso N le_rfl
    exact IsIso.epi_of_iso _

/-! ## The base stage: the skeleton and the `π₁`-killing cells -/

/-- **The invariant at the `1`-skeleton**, propagated from the one-point base. -/
theorem absGoodQ_skeleton {B E : Type} [TopologicalSpace B] [TopologicalSpace E] (p : C(E, B))
    (hp : Work.StemsB.IsSerreFibration p) (b₀ : B) [PathConnectedSpace B] (N : ℕ)
    (hfib : ∀ y : B, ∀ j : ℕ, 0 < j → j ≤ N →
      IsZero (ratH (TopCat.of (Work.StemsB.fibre p y)) j))
    (h0 : ∀ y : B, Nonempty (ratH (TopCat.of (Work.StemsB.fibre p y)) 0 ≅ ModuleCat.of ℚ ℚ)) :
    Work.Serre.E3aStep.AbsGoodQ p N (skelMap B b₀) := by
  haveI : PathConnectedSpace (Work.Serre.E3aSk.Skeleton B b₀) := pathConnectedSpace_skeleton B b₀
  refine Work.Serre.propagateAbsQ p N (ContinuousMap.const PUnit b₀)
    (absGoodQ_punit p b₀ N (fun j hj hjN => hfib b₀ j hj hjN) (h0 b₀))
    (Work.Serre.oneIncl PUnit _ (Work.Serre.E3aSk.skeletonAttach B b₀))
    (injective_oneIncl_punit _ _) (isInducing_oneIncl_punit _ _) (skelMap B b₀) ?_ ?_
  · intro x
    exact skelMap_base B b₀
  · intro i hi
    rw [stepMapQ_oneIncl_eq_oneCellStepMap p PUnit (↥(GenLoop (Fin 1) B b₀))
      (Work.Serre.E3aSk.skeletonAttach B b₀) (skelMap B b₀)]
    refine Work.Serre.oneCellStepRelHomologyIso PUnit _ (Work.Serre.E3aSk.skeletonAttach B b₀)
      (Work.StemsB.pullbackFst (skelMap B b₀) p)
      (Work.Serre.Assembly.pullbackFst_serre _ p hp) N ?_ i (by omega)
    intro z
    exact fibreData_pullback (skelMap B b₀) p z N hfib h0

/-- **The invariant at the base stage** (the skeleton with the `π₁`-killing `2`-cells attached),
propagated from the skeleton. -/
theorem absGoodQ_base {B E : Type} [TopologicalSpace B] [TopologicalSpace E] (p : C(E, B))
    (hp : Work.StemsB.IsSerreFibration p) (b₀ : B) [PathConnectedSpace B] (N : ℕ)
    (hfib : ∀ y : B, ∀ j : ℕ, 0 < j → j ≤ N →
      IsZero (ratH (TopCat.of (Work.StemsB.fibre p y)) j))
    (h0 : ∀ y : B, Nonempty (ratH (TopCat.of (Work.StemsB.fibre p y)) 0 ≅ ModuleCat.of ℚ ℚ)) :
    Work.Serre.E3aStep.AbsGoodQ p N (baseMap B b₀) := by
  refine Work.Serre.propagateAbsQ p N (skelMap B b₀) (absGoodQ_skeleton p hp b₀ N hfib h0)
    (Work.RatHurewicz.attachIncl 0 (Work.Serre.E3aSk.Skeleton B b₀) (KilIdx B b₀)
      (KilFam B b₀))
    (Work.RatHurewicz.AttachRange.attachIncl_injective 0 _ _ _)
    (Work.RatHurewicz.isInducing_attachIncl 0 _ _ _) (baseMap B b₀) ?_ ?_
  · intro x
    exact baseMap_incl B b₀ x
  · intro i hi
    rw [stepMapQ_attachIncl_eq_cellStepMap p (Work.Serre.E3aSk.Skeleton B b₀) 0 (KilIdx B b₀)
      (KilFam B b₀) (baseMap B b₀)]
    refine Work.Serre.cellStepRelHomologyIso 0 (Work.Serre.E3aSk.Skeleton B b₀) (KilIdx B b₀)
      (KilFam B b₀) (Work.StemsB.pullbackFst (baseMap B b₀) p)
      (Work.Serre.Assembly.pullbackFst_serre _ p hp) N ?_ i (by omega)
    intro z
    exact fibreData_pullback (baseMap B b₀) p z N hfib h0

/-! ## The induction along the tower -/

/-- **The invariant propagates along the model tower.** -/
theorem towerB_absGoodQ {B E : Type} [TopologicalSpace B] [TopologicalSpace E] (p : C(E, B))
    (hp : Work.StemsB.IsSerreFibration p) (b₀ : B) [PathConnectedSpace B] (N : ℕ)
    (hfib : ∀ y : B, ∀ j : ℕ, 0 < j → j ≤ N →
      IsZero (ratH (TopCat.of (Work.StemsB.fibre p y)) j))
    (h0 : ∀ y : B, Nonempty (ratH (TopCat.of (Work.StemsB.fibre p y)) 0 ≅ ModuleCat.of ℚ ℚ))
    (s₀ : Work.Serre.CWModel.StA B b₀ 0) (h₀ : Work.Serre.E3aStep.AbsGoodQ p N s₀.g)
    (k : ℕ) :
    Work.Serre.E3aStep.AbsGoodQ p N (towerB B b₀ s₀ k).g := by
  induction k with
  | zero => exact h₀
  | succ k ih =>
    haveI hpc : PathConnectedSpace (towerB B b₀ s₀ k).Y := (towerB B b₀ s₀ k).conn
    -- the generator step
    have hstepG : ∀ i : ℕ, i < N + 1 → IsIso (HomologicalComplex.homologyMap
        (Work.Serre.E3aStep.stepMapQ p
          (Work.RatHurewicz.attachIncl k (towerB B b₀ s₀ k).Y (GenIdx (towerB B b₀ s₀ k))
            (GenFr (towerB B b₀ s₀ k)))
          (Work.Serre.CWModel.genStep (towerB B b₀ s₀ k)).g) i) := by
      intro i hi
      rw [stepMapQ_attachIncl_eq_cellStepMap p (towerB B b₀ s₀ k).Y k
        (GenIdx (towerB B b₀ s₀ k)) (GenFr (towerB B b₀ s₀ k))
        (Work.Serre.CWModel.genStep (towerB B b₀ s₀ k)).g]
      refine Work.Serre.cellStepRelHomologyIso k (towerB B b₀ s₀ k).Y
        (GenIdx (towerB B b₀ s₀ k)) (GenFr (towerB B b₀ s₀ k))
        (Work.StemsB.pullbackFst (Work.Serre.CWModel.genStep (towerB B b₀ s₀ k)).g p)
        (Work.Serre.Assembly.pullbackFst_serre _ p hp) N ?_ i (by omega)
      intro z
      exact fibreData_pullback (Work.Serre.CWModel.genStep (towerB B b₀ s₀ k)).g p z N hfib h0
    have hG : Work.Serre.E3aStep.AbsGoodQ p N (Work.Serre.CWModel.genStep
        (towerB B b₀ s₀ k)).g :=
      Work.Serre.propagateAbsQ p N (towerB B b₀ s₀ k).g ih
        (Work.RatHurewicz.attachIncl k (towerB B b₀ s₀ k).Y (GenIdx (towerB B b₀ s₀ k))
          (GenFr (towerB B b₀ s₀ k)))
        (Work.RatHurewicz.AttachRange.attachIncl_injective k _ _ _)
        (Work.RatHurewicz.isInducing_attachIncl k _ _ _)
        (Work.Serre.CWModel.genStep (towerB B b₀ s₀ k)).g (fun x => rfl) hstepG
    -- the killing step
    have hstepK : ∀ i : ℕ, i < N + 1 → IsIso (HomologicalComplex.homologyMap
        (Work.Serre.E3aStep.stepMapQ p
          (Work.RatHurewicz.attachIncl (k + 1) (Work.Serre.CWModel.genStep
            (towerB B b₀ s₀ k)).Y (KillIdx2 (Work.Serre.CWModel.genStep (towerB B b₀ s₀ k)))
            (KillFr (Work.Serre.CWModel.genStep (towerB B b₀ s₀ k))))
          (Work.Serre.CWModel.killStep (Work.Serre.CWModel.genStep
            (towerB B b₀ s₀ k))).g) i) := by
      intro i hi
      rw [stepMapQ_attachIncl_eq_cellStepMap p (Work.Serre.CWModel.genStep
        (towerB B b₀ s₀ k)).Y (k + 1) (KillIdx2 (Work.Serre.CWModel.genStep (towerB B b₀ s₀ k)))
        (KillFr (Work.Serre.CWModel.genStep (towerB B b₀ s₀ k)))
        (Work.Serre.CWModel.killStep (Work.Serre.CWModel.genStep (towerB B b₀ s₀ k))).g]
      refine Work.Serre.cellStepRelHomologyIso (k + 1) (Work.Serre.CWModel.genStep
        (towerB B b₀ s₀ k)).Y (KillIdx2 (Work.Serre.CWModel.genStep (towerB B b₀ s₀ k)))
        (KillFr (Work.Serre.CWModel.genStep (towerB B b₀ s₀ k)))
        (Work.StemsB.pullbackFst (Work.Serre.CWModel.killStep (Work.Serre.CWModel.genStep
          (towerB B b₀ s₀ k))).g p)
        (Work.Serre.Assembly.pullbackFst_serre _ p hp) N ?_ i (by omega)
      intro z
      exact fibreData_pullback (Work.Serre.CWModel.killStep (Work.Serre.CWModel.genStep
        (towerB B b₀ s₀ k))).g p z N hfib h0
    change Work.Serre.E3aStep.AbsGoodQ p N (Work.Serre.CWModel.killStep
      (Work.Serre.CWModel.genStep (towerB B b₀ s₀ k))).g
    exact Work.Serre.propagateAbsQ p N (Work.Serre.CWModel.genStep (towerB B b₀ s₀ k)).g hG
      (Work.RatHurewicz.attachIncl (k + 1) (Work.Serre.CWModel.genStep
        (towerB B b₀ s₀ k)).Y (KillIdx2 (Work.Serre.CWModel.genStep (towerB B b₀ s₀ k)))
        (KillFr (Work.Serre.CWModel.genStep (towerB B b₀ s₀ k))))
      (Work.RatHurewicz.AttachRange.attachIncl_injective (k + 1) _ _ _)
      (Work.RatHurewicz.isInducing_attachIncl (k + 1) _ _ _)
      (Work.Serre.CWModel.killStep (Work.Serre.CWModel.genStep (towerB B b₀ s₀ k))).g
      (fun x => rfl) hstepK


/-! ## The conclusion -/

/-- **`E3(a)`: the honest-fibre form.**  A Serre fibration over a path connected base whose fibre is
rationally acyclic in degrees `≤ N` and rationally connected induces an isomorphism on rational
homology in degrees `< N`. -/
theorem serreE3aFibreAcyclic : Work.Serre.SerreE3aFibreAcyclic := by
  intro X B _ _ q b₀ N hq hB hfib h0 i hi
  haveI : PathConnectedSpace B := hB
  -- the fibre data at every point of the base
  have hfib_all : ∀ y : B, ∀ j : ℕ, 0 < j → j ≤ N →
      IsZero (ratH (TopCat.of (Work.StemsB.fibre q y)) j) := by
    intro y j hj hjN
    exact fibreAcyclic_of_path q hq b₀ y
      (PathConnectedSpace.somePath b₀ y : C(unitInterval, B))
      (PathConnectedSpace.somePath b₀ y).source
      (PathConnectedSpace.somePath b₀ y).target N hfib j hj hjN
  have h0_all : ∀ y : B,
      Nonempty (ratH (TopCat.of (Work.StemsB.fibre q y)) 0 ≅ ModuleCat.of ℚ ℚ) := by
    intro y
    exact fibreH0_of_path q hq b₀ y
      (PathConnectedSpace.somePath b₀ y : C(unitInterval, B))
      (PathConnectedSpace.somePath b₀ y).source
      (PathConnectedSpace.somePath b₀ y).target h0
  -- the fibre over `b₀` is nonempty
  haveI hpcF : PathConnectedSpace (Work.StemsB.fibre q b₀) :=
    Work.Serre.OneCell.pathConnectedSpace_of_ratH_zero_iso h0
  haveI hneF : Nonempty (Work.StemsB.fibre q b₀) := hpcF.nonempty
  -- the model
  set s := towerB B b₀ (baseState B b₀) (N + 1) with hs
  haveI hne : Nonempty s.Y := ⟨s.y₀⟩
  have hgbij : ∀ j : ℕ, j ≤ N → ∀ x : s.Y, Function.Bijective (piMapN s.g j x) :=
    towerB_piMapN_bijective B b₀ (baseState B b₀) N
  have hA : Work.Serre.E3aStep.AbsGoodQ q N s.g :=
    towerB_absGoodQ q hq b₀ N hfib_all h0_all (baseState B b₀)
      (absGoodQ_base q hq b₀ N hfib_all h0_all) (N + 1)
  -- the pullback is nonempty
  haveI hneP : Nonempty (Work.StemsB.Pullback q s.g) := by
    obtain ⟨⟨e, he⟩⟩ := hneF
    exact ⟨⟨(e, s.y₀), by rw [he, s.gbase]⟩⟩
  -- the comparison on the `X` side: the base change of the model map
  have hpull : ∀ j : ℕ, j < N →
      IsIso (ratHomologyMap (Work.StemsB.pullbackFst q s.g) j) :=
    fun j hj => Work.Serre.serreK2Proved (Work.StemsB.Pullback q s.g) X
      (Work.StemsB.pullbackFst q s.g) N
      (fun j hj x => Work.Serre.pullbackFst_piMapN_bijective q s.g hq N hgbij j hj x) j hj
  -- the comparison on the `Γ` side: the model fibration, transported across the swap of pullbacks
  have hmodel : ∀ j : ℕ, j < N →
      IsIso (ratHomologyMap (Work.StemsB.pullbackSnd q s.g) j) := by
    intro j hj
    have hcomp : ratHomologyMap (Work.StemsB.pullbackSnd q s.g) j
        = ratHomologyMap (Work.Serre.Assembly.pullbackSwap q s.g) j
          ≫ ratHomologyMap (Work.StemsB.pullbackFst s.g q) j := by
      rw [← Work.Serre.ratHomologyMap_comp]
      congr 1
    rw [hcomp]
    haveI h1 : IsIso (ratHomologyMap (Work.Serre.Assembly.pullbackSwap q s.g) j) :=
      Work.Serre.OneCell.isIso_ratHomologyMap_homeo
        (Work.Serre.Assembly.pullbackSwapHomeomorph q s.g) j
    haveI h2 : IsIso (ratHomologyMap (Work.StemsB.pullbackFst s.g q) j) := hA.1 j hj
    infer_instance
  -- the model map itself
  have hg : ∀ j : ℕ, j < N → IsIso (ratHomologyMap s.g j) :=
    fun j hj => Work.Serre.serreK2Proved s.Y B s.g N
      (fun j hj x => hgbij j (le_of_lt hj) x) j hj
  -- the square `q ∘ pullbackFst = g ∘ pullbackSnd` in homology
  have hsq : ratHomologyMap (Work.StemsB.pullbackFst q s.g) i ≫ ratHomologyMap q i
      = ratHomologyMap (Work.StemsB.pullbackSnd q s.g) i ≫ ratHomologyMap s.g i := by
    rw [← Work.Serre.ratHomologyMap_comp, ← Work.Serre.ratHomologyMap_comp]
    congr 1
    ext x
    exact x.2
  haveI : IsIso (ratHomologyMap (Work.StemsB.pullbackFst q s.g) i) := hpull i hi
  haveI h2 : IsIso (ratHomologyMap (Work.StemsB.pullbackSnd q s.g) i) := hmodel i hi
  haveI h3 : IsIso (ratHomologyMap s.g i) := hg i hi
  haveI : IsIso (ratHomologyMap (Work.StemsB.pullbackFst q s.g) i ≫ ratHomologyMap q i) := by
    rw [hsq]
    infer_instance
  exact IsIso.of_isIso_comp_left (ratHomologyMap (Work.StemsB.pullbackFst q s.g) i)
    (ratHomologyMap q i)

/-- **`E3(a)`** (the form stated in the blueprint, with the hypothesis on the *homotopy* fibre). -/
theorem serreE3a_of_fibreAcyclic : Work.Serre.SerreE3a :=
  Work.Serre.serreE3aStepA serreE3aFibreAcyclic


end

end Work.Serre.E3aModel
