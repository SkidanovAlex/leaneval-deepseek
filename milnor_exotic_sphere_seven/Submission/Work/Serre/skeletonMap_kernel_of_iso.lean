import Mathlib
import Submission.Work.Serre.E3aSkDefs
import Submission.Work.Serre.E3aModel
import Submission.Work.Serre.exists_skeletonMap
import Submission.Work.Serre.OneCell.OneCellGeom
import Submission.Work.Serre.OneCell.Defs
import Submission.Work.Serre.SkelPi.Basic
import Submission.Work.Serre.SkelPi.CellClassHom
import Submission.Work.Serre.SkelPi.Generate

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The `1`-skeleton of the model: a map with prescribed `π₁`-kernel

Given a group isomorphism `φ : π₁(X,pt) ≃* π₁(B,b₀)`, we construct a map
`f : Skeleton X pt → B` sending the base point to `b₀`, with `π₁(f)` surjective and with the same
kernel as the structure map `skelMap X pt : Skeleton X pt → X`.

The construction sends the `w`-th `1`-cell of the skeleton (a based loop of `X`) to a chosen based
loop of `B` representing `φ` of the class of that loop.  The computation of `π₁(f)` uses that the
classes of the `1`-cells generate `π₁` of the skeleton (a wedge of circles).
-/

open scoped Topology Topology.Homotopy unitInterval

namespace Work.Serre

/-- The chosen loop of `B` representing `φ` applied to the class of the `w`-th cell of the
skeleton, as a based cube loop of `B`. -/
noncomputable def skelChosenGenLoop {X : Type} [TopologicalSpace X] (pt : X)
    {B : Type} [TopologicalSpace B] (b₀ : B)
    (φ : HomotopyGroup (Fin 1) X pt ≃* HomotopyGroup (Fin 1) B b₀)
    (w : Work.Serre.SkelPi.Idx X pt) : Ω^ (Fin 1) B b₀ :=
  Quotient.out (φ (Work.StemsB.homotopyGroupCast (E3aModel.skelMap_base X pt) 0
    (Work.Serre.piMapN (E3aModel.skelMap X pt) 1 (Work.Serre.E3aSk.skeletonBase X pt)
      (Work.Serre.SkelPi.cellClassHom X pt w))))

/-- The chosen loop of `B` representing `φ` applied to the class of the `w`-th cell of the
skeleton, as a map on the interval. -/
noncomputable def skelChosenLoop {X : Type} [TopologicalSpace X] (pt : X)
    {B : Type} [TopologicalSpace B] (b₀ : B)
    (φ : HomotopyGroup (Fin 1) X pt ≃* HomotopyGroup (Fin 1) B b₀)
    (w : Work.Serre.SkelPi.Idx X pt) : C(unitInterval, B) :=
  ⟨fun t => (skelChosenGenLoop pt b₀ φ w).1 (fun _ => t), by fun_prop⟩

@[simp] theorem skelChosenLoop_apply {X : Type} [TopologicalSpace X] (pt : X)
    {B : Type} [TopologicalSpace B] (b₀ : B)
    (φ : HomotopyGroup (Fin 1) X pt ≃* HomotopyGroup (Fin 1) B b₀)
    (w : Work.Serre.SkelPi.Idx X pt) (t : unitInterval) :
    (skelChosenLoop pt b₀ φ w : unitInterval → B) t
      = (skelChosenGenLoop pt b₀ φ w).1 (fun _ => t) := rfl

theorem skelChosenLoop_boundary {X : Type} [TopologicalSpace X] (pt : X)
    {B : Type} [TopologicalSpace B] (b₀ : B)
    (φ : HomotopyGroup (Fin 1) X pt ≃* HomotopyGroup (Fin 1) B b₀)
    (w : Work.Serre.SkelPi.Idx X pt) :
    skelChosenLoop pt b₀ φ w 0 = b₀ ∧ skelChosenLoop pt b₀ φ w 1 = b₀ := by
  constructor
  · rw [skelChosenLoop_apply]
    exact (skelChosenGenLoop pt b₀ φ w).2 (fun _ => (0 : unitInterval)) (by simp [Cube.boundary])
  · rw [skelChosenLoop_apply]
    exact (skelChosenGenLoop pt b₀ φ w).2 (fun _ => (1 : unitInterval)) (by simp [Cube.boundary])

/-- The characteristic map of a cell of the skeleton, composed with the chosen loop of `B`. -/
noncomputable def skelCellMap {X : Type} [TopologicalSpace X] (pt : X)
    {B : Type} [TopologicalSpace B] (b₀ : B)
    (φ : HomotopyGroup (Fin 1) X pt ≃* HomotopyGroup (Fin 1) B b₀)
    (w : Work.Serre.SkelPi.Idx X pt) : C(Work.Serre.cellDiskOne, B) :=
  (skelChosenLoop pt b₀ φ w).comp
    ⟨fun x => Work.Serre.E3aSk.SkelMap.d1ToCube x 0, by fun_prop⟩

theorem skelCellMap_boundary {X : Type} [TopologicalSpace X] (pt : X)
    {B : Type} [TopologicalSpace B] (b₀ : B)
    (φ : HomotopyGroup (Fin 1) X pt ≃* HomotopyGroup (Fin 1) B b₀)
    (w : Work.Serre.SkelPi.Idx X pt) (z : Work.Serre.cellSphereZero) :
    skelCellMap pt b₀ φ w (Work.Serre.cellSphereZeroToDiskOne z) = b₀ := by
  obtain ⟨h0, h1⟩ := skelChosenLoop_boundary pt b₀ φ w
  have hz : z = Work.Serre.SkelPi.bndL ∨ z = Work.Serre.SkelPi.bndR := by
    have hz' : |(z : ℝ)| = 1 := by
      have h := Metric.mem_sphere.mp z.2
      rwa [Real.dist_eq, sub_zero] at h
    rcases (abs_eq (show (0 : ℝ) ≤ 1 by norm_num)).mp hz' with h | h
    · right
      refine Subtype.ext ?_
      rw [Work.Serre.SkelPi.bndR, h]
    · left
      refine Subtype.ext ?_
      rw [Work.Serre.SkelPi.bndL, h]
  have hcoe : ∀ a : Work.Serre.cellDiskOne, ((a : ℝ) = -1) → a = Work.Serre.SkelPi.endL :=
    fun a ha => Subtype.ext (by rw [Work.Serre.SkelPi.endL_coe]; exact ha)
  rw [skelCellMap, ContinuousMap.comp_apply]
  rcases hz with hz | hz
  · rw [hz, Work.Serre.SkelPi.cellSphereZeroToDiskOne_bndL]
    change (skelChosenLoop pt b₀ φ w) (((fun x => Work.Serre.E3aSk.SkelMap.d1ToCube x 0))
      Work.Serre.SkelPi.endL) = b₀
    have hd : ((fun x => Work.Serre.E3aSk.SkelMap.d1ToCube x 0) Work.Serre.SkelPi.endL)
        = (0 : unitInterval) := by
      refine Subtype.ext ?_
      show (((Work.Serre.SkelPi.endL : Work.Serre.cellDiskOne) : ℝ) + 1) / 2 = 0
      rw [Work.Serre.SkelPi.endL_coe]
      norm_num
    rw [hd]
    exact h0
  · rw [hz, Work.Serre.SkelPi.cellSphereZeroToDiskOne_bndR]
    change (skelChosenLoop pt b₀ φ w) (((fun x => Work.Serre.E3aSk.SkelMap.d1ToCube x 0))
      Work.Serre.SkelPi.endR) = b₀
    have hd : ((fun x => Work.Serre.E3aSk.SkelMap.d1ToCube x 0) Work.Serre.SkelPi.endR)
        = (1 : unitInterval) := by
      refine Subtype.ext ?_
      show (((Work.Serre.SkelPi.endR : Work.Serre.cellDiskOne) : ℝ) + 1) / 2 = 1
      rw [Work.Serre.SkelPi.endR_coe]
      norm_num
    rw [hd]
    exact h1

/-- **The map of the skeleton to `B`** sending the `w`-th cell to the chosen loop. -/
noncomputable def skelMapTo {X : Type} [TopologicalSpace X] (pt : X)
    {B : Type} [TopologicalSpace B] (b₀ : B)
    (φ : HomotopyGroup (Fin 1) X pt ≃* HomotopyGroup (Fin 1) B b₀) :
    C(Work.Serre.E3aSk.Skeleton X pt, B) :=
  Work.Serre.E3aSk.SkelMap.oneAttachG PUnit (Work.Serre.SkelPi.Idx X pt)
    (Work.Serre.E3aSk.skeletonAttach X pt) (ContinuousMap.const PUnit b₀)
    (skelCellMap pt b₀ φ) (fun w z => skelCellMap_boundary pt b₀ φ w z)

theorem skelMapTo_base {X : Type} [TopologicalSpace X] (pt : X)
    {B : Type} [TopologicalSpace B] (b₀ : B)
    (φ : HomotopyGroup (Fin 1) X pt ≃* HomotopyGroup (Fin 1) B b₀) :
    skelMapTo pt b₀ φ (Work.Serre.E3aSk.skeletonBase X pt) = b₀ := by
  rw [skelMapTo]
  exact Work.Serre.E3aSk.SkelMap.oneAttachG_incl PUnit (Work.Serre.SkelPi.Idx X pt)
    (Work.Serre.E3aSk.skeletonAttach X pt) (ContinuousMap.const PUnit b₀)
    (skelCellMap pt b₀ φ) (fun w z => skelCellMap_boundary pt b₀ φ w z) PUnit.unit

theorem skelMapTo_cell {X : Type} [TopologicalSpace X] (pt : X)
    {B : Type} [TopologicalSpace B] (b₀ : B)
    (φ : HomotopyGroup (Fin 1) X pt ≃* HomotopyGroup (Fin 1) B b₀)
    (w : Work.Serre.SkelPi.Idx X pt) (x : Work.Serre.cellDiskOne) :
    skelMapTo pt b₀ φ (Work.Serre.oneCellMap PUnit (Work.Serre.SkelPi.Idx X pt)
        (Work.Serre.E3aSk.skeletonAttach X pt) w x) = skelCellMap pt b₀ φ w x := rfl

/-- **The computation of `π₁` of the constructed map on the classes of the `1`-cells.** -/
theorem skelMapTo_piMapN_cellClass (X : Type) [TopologicalSpace X] (pt : X)
    {B : Type} [TopologicalSpace B] (b₀ : B)
    (φ : HomotopyGroup (Fin 1) X pt ≃* HomotopyGroup (Fin 1) B b₀)
    (w : Work.Serre.SkelPi.Idx X pt) :
    Work.Serre.piMapN (skelMapTo pt b₀ φ) 1 (Work.Serre.E3aSk.skeletonBase X pt)
        (Work.Serre.SkelPi.cellClassHom X pt w)
      = φ (Work.StemsB.homotopyGroupCast (E3aModel.skelMap_base X pt) 0
          (Work.Serre.piMapN (E3aModel.skelMap X pt) 1 (Work.Serre.E3aSk.skeletonBase X pt)
            (Work.Serre.SkelPi.cellClassHom X pt w))) := by
  rw [Work.Serre.SkelPi.cellClassHom, Work.Serre.piMapN_apply_mk]
  have hloop : Work.StemsB.genLoopMap (skelMapTo pt b₀ φ) 1
      (⟨(Work.Serre.SkelPi.cellMap X pt w).comp Work.Serre.E3aSk.SkelMap.cubeToD1,
        Work.Serre.SkelPi.cellCube_boundary X pt w⟩ :
        Ω^ (Fin 1) (Work.Serre.SkelPi.Skel X pt) (Work.Serre.SkelPi.base X pt))
      = skelChosenGenLoop pt b₀ φ w := by
    apply GenLoop.ext
    intro u
    show skelMapTo pt b₀ φ ((Work.Serre.SkelPi.cellMap X pt w)
        (Work.Serre.E3aSk.SkelMap.cubeToD1 u))
      = (skelChosenGenLoop pt b₀ φ w).1 u
    rw [show skelMapTo pt b₀ φ ((Work.Serre.SkelPi.cellMap X pt w)
          (Work.Serre.E3aSk.SkelMap.cubeToD1 u))
        = skelCellMap pt b₀ φ w (Work.Serre.E3aSk.SkelMap.cubeToD1 u) from rfl]
    rw [skelCellMap, ContinuousMap.comp_apply, skelChosenLoop_apply]
    show (skelChosenGenLoop pt b₀ φ w).1
        (fun _ : Fin 1 => Work.Serre.E3aSk.SkelMap.d1ToCube
          (Work.Serre.E3aSk.SkelMap.cubeToD1 u) 0)
      = (skelChosenGenLoop pt b₀ φ w).1 u
    rw [Work.Serre.E3aSk.SkelMap.d1ToCube_cubeToD1]
    rw [show (fun _ : Fin 1 => u 0) = u from
      funext (fun v => (congrArg u (Subsingleton.elim v 0)).symm)]
  rw [hloop, skelChosenGenLoop]
  exact Quotient.out_eq (s := GenLoop.Homotopic.setoid (Fin 1) b₀) _

/-- **The main result.**  Given a group isomorphism `φ : π₁(X, pt) ≃* π₁(B, b₀)`, there is a map
`f` from the `1`-skeleton of `X` to `B` which sends the base point to `b₀`, induces a surjection on
`π₁`, and has the same kernel on `π₁` as the structure map `skelMap X pt : Skeleton X pt → X`. -/
theorem skeletonMap_kernel_of_iso
    {X : Type} [TopologicalSpace X] (pt : X)
    {B : Type} [TopologicalSpace B] (b₀ : B)
    (φ : HomotopyGroup (Fin 1) X pt ≃* HomotopyGroup (Fin 1) B b₀) :
    ∃ f : C(Work.Serre.E3aSk.Skeleton X pt, B),
      f (Work.Serre.E3aSk.skeletonBase X pt) = b₀ ∧
      Function.Surjective (Work.Serre.piMapN f 1 (Work.Serre.E3aSk.skeletonBase X pt)) ∧
      ∀ α : HomotopyGroup (Fin 1) (Work.Serre.E3aSk.Skeleton X pt)
          (Work.Serre.E3aSk.skeletonBase X pt),
        (Work.Serre.piMapN f 1 (Work.Serre.E3aSk.skeletonBase X pt) α = 1 ↔
          Work.Serre.piMapN (Work.Serre.E3aModel.skelMap X pt) 1
            (Work.Serre.E3aSk.skeletonBase X pt) α = 1) := by
  classical
  have hagree : ∀ α : HomotopyGroup (Fin 1) (Work.Serre.E3aSk.Skeleton X pt)
      (Work.Serre.E3aSk.skeletonBase X pt),
      Work.Serre.piMapN (skelMapTo pt b₀ φ) 1 (Work.Serre.E3aSk.skeletonBase X pt) α
        = φ (Work.StemsB.homotopyGroupCast (Work.Serre.E3aModel.skelMap_base X pt) 0
            (Work.Serre.piMapN (Work.Serre.E3aModel.skelMap X pt) 1
              (Work.Serre.E3aSk.skeletonBase X pt) α)) := by
    let ψ : HomotopyGroup (Fin 1) (Work.Serre.E3aSk.Skeleton X pt)
        (Work.Serre.E3aSk.skeletonBase X pt) →* HomotopyGroup (Fin 1) B b₀ :=
      Work.StemsB.πmap (skelMapTo pt b₀ φ) 0 (Work.Serre.E3aSk.skeletonBase X pt)
    let χ : HomotopyGroup (Fin 1) (Work.Serre.E3aSk.Skeleton X pt)
        (Work.Serre.E3aSk.skeletonBase X pt) →* HomotopyGroup (Fin 1) B b₀ :=
      φ.toMonoidHom.comp
        ((Work.StemsB.homotopyGroupCast (Work.Serre.E3aModel.skelMap_base X pt) 0).toMonoidHom.comp
          (Work.StemsB.πmap (Work.Serre.E3aModel.skelMap X pt) 0
            (Work.Serre.E3aSk.skeletonBase X pt)))
    have key : ∀ α (_ : α ∈ Subgroup.closure
        (Set.range (Work.Serre.SkelPi.cellClassHom X pt))), ψ α = χ α := by
      intro α hα
      refine Subgroup.closure_induction (p := fun β _ => ψ β = χ β) ?_ ?_ ?_ ?_ hα
      · intro x hx
        obtain ⟨w, rfl⟩ := hx
        change Work.Serre.piMapN (skelMapTo pt b₀ φ) 1 (Work.Serre.E3aSk.skeletonBase X pt)
            (Work.Serre.SkelPi.cellClassHom X pt w)
          = φ (Work.StemsB.homotopyGroupCast (Work.Serre.E3aModel.skelMap_base X pt) 0
              (Work.Serre.piMapN (Work.Serre.E3aModel.skelMap X pt) 1
                (Work.Serre.E3aSk.skeletonBase X pt) (Work.Serre.SkelPi.cellClassHom X pt w)))
        exact skelMapTo_piMapN_cellClass X pt b₀ φ w
      · rw [map_one, map_one]
      · intro x y hx hy hpx hpy
        rw [map_mul, map_mul, hpx, hpy]
      · intro x hx hpx
        rw [map_inv, map_inv, hpx]
    intro α
    change ψ α = χ α
    exact key α (by
      rw [Work.Serre.SkelPi.closure_cellClassHom_eq_top X pt]
      exact Subgroup.mem_top α)
  refine ⟨skelMapTo pt b₀ φ, skelMapTo_base pt b₀ φ, ?_, ?_⟩
  · intro β
    obtain ⟨α, hα⟩ := Work.Serre.E3aModel.skelMap_surj X pt
      ((Work.StemsB.homotopyGroupCast (Work.Serre.E3aModel.skelMap_base X pt) 0).symm (φ.symm β))
    refine ⟨α, ?_⟩
    rw [hagree α, hα, MulEquiv.apply_symm_apply]
    exact MulEquiv.apply_symm_apply φ β
  · intro α
    rw [hagree α]
    constructor
    · intro h
      exact (Work.StemsB.homotopyGroupCast (Work.Serre.E3aModel.skelMap_base X pt) 0).map_eq_one_iff.mp
        (φ.map_eq_one_iff.mp h)
    · intro h
      exact φ.map_eq_one_iff.mpr
        ((Work.StemsB.homotopyGroupCast (Work.Serre.E3aModel.skelMap_base X pt) 0).map_eq_one_iff.mpr h)

end Work.Serre
