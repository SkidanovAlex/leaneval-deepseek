import Mathlib
import Submission.Work.Serre.SPC.B1Skeleton
import Submission.Work.Serre.SPC.piOne_killStep
import Submission.Work.PiS.Interfaces

set_option synthInstance.maxHeartbeats 400000


/-!
# Auxiliary constructions for the `k = 1` comparison

The `k = 1` comparison of two range models `Z`, `P` of `K(A,1)` is reduced to comparing two maps
out of the `1`-skeleton `Work.Serre.SPC.Skeleton Z z₀` (the wedge of one circle per based loop of
`Z`):

* `skeletonCellClass w` — the class in `π₁` of the `w`-th cell of the skeleton;
* `skeletonMap` (from `Work.Serre.SPC`) — the structure map `Skeleton Z z₀ → Z`, which sends the
  cell of `w` to `w` itself; hence `π₁(skeletonMap) (skeletonCellClass w) = [w]`
  (`piMapN_skeletonMap_skeletonCellClass`);
* `skeletonLoopMap Λ` — the map `Skeleton Z z₀ → P` which sends the cell of `w` to a loop of `P`
  representing `Λ [w]`; hence `π₁ (skeletonLoopMap Λ) (skeletonCellClass w) = Λ [w]`
  (`piMapN_skeletonLoopMap_skeletonCellClass`).

Since the cells generate `π₁` of the skeleton (`Work.EMFG.skeletonCellClasses_generate`), the two
structure maps have the same kernel, and the `π₁`-killing step `Work.Serre.SPC.piOne_killStep`
applies to both simultaneously.
-/

open scoped Topology Topology.Homotopy unitInterval

namespace Work.EMFG

open Work.Serre.SPC

noncomputable section

/-- The based loop in the skeleton `Skeleton B b₀` carried by the model `1`-cell of a based loop `w`
of `B` (the cell is glued at the base point, so the loop is well defined). -/
def skeletonCellLoop (B : Type) [TopologicalSpace B] (b₀ : B)
    (w : ↥(GenLoop (Fin 1) B b₀)) :
    ↥(GenLoop (Fin 1) (Skeleton B b₀) (skeletonBase B b₀)) :=
  ⟨(oneCellMap PUnit ↥(GenLoop (Fin 1) B b₀) (skeletonAttach B b₀) w).comp cubeToD1, by
    intro x hx
    obtain ⟨i, hi⟩ := hx
    have hx0 : x 0 = 0 ∨ x 0 = 1 := by
      rcases hi with h | h
      · left; simpa [Subsingleton.elim i 0] using h
      · right; simpa [Subsingleton.elim i 0] using h
    have hz : dist (2 * ((x 0 : unitInterval) : ℝ) - 1) 0 = 1 := by
      rw [Real.dist_eq, sub_zero]
      rcases hx0 with h | h
      · rw [show ((x 0 : unitInterval) : ℝ) = 0 from congrArg Subtype.val h]; norm_num
      · rw [show ((x 0 : unitInterval) : ℝ) = 1 from congrArg Subtype.val h]; norm_num
    show (oneCellMap PUnit ↥(GenLoop (Fin 1) B b₀) (skeletonAttach B b₀) w)
      (cellS0ToD1 ⟨2 * ((x 0 : unitInterval) : ℝ) - 1, hz⟩) = skeletonBase B b₀
    rw [← oneIncl_oneCellRel PUnit ↥(GenLoop (Fin 1) B b₀) (skeletonAttach B b₀) w
      ⟨2 * ((x 0 : unitInterval) : ℝ) - 1, hz⟩]
    rfl⟩

/-- The class in `π₁` of the `w`-th cell of the skeleton. -/
def skeletonCellClass (B : Type) [TopologicalSpace B] (b₀ : B)
    (w : ↥(GenLoop (Fin 1) B b₀)) :
    HomotopyGroup (Fin 1) (Skeleton B b₀) (skeletonBase B b₀) :=
  Quotient.mk _ (skeletonCellLoop B b₀ w)

/-- The structure map of the skeleton sends the cell of `w` to `w`, hence on `π₁` the cell class of
`w` maps to the class of `w`. -/
theorem piMapN_skeletonMap_skeletonCellClass (B : Type) [TopologicalSpace B] (b₀ : B)
    (w : ↥(GenLoop (Fin 1) B b₀)) :
    Work.Serre.piMapN (skeletonMap B b₀) 1 (skeletonBase B b₀) (skeletonCellClass B b₀ w)
      = Quotient.mk _ w := by
  rw [skeletonCellClass, Work.Serre.piMapN_apply_mk]
  apply Quotient.sound
  have hfun : ∀ t, Work.StemsB.genLoopMap (skeletonMap B b₀) 1 (skeletonCellLoop B b₀ w) t
      = w t := by
    intro t
    rw [Work.StemsB.genLoopMap_apply]
    show skeletonMap B b₀ ((oneCellMap PUnit ↥(GenLoop (Fin 1) B b₀) (skeletonAttach B b₀) w)
      (cubeToD1 t)) = w t
    rw [skeletonMap_cell]
    show ((w : C(Fin 1 → unitInterval, B)).comp d1ToCube) (cubeToD1 t) = w t
    rw [ContinuousMap.comp_apply, d1ToCube_cubeToD1]
    rfl
  have heq : Work.StemsB.genLoopMap (skeletonMap B b₀) 1 (skeletonCellLoop B b₀ w) = w :=
    Subtype.ext (ContinuousMap.ext hfun)
  change GenLoop.Homotopic (Work.StemsB.genLoopMap (skeletonMap B b₀) 1 (skeletonCellLoop B b₀ w)) w
  rw [heq]
  exact GenLoop.Homotopic.refl w

/-- A loop of `P` representing the class `x`, built from a chosen representative. -/
def loopOfClass {P : Type} [TopologicalSpace P] (p₀ : P)
    (x : HomotopyGroup (Fin 1) P p₀) : C(cellD1, P) :=
  loopOf p₀ (Quotient.out x)

theorem loopOfClass_boundary {P : Type} [TopologicalSpace P] (p₀ : P)
    (x : HomotopyGroup (Fin 1) P p₀) (z : cellS0) :
    loopOfClass p₀ x (cellS0ToD1 z) = p₀ :=
  loopOf_boundary p₀ (Quotient.out x) z

/-- **The structure map of the skeleton into `P`, carrying the cell of `w` to a loop of `P`
representing `Λ [w]`.** -/
def skeletonLoopMap {Z : Type} [TopologicalSpace Z] (z₀ : Z)
    {P : Type} [TopologicalSpace P] (p₀ : P)
    (Λ : HomotopyGroup (Fin 1) Z z₀ ≃* HomotopyGroup (Fin 1) P p₀) :
    C(Skeleton Z z₀, P) :=
  oneAttachG PUnit ↥(GenLoop (Fin 1) Z z₀) (skeletonAttach Z z₀)
    (ContinuousMap.const PUnit p₀)
    (fun w => loopOfClass p₀ (Λ (Quotient.mk _ w)))
    (fun w z => loopOfClass_boundary p₀ (Λ (Quotient.mk _ w)) z)

@[simp] theorem skeletonLoopMap_base {Z : Type} [TopologicalSpace Z] (z₀ : Z)
    {P : Type} [TopologicalSpace P] (p₀ : P)
    (Λ : HomotopyGroup (Fin 1) Z z₀ ≃* HomotopyGroup (Fin 1) P p₀) :
    skeletonLoopMap z₀ p₀ Λ (skeletonBase Z z₀) = p₀ := rfl

@[simp] theorem skeletonLoopMap_cell {Z : Type} [TopologicalSpace Z] (z₀ : Z)
    {P : Type} [TopologicalSpace P] (p₀ : P)
    (Λ : HomotopyGroup (Fin 1) Z z₀ ≃* HomotopyGroup (Fin 1) P p₀)
    (w : ↥(GenLoop (Fin 1) Z z₀)) (x : cellD1) :
    skeletonLoopMap z₀ p₀ Λ (oneCellMap PUnit ↥(GenLoop (Fin 1) Z z₀) (skeletonAttach Z z₀) w x)
      = loopOfClass p₀ (Λ (Quotient.mk _ w)) x := rfl

/-- On `π₁`, the cell class of `w` maps under `skeletonLoopMap` to `Λ` of the class of `w`. -/
theorem piMapN_skeletonLoopMap_skeletonCellClass {Z : Type} [TopologicalSpace Z] (z₀ : Z)
    {P : Type} [TopologicalSpace P] (p₀ : P)
    (Λ : HomotopyGroup (Fin 1) Z z₀ ≃* HomotopyGroup (Fin 1) P p₀)
    (w : ↥(GenLoop (Fin 1) Z z₀)) :
    Work.Serre.piMapN (skeletonLoopMap z₀ p₀ Λ) 1 (skeletonBase Z z₀)
      (skeletonCellClass Z z₀ w) = Λ (Quotient.mk _ w) := by
  rw [skeletonCellClass, Work.Serre.piMapN_apply_mk]
  set v : ↥(GenLoop (Fin 1) P p₀) := Quotient.out (Λ (Quotient.mk _ w)) with hv
  have hvq : Quotient.mk _ v = Λ (Quotient.mk _ w) := by rw [hv]; exact Quotient.out_eq _
  rw [← hvq]
  apply Quotient.sound
  have hfun : ∀ t, Work.StemsB.genLoopMap (skeletonLoopMap z₀ p₀ Λ) 1 (skeletonCellLoop Z z₀ w) t
      = v t := by
    intro t
    rw [Work.StemsB.genLoopMap_apply]
    show skeletonLoopMap z₀ p₀ Λ
      ((oneCellMap PUnit ↥(GenLoop (Fin 1) Z z₀) (skeletonAttach Z z₀) w) (cubeToD1 t)) = v t
    rw [skeletonLoopMap_cell]
    show loopOfClass p₀ (Λ (Quotient.mk _ w)) (cubeToD1 t) = v t
    rw [loopOfClass, hv]
    show ((v : C(Fin 1 → unitInterval, P)).comp d1ToCube) (cubeToD1 t) = v t
    rw [ContinuousMap.comp_apply, d1ToCube_cubeToD1]
    rfl
  have heq : Work.StemsB.genLoopMap (skeletonLoopMap z₀ p₀ Λ) 1 (skeletonCellLoop Z z₀ w) = v :=
    Subtype.ext (ContinuousMap.ext hfun)
  change GenLoop.Homotopic (Work.StemsB.genLoopMap (skeletonLoopMap z₀ p₀ Λ) 1
    (skeletonCellLoop Z z₀ w)) v
  rw [heq]
  exact GenLoop.Homotopic.refl v

end

end Work.EMFG
