import Mathlib
import Submission.Work.Serre.E3aSkDefs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The structure map of the `1`-skeleton of the model of `B`

`Work.Serre.E3aSk.Skeleton B b₀` is the space obtained from the one-point space `PUnit` by attaching
one `1`-cell per based loop of `B` (all of them glued at the single point of `PUnit`), i.e. the
wedge of one circle per element of `Ω^ (Fin 1) B b₀`.

The main result of this file, `Work.Serre.exists_skeletonMap`, provides the **structure map**

  `SkelMap.skeletonMap B b₀ : Skeleton B b₀ → B`

sending the cell of a based loop `w` to the loop `w` itself (reparametrised from the cube `Fin 1 → I`
to the model interval `D¹ = [-1,1]`), together with

* `skeletonMap_base` — it sends the base point of the skeleton to `b₀`;
* `skeletonMap_piOne_surjective` — the induced map `π₁(Skeleton B b₀) → π₁(B)` is **surjective**
  (the cell of a representative loop of a class `α ∈ π₁(B)` is a loop in the skeleton mapping onto
  `α`).

The same construction in the parallel `Work.Serre.SPC` vocabulary is `Work.Serre.SPC.skeletonMap`
in `Submission/Work/Serre/SPC/B1Skeleton.lean`; the two files cannot be imported together
(`Work.Serre.cellStepMap` is declared in both `E3aDefs.lean` and `cellStepDefs.lean`), so it is
repeated here in the `E3a`-vocabulary of `E3aDefs.lean`, and this time *with* the recursor
`oneAttachG` of the `1`-cell attachment, which only exists on the `SPC` side.

## Contents

(All the auxiliary constructions below live in the sub-namespace `Work.Serre.E3aSk.SkelMap`, so
that they cannot collide with a future addition to `E3aSkDefs.lean`.)

* `d1ToCube`/`cubeToD1` — the affine identification `D¹ = [-1,1] ≅ I`;
* `oneCellGlue`, `oneAttachG` (**the recursor** for `Work.Serre.attachOneCells`: a map out of a space
  obtained by attaching `1`-cells is given by a map on the old part together with maps on the cells,
  agreeing on the boundaries), with the computation rules `oneAttachG_incl`, `oneAttachG_cell`;
* `loopOf`, `loopOf_boundary` — a based loop of `B` as a map on `D¹`, constantly `b₀` on `S⁰`;
* `skeletonMap`, `skeletonMap_base`, `skeletonMap_cell`;
* `skeletonMap_piOne_surjective` and the target `Work.Serre.exists_skeletonMap`.
-/

open scoped Topology unitInterval

set_option linter.unusedVariables false

namespace Work.Serre.E3aSk.SkelMap

noncomputable section

/-! ## The affine identification `D¹ = [-1,1] ≅ I = [0,1]` -/

/-- The affine identification `D¹ = [-1,1] → I = [0,1]`, `t ↦ (t+1)/2`, as a map of cubes. -/
def d1ToCube : C(cellDiskOne, Fin 1 → unitInterval) where
  toFun t := fun _ => ⟨(t.1 + 1) / 2, by
    have h : dist t.1 0 ≤ 1 := Metric.mem_closedBall.mp t.2
    rw [Real.dist_eq, sub_zero] at h
    constructor <;> nlinarith [abs_le.mp h |>.1, abs_le.mp h |>.2]⟩
  continuous_toFun := by fun_prop

/-- Its inverse, `x ↦ 2x - 1`. -/
def cubeToD1 : C(Fin 1 → unitInterval, cellDiskOne) where
  toFun x := ⟨2 * ((x 0 : unitInterval) : ℝ) - 1, by
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero]
    have h := (x 0).2
    rw [abs_le]
    constructor <;> linarith [h.1, h.2]⟩
  continuous_toFun := by fun_prop

@[simp] theorem cubeToD1_d1ToCube (t : cellDiskOne) : cubeToD1 (d1ToCube t) = t := by
  refine Subtype.ext ?_
  show 2 * (((t.1 + 1) / 2 : ℝ)) - 1 = t.1
  ring

@[simp] theorem d1ToCube_cubeToD1 (x : Fin 1 → unitInterval) : d1ToCube (cubeToD1 x) = x := by
  funext i
  refine Subtype.ext ?_
  show ((2 * ((x 0 : unitInterval) : ℝ) - 1) + 1) / 2 = ((x i : unitInterval) : ℝ)
  have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
  rw [hi]
  ring

/-- The image of the boundary of `D¹` is in the boundary of the cube. -/
theorem d1ToCube_mem_boundary (z : cellSphereZero) :
    d1ToCube (cellSphereZeroToDiskOne z) ∈ Cube.boundary (Fin 1) := by
  show ∃ i : Fin 1, d1ToCube (cellSphereZeroToDiskOne z) i = 0 ∨
    d1ToCube (cellSphereZeroToDiskOne z) i = 1
  refine ⟨0, ?_⟩
  have hz : |(z : ℝ)| = 1 := by
    have := Metric.mem_sphere.mp z.2
    rwa [Real.dist_eq, sub_zero] at this
  have h : (((d1ToCube (cellSphereZeroToDiskOne z) 0 : unitInterval)) : ℝ) = ((z : ℝ) + 1) / 2 :=
    rfl
  rcases (abs_eq (show (0 : ℝ) ≤ 1 by norm_num)).mp hz with h1 | h1
  · right
    refine Subtype.ext ?_
    rw [h, h1]; norm_num
  · left
    refine Subtype.ext ?_
    rw [h, h1]; norm_num

/-! ## The recursor of the `1`-cell attachment -/

/-- The function on the disjoint union `Y ⊕ (Σ i, D¹)` given by `g` on `Y` and by the `G i` on
the cells. -/
def oneCellGlue (Y : Type) [TopologicalSpace Y] (ι : Type) (f : ι → C(cellSphereZero, Y))
    {B : Type} [TopologicalSpace B] (g : C(Y, B)) (G : ι → C(cellDiskOne, B)) :
    Y ⊕ (Σ _ : ι, cellDiskOne) → B :=
  Sum.elim g fun p : Σ _ : ι, cellDiskOne => G p.1 p.2

/-- The gluing function is continuous. -/
theorem continuous_oneCellGlue (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(cellSphereZero, Y))
    {B : Type} [TopologicalSpace B] (g : C(Y, B)) (G : ι → C(cellDiskOne, B)) :
    Continuous (oneCellGlue Y ι f g G) :=
  g.continuous.sumElim (continuous_sigma fun i => (G i).continuous)

/-- Two related points have the same image under the gluing function. -/
theorem oneCellGlue_rel (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(cellSphereZero, Y))
    {B : Type} [TopologicalSpace B] (g : C(Y, B)) (G : ι → C(cellDiskOne, B))
    (hG : ∀ (i : ι) (z : cellSphereZero), G i (cellSphereZeroToDiskOne z) = g (f i z)) :
    ∀ a b : Y ⊕ (Σ _ : ι, cellDiskOne),
      Relation.EqvGen (oneCellRel Y ι f) a b →
        oneCellGlue Y ι f g G a = oneCellGlue Y ι f g G b := by
  have hgen : ∀ a b : Y ⊕ (Σ _ : ι, cellDiskOne), oneCellRel Y ι f a b →
      oneCellGlue Y ι f g G a = oneCellGlue Y ι f g G b := by
    rintro a b ⟨i, z, rfl, rfl⟩
    simpa [oneCellGlue] using (hG i z).symm
  intro a b hab
  induction hab with
  | rel x y h => exact hgen x y h
  | refl x => rfl
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ ih1 ih2 => exact ih1.trans ih2

/-- **Extending a map over the attached `1`-cells**, given the values on the cells and the
compatibility on their boundaries. -/
def oneAttachG {B : Type} [TopologicalSpace B] (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(cellSphereZero, Y)) (g : C(Y, B)) (G : ι → C(cellDiskOne, B))
    (hG : ∀ (i : ι) (z : cellSphereZero), G i (cellSphereZeroToDiskOne z) = g (f i z)) :
    C(attachOneCells Y ι f, B) :=
  ⟨Quotient.lift (oneCellGlue Y ι f g G) (oneCellGlue_rel Y ι f g G hG),
    (continuous_oneCellGlue Y ι f g G).quotient_lift (oneCellGlue_rel Y ι f g G hG)⟩

@[simp] theorem oneAttachG_incl {B : Type} [TopologicalSpace B] (Y : Type) [TopologicalSpace Y]
    (ι : Type) (f : ι → C(cellSphereZero, Y)) (g : C(Y, B)) (G : ι → C(cellDiskOne, B))
    (hG : ∀ (i : ι) (z : cellSphereZero), G i (cellSphereZeroToDiskOne z) = g (f i z)) (y : Y) :
    oneAttachG Y ι f g G hG (oneIncl Y ι f y) = g y := rfl

@[simp] theorem oneAttachG_cell {B : Type} [TopologicalSpace B] (Y : Type) [TopologicalSpace Y]
    (ι : Type) (f : ι → C(cellSphereZero, Y)) (g : C(Y, B)) (G : ι → C(cellDiskOne, B))
    (hG : ∀ (i : ι) (z : cellSphereZero), G i (cellSphereZeroToDiskOne z) = g (f i z))
    (i : ι) (x : cellDiskOne) :
    oneAttachG Y ι f g G hG (oneCellMap Y ι f i x) = G i x := rfl

/-! ## The structure map of the `1`-skeleton -/

/-- A based loop of `B`, viewed on the model `1`-cell `D¹`. -/
def loopOf {B : Type} [TopologicalSpace B] (b₀ : B) (w : ↥(GenLoop (Fin 1) B b₀)) :
    C(cellDiskOne, B) :=
  w.1.comp d1ToCube

/-- Such a loop is constantly `b₀` on the boundary of the cell. -/
theorem loopOf_boundary {B : Type} [TopologicalSpace B] (b₀ : B)
    (w : ↥(GenLoop (Fin 1) B b₀)) (z : cellSphereZero) :
    loopOf b₀ w (cellSphereZeroToDiskOne z) = b₀ :=
  w.2 _ (d1ToCube_mem_boundary z)

/-- **The structure map of the `1`-skeleton**: the cell of a based loop `w` is sent to `w`. -/
def skeletonMap (B : Type) [TopologicalSpace B] (b₀ : B) : C(Skeleton B b₀, B) :=
  oneAttachG PUnit _ (skeletonAttach B b₀) (ContinuousMap.const PUnit b₀)
    (fun w => loopOf b₀ w)
    (fun w z => loopOf_boundary b₀ w z)

@[simp] theorem skeletonMap_base (B : Type) [TopologicalSpace B] (b₀ : B) :
    skeletonMap B b₀ (skeletonBase B b₀) = b₀ := rfl

@[simp] theorem skeletonMap_cell (B : Type) [TopologicalSpace B] (b₀ : B)
    (w : ↥(GenLoop (Fin 1) B b₀)) (x : cellDiskOne) :
    skeletonMap B b₀ (oneCellMap PUnit _ (skeletonAttach B b₀) w x) = loopOf b₀ w x := rfl

/-- **The structure map of the skeleton is surjective on `π₁`**: the cell of a representative of
`α` is a loop in the skeleton whose image under `skeletonMap` represents `α`. -/
theorem skeletonMap_piOne_surjective (B : Type) [TopologicalSpace B] (b₀ : B) :
    Function.Surjective (Work.Serre.piMapN (skeletonMap B b₀) 1 (skeletonBase B b₀)) := by
  intro α
  -- a based loop of `B` representing `α`, transported to the base point `b₀`
  let w : ↥(GenLoop (Fin 1) B b₀) :=
    ⟨(Quotient.out α).1, fun x hx =>
      ((Quotient.out α).2 x hx).trans (skeletonMap_base B b₀)⟩
  have hbd : ∀ x ∈ Cube.boundary (Fin 1),
      (oneCellMap PUnit ↥(GenLoop (Fin 1) B b₀) (skeletonAttach B b₀) w).comp cubeToD1 x
        = skeletonBase B b₀ := by
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
      (cellSphereZeroToDiskOne ⟨2 * ((x 0 : unitInterval) : ℝ) - 1, hz⟩) = skeletonBase B b₀
    rw [← oneIncl_oneCellRel PUnit ↥(GenLoop (Fin 1) B b₀) (skeletonAttach B b₀) w
      ⟨2 * ((x 0 : unitInterval) : ℝ) - 1, hz⟩]
    rfl
  let γ : ↥(GenLoop (Fin 1) (Skeleton B b₀) (skeletonBase B b₀)) :=
    ⟨(oneCellMap PUnit ↥(GenLoop (Fin 1) B b₀) (skeletonAttach B b₀) w).comp cubeToD1, hbd⟩
  refine ⟨Quotient.mk _ γ, ?_⟩
  rw [Work.Serre.piMapN_apply_mk, ← Quotient.out_eq α]
  refine Quotient.sound ?_
  have hfun : (Work.StemsB.genLoopMap (skeletonMap B b₀) 1 γ).1 = (Quotient.out α).1 :=
    ContinuousMap.ext (fun t => by
      show skeletonMap B b₀ (oneCellMap PUnit ↥(GenLoop (Fin 1) B b₀) (skeletonAttach B b₀) w
        (cubeToD1 t)) = (Quotient.out α).1 t
      rw [skeletonMap_cell]
      show ((w.1).comp d1ToCube) (cubeToD1 t) = (Quotient.out α).1 t
      rw [ContinuousMap.comp_apply, d1ToCube_cubeToD1])
  have hEq : Work.StemsB.genLoopMap (skeletonMap B b₀) 1 γ = Quotient.out α :=
    Subtype.ext hfun
  rw [hEq]

end

end Work.Serre.E3aSk.SkelMap

/-! ## The requested statement -/

namespace Work.Serre

/-- **The `1`-skeleton of the model of `B` maps to `B`**, sending the base point to `b₀` and
inducing a surjection on `π₁`.

This is `Work.Serre.E3aSk.SkelMap.skeletonMap` (`skeletonMap_base` and
`skeletonMap_piOne_surjective`). -/
theorem exists_skeletonMap (B : Type) [TopologicalSpace B] (b₀ : B) :
    ∃ sm : ContinuousMap (Work.Serre.E3aSk.Skeleton B b₀) B,
      sm (Work.Serre.E3aSk.skeletonBase B b₀) = b₀ ∧
      Function.Surjective (Work.Serre.piMapN sm 1 (Work.Serre.E3aSk.skeletonBase B b₀)) :=
  ⟨E3aSk.SkelMap.skeletonMap B b₀, E3aSk.SkelMap.skeletonMap_base B b₀,
    E3aSk.SkelMap.skeletonMap_piOne_surjective B b₀⟩

end Work.Serre
