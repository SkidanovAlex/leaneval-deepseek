import Mathlib
import Submission.Work.Serre.SPC.B1Setup
import Submission.Work.Serre.SPC.OneCellX
import Submission.Work.Serre.CWModel.Tower
import Submission.Work.Serre.Assembly.fibreConnectivityTransfer

set_option synthInstance.maxHeartbeats 400000


/-!
# The `1`-skeleton of the model of `B` (the `b = 1` case)

`Work.Serre.SPC.Skeleton B b₀` is the wedge of one circle per element of `π₁(B,b₀)`, with the map
`Work.Serre.SPC.skeletonMap B b₀ : Skeleton B b₀ → B` sending the cell of `α` to a representative
loop of `α`.  This is the bottom stage of the model of `B` for the case `b = 1` of the Serre pair
comparison; the `1`-cells are attached with *constant* attaching maps, so all of them are glued at
the single point `skeletonBase B b₀`.
-/

open CategoryTheory CategoryTheory.Limits
open scoped Topology unitInterval



namespace Work.Serre.SPC

noncomputable section

/-! ## Reparametrising the model `1`-cell -/

/-- The affine identification `D¹ = [-1,1] → I = [0,1]`, `t ↦ (t+1)/2`, as a map of cubes. -/
def d1ToCube : C(cellD1, Fin 1 → unitInterval) where
  toFun t := fun _ => ⟨(t.1 + 1) / 2, by
    have h : dist t.1 0 ≤ 1 := Metric.mem_closedBall.mp t.2
    rw [Real.dist_eq, sub_zero] at h
    constructor <;> nlinarith [abs_le.mp h |>.1, abs_le.mp h |>.2]⟩
  continuous_toFun := by fun_prop

/-- Its inverse, `x ↦ 2x - 1`. -/
def cubeToD1 : C(Fin 1 → unitInterval, cellD1) where
  toFun x := ⟨2 * ((x 0 : unitInterval) : ℝ) - 1, by
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero]
    have h := (x 0).2
    rw [abs_le]
    constructor <;> linarith [h.1, h.2]⟩
  continuous_toFun := by fun_prop

@[simp] theorem cubeToD1_d1ToCube (t : cellD1) : cubeToD1 (d1ToCube t) = t := by
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
theorem d1ToCube_mem_boundary (z : cellS0) : d1ToCube (cellS0ToD1 z) ∈ Cube.boundary (Fin 1) := by
  show ∃ i : Fin 1, d1ToCube (cellS0ToD1 z) i = 0 ∨ d1ToCube (cellS0ToD1 z) i = 1
  refine ⟨0, ?_⟩
  have hz : |(z : ℝ)| = 1 := by
    have := Metric.mem_sphere.mp z.2
    rwa [Real.dist_eq, sub_zero] at this
  have h : (((d1ToCube (cellS0ToD1 z) 0 : unitInterval)) : ℝ) = ((z : ℝ) + 1) / 2 := rfl
  rcases (abs_eq (show (0:ℝ) ≤ 1 by norm_num)).mp hz with h1 | h1
  · right
    refine Subtype.ext ?_
    rw [h, h1]; norm_num
  · left
    refine Subtype.ext ?_
    rw [h, h1]; norm_num

/-- A based loop of `B`, viewed on the model `1`-cell `D¹`. -/
def loopOf {B : Type} [TopologicalSpace B] (b₀ : B) (w : ↥(GenLoop (Fin 1) B b₀)) :
    C(cellD1, B) :=
  w.1.comp d1ToCube

/-- Such a loop is constantly `b₀` on the boundary of the cell. -/
theorem loopOf_boundary {B : Type} [TopologicalSpace B] (b₀ : B)
    (w : ↥(GenLoop (Fin 1) B b₀)) (z : cellS0) :
    loopOf b₀ w (cellS0ToD1 z) = b₀ :=
  w.2 _ (d1ToCube_mem_boundary z)

/-! ## The `1`-skeleton -/

/-- The attaching maps of the `1`-skeleton: all the cells are glued at the single point of `PUnit`. -/
def skeletonAttach (B : Type) [TopologicalSpace B] (b₀ : B) :
    ↥(GenLoop (Fin 1) B b₀) → C(cellS0, PUnit) :=
  fun _ => ContinuousMap.const cellS0 ⟨⟩

/-- **The `1`-skeleton of the model of `B`**: the wedge of one circle per based loop of `B`. -/
abbrev Skeleton (B : Type) [TopologicalSpace B] (b₀ : B) : Type :=
  attachOneCells PUnit ↥(GenLoop (Fin 1) B b₀) (skeletonAttach B b₀)

/-- The base point of the skeleton. -/
def skeletonBase (B : Type) [TopologicalSpace B] (b₀ : B) : Skeleton B b₀ :=
  oneIncl PUnit _ (skeletonAttach B b₀) ⟨⟩

/-- **The structure map of the `1`-skeleton**: the cell of a based loop `w` is sent to `w`. -/
def skeletonMap (B : Type) [TopologicalSpace B] (b₀ : B) : C(Skeleton B b₀, B) :=
  oneAttachG PUnit _ (skeletonAttach B b₀) (ContinuousMap.const PUnit b₀)
    (fun w => loopOf b₀ w)
    (fun w z => loopOf_boundary b₀ w z)

@[simp] theorem skeletonMap_base (B : Type) [TopologicalSpace B] (b₀ : B) :
    skeletonMap B b₀ (skeletonBase B b₀) = b₀ := rfl

@[simp] theorem skeletonMap_cell (B : Type) [TopologicalSpace B] (b₀ : B)
    (w : ↥(GenLoop (Fin 1) B b₀)) (x : cellD1) :
    skeletonMap B b₀ (oneCellMap PUnit _ (skeletonAttach B b₀) w x) = loopOf b₀ w x := rfl

theorem skeletonBase_eq (B : Type) [TopologicalSpace B] (b₀ : B) :
    Set.range (oneIncl PUnit ↥(GenLoop (Fin 1) B b₀) (skeletonAttach B b₀)) =
      ({skeletonBase B b₀} : Set (Skeleton B b₀)) := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro _ ⟨y, rfl⟩
    rw [show y = (⟨⟩ : PUnit) from Subsingleton.elim _ _]
    exact rfl
  · rintro _ rfl
    exact ⟨⟨⟩, rfl⟩

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
      (cellS0ToD1 ⟨2 * ((x 0 : unitInterval) : ℝ) - 1, hz⟩) = skeletonBase B b₀
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

end Work.Serre.SPC
