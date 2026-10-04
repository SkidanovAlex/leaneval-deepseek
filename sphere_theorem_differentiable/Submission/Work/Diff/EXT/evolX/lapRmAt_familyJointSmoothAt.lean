import Mathlib
import Submission.Work.Diff.EXT.curvDefs
import Submission.Work.Diff.EXT.curvDefs2
import Submission.Work.Diff.GE.lapRmAt_trace
import Submission.Work.Diff.EXT.covK_familySmooth
import Submission.Work.Diff.EXT.covK_onFrameFamily
import Submission.Work.Diff.EXT.covK_valueDepN
import Submission.Work.Diff.GE.lapRmAt_zero_continuous

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Joint smoothness of `lapRmAt` along a jointly smooth family of metrics and fields

The rough Laplacian `ΔRm = ∑_m ∇_m∇_m Rm` of the curvature, evaluated on four jointly smooth
families of tangent fields `V₁ … V₄` along a family of metrics `G` jointly smooth on an open set
`V ⊆ ℝ × M`, is jointly `C^∞` at every point of `V`.

Route.  At `p₀ ∈ V` pick a family `F` of frames which are `(G t)`-orthonormal and jointly `C^∞` on
an open `W ∋ p₀`, `W ⊆ V` (`Work.Diff.EXT.covK_onFrameFamily`).  On `W` the trace identity
`Work.Diff.GE.lapRmAt_trace` rewrites `ΔRm` as the sum of the six-slot components
`m ↦ ∇²Rm(e_m, e_m, a, b, c, d)`, each of which is a value of the covariant-derivative tower at
level `2` (`cov2Rm_eq_covKRmExt_two_of_smoothNear`, the local (neighbourhood-smoothness) form of
`Work.Diff.GE.cov2Rm_eq_covKRmExt_two`) and hence jointly `C^∞` on `W` by
`Work.Diff.EXT.covK_familySmooth`.
-/

namespace Work.Diff.EXT.evolX

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

section Bridge

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [T2Space M]
  [I.Boundaryless]

/-- **The level-`2` tower bridge, local form.**  If the six fields are `C^∞` on a neighbourhood of
`x`, then the frozen `(0,6)`-tensor `∇²Rm`, evaluated on their values at `x`, is the value at `x` of
the level-`2` covariant-derivative tower on those fields.

This is the form of `Work.Diff.GE.cov2Rm_eq_covKRmExt_two` (which assumes the fields globally `C^∞`)
needed to identify the summands of `lapRmAt` in a frame family: the fields occurring there are smooth
only on a neighbourhood of the base point.  The proof globalises the fields (inside
`Work.Diff.EXT.covK_valueDepN`) and then applies the global bridge. -/
theorem cov2Rm_eq_covKRmExt_two_of_smoothNear
    (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M) (x : M)
    (U₀ U₁ AA BB CC DD : Work.Diff.EXT.TField (I := I) (M := M))
    (hU₀ : Work.Diff.EXT.SmoothNear (I := I) U₀ x) (hU₁ : Work.Diff.EXT.SmoothNear (I := I) U₁ x)
    (hAA : Work.Diff.EXT.SmoothNear (I := I) AA x) (hBB : Work.Diff.EXT.SmoothNear (I := I) BB x)
    (hCC : Work.Diff.EXT.SmoothNear (I := I) CC x) (hDD : Work.Diff.EXT.SmoothNear (I := I) DD x) :
    Work.Diff.GE.cov2Rm g x (U₀ x) (U₁ x) (AA x) (BB x) (CC x) (DD x)
      = Work.Diff.EXT.covKRmExt g 2 (fun r : Fin 2 => if r = 0 then U₀ else U₁) AA BB CC DD x := by
  have hvd := Work.Diff.EXT.covK_valueDepN (I := I) (M := M) hLC g 2
    (Work.Diff.EXT.covK_linear (I := I) (M := M) hLC g 2)
    (Work.Diff.EXT.covK_germ (I := I) (M := M) hLC g 2)
  have hSN : ∀ u : TangentSpace I x, Work.Diff.EXT.SmoothNear (I := I)
      (fun y : M => Submission.Diff.smoothExt x u y) x := fun u =>
    Work.Diff.EXT.SmoothTField.smoothNear (Work.Diff.GE.smoothExt_cmdiff x u) x
  have hV0 : ∀ r : Fin 2, Work.Diff.EXT.SmoothNear (I := I)
      ((fun r : Fin 2 => if r = 0 then U₀ else U₁) r) x := by
    intro r
    fin_cases r
    · simpa using hU₀
    · simpa using hU₁
  have hV1 : ∀ r : Fin 2, Work.Diff.EXT.SmoothNear (I := I)
      ((fun r : Fin 2 => if r = 0 then (fun y : M => Submission.Diff.smoothExt x (U₀ x) y)
        else (fun y : M => Submission.Diff.smoothExt x (U₁ x) y)) r) x := by
    intro r
    fin_cases r
    · simpa using hSN (U₀ x)
    · simpa using hSN (U₁ x)
  have hval : ∀ r : Fin 2, (fun r : Fin 2 => if r = 0 then U₀ else U₁) r x
      = (fun r : Fin 2 => if r = 0 then (fun y : M => Submission.Diff.smoothExt x (U₀ x) y)
          else (fun y : M => Submission.Diff.smoothExt x (U₁ x) y)) r x := by
    intro r
    fin_cases r <;> simp [Work.Diff.GE.smoothExt_apply]
  have hvalAA : AA x = (fun y : M => Submission.Diff.smoothExt x (AA x) y) x :=
    (Work.Diff.GE.smoothExt_apply x (AA x)).symm
  have hvalBB : BB x = (fun y : M => Submission.Diff.smoothExt x (BB x) y) x :=
    (Work.Diff.GE.smoothExt_apply x (BB x)).symm
  have hvalCC : CC x = (fun y : M => Submission.Diff.smoothExt x (CC x) y) x :=
    (Work.Diff.GE.smoothExt_apply x (CC x)).symm
  have hvalDD : DD x = (fun y : M => Submission.Diff.smoothExt x (DD x) y) x :=
    (Work.Diff.GE.smoothExt_apply x (DD x)).symm
  have hmain : Work.Diff.EXT.covKRmExt g 2 (fun r : Fin 2 => if r = 0 then U₀ else U₁) AA BB CC DD x
      = Work.Diff.EXT.covKRmExt g 2
          (fun r : Fin 2 => if r = 0 then (fun y : M => Submission.Diff.smoothExt x (U₀ x) y)
            else (fun y : M => Submission.Diff.smoothExt x (U₁ x) y))
          (fun y : M => Submission.Diff.smoothExt x (AA x) y)
          (fun y : M => Submission.Diff.smoothExt x (BB x) y)
          (fun y : M => Submission.Diff.smoothExt x (CC x) y)
          (fun y : M => Submission.Diff.smoothExt x (DD x) y) x :=
    hvd _ _ _ _ _ _ _ _ _ _ x hV0 hV1 hAA (hSN (AA x)) hBB (hSN (BB x)) hCC (hSN (CC x))
      hDD (hSN (DD x)) hval hvalAA hvalBB hvalCC hvalDD
  rw [hmain]
  have hglob := Work.Diff.GE.cov2Rm_eq_covKRmExt_two (I := I) (M := M) hLC g x
    (V0 := fun y : M => Submission.Diff.smoothExt x (U₀ x) y)
    (V1 := fun y : M => Submission.Diff.smoothExt x (U₁ x) y)
    (A := fun y : M => Submission.Diff.smoothExt x (AA x) y)
    (B := fun y : M => Submission.Diff.smoothExt x (BB x) y)
    (C := fun y : M => Submission.Diff.smoothExt x (CC x) y)
    (D := fun y : M => Submission.Diff.smoothExt x (DD x) y)
    (Work.Diff.GE.smoothExt_cmdiff x (U₀ x)) (Work.Diff.GE.smoothExt_cmdiff x (U₁ x))
    (Work.Diff.GE.smoothExt_cmdiff x (AA x)) (Work.Diff.GE.smoothExt_cmdiff x (BB x))
    (Work.Diff.GE.smoothExt_cmdiff x (CC x)) (Work.Diff.GE.smoothExt_cmdiff x (DD x))
  simpa only [Work.Diff.GE.smoothExt_apply] using hglob

/-- **Joint smoothness of `∇²Rm` on six jointly smooth families of fields.**
If `G` is a family of metrics jointly `C^∞` on an open set `V ⊆ ℝ × M` and
`X₁, X₂, X₃, X₄, X₅, X₆` are families of tangent fields jointly `C^∞` on `V` (`JointField`), then
`(t,y) ↦ ∇²Rm(G t)(X₁ t y, X₂ t y, X₃ t y, X₄ t y, X₅ t y, X₆ t y)` is `C^∞` on `V`.

Each value is the level-`2` tower value on the first two fields and the last four
(`cov2Rm_eq_covKRmExt_two_of_smoothNear`), which is jointly `C^∞` by
`Work.Diff.EXT.covK_familySmooth`. -/
theorem cov2Rm_familyJointSmooth
    (hLC : Submission.Diff.LCSmooth I M)
    {G : ℝ → Submission.Diff.SMet I M} {V : Set (ℝ × M)} (hV : IsOpen V)
    (hG : Work.Diff.EXT.JointMet G V)
    {X₁ X₂ X₃ X₄ X₅ X₆ : ℝ → Work.Diff.EXT.TField (I := I) (M := M)}
    (h₁ : Work.Diff.EXT.JointField X₁ V) (h₂ : Work.Diff.EXT.JointField X₂ V)
    (h₃ : Work.Diff.EXT.JointField X₃ V) (h₄ : Work.Diff.EXT.JointField X₄ V)
    (h₅ : Work.Diff.EXT.JointField X₅ V) (h₆ : Work.Diff.EXT.JointField X₆ V) :
    ContMDiffOn ((modelWithCornersSelf ℝ ℝ).prod I) (modelWithCornersSelf ℝ ℝ) ∞
      (fun p : ℝ × M => Work.Diff.GE.cov2Rm (G p.1) p.2 (X₁ p.1 p.2) (X₂ p.1 p.2)
        (X₃ p.1 p.2) (X₄ p.1 p.2) (X₅ p.1 p.2) (X₆ p.1 p.2)) V := by
  have hVf : ∀ i : Fin 2, Work.Diff.EXT.JointField
      (fun t : ℝ => (fun r : Fin 2 => if r = 0 then X₁ t else X₂ t) i) V := by
    intro i
    by_cases h : i = 0
    · have h1 : (fun t : ℝ => (fun r : Fin 2 => if r = 0 then X₁ t else X₂ t) i) = X₁ := by
        funext t
        rw [h]
        show (if ((0 : Fin 2) = 0) then X₁ t else X₂ t) = X₁ t
        exact if_pos rfl
      rw [h1]
      exact h₁
    · have h1 : (fun t : ℝ => (fun r : Fin 2 => if r = 0 then X₁ t else X₂ t) i) = X₂ := by
        funext t
        show (if (i = 0) then X₁ t else X₂ t) = X₂ t
        rw [if_neg h]
      rw [h1]
      exact h₂
  have htower := Work.Diff.EXT.covK_familySmooth (I := I) (M := M) hLC hV hG 2
    (Vf := fun t : ℝ => fun r : Fin 2 => if r = 0 then X₁ t else X₂ t) hVf h₃ h₄ h₅ h₆
  intro p hp
  have hAt : ContMDiffAt ((modelWithCornersSelf ℝ ℝ).prod I) (modelWithCornersSelf ℝ ℝ) ∞
      (fun q : ℝ × M => Work.Diff.EXT.covKRmExt (G q.1) 2
        (fun r : Fin 2 => if r = 0 then X₁ q.1 else X₂ q.1) (X₃ q.1) (X₄ q.1) (X₅ q.1) (X₆ q.1)
        q.2) p :=
    htower.contMDiffAt (hV.mem_nhds hp)
  refine (hAt.congr_of_eventuallyEq ?_).contMDiffWithinAt
  filter_upwards [hV.mem_nhds hp] with q hq
  exact cov2Rm_eq_covKRmExt_two_of_smoothNear (I := I) (M := M) hLC (G q.1) q.2
    (X₁ q.1) (X₂ q.1) (X₃ q.1) (X₄ q.1) (X₅ q.1) (X₆ q.1)
    (Work.Diff.EXT.jointField_sliceNear (I := I) (M := M) hV h₁ hq)
    (Work.Diff.EXT.jointField_sliceNear (I := I) (M := M) hV h₂ hq)
    (Work.Diff.EXT.jointField_sliceNear (I := I) (M := M) hV h₃ hq)
    (Work.Diff.EXT.jointField_sliceNear (I := I) (M := M) hV h₄ hq)
    (Work.Diff.EXT.jointField_sliceNear (I := I) (M := M) hV h₅ hq)
    (Work.Diff.EXT.jointField_sliceNear (I := I) (M := M) hV h₆ hq)

end Bridge

theorem lapRmAt_familyJointSmoothAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M)
    {G : ℝ → Submission.Diff.SMet I M} {V : Set (ℝ × M)} (hV : IsOpen V)
    (hG : Work.Diff.EXT.JointMet G V)
    {V₁ V₂ V₃ V₄ : ℝ → Work.Diff.EXT.TField (I := I) (M := M)}
    (hV₁ : Work.Diff.EXT.JointField V₁ V) (hV₂ : Work.Diff.EXT.JointField V₂ V)
    (hV₃ : Work.Diff.EXT.JointField V₃ V) (hV₄ : Work.Diff.EXT.JointField V₄ V)
    {p₀ : ℝ × M} (hp₀ : p₀ ∈ V) :
    ContMDiffAt ((modelWithCornersSelf ℝ ℝ).prod I) (modelWithCornersSelf ℝ ℝ)
      ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × M => Work.Diff.GE.lapRmAt (G p.1) p.2 (V₁ p.1 p.2) (V₂ p.1 p.2)
        (V₃ p.1 p.2) (V₄ p.1 p.2)) p₀ := by
  classical
  obtain ⟨W, hWopen, hp₀W, hWV, F, hFjoint, hFON⟩ :=
    Work.Diff.EXT.covK_onFrameFamily (I := I) (M := M) (G := G) (V := V) hV hG hp₀
  have hGW : Work.Diff.EXT.JointMet G W := hG.mono hWV
  have key : ∀ p ∈ W, ContMDiffAt ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun q : ℝ × M => Work.Diff.GE.lapRmAt (G q.1) q.2 (V₁ q.1 q.2) (V₂ q.1 q.2)
        (V₃ q.1 q.2) (V₄ q.1 q.2)) p := by
    intro p hp
    have hsum : ContMDiffAt ((modelWithCornersSelf ℝ ℝ).prod I) (modelWithCornersSelf ℝ ℝ) ∞
        (fun q : ℝ × M => ∑ m : Fin (Module.finrank ℝ E),
          Work.Diff.GE.cov2Rm (G q.1) q.2 (F q.1 q.2 m) (F q.1 q.2 m) (V₁ q.1 q.2)
            (V₂ q.1 q.2) (V₃ q.1 q.2) (V₄ q.1 q.2)) p := by
      refine ContMDiffAt.sum (t := Finset.univ) (fun m _ => ?_)
      exact ((cov2Rm_familyJointSmooth (I := I) (M := M) hLC hWopen hGW
        (X₁ := fun t : ℝ => fun y : M => F t y m) (X₂ := fun t : ℝ => fun y : M => F t y m)
        (X₃ := V₁) (X₄ := V₂) (X₅ := V₃) (X₆ := V₄)
        (hFjoint m) (hFjoint m) (hV₁.mono hWV) (hV₂.mono hWV) (hV₃.mono hWV) (hV₄.mono hWV)
        ).contMDiffAt (hWopen.mem_nhds hp))
    refine hsum.congr_of_eventuallyEq ?_
    filter_upwards [hWopen.mem_nhds hp] with q hq
    exact Work.Diff.GE.lapRmAt_trace (I := I) (M := M) hLC (G q.1) q.2 (F q.1 q.2)
      (hFON q hq) (V₁ q.1 q.2) (V₂ q.1 q.2) (V₃ q.1 q.2) (V₄ q.1 q.2)
  have hOn : ContMDiffOn ((modelWithCornersSelf ℝ ℝ).prod I) (modelWithCornersSelf ℝ ℝ) ∞
      (fun q : ℝ × M => Work.Diff.GE.lapRmAt (G q.1) q.2 (V₁ q.1 q.2) (V₂ q.1 q.2)
        (V₃ q.1 q.2) (V₄ q.1 q.2)) W := fun p hp => (key p hp).contMDiffWithinAt
  exact hOn.contMDiffAt (hWopen.mem_nhds hp₀W)

end Work.Diff.EXT.evolX
