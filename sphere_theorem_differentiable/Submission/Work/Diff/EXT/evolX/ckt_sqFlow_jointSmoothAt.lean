import Mathlib
import Submission.Work.Diff.EXT.ricCore
import Submission.Work.Diff.EXT.covK_familySmooth
import Submission.Work.Diff.EXT.ckt_step_aux
import Submission.Work.Diff.GE.continuous_flow_quantities

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Joint smoothness of the curvature tower along the time-reparametrised flow `τ ↦ G(τ²)`

`IsRicciFlow G T` gives joint smoothness of the family of metrics only on the *half-open* interval
`[0,T)`.  After the reparametrisation `t = τ²` the family `cfq_sqFlow G = fun τ ↦ G (τ ^ 2)` is
jointly smooth on the *open* interval `(-ρ, ρ)` as soon as `ρ ^ 2 < T`
(`Work.Diff.GE.cfq_jointSmooth_sqFlow`), and on an open neighbourhood of an interior point the
joint smoothness of the tower `(τ,y) ↦ ∇^k Rm (G (τ²))` on a tuple of smooth fields follows from
the general family statement `Work.Diff.EXT.covK_familySmooth` together with the bridge
`Work.Diff.EXT.ckt_eq_covKRmExt`.

This is the reparametrised version of `Work.Diff.EXT.ckt_familySmoothAt` (which requires the
interior time `t` to be *strictly positive*); here `τ` may be any point of `(-ρ, ρ)`, in particular
`τ = 0`, which is the point where the half-openness of `[0,T)` has to be undone.
-/

set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Bundle Topology

namespace Work.Diff.EXT.evolX

theorem ckt_sqFlow_jointSmoothAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M)
    {G : ℝ → Submission.Diff.SMet I M} {T ρ : ℝ} (hT : 0 < T) (hρ : 0 < ρ) (hρT : ρ ^ 2 < T)
    (hflow : Submission.Diff.IsRicciFlow G T)
    {k : ℕ} {U : Fin (k + 4) → Work.Diff.EXT.TField (I := I) (M := M)}
    (hU : ∀ i, Work.Diff.EXT.SmoothTField (I := I) (M := M) (U i))
    {τ : ℝ} (hτ : τ ∈ Set.Ioo (-ρ) ρ) {y : M} :
    Work.Diff.EXT.JointSmoothAt I M
      (fun p : ℝ × M => Work.Diff.EXT.ckt (Work.Diff.GE.cfq_sqFlow G p.1) k U p.2) τ y := by
  -- The reparametrised flow is jointly smooth on the *open* interval `(-ρ, ρ)`.
  have hsm : Submission.Diff.JointSmooth (Work.Diff.GE.cfq_sqFlow G) (Set.Ioo (-ρ) ρ) :=
    Work.Diff.GE.cfq_jointSmooth_sqFlow (I := I) (M := M) G hT hρ hρT hflow.1
  have hV : IsOpen (Set.Ioo (-ρ) ρ ×ˢ (Set.univ : Set M)) := isOpen_Ioo.prod isOpen_univ
  have hJM : Work.Diff.EXT.JointMet (Work.Diff.GE.cfq_sqFlow G)
      (Set.Ioo (-ρ) ρ ×ˢ (Set.univ : Set M)) :=
    (Work.Diff.EXT.jointMet_prod (I := I) (M := M) (Work.Diff.GE.cfq_sqFlow G)
      (Set.Ioo (-ρ) ρ)).mp hsm
  have hsub : (Set.Ioo (-ρ) ρ ×ˢ (Set.univ : Set M)) ⊆ (Set.univ : Set (ℝ × M)) :=
    Set.subset_univ _
  -- The `U i` are constant (in time) families of globally smooth fields.
  have hVf : ∀ i : Fin k, Work.Diff.EXT.JointField
      (fun _ : ℝ => U (Fin.castAdd 4 i)) (Set.Ioo (-ρ) ρ ×ˢ (Set.univ : Set M)) :=
    fun i => (Work.Diff.EXT.jointField_const (I := I) (M := M) (hU _)).mono hsub
  have hA : Work.Diff.EXT.JointField
      (fun _ : ℝ => U (Fin.natAdd k 0)) (Set.Ioo (-ρ) ρ ×ˢ (Set.univ : Set M)) :=
    (Work.Diff.EXT.jointField_const (I := I) (M := M) (hU _)).mono hsub
  have hB : Work.Diff.EXT.JointField
      (fun _ : ℝ => U (Fin.natAdd k 1)) (Set.Ioo (-ρ) ρ ×ˢ (Set.univ : Set M)) :=
    (Work.Diff.EXT.jointField_const (I := I) (M := M) (hU _)).mono hsub
  have hC : Work.Diff.EXT.JointField
      (fun _ : ℝ => U (Fin.natAdd k 2)) (Set.Ioo (-ρ) ρ ×ˢ (Set.univ : Set M)) :=
    (Work.Diff.EXT.jointField_const (I := I) (M := M) (hU _)).mono hsub
  have hD : Work.Diff.EXT.JointField
      (fun _ : ℝ => U (Fin.natAdd k 3)) (Set.Ioo (-ρ) ρ ×ˢ (Set.univ : Set M)) :=
    (Work.Diff.EXT.jointField_const (I := I) (M := M) (hU _)).mono hsub
  have h4 := Work.Diff.EXT.covK_familySmooth (I := I) (M := M) hLC hV hJM k hVf hA hB hC hD
  -- The tower `ckt` is the frozen `covKRmExt` on the split tuple.
  have hfun : (fun p : ℝ × M => Work.Diff.EXT.ckt (Work.Diff.GE.cfq_sqFlow G p.1) k U p.2)
      = fun p : ℝ × M => Work.Diff.EXT.covKRmExt (Work.Diff.GE.cfq_sqFlow G p.1) k
          (fun i : Fin k => U (Fin.castAdd 4 i))
          (U (Fin.natAdd k 0)) (U (Fin.natAdd k 1)) (U (Fin.natAdd k 2))
          (U (Fin.natAdd k 3)) p.2 := by
    funext p
    exact Work.Diff.EXT.ckt_eq_covKRmExt (Work.Diff.GE.cfq_sqFlow G p.1) k U p.2
  rw [← hfun] at h4
  exact h4.contMDiffAt (hV.mem_nhds ⟨hτ, Set.mem_univ y⟩)

end Work.Diff.EXT.evolX
