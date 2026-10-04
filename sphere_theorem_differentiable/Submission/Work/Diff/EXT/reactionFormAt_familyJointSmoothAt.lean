import Mathlib
import Submission.Work.Diff.EXT.rmP_derivWithin_Ioi
import Submission.Work.Diff.EXT.covK_onFrameFamily
import Submission.Work.Diff.EXT.curvDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Joint smoothness of the reaction form along a jointly smooth metric family (area EXT)

The reaction form `reactionFormAt F g x a b c d` is a fourfold contraction of the curvature array
`F (Rm g x)` with the metric pairings of the four vectors against the chosen orthonormal frame
`onFrame g x`.  The frame `onFrame g x` jumps with `x`, so smoothness of the reaction form is only
visible after replacing it — using the equivariance of `F` under orthogonal changes of frame — by a
*jointly smooth* family of orthonormal frames.

This file proves `Work.Diff.EXT.reactionFormAt_familyJointSmoothAt`: for `F = reactionMap` and a
metric family `G` jointly smooth on an open set `V ⊆ ℝ × M`, and jointly smooth field families
`V₁ … V₄` on `V`, the function
`p ↦ reactionFormAt reactionMap (G p.1) p.2 (V₁ p.1 p.2) … (V₄ p.1 p.2)` is `C^∞` at every point of
`V`.  The proof is the *local* (`JointMet`-on-an-open-set) form of the argument of
`Work.Diff.EXT.reactAux_jointSmoothAt` (`Submission/Work/Diff/EXT/rmP_derivWithin_Ioi.lean`), which
was stated for a metric family smooth on a *cylinder* `J ×ˢ univ`; here we run the same computation
with the pointwise ingredients `Work.Diff.EXT.rmP_familySmooth` and
`Work.Diff.EXT.covK_metric_pairing_family`, which are already available in the local form.
-/

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.EXT

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
  [I.Boundaryless] [T2Space M]

/-- **Joint smoothness of the reaction form on an open subset of `ℝ × M`.**

If the metric family `G` is jointly `C^∞` on the open set `U ∋ (t,x)`, if `e` is a jointly smooth
family of orthonormal frames for `G` on `U`, and if `V₁ … V₄` are jointly smooth field families on
`U`, then the reaction form `F(Rm)` in the moving frame `e` (equivalently, by frame independence of
the reaction form, the reaction form in the chosen frame `onFrame`) is `C^∞` at `(t, x)`.

This is the local form of `Work.Diff.EXT.reactAux_jointSmoothAt`; the two pointwise inputs
(`rmP_familySmooth` for the curvature components, `covK_metric_pairing_family` for the metric
pairings) are already available in their local form. -/
theorem reactionFormAt_jointSmoothAt_of_jointMet
    (hLC : Submission.Diff.LCSmooth I M)
    (F : Submission.Diff.Alg.Curv4 (Module.finrank ℝ E) →
      Submission.Diff.Alg.Curv4 (Module.finrank ℝ E))
    (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hFrot : ∀ A ∈ Matrix.orthogonalGroup (Fin (Module.finrank ℝ E)) ℝ, ∀ R,
      F (Submission.Diff.Alg.rot A R) = Submission.Diff.Alg.rot A (F R))
    {G : ℝ → Submission.Diff.SMet I M} {U : Set (ℝ × M)} (hU : IsOpen U) (hG : JointMet G U)
    {t : ℝ} {x : M} (hxU : (t, x) ∈ U)
    {e : ℝ → Fin (Module.finrank ℝ E) → Π y : M, TangentSpace I y}
    (he : ∀ i : Fin (Module.finrank ℝ E),
      JointField (fun s : ℝ ↦ fun y : M ↦ e s i y) U)
    (hON : ∀ p ∈ U, Submission.Diff.IsONFrame (G p.1) p.2 (fun i => e p.1 i p.2))
    {V₁ V₂ V₃ V₄ : ℝ → TField (I := I) (M := M)}
    (hV₁ : JointField V₁ U) (hV₂ : JointField V₂ U)
    (hV₃ : JointField V₃ U) (hV₄ : JointField V₄ U) :
    ContMDiffAt ((modelWithCornersSelf ℝ ℝ).prod I) (modelWithCornersSelf ℝ ℝ)
      ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × M ↦ Work.Diff.GE.reactionFormAt F (G p.1) p.2
        (V₁ p.1 p.2) (V₂ p.1 p.2) (V₃ p.1 p.2) (V₄ p.1 p.2)) (t, x) := by
  -- the reaction form computed in the moving frame `e` is smooth at `(t,x)`
  have h : ContMDiffAt ((modelWithCornersSelf ℝ ℝ).prod I) (modelWithCornersSelf ℝ ℝ)
      ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × M ↦ Work.Diff.GE.Rfa.reactionFormAtE F (G p.1) p.2 (fun i => e p.1 i p.2)
        (V₁ p.1 p.2) (V₂ p.1 p.2) (V₃ p.1 p.2) (V₄ p.1 p.2)) (t, x) := by
    have hrm : ∀ i j k l : Fin (Module.finrank ℝ E),
        ContMDiffAt ((modelWithCornersSelf ℝ ℝ).prod I) (modelWithCornersSelf ℝ ℝ)
          (((⊤ : ℕ∞) : WithTop ℕ∞))
          (fun p : ℝ × M ↦ Submission.Diff.rmP (G p.1) p.2 (e p.1 i p.2) (e p.1 j p.2)
            (e p.1 k p.2) (e p.1 l p.2)) (t, x) := by
      intro i j k l
      exact (Work.Diff.EXT.rmP_familySmooth (I := I) (M := M) hLC hU hG
        (he i) (he j) (he k) (he l)).contMDiffAt (hU.mem_nhds hxU)
    have harr : ContMDiffAt ((modelWithCornersSelf ℝ ℝ).prod I)
        (modelWithCornersSelf ℝ (Submission.Diff.Alg.Curv4 (Module.finrank ℝ E)))
        (((⊤ : ℕ∞) : WithTop ℕ∞))
        (fun p : ℝ × M ↦ Work.Diff.GE.Rfa.rmFrameField (G p.1) (fun i ↦ e p.1 i) p.2)
        (t, x) := by
      rw [contMDiffAt_pi_space]
      intro i
      rw [contMDiffAt_pi_space]
      intro j
      rw [contMDiffAt_pi_space]
      intro k
      rw [contMDiffAt_pi_space]
      intro l
      simpa only [Work.Diff.GE.Rfa.rmFrameField] using hrm i j k l
    have hFrm : ContMDiffAt ((modelWithCornersSelf ℝ ℝ).prod I)
        (modelWithCornersSelf ℝ (Submission.Diff.Alg.Curv4 (Module.finrank ℝ E)))
        (((⊤ : ℕ∞) : WithTop ℕ∞))
        (fun p : ℝ × M ↦ F (Work.Diff.GE.Rfa.rmFrameField (G p.1) (fun i ↦ e p.1 i) p.2))
        (t, x) :=
      (hF.contMDiff.contMDiffAt).comp (t, x) harr
    have hFcomp : ∀ i j k l : Fin (Module.finrank ℝ E),
        ContMDiffAt ((modelWithCornersSelf ℝ ℝ).prod I) (modelWithCornersSelf ℝ ℝ)
          (((⊤ : ℕ∞) : WithTop ℕ∞))
          (fun p : ℝ × M ↦
            (F (Work.Diff.GE.Rfa.rmFrameField (G p.1) (fun i ↦ e p.1 i) p.2)) i j k l)
          (t, x) := by
      intro i j k l
      exact contMDiffAt_pi_space.mp (contMDiffAt_pi_space.mp (contMDiffAt_pi_space.mp
        (contMDiffAt_pi_space.mp hFrm i) j) k) l
    have hpair : ∀ (i : Fin (Module.finrank ℝ E)) (V : ℝ → Π y : M, TangentSpace I y),
        JointField V U →
        ContMDiffAt ((modelWithCornersSelf ℝ ℝ).prod I) (modelWithCornersSelf ℝ ℝ)
          (((⊤ : ℕ∞) : WithTop ℕ∞))
          (fun p : ℝ × M ↦ (G p.1).inner p.2 (e p.1 i p.2) (V p.1 p.2)) (t, x) :=
      fun i V hV => (Work.Diff.EXT.covK_metric_pairing_family (I := I) (M := M) hG
        (he i) hV).contMDiffAt (hU.mem_nhds hxU)
    simp only [Work.Diff.GE.Rfa.reactionFormAtE]
    refine ContMDiffAt.sum (t := Finset.univ) (fun i _ => ?_)
    refine ContMDiffAt.sum (t := Finset.univ) (fun j _ => ?_)
    refine ContMDiffAt.sum (t := Finset.univ) (fun k _ => ?_)
    refine ContMDiffAt.sum (t := Finset.univ) (fun l _ => ?_)
    refine ContMDiffAt.mul ?_ (hFcomp i j k l)
    refine ContMDiffAt.mul ?_ (hpair l V₄ hV₄)
    refine ContMDiffAt.mul ?_ (hpair k V₃ hV₃)
    exact ContMDiffAt.mul (hpair i V₁ hV₁) (hpair j V₂ hV₂)
  -- frame independence transfers the smoothness to the `onFrame`-version
  exact h.congr_of_eventuallyEq
    (reactAux_eventuallyEq (I := I) (M := M) hLC F hFrot hU hxU hON V₁ V₂ V₃ V₄)

theorem reactionFormAt_familyJointSmoothAt
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
      (fun p : ℝ × M => Work.Diff.GE.reactionFormAt Work.Diff.GE.reactionMap (G p.1) p.2
        (V₁ p.1 p.2) (V₂ p.1 p.2) (V₃ p.1 p.2) (V₄ p.1 p.2)) p₀ := by
  classical
  obtain ⟨W, hWopen, hp₀W, hWV, Fr, hFr, hFrON⟩ :=
    Work.Diff.EXT.covK_onFrameFamily (I := I) (M := M) (G := G) hV hG hp₀
  have hmet : JointMet G W := hG.mono hWV
  have hmono : ∀ {A : ℝ → TField (I := I) (M := M)}, JointField A V → JointField A W :=
    fun hA => hA.mono hWV
  have hres := reactionFormAt_jointSmoothAt_of_jointMet (I := I) (M := M) hLC
    Work.Diff.GE.reactionMap (Work.Diff.GE.reactionMap_contDiff (Module.finrank ℝ E))
    (Work.Diff.GE.reactionMap_rot (Module.finrank ℝ E)) hWopen hmet hp₀W
    (e := fun s i y => Fr s y i) (fun i => hFr i) hFrON
    (hmono hV₁) (hmono hV₂) (hmono hV₃) (hmono hV₄)
  simpa only [Prod.mk.eta] using hres

end Work.Diff.EXT
