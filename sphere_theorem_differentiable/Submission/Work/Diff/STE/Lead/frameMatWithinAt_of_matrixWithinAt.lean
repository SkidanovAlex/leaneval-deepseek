/-
# Smoothness of a form prescribed by a *within*-smooth chart matrix, read in a frame

This is the `ContMDiffWithinAt` (within-set) version of
`Work.Diff.EXT.FrameKit.frameMat_of_chartData`.

Let `x₀` be a chart centre, `Ω ⊆ (extChartAt I x₀).target` a set of chart coordinates and
`A : ℝ × E → MatE` a matrix-valued function which is `C^∞` *within* `J ×ˢ Ω` at
`(τ, (extChartAt I x₀) x)`.  Then the matrix of the bilinear form, whose matrix in the coordinate
frame of the chart at `x₀` is `A t ((extChartAt I x₀) y)`, read in the frame of the chart at an
arbitrary point `x` (`x ∈ (chartAt H x₀).source`), is `C^∞` within
`J ×ˢ (((extChartAt I x₀) ⁻¹' Ω) ∩ (chartAt H x).source)` at `(τ, x)`.

## Proof

The point of the statement is that `Ω` may be a *proper* subset of the chart target (typically a
domain on which the parabolic equation has a solution), so one cannot replace `A` by a globally
smooth function; instead `MapsTo` is used to feed `hW` through the composition
`ContMDiffWithinAt.comp`:

* `p ↦ (p.1, (extChartAt I x₀) p.2)` is `C^∞` within any set (it is `C^∞` at `(τ, x)` because
  `x ∈ (chartAt H x₀).source`) and maps the within-set `J ×ˢ (((extChartAt I x₀) ⁻¹' Ω) ∩ …)`
  into `J ×ˢ Ω`; composing with `A` gives the within-smoothness of
  `p ↦ A p.1 ((extChartAt I x₀) p.2)`;
* the frame vectors of the chart at `x`, written in the coordinates of the chart at `x₀`, are
  `C^∞` at `x` (`Work.Diff.EXT.FrameKit.contMDiffAt_frameCoords_frameVector`), so all the
  remaining factors in the pointwise formula `Work.Diff.EXT.formInFrame_apply` are smooth at
  `(τ, x)` (hence within the set); sums and products finish;
* finally `Work.Diff.EXT.frameMat`/`formInFrame_apply` identify the assembled sum with the
  frame matrix pointwise everywhere, so `ContMDiffWithinAt.congr_of_eventuallyEq` concludes.
-/
import Mathlib
import Submission.Work.Diff.EXT.FrameKit.frameMat_of_chartData
import Submission.Work.Diff.STE.Lead.JointSmoothKit

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.Lead

theorem frameMatWithinAt_of_matrixWithinAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [I.Boundaryless]
    {x₀ x : M} {A : ℝ → E → Work.Diff.EXT.MatE (E := E)} {J : Set ℝ} {Ω : Set E} {τ : ℝ}
    (hx : x ∈ (chartAt H x₀).source) (hxΩ : (extChartAt I x₀) x ∈ Ω)
    (hΩ : Ω ⊆ (extChartAt I x₀).target)
    (hW : ContMDiffWithinAt ((modelWithCornersSelf ℝ ℝ).prod (modelWithCornersSelf ℝ E))
      (modelWithCornersSelf ℝ (Work.Diff.EXT.MatE (E := E))) (⊤ : ℕ∞)
      (fun p : ℝ × E => A p.1 p.2) (J ×ˢ Ω) (τ, (extChartAt I x₀) x)) :
    ContMDiffWithinAt ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ (Work.Diff.EXT.MatE (E := E))) (⊤ : ℕ∞)
      (fun p : ℝ × M => Work.Diff.EXT.frameMat (I := I) x p.2
        (Work.Diff.EXT.formInFrame (I := I) x₀ p.2 (fun i j => A p.1 ((extChartAt I x₀) p.2) i j)))
      (J ×ˢ (((extChartAt I x₀) ⁻¹' Ω) ∩ (chartAt H x).source)) (τ, x) := by
  classical
  -- the within-set of the conclusion
  let S : Set (ℝ × M) := J ×ˢ (((extChartAt I x₀) ⁻¹' Ω) ∩ (chartAt H x).source)
  change ContMDiffWithinAt ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ (Work.Diff.EXT.MatE (E := E))) (⊤ : ℕ∞)
      (fun p : ℝ × M => Work.Diff.EXT.frameMat (I := I) x p.2
        (Work.Diff.EXT.formInFrame (I := I) x₀ p.2 (fun i j => A p.1 ((extChartAt I x₀) p.2) i j)))
      S (τ, x)
  -- the frame vectors of the chart at `x`, in the coordinates of the chart at `x₀`
  let V : Fin (Module.finrank ℝ E) → ℝ × M → E := fun i p =>
    Work.Diff.EXT.frameCoords (I := I) x₀ p.2
      (Submission.Geodesic.frameVector (I := I) x p.2 (Work.Diff.EXT.bB (E := E) i))
  have hsndAt : ContMDiffAt ((modelWithCornersSelf ℝ ℝ).prod I) I (⊤ : ℕ∞)
      (Prod.snd : ℝ × M → M) (τ, x) := contMDiffAt_snd
  have hVsmAt : ∀ i, ContMDiffAt ((modelWithCornersSelf ℝ ℝ).prod I) (modelWithCornersSelf ℝ E)
      (⊤ : ℕ∞) (V i) (τ, x) := by
    intro i
    exact ContMDiffAt.comp (f := (Prod.snd : ℝ × M → M))
      (g := fun y : M => Work.Diff.EXT.frameCoords (I := I) x₀ y
        (Submission.Geodesic.frameVector (I := I) x y (Work.Diff.EXT.bB (E := E) i)))
      (τ, x)
      (Work.Diff.EXT.FrameKit.contMDiffAt_frameCoords_frameVector (I := I) (E := E) x₀ x i hx)
      hsndAt
  -- the coordinate map `p ↦ (p.1, (extChartAt I x₀) p.2)` and the chart matrix
  have hfst : ContMDiffWithinAt ((modelWithCornersSelf ℝ ℝ).prod I) (modelWithCornersSelf ℝ ℝ)
      (⊤ : ℕ∞) (fun p : ℝ × M => p.1) S (τ, x) := contMDiffWithinAt_fst
  have hχsnd : ContMDiffWithinAt ((modelWithCornersSelf ℝ ℝ).prod I) (modelWithCornersSelf ℝ E)
      (⊤ : ℕ∞) (fun p : ℝ × M => (extChartAt I x₀) p.2) S (τ, x) :=
    (ContMDiffAt.comp (f := (Prod.snd : ℝ × M → M)) (g := fun y : M => (extChartAt I x₀) y)
      (τ, x) (contMDiffAt_extChartAt' (I := I) (x := x₀) (x' := x) hx) hsndAt).contMDiffWithinAt
  have hχ : ContMDiffWithinAt ((modelWithCornersSelf ℝ ℝ).prod I)
      ((modelWithCornersSelf ℝ ℝ).prod (modelWithCornersSelf ℝ E)) (⊤ : ℕ∞)
      (fun p : ℝ × M => (p.1, (extChartAt I x₀) p.2)) S (τ, x) :=
    hfst.prodMk hχsnd
  -- the within-smoothness of the chart matrix, by composition with `hW`
  have hWc : ContMDiffWithinAt ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ (Work.Diff.EXT.MatE (E := E))) (⊤ : ℕ∞)
      (fun p : ℝ × M => A p.1 ((extChartAt I x₀) p.2)) S (τ, x) :=
    hW.comp (τ, x) hχ (fun p hp => Set.mem_prod.mpr ⟨hp.1, hp.2.1⟩)
  have hentry : ∀ k l : Fin (Module.finrank ℝ E),
      ContMDiffWithinAt ((modelWithCornersSelf ℝ ℝ).prod I) (modelWithCornersSelf ℝ ℝ) (⊤ : ℕ∞)
        (fun p : ℝ × M => A p.1 ((extChartAt I x₀) p.2) k l) S (τ, x) := by
    intro k l
    exact contMDiffWithinAt_pi_space.mp (contMDiffWithinAt_pi_space.mp hWc k) l
  have hcoord : ∀ k i : Fin (Module.finrank ℝ E),
      ContMDiffWithinAt ((modelWithCornersSelf ℝ ℝ).prod I) (modelWithCornersSelf ℝ ℝ) (⊤ : ℕ∞)
        (fun p : ℝ × M => Work.Diff.EXT.bCoordCLM (E := E) k (V i p)) S (τ, x) := by
    intro k i
    exact (((Work.Diff.EXT.bCoordCLM (E := E) k).contMDiffAt).comp (τ, x)
      (hVsmAt i)).contMDiffWithinAt
  -- the assembled sum, which is the pointwise formula for the frame matrix
  have hG : ContMDiffWithinAt ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ (Work.Diff.EXT.MatE (E := E))) (⊤ : ℕ∞)
      (fun p : ℝ × M => fun i j => ∑ k, ∑ l,
        A p.1 ((extChartAt I x₀) p.2) k l * Work.Diff.EXT.bCoordCLM (E := E) k (V i p) *
          Work.Diff.EXT.bCoordCLM (E := E) l (V j p)) S (τ, x) := by
    rw [contMDiffWithinAt_pi_space]
    intro i
    rw [contMDiffWithinAt_pi_space]
    intro j
    refine ContMDiffWithinAt.sum (t := Finset.univ) (f := fun k p => ∑ l,
      A p.1 ((extChartAt I x₀) p.2) k l * Work.Diff.EXT.bCoordCLM (E := E) k (V i p) *
        Work.Diff.EXT.bCoordCLM (E := E) l (V j p)) ?_
    intro k hk
    refine ContMDiffWithinAt.sum (t := Finset.univ) (f := fun l p =>
      A p.1 ((extChartAt I x₀) p.2) k l * Work.Diff.EXT.bCoordCLM (E := E) k (V i p) *
        Work.Diff.EXT.bCoordCLM (E := E) l (V j p)) ?_
    intro l hl
    exact ((hentry k l).mul (hcoord k i)).mul (hcoord l j)
  have hFG : ∀ p : ℝ × M, Work.Diff.EXT.frameMat (I := I) x p.2
        (Work.Diff.EXT.formInFrame (I := I) x₀ p.2
          (fun i j => A p.1 ((extChartAt I x₀) p.2) i j))
      = fun i j => ∑ k, ∑ l, A p.1 ((extChartAt I x₀) p.2) k l *
          Work.Diff.EXT.bCoordCLM (E := E) k (V i p) *
          Work.Diff.EXT.bCoordCLM (E := E) l (V j p) := by
    intro p
    funext i j
    rw [Work.Diff.EXT.frameMat]
    rw [Work.Diff.EXT.formInFrame_apply]
    rfl
  exact hG.congr_of_eventuallyEq (Filter.Eventually.of_forall hFG) (hFG (τ, x))

end Work.Diff.STE.Lead
