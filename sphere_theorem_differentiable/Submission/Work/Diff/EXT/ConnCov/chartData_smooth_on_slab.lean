import Mathlib
import Submission.Work.Diff.EXT.ConnCov.ChartTowerDefs
import Submission.Work.Diff.EXT.ConnCov.reactJetsKit
import Submission.Work.Diff.EXT.ConnCov.rmChartTower_jets
import Submission.Work.Diff.EXT.ConnCov.sliceDeriv_contDiffAt
import Submission.Work.Diff.EXT.ConnCov.rmChartExpr_contDiffAt

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.EXT.ConnCov

theorem chartData_smooth_on_slab
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M]
    (G : ℝ → Submission.Diff.SMet I M) (σ T : ℝ) (Mm : ℕ) (x₀ : M) (K' : Set E)
    (hK't : K' ⊆ (extChartAt I x₀).target)
    (hjA : ∀ t ∈ Set.Ico σ T, ∀ y ∈ K', ∀ (i j l : Fin (Module.finrank ℝ E)),
      ContDiffAt ℝ (⊤ : ℕ∞)
        (fun p : ℝ × E => Work.Diff.EXT.aComp (I := I) (M := M) G x₀ p.1 p.2 i j l) (t, y)) :
    (∀ t ∈ Set.Ico σ T, ∀ y ∈ K', ∀ (m : ℕ), m ≤ Mm →
        ∀ (v : Fin m → Fin (Module.finrank ℝ E)) (i j k l : Fin (Module.finrank ℝ E)),
          ContDiffAt ℝ (⊤ : ℕ∞)
            (fun y' : E => Work.Diff.EXT.ConnCov.rmChartTower (I := I) (M := M) G x₀ t m v i j k l y') y)
      ∧ (∀ t ∈ Set.Ico σ T, ∀ y ∈ K', ∀ (i j l : Fin (Module.finrank ℝ E)),
          ContDiffAt ℝ (⊤ : ℕ∞)
            (fun y' : E => Work.Diff.EXT.ConnCov.reactArr (I := I) (M := M) G x₀ t y' i j l) y) := by
  classical
  -- ## The moving-curvature tower: every level is smooth in the chart coordinate.
  --
  -- The tower does not depend on `hjA` at all: `rmChartTower` is built from the chart curvature
  -- array `rmChartExpr` and the chart Christoffel symbols `chrCoord`, both of which are functions
  -- of the *single* smooth metric `G t`.  Hence the base case is
  -- `Work.Diff.EXT.ConnCov.rmChartExpr_contDiffAt`, and the recursion step is the observation that
  -- the chart derivative of a smooth function is smooth (`ContDiffAt.fderiv_right`) and that
  -- products/sums of smooth functions are smooth.
  have hmain1 : ∀ t ∈ Set.Ico σ T, ∀ y ∈ K', ∀ m : ℕ, m ≤ Mm →
      ∀ (v : Fin m → Fin (Module.finrank ℝ E)) (i j k l : Fin (Module.finrank ℝ E)),
        ContDiffAt ℝ (⊤ : ℕ∞)
          (fun y' : E => Work.Diff.EXT.ConnCov.rmChartTower (I := I) (M := M) G x₀ t m v i j k l y') y := by
    intro t ht y hy m
    induction m with
    | zero =>
      intro _ v i j k l
      simpa only [Work.Diff.EXT.ConnCov.rmChartTower_zero] using
        (Work.Diff.EXT.ConnCov.rmChartExpr_contDiffAt (I := I) (M := M) G x₀ t (hK't hy) i j k l)
    | succ m ih =>
      intro hm v i j k l
      have hmm : m ≤ Mm := by omega
      have hih := ih hmm
      -- the derivative term (the slice derivative of the level-`m` array)
      have hFd : ContDiffAt ℝ (⊤ : ℕ∞) (fun y' : E =>
          fderiv ℝ (fun y'' : E => Work.Diff.EXT.ConnCov.rmChartTower (I := I) (M := M) G x₀ t m
              (fun s : Fin m => v s.succ) i j k l y'') y'
            (Work.Diff.GE.cBasis (E := E) (v 0))) y :=
        ((hih (fun s : Fin m => v s.succ) i j k l).fderiv_right (by simp)).clm_apply contDiffAt_const
      -- the five Christoffel contractions
      have hS1 : ContDiffAt ℝ (⊤ : ℕ∞) (fun y' : E =>
          ∑ r : Fin m, ∑ p : Fin (Module.finrank ℝ E),
            Work.Diff.GE.chrCoord (I := I) G x₀ p (v 0) (v r.succ) t
                (Work.Diff.EXT.pt (I := I) x₀ y')
              * Work.Diff.EXT.ConnCov.rmChartTower (I := I) (M := M) G x₀ t m
                  (Function.update (fun s : Fin m => v s.succ) r p) i j k l y') y := by
        refine ContDiffAt.sum (s := Finset.univ) fun r _ =>
          ContDiffAt.sum (s := Finset.univ) fun p _ => ?_
        exact (chrCoord_contDiffAt (I := I) (M := M) G x₀ t (hK't hy) p (v 0) (v r.succ)).mul
          (hih (Function.update (fun s : Fin m => v s.succ) r p) i j k l)
      have hS2 : ContDiffAt ℝ (⊤ : ℕ∞) (fun y' : E =>
          ∑ p : Fin (Module.finrank ℝ E),
            Work.Diff.GE.chrCoord (I := I) G x₀ p (v 0) i t (Work.Diff.EXT.pt (I := I) x₀ y')
              * Work.Diff.EXT.ConnCov.rmChartTower (I := I) (M := M) G x₀ t m
                  (fun s : Fin m => v s.succ) p j k l y') y := by
        refine ContDiffAt.sum (s := Finset.univ) fun p _ => ?_
        exact (chrCoord_contDiffAt (I := I) (M := M) G x₀ t (hK't hy) p (v 0) i).mul
          (hih (fun s : Fin m => v s.succ) p j k l)
      have hS3 : ContDiffAt ℝ (⊤ : ℕ∞) (fun y' : E =>
          ∑ p : Fin (Module.finrank ℝ E),
            Work.Diff.GE.chrCoord (I := I) G x₀ p (v 0) j t (Work.Diff.EXT.pt (I := I) x₀ y')
              * Work.Diff.EXT.ConnCov.rmChartTower (I := I) (M := M) G x₀ t m
                  (fun s : Fin m => v s.succ) i p k l y') y := by
        refine ContDiffAt.sum (s := Finset.univ) fun p _ => ?_
        exact (chrCoord_contDiffAt (I := I) (M := M) G x₀ t (hK't hy) p (v 0) j).mul
          (hih (fun s : Fin m => v s.succ) i p k l)
      have hS4 : ContDiffAt ℝ (⊤ : ℕ∞) (fun y' : E =>
          ∑ p : Fin (Module.finrank ℝ E),
            Work.Diff.GE.chrCoord (I := I) G x₀ p (v 0) k t (Work.Diff.EXT.pt (I := I) x₀ y')
              * Work.Diff.EXT.ConnCov.rmChartTower (I := I) (M := M) G x₀ t m
                  (fun s : Fin m => v s.succ) i j p l y') y := by
        refine ContDiffAt.sum (s := Finset.univ) fun p _ => ?_
        exact (chrCoord_contDiffAt (I := I) (M := M) G x₀ t (hK't hy) p (v 0) k).mul
          (hih (fun s : Fin m => v s.succ) i j p l)
      have hS5 : ContDiffAt ℝ (⊤ : ℕ∞) (fun y' : E =>
          ∑ p : Fin (Module.finrank ℝ E),
            Work.Diff.GE.chrCoord (I := I) G x₀ p (v 0) l t (Work.Diff.EXT.pt (I := I) x₀ y')
              * Work.Diff.EXT.ConnCov.rmChartTower (I := I) (M := M) G x₀ t m
                  (fun s : Fin m => v s.succ) i j k p y') y := by
        refine ContDiffAt.sum (s := Finset.univ) fun p _ => ?_
        exact (chrCoord_contDiffAt (I := I) (M := M) G x₀ t (hK't hy) p (v 0) l).mul
          (hih (fun s : Fin m => v s.succ) i j k p)
      -- assemble the recursion step
      have hmain : ContDiffAt ℝ (⊤ : ℕ∞) (fun y' : E =>
          fderiv ℝ (fun y'' : E => Work.Diff.EXT.ConnCov.rmChartTower (I := I) (M := M) G x₀ t m
              (fun s : Fin m => v s.succ) i j k l y'') y'
            (Work.Diff.GE.cBasis (E := E) (v 0))
          - (∑ r : Fin m, ∑ p : Fin (Module.finrank ℝ E),
            Work.Diff.GE.chrCoord (I := I) G x₀ p (v 0) (v r.succ) t
                (Work.Diff.EXT.pt (I := I) x₀ y')
              * Work.Diff.EXT.ConnCov.rmChartTower (I := I) (M := M) G x₀ t m
                  (Function.update (fun s : Fin m => v s.succ) r p) i j k l y')
          - (∑ p : Fin (Module.finrank ℝ E),
            Work.Diff.GE.chrCoord (I := I) G x₀ p (v 0) i t (Work.Diff.EXT.pt (I := I) x₀ y')
              * Work.Diff.EXT.ConnCov.rmChartTower (I := I) (M := M) G x₀ t m
                  (fun s : Fin m => v s.succ) p j k l y')
          - (∑ p : Fin (Module.finrank ℝ E),
            Work.Diff.GE.chrCoord (I := I) G x₀ p (v 0) j t (Work.Diff.EXT.pt (I := I) x₀ y')
              * Work.Diff.EXT.ConnCov.rmChartTower (I := I) (M := M) G x₀ t m
                  (fun s : Fin m => v s.succ) i p k l y')
          - (∑ p : Fin (Module.finrank ℝ E),
            Work.Diff.GE.chrCoord (I := I) G x₀ p (v 0) k t (Work.Diff.EXT.pt (I := I) x₀ y')
              * Work.Diff.EXT.ConnCov.rmChartTower (I := I) (M := M) G x₀ t m
                  (fun s : Fin m => v s.succ) i j p l y')
          - (∑ p : Fin (Module.finrank ℝ E),
            Work.Diff.GE.chrCoord (I := I) G x₀ p (v 0) l t (Work.Diff.EXT.pt (I := I) x₀ y')
              * Work.Diff.EXT.ConnCov.rmChartTower (I := I) (M := M) G x₀ t m
                  (fun s : Fin m => v s.succ) i j k p y')) y :=
        ((((hFd.sub hS1).sub hS2).sub hS3).sub hS4).sub hS5
      simpa only [Work.Diff.EXT.ConnCov.rmChartTower_succ] using hmain
  -- ## The reaction array: `reactArr = ∂_t aComp` is the slice derivative of a jointly `C^∞`
  -- function, hence smooth in the chart coordinate.
  have hmain2 : ∀ t ∈ Set.Ico σ T, ∀ y ∈ K', ∀ (i j l : Fin (Module.finrank ℝ E)),
      ContDiffAt ℝ (⊤ : ℕ∞)
        (fun y' : E => Work.Diff.EXT.ConnCov.reactArr (I := I) (M := M) G x₀ t y' i j l) y := by
    intro t ht y hy i j l
    have h := Work.Diff.EXT.ConnCov.sliceDeriv_contDiffAt (E := E)
      (A := fun p : ℝ × E => Work.Diff.EXT.aComp (I := I) (M := M) G x₀ p.1 p.2 i j l)
      (t := t) (y := y) (hjA t ht y hy i j l)
    simpa only [Work.Diff.EXT.ConnCov.reactArr] using h
  exact ⟨hmain1, hmain2⟩

end Work.Diff.EXT.ConnCov
