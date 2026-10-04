import Mathlib
import Submission.Work.Diff.EXT.ConnCov.ChartTowerDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.EXT.ConnCov

theorem fderiv_rmChartTower_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    (G : ℝ → Submission.Diff.SMet I M) (x₀ : M) (t : ℝ) (m : ℕ)
    (v : Fin m → Fin (Module.finrank ℝ E)) (a i j k l : Fin (Module.finrank ℝ E)) :
    (fun y : E => fderiv ℝ (fun y' : E => Work.Diff.EXT.ConnCov.rmChartTower (I := I) (M := M)
        G x₀ t m v i j k l y') y (Work.Diff.GE.cBasis (E := E) a))
      = fun y : E =>
          Work.Diff.EXT.ConnCov.rmChartTower (I := I) (M := M) G x₀ t (m + 1)
              (Fin.cons a v) i j k l y
          + (∑ r : Fin m, ∑ p : Fin (Module.finrank ℝ E),
              Work.Diff.GE.chrCoord (I := I) G x₀ p a (v r) t (Work.Diff.EXT.pt (I := I) x₀ y)
                * Work.Diff.EXT.ConnCov.rmChartTower (I := I) (M := M) G x₀ t m
                    (Function.update v r p) i j k l y)
          + (∑ p : Fin (Module.finrank ℝ E),
              Work.Diff.GE.chrCoord (I := I) G x₀ p a i t (Work.Diff.EXT.pt (I := I) x₀ y)
                * Work.Diff.EXT.ConnCov.rmChartTower (I := I) (M := M) G x₀ t m
                    v p j k l y)
          + (∑ p : Fin (Module.finrank ℝ E),
              Work.Diff.GE.chrCoord (I := I) G x₀ p a j t (Work.Diff.EXT.pt (I := I) x₀ y)
                * Work.Diff.EXT.ConnCov.rmChartTower (I := I) (M := M) G x₀ t m
                    v i p k l y)
          + (∑ p : Fin (Module.finrank ℝ E),
              Work.Diff.GE.chrCoord (I := I) G x₀ p a k t (Work.Diff.EXT.pt (I := I) x₀ y)
                * Work.Diff.EXT.ConnCov.rmChartTower (I := I) (M := M) G x₀ t m
                    v i j p l y)
          + (∑ p : Fin (Module.finrank ℝ E),
              Work.Diff.GE.chrCoord (I := I) G x₀ p a l t (Work.Diff.EXT.pt (I := I) x₀ y)
                * Work.Diff.EXT.ConnCov.rmChartTower (I := I) (M := M) G x₀ t m
                    v i j k p y) := by
  -- `rmChartTower` at level `m + 1` is, by definition, the chart derivative of the level-`m`
  -- array in the direction `v 0`, minus the five Christoffel contractions (`chrCoord`) of the
  -- coordinate frame.  The statement below is that very recursion, solved for the derivative:
  -- the level-`(m+1)` term is moved to the left (where it appears with the opposite sign) and the
  -- five contractions are added back on the right.
  funext y
  -- remove the harmless eta-expansion of the function whose `fderiv` is taken
  change (fderiv ℝ (Work.Diff.EXT.ConnCov.rmChartTower (I := I) (M := M)
      G x₀ t m v i j k l) y) (Work.Diff.GE.cBasis (E := E) a) = _
  -- the tail of `Fin.cons a v` is `v`
  have heta : (fun s : Fin m => v s) = v := rfl
  -- expand `rmChartTower` at level `m + 1` with the vector `Fin.cons a v`
  simp only [rmChartTower_succ, Fin.cons_zero, Fin.cons_succ, heta]
  -- now both sides are the same expression in the abelian group `ℝ`
  ring

end Work.Diff.EXT.ConnCov
