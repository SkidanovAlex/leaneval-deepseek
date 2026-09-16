import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.Harmonic.Analytic

open scoped BigOperators Topology

namespace Commons.Analysis.Complex

/-- Finite real-linear combinations (over a finset of parameters) of functions that are
harmonic in a neighborhood of a closed ball are again harmonic in a neighborhood of that
closed ball. -/
theorem harmonicOnNhd_finset_sum {a : ℂ} {R : ℝ} {s : Finset ℂ} {c : ℂ → ℝ}
    {h : ℂ → ℂ → ℝ}
    (hh : ∀ u ∈ s, InnerProductSpace.HarmonicOnNhd (fun z : ℂ => h u z)
      (Metric.closedBall a |R|)) :
    InnerProductSpace.HarmonicOnNhd
      (fun z : ℂ => ∑ u ∈ s, c u * h u z) (Metric.closedBall a |R|) := by
  classical
  let S : Set ℂ := Metric.closedBall a |R|
  let g : ℂ → ℂ → ℝ := fun u z => c u • h u z
  have hgS : ∀ u ∈ s, InnerProductSpace.HarmonicOnNhd (g u) S := by
    intro u hu
    have hhS : InnerProductSpace.HarmonicOnNhd (fun z : ℂ => h u z) S := by
      simpa [S] using hh u hu
    have hsmul : InnerProductSpace.HarmonicOnNhd ((c u) • (fun z : ℂ => h u z)) S :=
      hhS.const_smul
    change InnerProductSpace.HarmonicOnNhd (fun z : ℂ => c u • h u z) S
    exact hsmul
  have hG : InnerProductSpace.HarmonicOnNhd (∑ u ∈ s, g u) S := by
    refine Finset.sum_induction g (fun G : ℂ → ℝ => InnerProductSpace.HarmonicOnNhd G S)
      ?hom ?zero ?base
    · intro G H hG hH
      exact hG.add hH
    · exact InnerProductSpace.harmonicOnNhd_const (E := ℂ) (F := ℝ) (s := S) (c := (0 : ℝ))
    · exact hgS
  have hEq : (fun z : ℂ => ∑ u ∈ s, c u * h u z) = (∑ u ∈ s, g u) := by
    funext z
    simp [g, smul_eq_mul]
  simpa [S, hEq] using hG

end Commons.Analysis.Complex