import Mathlib
import Submission.Commons.Analysis.Calculus.ContDiff.crossProduct

open scoped Matrix

namespace Commons.Analysis.CrossProduct

/-- The cross product `p.1 ⨯₃ p.2` on `EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)`,
transported through the `WithLp` equivalence, is a smooth (`C^∞`) map. -/
theorem cross3_contDiff :
    ContDiff ℝ ⊤ (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
      WithLp.toLp 2 (WithLp.ofLp p.1 ⨯₃ WithLp.ofLp p.2)) := by
  let E : Type := EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)
  have hu : ContDiffOn ℝ ⊤ (fun p : E => p.1) Set.univ :=
    (contDiff_fst (𝕜 := ℝ) (n := ⊤) (E := EuclideanSpace ℝ (Fin 3))
      (F := EuclideanSpace ℝ (Fin 3))).contDiffOn
  have hv : ContDiffOn ℝ ⊤ (fun p : E => p.2) Set.univ :=
    (contDiff_snd (𝕜 := ℝ) (n := ⊤) (E := EuclideanSpace ℝ (Fin 3))
      (F := EuclideanSpace ℝ (Fin 3))).contDiffOn
  exact contDiffOn_univ.mp
    (Commons.Analysis.Calculus.ContDiff.crossProduct (E := E) (s := Set.univ) (n := ⊤)
      (u := fun p : E => p.1) (v := fun p : E => p.2) hu hv)

end Commons.Analysis.CrossProduct
