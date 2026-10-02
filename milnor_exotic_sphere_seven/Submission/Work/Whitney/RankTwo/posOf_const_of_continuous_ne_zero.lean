import Mathlib
import Submission.Work.Whitney.RankTwo.Cochains

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.Whitney.RankTwo

open Set

/-- A continuous nowhere-vanishing real function on the standard 2-simplex has the same sign at
both vertices: the simplex is (path) connected, so the image of `f` cannot meet both `Ioi 0`
and `Iio 0`. -/
theorem posOf_const_of_continuous_ne_zero {f : C(stdSimplex ℝ (Fin 2), ℝ)}
    (hf : ∀ q, f q ≠ 0) :
    (0 < f (stdSimplex.vertex (S := ℝ) (0 : Fin 2)))
      ↔ (0 < f (stdSimplex.vertex (S := ℝ) (1 : Fin 2))) := by
  have hpc : IsPreconnected (univ : Set ↥(stdSimplex ℝ (Fin 2))) := isPreconnected_univ
  have hcont : ContinuousOn (fun q : ↥(stdSimplex ℝ (Fin 2)) => f q) univ :=
    continuousOn_univ.mpr f.continuous
  rcases hpc.mapsTo_Ioi_or_Iio hcont (fun x _ => hf x) with h | h
  · exact ⟨fun _ => h (mem_univ _), fun _ => h (mem_univ _)⟩
  · refine ⟨fun h0 => ?_, fun h1 => ?_⟩
    · exact absurd h0 (not_lt.mpr (le_of_lt (h (mem_univ _))))
    · exact absurd h1 (not_lt.mpr (le_of_lt (h (mem_univ _))))

end Work.Whitney.RankTwo
