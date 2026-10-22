import Mathlib
import Submission.Work.SINGMV.Defs

namespace Work.SingMV

theorem affineSimplex_comp {k l n : ℕ} (q : Fin (k+1) → Convexity.StdSimplex ℝ (Fin (n+1)))
    (p : Fin (l+1) → Convexity.StdSimplex ℝ (Fin (k+1))) :
    (Work.SingMV.affineSimplex q).comp (Work.SingMV.affineSimplex p) =
      Work.SingMV.affineSimplex (fun i => Work.SingMV.affineSimplex q (p i)) := by
  -- Both sides are continuous maps; compare them pointwise.
  apply ContinuousMap.ext
  intro x
  -- Unfolding `affineSimplex` reduces this to the corresponding identity for the underlying
  -- bundled affine maps `StdSimplex.affineMapMk`, which is `StdSimplex.comp_affineMapMk`.
  show Convexity.StdSimplex.affineMapMk (R := ℝ) q
      (Convexity.StdSimplex.affineMapMk (R := ℝ) p x) = _
  exact DFunLike.congr_fun (Convexity.StdSimplex.comp_affineMapMk (R := ℝ)
    (Convexity.StdSimplex.affineMapMk (R := ℝ) q) p) x

end Work.SingMV
