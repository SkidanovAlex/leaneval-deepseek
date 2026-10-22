import Mathlib
import Submission.Work.SINGMV.Defs

namespace Work.SingMV

theorem affineSimplex_subBarycenter {k n : ℕ} (q : Fin (k+1) → Convexity.StdSimplex ℝ (Fin (n+1)))
    (A : Finset (Fin (k+1))) (hA : A.Nonempty) :
    Work.SingMV.affineSimplex q (Convexity.StdSimplex.subBarycenter A hA) =
      Convexity.iConvexComb (R := ℝ) (Convexity.StdSimplex.subBarycenter A hA) q :=
  -- `affineSimplex q` is the bundled affine map `StdSimplex.affineMapMk q`, whose value
  -- at `s` is by definition the convex combination `iConvexComb s q`; the equality is
  -- therefore definitional.
  rfl

end Work.SingMV
