import Mathlib
import Submission.Work.LinnikAreas.JutilaPieces.S3ModelDefs
import Submission.Work.ZeroDensity.Jutila.Bz3Defs
import Submission.Work.ZeroDensity.Jutila.Bz3Reduce
import Submission.Work.LinnikAreas.JutilaPieces.S3ModelAux

namespace Work.LinnikAreas.JutilaPieces

theorem S3ModelDS (z N : ℕ) :
    Work.ZeroDensity.Jutila.s3cont z N
      = (Real.pi ^ 2 / 6)⁻¹ *
          ∑ q ∈ Finset.Icc 1 (N / z),
            ((N : ℝ) / (q : ℝ)) *
              Work.LinnikAreas.JutilaPieces.s3DSabs (Work.LinnikAreas.JutilaPieces.Qf z N q)
                (N / (q * z)) := by sorry

end Work.LinnikAreas.JutilaPieces
