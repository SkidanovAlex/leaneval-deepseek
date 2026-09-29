import Mathlib
import Submission.Work.TMC7Core.Cocycle

/-!
# The rift of two `SL₂(ℂ)` matrices

`rift X W = ‖X W‖_F / (‖X‖_F ‖W‖_F)` is the normalised norm of the product; it lies in
`(0,1]` and equals `1` exactly when the two matrices are "perfectly aligned".  It measures how
much of the product of the two operator norms survives in the actual product, and is the
quantity that the avalanche principle linearises.
-/

open Matrix
open scoped Matrix.Norms.Frobenius

noncomputable section

namespace Work.TMC7Core.Avalanche

/-- The **rift** `R(X,W) = ‖X W‖_F / (‖X‖_F ‖W‖_F)` of two matrices. -/
def rift (X W : Matrix (Fin 2) (Fin 2) ℂ) : ℝ := frob (X * W) / (frob X * frob W)

end Work.TMC7Core.Avalanche
